//! The faceted candidate's planar faces, made in one B-rep then stitched with the existing
//! native topology API. Every face receives ALL of its loops together, so holes remain holes.
//! This builds geometry only; ops finish and original-source reconstruction certification are
//! mandatory. Neither stitching nor source face normals are an acceptance proof.
//! Planes use a source endpoint origin and unit UV; holes stay in their supplied order.
//! This is candidate construction, not exactness certification or a theorem retry.
//!
use crate::curve::{curve::Curve, line::Line};
use crate::error::EntityRef;
use crate::eval::Frame;
use crate::geom::{extent2d::Extent2d, tol::USE_DEFAULT};
use crate::kernel::Kernel;
use crate::math::{Vec2, Vec3};
use crate::nurbs::b_spline_surface_n_lib::p2::OrientType;
use crate::query::brep::BrepIdentity;
use crate::surface::{plane::Plane, surface::Surface};
use crate::topology::brep::{
    p2::{caller_cache_key, ArenaNotifyState},
    p3::new_brep,
    p5::{stitch_and_orient_with_identity, StitchAndOrientOptions},
    p7::{make_face_with_curves, FaceCurvesInput},
};
use crate::topology::{Brep, FaceId};

use super::faceted::{FacetedFace, FacetedPlan, NativeEdge};
use super::frame::FrameGeometry;
use super::numeric::Vec3Numeric;
use super::types::{invalid, MeshError, Result};

const OP: &str = "mesh_reconstruction::build_faceted";
const MAX_FACES: usize = 50_000;
const MAX_EDGES: usize = 150_000;

fn finite_chart(domain: &Extent2d) -> bool {
    domain.is_bounded()
        && [
            domain.u_min(),
            domain.v_min(),
            domain.u_max(),
            domain.v_max(),
        ]
        .iter()
        .all(|v| v.is_finite())
        && domain.u_min() < domain.u_max()
        && domain.v_min() < domain.v_max()
        && domain.x_length().is_finite()
        && domain.y_length().is_finite()
}

/// Choose ONE source-anchored unit-scale parameter chart, before constructing
/// any native face. The normal/loops are planning data, never acceptance proof.
/// No bounding-sphere origin, fitted plane, normalization of UV coordinates or
/// tolerance padding is used. Every final face is still checked by the caller.
fn source_plane(k: &Kernel, face: &FacetedFace) -> Result<(Plane, Extent2d)> {
    k.check_cancelled(OP)?;
    let first = face
        .loops
        .first()
        .and_then(|wire| wire.first())
        .ok_or_else(|| invalid("a faceted face has no source anchor"))?;
    let NativeEdge::Line { a: origin, .. } = *first;
    if !origin.is_finite() || !face.normal.is_finite() {
        return Err(invalid("a faceted face anchor and normal must be finite"));
    }
    let frame = <Frame as FrameGeometry>::from_normal(origin, face.normal)
        .ok_or_else(|| invalid("a faceted face has no finite nondegenerate frame"))?;
    let mut domain = Extent2d::new();
    for wire in &face.loops {
        for edge in wire {
            k.check_cancelled(OP)?;
            let NativeEdge::Line { a, b } = *edge;
            for point in [a, b] {
                if !point.is_finite() {
                    return Err(invalid("a faceted endpoint must be finite"));
                }
                let uv = frame.to_local(point);
                if !(uv.x.is_finite() && uv.y.is_finite()) {
                    return Err(invalid("a faceted chart projection overflowed"));
                }
                domain.add_point(uv);
            }
        }
    }
    if !finite_chart(&domain) {
        return Err(invalid("a faceted face needs a finite nondegenerate chart"));
    }
    let mut plane = Plane::new(
        origin,
        Vec3::from_array(frame.x_axis),
        Vec3::from_array(frame.y_axis),
        Vec2::new(1., 1.),
        &domain,
    );
    // Plane owns its canonical placement. Bound in THAT stored placement,
    // rather than assuming its canonicalization kept the proposed axes bitwise.
    // The fresh Plane has no NURB; its final finite domain is set before first use.
    let mut actual_domain = Extent2d::new();
    for wire in &face.loops {
        for edge in wire {
            k.check_cancelled(OP)?;
            let NativeEdge::Line { a, b } = *edge;
            for point in [a, b] {
                let uv = plane.project_point_to_uv_domain(point);
                if !(uv.x.is_finite() && uv.y.is_finite()) {
                    return Err(invalid("a stored faceted chart projection overflowed"));
                }
                actual_domain.add_point(uv);
            }
        }
    }
    if !finite_chart(&actual_domain) {
        return Err(invalid("a stored faceted chart is unbounded or degenerate"));
    }
    plane.update_analytical_domain(&actual_domain);
    Ok((plane, actual_domain))
}

/// Make a candidate with each coplanar group's source loops intact, then sew coincident
/// boundaries using the native stitch/orient operation. No face or hole is independently
/// filled; the planar face builder receives the complete nested loop family at once.
///
/// # Errors
/// Empty/invalid plan, work budget exhaustion, cancellation, or native construction refusal.
pub fn build_faceted(k: &mut Kernel, plan: &FacetedPlan) -> Result<Brep> {
    k.check_cancelled(OP)?;
    if plan.faces.is_empty() {
        return Err(invalid("a faceted plan has no faces"));
    }
    if plan.faces.len() > MAX_FACES {
        return Err(MeshError::BudgetExceeded {
            stage: OP,
            limit: MAX_FACES,
        });
    }
    // Each valid directed loop has edges. Bound even an inventory of empty
    // containers BEFORE traversing it; the existing edge cap already implies
    // this loop bound, so no valid class receives a smaller budget.
    let mut loop_count = 0usize;
    for face in &plan.faces {
        k.check_cancelled(OP)?;
        if face.loops.is_empty() {
            return Err(invalid("a faceted face has an empty boundary"));
        }
        loop_count = loop_count
            .checked_add(face.loops.len())
            .ok_or(MeshError::BudgetExceeded {
                stage: OP,
                limit: MAX_EDGES,
            })?;
        if loop_count > MAX_EDGES {
            return Err(MeshError::BudgetExceeded {
                stage: OP,
                limit: MAX_EDGES,
            });
        }
    }
    let mut edge_count = 0usize;
    for face in &plan.faces {
        for wire in &face.loops {
            k.check_cancelled(OP)?;
            if wire.len() < 3 {
                return Err(invalid(
                    "a faceted directed loop needs at least three edges",
                ));
            }
            edge_count = edge_count
                .checked_add(wire.len())
                .ok_or(MeshError::BudgetExceeded {
                    stage: OP,
                    limit: MAX_EDGES,
                })?;
            if edge_count > MAX_EDGES {
                return Err(MeshError::BudgetExceeded {
                    stage: OP,
                    limit: MAX_EDGES,
                });
            }
            for (edge, next) in wire.iter().zip(wire.iter().skip(1).chain(wire.first())) {
                k.check_cancelled(OP)?;
                let (NativeEdge::Line { b, .. }, NativeEdge::Line { a, .. }) = (edge, next);
                if b.to_array() != a.to_array() {
                    return Err(invalid("a faceted directed loop is not exactly closed"));
                }
            }
        }
    }
    let mut body = new_brep(k, USE_DEFAULT, USE_DEFAULT)?;
    let region = body.infinite_region();
    let mut state = ArenaNotifyState::new(&body);
    let mut env = state.env(None);
    let this_face = |face: FaceId| crate::topology::loopuse::notify_ref(EntityRef::Face(face));
    for face in &plan.faces {
        k.check_cancelled(OP)?;
        let (plane, domain) = source_plane(k, face)?;
        let count = face
            .loops
            .iter()
            .map(Vec::len)
            .try_fold(0usize, usize::checked_add)
            .ok_or(MeshError::BudgetExceeded {
                stage: OP,
                limit: MAX_EDGES,
            })?;
        let mut loops = Vec::new();
        let mut curves = Vec::new();
        let mut orientations = Vec::new();
        loops
            .try_reserve_exact(face.loops.len())
            .map_err(|_| invalid("faceted loop storage allocation refused"))?;
        curves
            .try_reserve_exact(count)
            .map_err(|_| invalid("faceted curve storage allocation refused"))?;
        orientations
            .try_reserve_exact(count)
            .map_err(|_| invalid("faceted orientation storage allocation refused"))?;
        for wire in &face.loops {
            loops.push(wire.len());
            for edge in wire {
                k.check_cancelled(OP)?;
                let NativeEdge::Line { a, b } = *edge;
                curves.push(Some(Curve::from(Line::create_line_segment(3, a, b, None)?)));
                orientations.push(OrientType::Same);
            }
        }
        let input = FaceCurvesInput {
            loops,
            curves_3d: Some(curves),
            uv_curves: None,
            orientations,
            loop_points: Vec::new(),
        };
        let made = make_face_with_curves(
            k,
            &mut body,
            region,
            input,
            Surface::from(plane),
            &domain,
            OrientType::Same,
            None,
            &this_face,
            &mut env,
        )?;
        if made.face.is_none() {
            return Err(invalid("a faceted boundary made no planar face"));
        }
    }
    // Preserve the face-builder notification identities while native stitching consults its
    // geometry owners. This is the same existing path used by native primitive construction.
    let keys = |object| caller_cache_key(env.key_of, object);
    stitch_and_orient_with_identity(
        k,
        &mut body,
        &StitchAndOrientOptions::default(),
        Some(BrepIdentity {
            keys: &keys,
            ..BrepIdentity::default()
        }),
    )?;
    body.refresh_cached_topology();
    // Sewing establishes the actual shell/region containment tree. A solid intent
    // must then alternate material/void through THAT tree, including cavities;
    // independently marking each sewn shell as material loses nested voids.
    if crate::topology::brep::p2::is_manifold_solid(&body)? {
        crate::topology::brep::p1::set_region_is_void_flags_for_nested_solids(k, &mut body)?;
    }
    k.check_cancelled(OP)?;
    Ok(body)
}
