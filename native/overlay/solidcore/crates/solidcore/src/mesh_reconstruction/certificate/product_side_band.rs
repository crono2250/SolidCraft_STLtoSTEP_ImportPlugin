//! Full actual natural-rectangle side to the SAME common product model.
//!
//! The actual evaluator band (not a family label/net approximation) is bound by
//! pointer to the immutable face definition. Net families require the strict raw
//! UV rectangle. Plane instead binds ALL actual affine UV roots to one exact
//! coherent rectangular parameter/CW witness in unchanged native zones; a chosen
//! layout alone is never a certificate. Its low/high native edges must be
//! precisely the actual cap uses of the proved common model. Every positive
//! rational ruling-base root is covered once; every source/model cell of that
//! complete cap edge is paired once in order. Whole paired Bernstein bounds plus
//! the authoritative ruling residual cover BOTH set directions on the FULL side.
//!
//! This is a side support/trim band, not a complete solid certificate. The two
//! filled caps and
//! complete nativeCW/material correspondence remain obligations of its consumer.
//! In particular a successful side token never authorizes body adoption alone.
//! A separate required sign proof uses the SAME sewn cap model and exact D;
//! the projected cached-net profile cannot substitute for that common model.
//! Existing native net/Plane derivative signs are retained independently; neither
//! scalar claims generic native API-normal repair correctness.
//! Whole actual derivative numerators also preserve each original source side
//! outward normal, accounting for native faceuse and source-rim orientations.
//! Generator model endpoints are the SAME proved cap points in their native vertex
//! balls; every complete actual generator curve is bounded in its unchanged tube.
//! Net-evaluator families retain their full net proof. Constant-radius Cylinder
//! additionally retains its full actual evaluator value authority. Plane uses
//! its actual affine definition and a bounded positive bilinear proxy, not a net flag.
//! Deviations: none. Degree1..8; full-multiplicity positive roots; shared `MeshWork`.
use super::super::actual_roots::actual_used_roots;
use super::super::work::MeshWork;
use super::actual_ruling::{actual_ruling_rectangle_with_work, ActualRulingBand};
use super::exact_geometry as x;
use super::exact_planar::affine_ends;
use super::hulls::{paired_curve_upper, CurveBounds, PointBox};
use super::native_profile::NativeProfile;
use super::plane_trim_image::affine_plane_pair_with_work;
use super::product_profiles::ProductProfiles;
use super::rectangular_trim::{
    prove_rectangular_trim_with_work, rectangle_layout_claim_with_work, RectangleLayout,
};
use super::sewn_curve::{enclose_controls_with_work, ProjectivePoint};
use crate::blend::fillet_section::interval::Ivl;
use crate::geom::tol::zone_tol3d;
use crate::nurbs::b_spline_surface_n_lib::p2::OrientType;
use crate::surface::{plane::Plane, surface::SurfaceKind};
use crate::topology::{edge, edgeuse::p1 as eu, vertex, Brep, EdgeId, FaceId, FaceuseId, VertexId};
use crate::{Kernel, Result, SolidError};
use std::collections::{BTreeMap, BTreeSet};
const OP: &str = "mesh_reconstruction::certificate::product_side_band";
fn refused(reason: &'static str) -> SolidError {
    SolidError::Unsupported {
        operation: OP,
        reason,
    }
}
fn invariant(reason: &'static str) -> SolidError {
    SolidError::PortInvariant {
        operation: OP,
        reason,
    }
}
/// One ordered part of an actual ruling-base root, on exact stored unit parameters.
/// Claims can steer the pairing; complete single coverage and whole errors are proved.
pub(crate) struct BandCellClaim {
    pub(crate) root: usize,
    pub(crate) unit: [f64; 2],
}
pub(crate) struct ProductSideBand<'p, 'l, 'ld, 'ud, 'g, 's, 'raw> {
    profiles: &'p ProductProfiles<'l, 'ld, 'ud, 'g, 's, 'raw>,
    actual: ActualRulingBand<'g>,
    rectangle: RectangleLayout<'g>,
    low_edge: EdgeId,
    high_edge: EdgeId,
    source_actual_upper: f64,
    model_definition_upper: f64,
    generator_error_upper: f64,
    orientation_numerator_lower: f64,
    model_orientation_numerator_lower: f64,
    actual_uv_model_upper: f64,
}
impl<'p, 'l, 'ld, 'ud, 'g, 's, 'raw> ProductSideBand<'p, 'l, 'ld, 'ud, 'g, 's, 'raw> {
    pub(crate) fn profiles(&self) -> &'p ProductProfiles<'l, 'ld, 'ud, 'g, 's, 'raw> {
        self.profiles
    }
    pub(crate) fn actual(&self) -> &ActualRulingBand<'g> {
        &self.actual
    }
    pub(crate) fn rectangle(&self) -> &RectangleLayout<'g> {
        &self.rectangle
    }
    pub(crate) fn cap_edges(&self) -> [EdgeId; 2] {
        [self.low_edge, self.high_edge]
    }
    pub(crate) fn source_actual_upper(&self) -> f64 {
        self.source_actual_upper
    }
    pub(crate) fn orientation_numerator_lower(&self) -> f64 {
        self.orientation_numerator_lower
    }
    /// Complete orientation of the SAME sewn common model, not a cached net.
    pub(crate) fn model_orientation_numerator_lower(&self) -> f64 {
        self.model_orientation_numerator_lower
    }
    pub(crate) fn actual_uv_model_upper(&self) -> f64 {
        self.actual_uv_model_upper
    }
    pub(crate) fn generator_error_upper(&self) -> f64 {
        self.generator_error_upper
    }
    pub(crate) fn model_definition_upper(&self) -> f64 {
        self.model_definition_upper
    }
}
fn equal(a: &x::E, b: f64) -> bool {
    x::scalar(b)
        .and_then(|b| x::sub(a, &b))
        .is_some_and(|d| x::zero(&d))
}
/// Exact positive full-multiplicity root controls; no rounded knot insertion or
/// reuse of the display surface. Each control is already the exact band witness.
fn roots(
    k: &Kernel,
    work: &MeshWork,
    actual: &ActualRulingBand<'_>,
) -> Result<Vec<Vec<ProjectivePoint>>> {
    let band = actual.band();
    let p = band.profile_degree;
    if !(1..=8).contains(&p) {
        return Err(refused("side profile degree outside certified class"));
    }
    let mut groups: Vec<(f64, usize)> = Vec::new();
    for &v in &band.profile_knots {
        work.spend_core(k, 1)?;
        if !v.is_finite() || groups.last().is_some_and(|&(old, _)| old > v) {
            return Err(invariant("certified ruling profile knots invalid"));
        }
        if let Some((old, count)) = groups.last_mut() {
            if *old == v {
                *count = count
                    .checked_add(1)
                    .ok_or_else(|| refused("knot multiplicity overflow"))?;
                continue;
            }
        }
        work.reserve_cells_core(k, 1)?;
        groups.push((v, 1));
    }
    let (Some(&(lo, lc)), Some(&(hi, hc))) = (groups.first(), groups.last()) else {
        return Err(refused("side profile domain missing"));
    };
    if !(lo < hi && lc == p + 1 && hc == p + 1)
        || groups
            .iter()
            .skip(1)
            .take(groups.len().saturating_sub(2))
            .any(|&(_, m)| m != p)
    {
        return Err(refused(
            "side profile needs complete exact Bezier root partition",
        ));
    }
    let n = groups
        .len()
        .checked_sub(1)
        .ok_or_else(|| invariant("side root count underflow"))?;
    let expected = n
        .checked_mul(p)
        .and_then(|n| n.checked_add(1))
        .ok_or_else(|| refused("side control count overflow"))?;
    if expected != band.base_controls.len() {
        return Err(invariant(
            "certified ruling root/control count inconsistent",
        ));
    }
    let mut out = Vec::new();
    for i in 0..n {
        let start = i
            .checked_mul(p)
            .ok_or_else(|| refused("side control offset overflow"))?;
        let end = start
            .checked_add(p + 1)
            .ok_or_else(|| refused("side control range overflow"))?;
        let data = band
            .base_controls
            .get(start..end)
            .ok_or_else(|| invariant("side root controls absent"))?;
        let mut row = Vec::new();
        for [a, b, c, w] in data {
            work.spend_core(k, 1)?;
            if x::sign(w) != Some(1) {
                return Err(invariant("certified ruling weight not positive"));
            }
            work.reserve_cells_core(k, 1)?;
            row.push(ProjectivePoint {
                xyz: [a.clone(), b.clone(), c.clone()],
                w: w.clone(),
            });
        }
        work.reserve_cells_core(k, 1)?;
        out.push(row);
    }
    Ok(out)
}
fn native<T>(k: &Kernel, work: &MeshWork, r: super::super::Result<T>) -> Result<T> {
    work.spend_core(k, 0)?;
    match r {
        Ok(v) => Ok(v),
        Err(super::super::MeshError::Kernel(e)) => Err(e),
        Err(
            super::super::MeshError::Undecided { .. } | super::super::MeshError::Refused { .. },
        ) => Err(refused("actual cap root extraction unresolved")),
        Err(_) => Err(invariant(
            "actual cap root extraction returned unexpected failure",
        )),
    }
}
// Equality is of exact PROJECTIVE POINTS, not of whole curves or weights.
fn same_point(a: &ProjectivePoint, b: &ProjectivePoint) -> bool {
    a.xyz.iter().zip(&b.xyz).all(|(a0, b0)| {
        x::mul(a0, &b.w)
            .and_then(|v| x::sub(&v, &x::mul(b0, &a.w)?))
            .is_some_and(|v| x::zero(&v))
    })
}
fn cap_vertices(
    k: &Kernel,
    work: &MeshWork,
    profile: &NativeProfile<'_, '_, '_, '_>,
    rim: usize,
    usage: usize,
    vertices: &mut BTreeMap<VertexId, ProjectivePoint>,
) -> Result<()> {
    let draft = profile.draft();
    let graph = draft
        .graphs()
        .get(rim)
        .ok_or_else(|| invariant("proven cap graph missing"))?;
    let patch = draft
        .complex()
        .patches
        .get(draft.patch())
        .ok_or_else(|| invariant("proven cap patch missing"))?;
    let target = patch
        .rims
        .get(rim)
        .and_then(|r| r.get(usage))
        .ok_or_else(|| invariant("proven cap edge use missing"))?;
    let mut first = None;
    let mut last = None;
    for (i, cell) in graph.cells.iter().enumerate() {
        work.spend_core(k, 1)?;
        if cell.claim.curve == usage {
            if first.is_none() {
                first = Some(i);
            }
            last = Some(i);
        }
    }
    let controls = profile
        .controls_3d()
        .get(rim)
        .ok_or_else(|| invariant("proven cap controls missing"))?;
    let a = first
        .and_then(|i| controls.get(i))
        .and_then(|r| r.first())
        .ok_or_else(|| invariant("proven cap model start missing"))?;
    let z = last
        .and_then(|i| controls.get(i))
        .and_then(|r| r.last())
        .ok_or_else(|| invariant("proven cap model end missing"))?;
    for (vertex, p) in [(target.start, a), (target.end, z)] {
        work.spend_core(k, 1)?;
        if let Some(old) = vertices.get(&vertex) {
            if !same_point(old, p) {
                return Err(refused(
                    "actual common cap vertex has incompatible chosen model points",
                ));
            }
        } else {
            work.reserve_cells_core(k, 1)?;
            vertices.insert(
                vertex,
                ProjectivePoint {
                    xyz: p.xyz.clone(),
                    w: p.w.clone(),
                },
            );
        }
    }
    Ok(())
}
// A degree1 model at an exact native t. Homogeneous integer-scaled arithmetic
// retains the precise affine fraction even if (t-a)/(b-a) is not an f64.
fn segment_at(
    p: &ProjectivePoint,
    q: &ProjectivePoint,
    a: f64,
    b: f64,
    t: f64,
) -> Option<ProjectivePoint> {
    let a = x::scalar(a)?;
    let b = x::scalar(b)?;
    let t = x::scalar(t)?;
    let d = x::sub(&b, &a)?;
    let sign = x::sign(&d)?;
    if sign == 0 {
        return None;
    }
    let left = x::scale(&x::sub(&b, &t)?, f64::from(sign))?;
    let right = x::scale(&x::sub(&t, &a)?, f64::from(sign))?;
    if x::sign(&left)? < 0 || x::sign(&right)? < 0 {
        return None;
    }
    let w = x::mul(&x::mul(&p.w, &q.w)?, &x::scale(&d, f64::from(sign))?)?;
    if x::sign(&w) != Some(1) {
        return None;
    }
    let mut xyz = Vec::new();
    for (p0, q0) in p.xyz.iter().zip(&q.xyz) {
        xyz.push(x::add(
            &x::mul(&x::mul(p0, &q.w)?, &left)?,
            &x::mul(&x::mul(q0, &p.w)?, &right)?,
        )?);
    }
    let [Some(a), Some(b), Some(c)] = [xyz.first(), xyz.get(1), xyz.get(2)] else {
        return None;
    };
    Some(ProjectivePoint {
        xyz: [a.clone(), b.clone(), c.clone()],
        w,
    })
}
fn translated(a: &ProjectivePoint, b: &ProjectivePoint, d: &x::P) -> bool {
    a.xyz.iter().zip(&b.xyz).zip(d).all(|((a0, b0), d0)| {
        x::mul(b0, &a.w)
            .and_then(|v| x::sub(&v, &x::mul(a0, &b.w)?))
            .and_then(|v| x::sub(&v, &x::mul(d0, &x::mul(&a.w, &b.w)?)?))
            .is_some_and(|v| x::zero(&v))
    })
}
fn generator_bound(
    k: &Kernel,
    work: &MeshWork,
    b: &Brep,
    trim: &RectangleLayout<'_>,
    caps: [EdgeId; 2],
    direction: &x::P,
    vertices: &BTreeMap<VertexId, ProjectivePoint>,
) -> Result<f64> {
    let mut upper = 0.0_f64;
    for usage in &trim.edges {
        work.spend_core(k, 1)?;
        if caps.contains(&usage.edge) {
            continue;
        }
        let record = b.edgeuse(usage.use_id)?;
        let (Some(a), Some(z)) = edge::start_end_vertices(b, usage.edge)? else {
            return Err(refused("actual generator endpoints missing"));
        };
        let forward = match record.orientation {
            OrientType::Same => true,
            OrientType::Opposite => false,
            OrientType::Unknown => return Err(refused("actual generator use sense unresolved")),
        };
        let (a, z) = if forward { (a, z) } else { (z, a) };
        let a = vertices
            .get(&a)
            .ok_or_else(|| refused("actual generator start is not a common cap vertex"))?;
        let z = vertices
            .get(&z)
            .ok_or_else(|| refused("actual generator end is not a common cap vertex"))?;
        if !translated(a, z, direction) && !translated(z, a, direction) {
            return Err(refused(
                "actual generator endpoints do not bind the same exact common product join",
            ));
        }
        let curve =
            edge::curve(b, usage.edge)?.ok_or_else(|| refused("actual generator curve missing"))?;
        let used = edge::interval(b, usage.edge)?;
        let roots = native(k, work, actual_used_roots(k, work, curve, used, forward))?;
        let start = roots
            .first()
            .and_then(|r| r.native_interval.first())
            .copied()
            .ok_or_else(|| refused("actual generator root partition empty"))?;
        let finish = roots
            .last()
            .and_then(|r| r.native_interval.get(1))
            .copied()
            .ok_or_else(|| invariant("actual generator final parameter missing"))?;
        let mut end = start;
        let mut edge_upper = 0.0_f64;
        for root in &roots {
            work.spend_core(k, 1)?;
            let [ta, tz] = root.native_interval;
            if ta != end {
                return Err(invariant("actual generator root partition not contiguous"));
            }
            work.reserve_cells_core(k, 2)?;
            let ma = segment_at(a, z, start, finish, ta).ok_or_else(|| {
                refused("exact model generator parameter outside arithmetic range")
            })?;
            let mz = segment_at(a, z, start, finish, tz).ok_or_else(|| {
                refused("exact model generator parameter outside arithmetic range")
            })?;
            let model = enclose_controls_with_work(k, work, &[ma, mz], &root.piece)?
                .ok_or_else(|| refused("complete model generator cannot be enclosed"))?;
            edge_upper = edge_upper.max(paired_curve_upper(&root.piece, &model, 0., 0.)?);
            end = tz;
        }
        let radius = zone_tol3d(k, edge::tolerance(b, usage.edge)?);
        if !radius.is_finite() || radius <= 0. || edge_upper > radius {
            return Err(refused(
                "full common generator exceeds unchanged native edge tube",
            ));
        }
        upper = upper.max(edge_upper);
    }
    Ok(upper)
}
fn outward_normal(
    graph: &super::super::profile_chain::ChainGraphCover<'_>,
    cell: usize,
    direction: &x::P,
    sense: i32,
) -> Result<[Ivl; 3]> {
    let cell = graph
        .cells
        .get(cell)
        .ok_or_else(|| invariant("proved source side cell missing"))?;
    let i = cell.claim.source_edge;
    let a = graph
        .source
        .get(i)
        .ok_or_else(|| invariant("proved source edge start missing"))?;
    let next = i
        .checked_add(1)
        .ok_or_else(|| invariant("proved source edge overflow"))?;
    let z = graph
        .source
        .get(next)
        .or_else(|| graph.source.first())
        .ok_or_else(|| invariant("proved source edge end missing"))?;
    let n = x::difference(z, a)
        .and_then(|d| x::cross(&d, direction))
        .ok_or_else(|| refused("exact original side normal outside arithmetic range"))?;
    let [Some(a), Some(b), Some(c)] =
        n.map(|v| x::scale(&v, f64::from(sense)).and_then(|v| x::interval(&v)))
    else {
        return Err(refused("exact source material normal cannot be enclosed"));
    };
    Ok([a, b, c])
}
/// Tensor enclosure of EXACT sewn curve Q and EXACT translated curve Q+D.
/// The caller obtains Q from its borrowed `ProductProfiles`, never a substitute
/// projected-net profile. All native sign switches are explicit; only sign, not
/// derivative magnitude, is asserted on normalized strictly increasing cells.
fn common_model_orientation_with_work(
    bounds: &CurveBounds<'_>,
    curve: &crate::query::distance_bound::Piece,
    direction: &x::P,
    reverse_ruling: bool,
    ruling_is_u: bool,
    normal: PointBox,
) -> Result<f64> {
    use crate::offset::construction::bernstein::Bernstein2;
    use crate::query::distance_bound::Piece;
    let (k, work) = bounds.context();
    work.spend_core(k, 0)?;
    let [_, _, _, weights] = &curve.h;
    let (p, q) = weights.degrees();
    let n = p
        .checked_add(1)
        .ok_or_else(|| refused("model control count overflow"))?;
    if !(1..=8).contains(&p)
        || q != 0
        || !curve.err.is_finite()
        || curve.err < 0.
        || curve
            .h
            .iter()
            .any(|h| h.degrees() != (p, 0) || h.coefficients().len() != n)
    {
        return Err(refused(
            "common model is not a complete positive curve root",
        ));
    }
    let cells = n
        .checked_mul(8)
        .ok_or_else(|| refused("model tensor storage overflow"))?;
    work.spend_core(
        k,
        cells
            .checked_mul(64)
            .ok_or_else(|| refused("model tensor work overflow"))?,
    )?;
    work.reserve_cells_core(k, cells)?;
    let mut directions = [Ivl::from(0.); 3];
    work.reserve_cells_core(k, 3)?;
    for (slot, axis) in directions.iter_mut().zip(direction) {
        work.spend_core(k, axis.len())?;
        *slot = x::interval(axis).ok_or_else(|| refused("common translation is not finite"))?;
    }
    let mut columns: [Vec<f64>; 4] = core::array::from_fn(|_| Vec::new());
    let mut error = 0_f64;
    let uncertainty = Ivl::new(-curve.err, curve.err);
    for i in 0..n {
        let weight = Ivl::from(
            *weights
                .coefficients()
                .get(i)
                .ok_or_else(|| invariant("model weight missing"))?,
        ) + uncertainty;
        if !weight.is_finite() || !weight.is_positive() {
            return Err(refused("model weights not proved positive"));
        }
        for (axis, out) in columns.iter_mut().enumerate() {
            let values = if axis == 3 {
                [weight, weight]
            } else {
                let a = Ivl::from(
                    *curve
                        .h
                        .get(axis)
                        .and_then(|p| p.coefficients().get(i))
                        .ok_or_else(|| invariant("model coefficient missing"))?,
                ) + uncertainty;
                let delta = *directions
                    .get(axis)
                    .ok_or_else(|| invariant("model translation component missing"))?;
                let z = a + delta * weight;
                if reverse_ruling {
                    [z, a]
                } else {
                    [a, z]
                }
            };
            for value in values {
                if !value.is_finite() {
                    return Err(refused("common model tensor overflow"));
                }
                let centre = 0.5 * value.lo + 0.5 * value.hi;
                let radius = (value - Ivl::from(centre)).mag();
                if !centre.is_finite() || !radius.is_finite() {
                    return Err(refused("common model tensor enclosure not finite"));
                }
                error = error.max(radius);
                out.push(centre);
            }
        }
    }
    let [a, b, c, w] = columns;
    let piece = Piece {
        h: [
            Bernstein2::new(p, 1, a)?,
            Bernstein2::new(p, 1, b)?,
            Bernstein2::new(p, 1, c)?,
            Bernstein2::new(p, 1, w)?,
        ],
        err: error,
        lower: 0.,
        depth: 0,
        uv: [0., 1., 0., 1.],
        parameter_ends: [0., 1., 0., 1.].map(Ivl::from),
    };
    let normal = if ruling_is_u {
        normal.map(|n| Ivl::new(-n.hi, -n.lo))
    } else {
        normal
    };
    bounds.orientation(&piece, normal)
}

/// Bind EVERY actual affine Plane UV root to the SAME coherent rectangle/model
/// boundary, not to a selected endpoint sample or rectangular flag. Exact clamp
/// events bound full S images; material/use ownership and real vertices are read
/// from this immutable final B-rep. Full model support error is added, never hidden.
fn plane_uv_boundary_with_work(
    k: &Kernel,
    work: &MeshWork,
    plane: &Plane,
    layout: &RectangleLayout<'_>,
    model_error: f64,
) -> Result<f64> {
    work.spend_core(k, 0)?;
    let b = layout.rebuilt;
    let mut upper = 0.0_f64;
    for boundary in &layout.edges {
        work.spend_core(k, 1)?;
        let record = b.edgeuse(boundary.use_id)?;
        if record.edge != Some(boundary.edge)
            || eu::faceuse(b, boundary.use_id)? != Some(layout.faceuse)
        {
            return Err(refused(
                "actual Plane UV edge/use owner differs from coherent side",
            ));
        }
        let (curve, owner) = eu::uv_trim_curve(b, boundary.use_id)?;
        let curve = curve.ok_or_else(|| refused("actual Plane UV trim missing"))?;
        let owner = owner
            .and_then(|u| eu::faceuse(b, u).transpose())
            .transpose()?
            .ok_or_else(|| refused("actual Plane UV trim owner missing"))?;
        if b.faceuse(owner)?.face != Some(layout.face) {
            return Err(refused("actual Plane UV trim belongs to another face"));
        }
        work.reserve_cells_core(k, 2)?;
        let mut actual =
            affine_ends(curve, edge::interval(b, boundary.edge)?, true).ok_or_else(|| {
                refused("actual Plane boundary is not a proved full affine UV definition")
            })?;
        let forward = match record.orientation {
            OrientType::Same => true,
            OrientType::Opposite => false,
            OrientType::Unknown => {
                return Err(refused("actual Plane UV traversal sense unresolved"))
            }
        };
        if !forward {
            actual.swap(0, 1);
        }
        let pair = affine_plane_pair_with_work(k, work, plane, &actual, &boundary.ends)?;
        let error = (Ivl::from(pair.distance_upper) + Ivl::from(model_error)).hi;
        let radius = zone_tol3d(k, edge::tolerance(b, boundary.edge)?);
        if !error.is_finite() || !radius.is_finite() || radius <= 0. || error > radius {
            return Err(refused(
                "WHOLE actual Plane UV image leaves same model edge's unchanged native tube",
            ));
        }
        upper = upper.max(error);
        let (Some(a), Some(z)) = edge::start_end_vertices(b, boundary.edge)? else {
            return Err(refused("actual Plane edge vertices missing"));
        };
        let ids = if forward { [a, z] } else { [z, a] };
        for (id, image) in ids.into_iter().zip(pair.actual_endpoints) {
            work.spend_core(k, 1)?;
            let p = vertex::point(b, id)?;
            let gap = super::hulls::point_distance_upper(
                image,
                [Ivl::from(p.x), Ivl::from(p.y), Ivl::from(p.z)],
            )?;
            let radius = zone_tol3d(k, vertex::tolerance(b, id)?);
            if !gap.is_finite() || !radius.is_finite() || radius <= 0. || gap > radius {
                return Err(refused(
                    "actual Plane UV real endpoint leaves its unchanged native vertex ball",
                ));
            }
        }
    }
    Ok(upper)
}
/// One complete actual side and ONE complete native cap edge. `reverse_profile`
/// states which traversal pairs the actual profile with the cap model; the full
/// displacement proof, not that boolean, determines whether it is admissible.
pub(crate) fn prove_product_side_band_with_work<'p, 'l, 'ld, 'ud, 'g, 's, 'raw>(
    k: &'g Kernel,
    work: &MeshWork,
    profiles: &'p ProductProfiles<'l, 'ld, 'ud, 'g, 's, 'raw>,
    face: FaceId,
    faceuse: FaceuseId,
    ruling_is_u: bool,
    reverse_ruling: bool,
    lower_rim: usize,
    lower_use: usize,
    reverse_profile: bool,
    claims: &[BandCellClaim],
    tolerance: f64,
) -> Result<ProductSideBand<'p, 'l, 'ld, 'ud, 'g, 's, 'raw>> {
    work.spend_core(k, 0)?;
    if !tolerance.is_finite() || tolerance <= 0. {
        return Err(refused("side tolerance invalid"));
    }
    let lower = profiles.lower();
    let draft = lower.draft();
    let b = draft.complex().brep();
    let record = b.face(face)?;
    let s = record
        .surface
        .as_ref()
        .ok_or_else(|| refused("actual side surface absent"))?;
    // Family event, not a failed-proof fallback. The Plane branch chooses a
    // coherent parameter witness CLAIM and must prove all stored UV-root images
    // below. Net-evaluator families retain the original exact raw rectangle proof.
    let plane = match s.kind_with_nurb(k)? {
        SurfaceKind::Plane(p) => Some(p),
        _ => None,
    };
    let trim = if plane.is_some() {
        rectangle_layout_claim_with_work(k, work, b, face, faceuse)?.ok_or_else(|| {
            refused("actual Plane side has no complete four-use affine layout claim")
        })?
    } else {
        prove_rectangular_trim_with_work(k, work, b, face, faceuse)?
            .ok_or_else(|| refused("actual side has no complete raw rectangle trim proof"))?
            .into_layout()
    };
    if trim.edges.len() != 4 {
        return Err(refused(
            "full product side requires one complete edge per rectangle side",
        ));
    }
    let original = draft.source();
    let actual = actual_ruling_rectangle_with_work(
        k,
        work,
        s,
        trim.domain,
        original.cap_normal(),
        original
            .cap_levels()
            .first()
            .ok_or_else(|| invariant("proved low cap level missing"))?,
        original.translation(),
        ruling_is_u,
        reverse_ruling,
    )?
    .ok_or_else(|| refused("actual side has no authoritative whole-definition product band"))?;
    if trim.domain != actual.domain() {
        return Err(refused(
            "actual side trim differs from complete authoritative band domain",
        ));
    }
    let graph = draft
        .graphs()
        .get(lower_rim)
        .ok_or_else(|| refused("claimed lower cap rim absent"))?;
    let patch = draft
        .complex()
        .patches
        .get(draft.patch())
        .ok_or_else(|| invariant("proven lower cap patch absent"))?;
    let usage = patch
        .rims
        .get(lower_rim)
        .and_then(|r| r.get(lower_use))
        .ok_or_else(|| refused("claimed actual cap edge absent"))?;
    let curve = graph
        .uses
        .get(lower_use)
        .ok_or_else(|| invariant("proven lower graph use absent"))?;
    let [umin, umax, vmin, vmax] = trim.domain;
    let (axis, lo, hi) = if actual.band().ruling_is_u {
        (0, umin, umax)
    } else {
        (1, vmin, vmax)
    };
    let [low, high] = if actual.reverse_ruling() {
        [hi, lo]
    } else {
        [lo, hi]
    };
    let mut low_edge = None;
    let mut high_edge = None;
    for edge in &trim.edges {
        work.spend_core(k, 1)?;
        let (Some(a), Some(c)) = (
            edge.ends.first().and_then(|p| p.get(axis)),
            edge.ends.get(1).and_then(|p| p.get(axis)),
        ) else {
            return Err(invariant("actual rectangle coordinate absent"));
        };
        if equal(a, low) && equal(c, low) && low_edge.replace(edge.edge).is_some() {
            return Err(refused(
                "side low boundary has multiple native edge entities",
            ));
        }
        if equal(a, high) && equal(c, high) && high_edge.replace(edge.edge).is_some() {
            return Err(refused(
                "side high boundary has multiple native edge entities",
            ));
        }
    }
    let (Some(low_edge), Some(high_edge)) = (low_edge, high_edge) else {
        return Err(refused("complete side cap boundaries absent"));
    };
    if low_edge != usage.edge || low_edge == high_edge {
        return Err(refused(
            "actual side low edge is not its proven source cap edge",
        ));
    }
    // The void-side cap and side uses run oppositely on the same edge.
    // Bind the model parameter direction explicitly even for arbitrarily tiny
    // features, where mere close sets cannot establish the correct CW direction.
    let low_boundary = trim
        .edges
        .iter()
        .find(|e| e.edge == low_edge)
        .ok_or_else(|| invariant("chosen low rectangle use absent"))?;
    let profile_axis = usize::from(actual.band().ruling_is_u);
    let (Some(a), Some(z)) = (
        low_boundary.ends.first().and_then(|p| p.get(profile_axis)),
        low_boundary.ends.get(1).and_then(|p| p.get(profile_axis)),
    ) else {
        return Err(invariant("chosen low profile coordinates absent"));
    };
    let sign = x::sub(z, a)
        .and_then(|v| x::sign(&v))
        .filter(|&s| s != 0)
        .ok_or_else(|| refused("chosen low rectangle profile direction unresolved"))?;
    if reverse_profile != (sign > 0) {
        return Err(refused(
            "model profile direction disagrees with opposite native cap/side uses",
        ));
    }
    let mut expected = Vec::new();
    for (i, cell) in graph.cells.iter().enumerate() {
        work.spend_core(k, 1)?;
        if cell.claim.curve == lower_use {
            work.reserve_cells_core(k, 1)?;
            expected.push(i);
        }
    }
    if expected.is_empty() || claims.len() != expected.len() {
        return Err(refused("complete side/cap model cell counts differ"));
    }
    // Every paired high cell must use exactly this actual side's high edge.
    // ProductProfiles has already verified a bijection and exact D-translation.
    let upper = profiles.upper();
    let upatch = upper
        .draft()
        .complex()
        .patches
        .get(upper.draft().patch())
        .ok_or_else(|| invariant("proven upper patch absent"))?;
    let mut high_cells = BTreeSet::new();
    for &cell in &expected {
        let mut pair = None;
        for candidate in profiles.cells() {
            work.spend_core(k, 1)?;
            if candidate.lower == [lower_rim, cell] && pair.replace(candidate).is_some() {
                return Err(invariant("common cell correspondence duplicated"));
            }
        }
        let pair = pair.ok_or_else(|| invariant("proven common cell correspondence absent"))?;
        work.reserve_cells_core(k, 1)?;
        if !high_cells.insert(pair.upper) {
            return Err(invariant("high common cell used twice"));
        }
        let [ri, ci] = pair.upper;
        let highgraph = upper
            .draft()
            .graphs()
            .get(ri)
            .ok_or_else(|| invariant("proven upper graph absent"))?;
        let highcell = highgraph
            .cells
            .get(ci)
            .ok_or_else(|| invariant("proven upper cell absent"))?;
        let target = upatch
            .rims
            .get(ri)
            .and_then(|r| r.get(highcell.claim.curve))
            .ok_or_else(|| invariant("proven upper target use absent"))?;
        if target.edge != high_edge {
            return Err(refused(
                "actual side high boundary differs from common translated model edge",
            ));
        }
    }
    for (ri, graph) in upper.draft().graphs().iter().enumerate() {
        for (ci, cell) in graph.cells.iter().enumerate() {
            work.spend_core(k, 1)?;
            let target = upatch
                .rims
                .get(ri)
                .and_then(|r| r.get(cell.claim.curve))
                .ok_or_else(|| invariant("proven upper target cell missing"))?;
            if (target.edge == high_edge) != high_cells.contains(&[ri, ci]) {
                return Err(refused(
                    "actual side high cap edge has unmatched common model cells",
                ));
            }
        }
    }
    let mut model_vertices = BTreeMap::new();
    cap_vertices(k, work, lower, lower_rim, lower_use, &mut model_vertices)?;
    let mut high_uses = BTreeSet::new();
    for [ri, ci] in &high_cells {
        work.spend_core(k, 1)?;
        let g = upper
            .draft()
            .graphs()
            .get(*ri)
            .ok_or_else(|| invariant("high graph missing"))?;
        let u = g
            .cells
            .get(*ci)
            .ok_or_else(|| invariant("high cell missing"))?
            .claim
            .curve;
        work.reserve_cells_core(k, 1)?;
        high_uses.insert((*ri, u));
    }
    for (ri, u) in high_uses {
        cap_vertices(k, work, upper, ri, u, &mut model_vertices)?;
    }
    let generator_error_upper = generator_bound(
        k,
        work,
        b,
        &trim,
        [low_edge, high_edge],
        draft.source().translation(),
        &model_vertices,
    )?;
    if reverse_profile {
        expected.reverse();
    }
    let extracted = native(
        k,
        work,
        actual_used_roots(k, work, curve.curve, curve.interval, curve.forward),
    )?;
    let metadata = &extracted
        .first()
        .ok_or_else(|| invariant("proven cap edge has no actual roots"))?
        .piece;
    let roots = roots(k, work, &actual)?;
    let mut ri = 0usize;
    let mut end = 0.;
    let mut base_upper = 0.0_f64;
    let mut orientation_numerator_lower = f64::INFINITY;
    let mut model_orientation_numerator_lower = f64::INFINITY;
    let bounds = CurveBounds::new(k, work)?;
    let source_sense = *draft
        .source_senses()
        .get(lower_rim)
        .ok_or_else(|| invariant("proved source rim sense missing"))?;
    let face_sense = match b.faceuse(faceuse)?.orientation {
        OrientType::Same => 1,
        OrientType::Opposite => -1,
        OrientType::Unknown => return Err(refused("actual side material normal sense unresolved")),
    };
    if ![-1, 1].contains(&source_sense) {
        return Err(invariant("proved original cap rim sense invalid"));
    }
    for (claim, &ci) in claims.iter().zip(&expected) {
        work.spend_core(k, 1)?;
        let [a, z] = claim.unit;
        if claim.root != ri
            || a != end
            || !(a.is_finite() && z.is_finite() && 0. <= a && a < z && z <= 1.)
        {
            return Err(refused(
                "side actual profile root partition incomplete or overlapping",
            ));
        }
        let normal = outward_normal(
            graph,
            ci,
            draft.source().translation(),
            source_sense * face_sense,
        )?;
        orientation_numerator_lower = orientation_numerator_lower
            .min(actual.orientation_lower_in_bounds(&bounds, ri, claim.unit, normal)?);
        let raw = roots
            .get(ri)
            .ok_or_else(|| refused("claimed actual side root absent"))?;
        let full = enclose_controls_with_work(k, work, raw, metadata)?
            .ok_or_else(|| refused("exact ruling profile cannot be enclosed"))?;
        let segment = full.restricted_u(a, z)?;
        let model = lower
            .controls_3d()
            .get(lower_rim)
            .and_then(|r| r.get(ci))
            .ok_or_else(|| invariant("proven lower model cell absent"))?;
        let mut oriented = Vec::new();
        for i in 0..model.len() {
            work.spend_core(k, 1)?;
            let j = if reverse_profile {
                model
                    .len()
                    .checked_sub(i)
                    .and_then(|j| j.checked_sub(1))
                    .ok_or_else(|| invariant("reversed model index underflow"))?
            } else {
                i
            };
            let p = model
                .get(j)
                .ok_or_else(|| invariant("proven lower model coefficient absent"))?;
            work.reserve_cells_core(k, 1)?;
            oriented.push(ProjectivePoint {
                xyz: p.xyz.clone(),
                w: p.w.clone(),
            });
        }
        let paired = enclose_controls_with_work(k, work, &oriented, &segment)?
            .ok_or_else(|| refused("common model root cannot be enclosed"))?;
        model_orientation_numerator_lower =
            model_orientation_numerator_lower.min(common_model_orientation_with_work(
                &bounds,
                &paired,
                draft.source().translation(),
                actual.reverse_ruling(),
                actual.band().ruling_is_u,
                normal,
            )?);
        base_upper = base_upper.max(paired_curve_upper(&segment, &paired, 0., 0.)?);
        end = z;
        if z == 1. {
            ri = ri
                .checked_add(1)
                .ok_or_else(|| refused("side root count overflow"))?;
            end = 0.;
        }
    }
    if ri != roots.len() || end != 0. {
        return Err(refused("actual side profile roots not fully covered"));
    }
    let error = (Ivl::from(base_upper) + Ivl::from(actual.band().definition_error_upper)).hi;
    if !error.is_finite() || error > zone_tol3d(k, record.tolerance) {
        return Err(refused(
            "complete actual side exceeds unchanged native face band",
        ));
    }
    let actual_uv_model_upper = if let Some(plane) = plane {
        plane_uv_boundary_with_work(k, work, plane, &trim, error)?
    } else {
        error
    };
    // SourcePrism gives a true product with exactly D; same r interpolates source
    // and model, so the proven complete lower-rim bound holds at EVERY height.
    let full = (Ivl::from(lower.source_model_upper())
        + Ivl::from(error.max(generator_error_upper).max(actual_uv_model_upper)))
    .hi;
    if !full.is_finite() || full > tolerance {
        return Err(refused(
            "complete source/actual side exceeds requested tolerance",
        ));
    }
    work.spend_core(k, 0)?;
    Ok(ProductSideBand {
        profiles,
        actual,
        rectangle: trim,
        low_edge,
        high_edge,
        source_actual_upper: full,
        model_definition_upper: error,
        generator_error_upper,
        orientation_numerator_lower,
        model_orientation_numerator_lower,
        actual_uv_model_upper,
    })
}

#[cfg(test)]
mod tests {
    use super::super::actual_ruling::actual_ruling_band_with_work;
    use super::*;
    use crate::kernel::KernelOptions;
    use crate::nurbs::{b_spline_surface::BSplineSurface, math::CPoint, srf_basic};
    use crate::surface::surface::Surface;
    fn point(p: [f64; 3], w: f64) -> ProjectivePoint {
        ProjectivePoint {
            xyz: x::point(p).unwrap(),
            w: x::scalar(w).unwrap(),
        }
    }
    #[test]
    fn generator_pair_retains_exact_nonrepresentable_native_parameter_fraction() {
        let a = point([0., 0., 0.], 2.);
        let z = point([0., 0., 15.], 3.);
        // Euclidean endpoint height5 and exact t1/3 produce height5/3,
        // represented homogeneously: rounding an interpolation fraction is not used.
        let m = segment_at(&a, &z, 0., 3., 1.).unwrap();
        assert!(x::sub(
            &x::scale(m.xyz.get(2).unwrap(), 3.).unwrap(),
            &x::scale(&m.w, 5.).unwrap()
        )
        .is_some_and(|v| x::zero(&v)));
        let d = x::point([0., 0., 5.]).unwrap();
        assert!(translated(&a, &z, &d));
        assert!(!translated(&a, &point([0.01, 0., 15.], 3.), &d));
        assert!(segment_at(&a, &z, 0., 3., 4.).is_none());
    }
    #[test]
    fn authoritative_complete_ruling_roots_cannot_ignore_interior_control_motion() {
        let k = Kernel::new(&KernelOptions::default());
        let work = MeshWork::new();
        let net = srf_basic::Surface::new(
            vec![
                vec![
                    CPoint::new(0., 0., 0., 1.),
                    CPoint::new(1., 1., 0., 1.),
                    CPoint::new(2., 0., 0., 1.),
                ],
                vec![
                    CPoint::new(0., 0., 5., 1.),
                    CPoint::new(1., 1., 5., 1.),
                    CPoint::new(2., 0., 5., 1.),
                ],
            ],
            1,
            2,
            vec![0., 0., 1., 1.],
            vec![0., 0., 0., 1., 1., 1.],
        )
        .unwrap();
        let surface = Surface::from(BSplineSurface::from_nurb(net, true));
        let actual = actual_ruling_band_with_work(
            &k,
            &work,
            &surface,
            &x::point([0., 0., 1.]).unwrap(),
            &x::scalar(0.).unwrap(),
            &x::point([0., 0., 5.]).unwrap(),
            true,
            false,
        )
        .unwrap()
        .unwrap();
        let roots = roots(&k, &work, &actual).unwrap();
        assert_eq!(roots.len(), 1);
        let base = roots.first().unwrap();
        assert_eq!(base.len(), 3);
        // Unit metadata is not geometry authority; exact controls above came
        // from the actual definition's complete immutable ruling token.
        let b =
            crate::offset::construction::bernstein::Bernstein2::new(1, 0, vec![0., 1.]).unwrap();
        let piece = crate::query::distance_bound::Piece {
            h: [
                b.clone(),
                b.clone(),
                b.clone(),
                crate::offset::construction::bernstein::Bernstein2::new(1, 0, vec![1., 1.])
                    .unwrap(),
            ],
            err: 0.,
            lower: 0.,
            depth: 0,
            uv: [0., 1., 0., 0.],
            parameter_ends: [Ivl::from(0.), Ivl::from(1.), Ivl::from(0.), Ivl::from(0.)],
        };
        let exact = enclose_controls_with_work(&k, &work, base, &piece)
            .unwrap()
            .unwrap();
        let moved = vec![
            point([0., 0., 0.], 1.),
            point([1., 0., 0.], 1.),
            point([2., 0., 0.], 1.),
        ];
        let model = enclose_controls_with_work(&k, &work, &moved, &piece)
            .unwrap()
            .unwrap();
        assert!(paired_curve_upper(&exact, &model, 0., 0.).unwrap() >= 0.5);
    }

    fn model_curve(
        k: &Kernel,
        work: &MeshWork,
        controls: &[ProjectivePoint],
    ) -> crate::query::distance_bound::Piece {
        use crate::offset::construction::bernstein::Bernstein2;
        let n = controls.len();
        let reference = crate::query::distance_bound::Piece {
            h: [
                Bernstein2::new(n - 1, 0, vec![0.; n]).unwrap(),
                Bernstein2::new(n - 1, 0, vec![0.; n]).unwrap(),
                Bernstein2::new(n - 1, 0, vec![0.; n]).unwrap(),
                Bernstein2::new(n - 1, 0, vec![1.; n]).unwrap(),
            ],
            err: 0.,
            lower: 0.,
            depth: 0,
            uv: [0., 1., 0., 0.],
            parameter_ends: [0., 1., 0., 0.].map(Ivl::from),
        };
        enclose_controls_with_work(k, work, controls, &reference)
            .unwrap()
            .unwrap()
    }
    #[test]
    fn same_sewn_model_orientation_keeps_native_profile_ruling_and_uv_senses() {
        let k = Kernel::default();
        let work = MeshWork::new();
        let bounds = CurveBounds::new(&k, &work).unwrap();
        for shift in [[0., 0., 5.], [1., 2., 5.]] {
            let direction = x::point(shift).unwrap();
            for reversed_profile in [false, true] {
                let controls = if reversed_profile {
                    vec![point([9., 0., 0.], 3.), point([0., 0., 0.], 2.)]
                } else {
                    vec![point([0., 0., 0.], 2.), point([9., 0., 0.], 3.)]
                };
                let model = model_curve(&k, &work, &controls);
                for reverse_ruling in [false, true] {
                    for ruling_is_u in [false, true] {
                        // Q runs from0 to3 on X with positive rational weights. The
                        // true product is Q+sD; its forward cross is (0,-Dz,Dy).
                        let flips = u8::from(reversed_profile)
                            + u8::from(reverse_ruling)
                            + u8::from(ruling_is_u);
                        let sign = if flips % 2 == 0 { 1. } else { -1. };
                        let normal = [0., -shift[2] * sign, shift[1] * sign].map(Ivl::from);
                        assert!(
                            common_model_orientation_with_work(
                                &bounds,
                                &model,
                                &direction,
                                reverse_ruling,
                                ruling_is_u,
                                normal
                            )
                            .unwrap()
                                > 0.
                        );
                        let opposite = normal.map(|v| Ivl::new(-v.hi, -v.lo));
                        assert!(matches!(
                            common_model_orientation_with_work(
                                &bounds,
                                &model,
                                &direction,
                                reverse_ruling,
                                ruling_is_u,
                                opposite
                            ),
                            Err(SolidError::Unsupported { .. })
                        ));
                    }
                }
            }
        }
        work.check(&k).unwrap();
    }
    #[test]
    fn positive_cached_net_orientation_cannot_replace_the_whole_sewn_model() {
        let k = Kernel::default();
        let work = MeshWork::new();
        let bounds = CurveBounds::new(&k, &work).unwrap();
        let direction = x::point([0., 0., 5.]).unwrap();
        let normal = [0., -1., 0.].map(Ivl::from);
        let net = srf_basic::Surface::new(
            vec![
                vec![CPoint::new(0., 0., 0., 1.), CPoint::new(0., 0., 5., 1.)],
                vec![CPoint::new(3., 0., 0., 1.), CPoint::new(3., 0., 5., 1.)],
            ],
            1,
            1,
            vec![0., 0., 1., 1.],
            vec![0., 0., 1., 1.],
        )
        .unwrap();
        let surface = Surface::from(BSplineSurface::from_nurb(net, true));
        let actual = actual_ruling_band_with_work(
            &k,
            &work,
            &surface,
            &x::point([0., 0., 1.]).unwrap(),
            &x::scalar(0.).unwrap(),
            &direction,
            false,
            false,
        )
        .unwrap()
        .unwrap();
        assert!(
            actual
                .orientation_lower_in_bounds(&bounds, 0, [0., 1.], normal)
                .unwrap()
                > 0.
        );
        // Same0/3 endpoints as that positive straight cached net, but the SAME
        // chosen quadratic model turns back after its interior control at10.
        let folded = model_curve(
            &k,
            &work,
            &[
                point([0., 0., 0.], 1.),
                point([10., 0., 0.], 1.),
                point([3., 0., 0.], 1.),
            ],
        );
        assert!(matches!(
            common_model_orientation_with_work(&bounds, &folded, &direction, false, false, normal),
            Err(SolidError::Unsupported { .. })
        ));
        let straight = model_curve(
            &k,
            &work,
            &[point([0., 0., 0.], 1.), point([3., 0., 0.], 1.)],
        );
        let huge = x::point([0., 0., f64::MAX]).unwrap();
        assert!(matches!(
            common_model_orientation_with_work(&bounds, &straight, &huge, false, false, normal),
            Err(SolidError::Unsupported { .. })
        ));
        assert!(matches!(
            common_model_orientation_with_work(
                &bounds,
                &straight,
                &x::point([0., 0., 0.]).unwrap(),
                false,
                false,
                normal
            ),
            Err(SolidError::Unsupported { .. })
        ));
        work.check(&k).unwrap();
    }

    #[test]
    fn same_sewn_rational_quadrant_keeps_orientation_over_the_whole_root() {
        let k = Kernel::default();
        let work = MeshWork::new();
        let bounds = CurveBounds::new(&k, &work).unwrap();
        let direction = x::point([0., 0., 5.]).unwrap();
        let weight = 0.5_f64.sqrt();
        for reverse_profile in [false, true] {
            let mut controls = vec![
                point([3., 0., 0.], 1.),
                point([3. * weight, 3. * weight, 0.], weight),
                point([0., 3., 0.], 1.),
            ];
            if reverse_profile {
                controls.reverse();
            }
            let model = model_curve(&k, &work, &controls);
            for reverse_ruling in [false, true] {
                for ruling_is_u in [false, true] {
                    // y-x=3z/[((1+w)+(1-w)z^2)/2], z=2t-1. Its
                    // derivative numerator is3*((1+w)-(1-w)z^2)>=6w>0.
                    // Thus (Q' cross(0,0,5)) dot(1,1,0)>0 on ALL t.
                    let flips = u8::from(reverse_profile)
                        + u8::from(reverse_ruling)
                        + u8::from(ruling_is_u);
                    let sign = if flips % 2 == 0 { 1. } else { -1. };
                    let normal = [sign, sign, 0.].map(Ivl::from);
                    assert!(
                        common_model_orientation_with_work(
                            &bounds,
                            &model,
                            &direction,
                            reverse_ruling,
                            ruling_is_u,
                            normal
                        )
                        .unwrap()
                            > 0.
                    );
                    let opposite = normal.map(|v| Ivl::new(-v.hi, -v.lo));
                    assert!(matches!(
                        common_model_orientation_with_work(
                            &bounds,
                            &model,
                            &direction,
                            reverse_ruling,
                            ruling_is_u,
                            opposite
                        ),
                        Err(SolidError::Unsupported { .. })
                    ));
                }
            }
        }
        work.check(&k).unwrap();
    }
}
