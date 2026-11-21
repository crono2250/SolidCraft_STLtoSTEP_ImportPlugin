//! Exact oriented planar-chain identity, a complete reconstruction certificate path.
//!
//! A compact oriented planar 2-chain is determined by its oriented boundary: its
//! multiplicity is constant on complementary components, changes by the boundary's
//! signed crossing, and is zero at infinity. We independently prove every source
//! triangle is in its actual target plane with the same orientation, prove every
//! actual native trim is a straight line exactly meeting its 3D edge/vertices, and
//! prove the complete oriented boundary chains equal after collinear subdivision.
//! The actual coordinatewise Plane clamp has nonnegative Jacobian: out-of-domain
//! strips collapse to zero 2-chain, while its interior map is injective. Complete
//! iso-trim images are monotone exact segments (endpoint plateaus carry zero chain),
//! so the pushforward boundary is the checked native 3D chain. Non-ISO clamping
//! refuses. This uses actual S semantics, not a guessed tolerance or net extension.
//! Source embedded-manifold validation excludes overlapping source sheets. Hence the
//! complete actual target and source boundaries coincide, with equal material winding.
//! This preserves holes, nesting, thin walls and embedding with error exactly zero.
//!
//! No sampled distance, area epsilon, genus count or caller support/trim flag accepts.
//! Native expansion arithmetic proves exact polynomial endpoint/plane identities;
//! out-of-range arithmetic and genuinely moved/curved geometry refuse this path.
//!
//! Deviations: none. No recursion. At most 8192 faces and 2,000,000 face/triangle or
//! segment comparisons. Native loops/edges obey `target_complex`'s bounded traversal.
use super::super::types::MeshInput;
use super::super::work::MeshWork;
use super::exact_geometry as x;
use super::source_topology::SourceManifold;
use super::target_complex::{target_complex_with_work, TargetCover, TargetPatchClaim};
use crate::curve::curve::{Curve, CurveKind};
use crate::geom::extent1d::Extent1d;
use crate::kernel::Kernel;
use crate::math::Vec3;
use crate::nurbs::b_spline_surface_n_lib::p2::OrientType;
use crate::nurbs::math::{NOW, NOZ};
use crate::surface::plane::Plane;
use crate::surface::surface::SurfaceKind;
use crate::topology::{edgeuse::p1 as eu, Brep, FaceId};
use crate::Result;
use std::collections::BTreeMap;

type BoundarySegment = ([f64; 3], [f64; 3]);

const MAX_WORK: usize = 2_000_000;
pub(crate) enum ExactPlanar {
    Proven,
    Undecided(&'static str),
}
fn array(v: Vec3) -> [f64; 3] {
    [v.x, v.y, v.z]
}
fn work(k: &Kernel, account: &MeshWork, left: &mut usize) -> Result<bool> {
    account.spend_core(k, 1)?;
    if *left == 0 {
        Ok(false)
    } else {
        *left -= 1;
        Ok(true)
    }
}
fn on_plane(p: [f64; 3], plane: &Plane) -> bool {
    let position = plane.position();
    x::vec(position.x_axis())
        .and_then(|a| x::cross(&a, &x::vec(position.y_axis())?))
        .and_then(|n| {
            x::dot(
                &n,
                &x::difference(&x::point(p)?, &x::vec(position.origin())?)?,
            )
        })
        .is_some_and(|value| x::zero(&value))
}
fn triangle_orientation(t: [[f64; 3]; 3], plane: &Plane, sense: i32) -> bool {
    let [a, b, c] = t;
    let p = plane.position();
    x::point(a)
        .and_then(|a| {
            x::cross(
                &x::difference(&x::point(b)?, &a)?,
                &x::difference(&x::point(c)?, &a)?,
            )
        })
        .and_then(|n| x::dot(&n, &x::cross(&x::vec(p.x_axis())?, &x::vec(p.y_axis())?)?))
        .and_then(|value| x::sign(&value))
        .is_some_and(|s| s * sense > 0)
}
fn face_sense(b: &Brep, face: FaceId) -> Result<Option<i32>> {
    let (Some(a), Some(c)) = crate::topology::face::p2::faceuses(b, face)? else {
        return Ok(None);
    };
    let side = |u| -> Result<Option<bool>> {
        match eu::faceuse_region(b, u)? {
            Some(r) => Ok(Some(crate::mass::integrator::properties::region_material(
                b, r,
            )?)),
            None => Ok(None),
        }
    };
    let chosen = match (side(a)?, side(c)?) {
        (Some(false), Some(true)) => a,
        (Some(true), Some(false)) => c,
        _ => return Ok(None),
    };
    Ok(match b.faceuse(chosen)?.orientation {
        OrientType::Same => Some(1),
        OrientType::Opposite => Some(-1),
        OrientType::Unknown => None,
    })
}

/// Exact endpoint expressions of a true affine line over its COMPLETE used interval.
/// An analytic Line is read from P+s*scale*V, never assumed equal to its rounded net.
pub(crate) fn affine_ends(curve: &Curve, interval: Extent1d, uv: bool) -> Option<[x::P; 2]> {
    let natural = curve.natural_interval();
    if !interval.is_bounded()
        || ![interval.min(), interval.max()]
            .iter()
            .all(|v| v.is_finite())
        || interval.min() >= interval.max()
    {
        return None;
    }
    match curve.kind() {
        CurveKind::Line(line) => {
            // A bounded analytic line is currently certified only over its full
            // natural interval. Its tiny-domain evaluator branch is not the
            // STEP affine map and remains refused.
            let endpoints = if line.is_bounded() {
                if natural.min() != interval.min()
                    || natural.max() != interval.max()
                    || !natural.length().is_finite()
                    || crate::geom::tol::is_zero(natural.length())
                {
                    return None;
                }
                let analytic = line.step_interval();
                let (min, max) = (analytic.min(), analytic.max());
                if !(min.is_finite()
                    && max.is_finite()
                    && min < max
                    && analytic.length().is_finite())
                {
                    return None;
                }
                if line.inside_out() {
                    [max, min]
                } else {
                    [min, max]
                }
            } else {
                // A record's Line imports as an unbounded canonical definition.
                // Its ACTUAL evaluator maps every used parameter t to +/-t:
                // there is no natural-domain normalization, clamp or net lookup.
                // Thus these endpoints bind the entire finite edge interval,
                // not a segment guessed from two evaluated samples.
                let a = interval.min();
                let b = interval.max();
                if line.inside_out() {
                    [-a, -b]
                } else {
                    [a, b]
                }
            };
            let mut origin = array(line.line_point());
            let mut direction = array(line.line_vector());
            if uv {
                origin[2] = 0.;
                direction[2] = 0.;
            }
            let origin = x::point(origin)?;
            let direction = x::point(direction)?;
            let mut result = Vec::new();
            for t in endpoints {
                let s = x::scalar(t).and_then(|v| x::scale(&v, line.line_scale()))?;
                let mut point = Vec::new();
                for (o, d) in origin.iter().zip(&direction) {
                    let v = x::mul(d, &s).and_then(|v| x::add(o, &v))?;
                    point.push(v);
                }
                let [Some(a), Some(b), Some(c)] = [point.first(), point.get(1), point.get(2)]
                else {
                    return None;
                };
                result.push([a.clone(), b.clone(), c.clone()]);
            }
            let [Some(a), Some(b)] = [result.first(), result.get(1)] else {
                return None;
            };
            Some([a.clone(), b.clone()])
        }
        CurveKind::BSpline(base) => {
            if natural.min() != interval.min() || natural.max() != interval.max() {
                return None;
            }
            let net = base.gw_nurb()?;
            let [a, b] = net.cpts() else {
                return None;
            };
            let [k0, k1, k2, k3] = net.knots() else {
                return None;
            };
            if net.degree() != 1
                || *k0 != interval.min()
                || *k1 != *k0
                || *k2 != interval.max()
                || *k3 != *k2
                || [a, b].iter().any(|p| p.w != NOW && p.w != 1.)
            {
                return None;
            }
            let read =
                |p: &crate::nurbs::math::CPoint| x::point([p.x, p.y, if uv { 0. } else { p.z }]);
            if !uv && [a, b].iter().any(|p| p.z == NOZ) {
                return None;
            }
            match (read(a), read(b)) {
                (Some(a), Some(b)) => Some([a, b]),
                _ => None,
            }
        }
        _ => None,
    }
}
fn plane_value(plane: &Plane, uv: &x::P) -> Option<x::P> {
    let position = plane.position();
    let origin = x::vec(position.origin())?;
    let a = x::vec(position.x_axis())?;
    let b = x::vec(position.y_axis())?;
    let [u, v, _] = uv;
    let scale = plane.uv_scale();
    let u = x::scale(u, scale.x)?;
    let v = x::scale(v, scale.y)?;
    let mut result = Vec::new();
    for ((o, a), b) in origin.iter().zip(&a).zip(&b) {
        result.push(x::add(&x::add(o, &x::mul(a, &u)?)?, &x::mul(b, &v)?)?);
    }
    let [Some(a), Some(b), Some(c)] = [result.first(), result.get(1), result.get(2)] else {
        return None;
    };
    Some([a.clone(), b.clone(), c.clone()])
}
fn uv_inside(plane: &Plane, point: &x::P) -> bool {
    let domain = plane.step_uv_domain();
    let (lo, hi) = (domain.min(), domain.max());
    let [u, v, _] = point;
    [(u, lo.x, hi.x), (v, lo.y, hi.y)]
        .into_iter()
        .all(|(a, lo, hi)| {
            x::scalar(lo)
                .and_then(|b| x::sub(a, &b))
                .and_then(|d| x::sign(&d))
                .is_some_and(|s| s >= 0)
                && x::scalar(hi)
                    .and_then(|b| x::sub(&b, a))
                    .and_then(|d| x::sign(&d))
                    .is_some_and(|s| s >= 0)
        })
}

/// Exact complete IMAGE segment of S applied to one actual affine UV trim.
/// `Plane::evaluate_point` clamps each coordinate unless its actual out-of-bounds
/// flag is enabled. Inside-domain trims remain affine. For an ISO trim, coordinate
/// clamping is continuous and monotone, so if either complete OUTPUT coordinate
/// is constant the COMPLETE image is the oriented
/// segment between its clamped endpoints, including possible endpoint plateaus.
/// Arbitrary non-ISO clamping can bend and is deliberately not covered here.
/// This computes no tolerance enlargement and does not substitute an affine
/// continuation for the actual definition S.
pub(super) fn plane_trim_segment(plane: &Plane, uv: &[x::P; 2]) -> Option<[x::P; 2]> {
    let enabled = plane.is_out_of_bounds_enabled();
    let inside = uv.iter().all(|p| uv_inside(plane, p));
    if enabled || inside {
        return Some([plane_value(plane, &uv[0])?, plane_value(plane, &uv[1])?]);
    }
    let domain = plane.step_uv_domain();
    if !domain.is_bounded() {
        return None;
    }
    let bounds = [
        (domain.u_min(), domain.u_max()),
        (domain.v_min(), domain.v_max()),
    ];
    let mut ends = [uv[0].clone(), uv[1].clone()];
    for p in &mut ends {
        if !x::zero(&p[2]) {
            return None;
        }
        for (coordinate, (lo, hi)) in p.iter_mut().zip(bounds) {
            if !(lo.is_finite() && hi.is_finite() && lo < hi) {
                return None;
            }
            let (lo, hi) = (x::scalar(lo)?, x::scalar(hi)?);
            if x::sign(&x::sub(coordinate, &lo)?)? < 0 {
                *coordinate = lo;
            } else if x::sign(&x::sub(coordinate, &hi)?)? > 0 {
                *coordinate = hi;
            }
        }
    }
    // Each clamped coordinate is monotone, so its COMPLETE range is between
    // these endpoints. Equal clamped ends prove it constant everywhere, even
    // if the raw coordinate varied wholly outside one domain side.
    let image_delta = x::difference(&ends[1], &ends[0])?;
    if !x::zero(&image_delta[0]) && !x::zero(&image_delta[1]) {
        return None;
    }
    Some([plane_value(plane, &ends[0])?, plane_value(plane, &ends[1])?])
}

/// Proves one complete oriented segment is partitioned EXACTLY ONCE by collinear
/// same-direction candidate intervals. This is geometric chain equality, not endpoint
/// proximity or a sample count. Both directions are checked by the caller.
fn covered(
    k: &Kernel,
    account: &MeshWork,
    a: [f64; 3],
    b: [f64; 3],
    candidates: &[([f64; 3], [f64; 3])],
    budget: &mut usize,
) -> Result<bool> {
    let Some(axis) = a.iter().zip(b).position(|(&x, y)| x != y) else {
        return Ok(false);
    };
    let (Some(&a_axis), Some(&b_axis)) = (a.get(axis), b.get(axis)) else {
        return Ok(false);
    };
    let (lo, hi) = (a_axis.min(b_axis), a_axis.max(b_axis));
    let positive = a_axis < b_axis;
    let mut intervals = Vec::new();
    for &(p, q) in candidates {
        if !work(k, account, budget)? {
            return Ok(false);
        }
        if !x::same_line(a, b, p) || !x::same_line(a, b, q) {
            continue;
        }
        let (Some(&u), Some(&v)) = (p.get(axis), q.get(axis)) else {
            return Ok(false);
        };
        let (left, right) = (u.min(v).max(lo), u.max(v).min(hi));
        if left >= right {
            continue;
        }
        if (u < v) != positive {
            return Ok(false);
        }
        intervals.push((left, right));
    }
    intervals.sort_unstable_by(|a, b| a.0.total_cmp(&b.0).then_with(|| a.1.total_cmp(&b.1)));
    let mut end = lo;
    for (left, right) in intervals {
        if left != end {
            return Ok(false);
        }
        end = right;
    }
    Ok(end == hi)
}

pub(crate) fn prove_with_work(
    k: &Kernel,
    account: &MeshWork,
    input: &MeshInput,
    source: &SourceManifold<'_>,
    b: &Brep,
) -> Result<ExactPlanar> {
    macro_rules! refuse {
        ($why:expr) => {
            return Ok(ExactPlanar::Undecided($why))
        };
    }
    if b.face_list().is_empty() || b.face_list().len() > 8192 {
        refuse!("the exact planar face budget was exceeded");
    }
    let mut budget = MAX_WORK;
    // Derive, rather than trust, support-plane attribution. A group may contain
    // several actual coplanar faces, whose internal seams cancel as oriented chains.
    let mut groups: Vec<(FaceId, i32, Vec<FaceId>)> = Vec::new();
    for &f in b.face_list() {
        if !work(k, account, &mut budget)? {
            refuse!("the exact planar work budget was exhausted");
        }
        let Some(surface) = &b.face(f)?.surface else {
            refuse!("an actual face has no surface");
        };
        if surface.has_kept_definition()
            || surface.procedural_blend().is_some()
            || surface.procedural_sweep().is_some()
        {
            refuse!("a carried surface definition is not proved by its Plane label");
        }
        let SurfaceKind::Plane(plane) = surface.kind_with_nurb(k)? else {
            refuse!("the candidate contains a non-planar surface");
        };
        let scale = plane.uv_scale();
        if !(scale.x > 0. && scale.y > 0. && scale.x.is_finite() && scale.y.is_finite()) {
            refuse!("a plane's parameter orientation is unsupported");
        }
        let Some(sense) = face_sense(b, f)? else {
            refuse!("an actual face has no decisive void/material side");
        };
        let mut group = None;
        for (gi, (representative, other_sense, _)) in groups.iter().enumerate() {
            if !work(k, account, &mut budget)? {
                refuse!("the exact planar work budget was exhausted");
            }
            let Some(other_surface) = &b.face(*representative)?.surface else {
                refuse!("a representative plane is missing");
            };
            let SurfaceKind::Plane(other) = other_surface.kind_with_nurb(k)? else {
                refuse!("a representative support changed kind");
            };
            let a = other.position();
            let z = plane.position();
            let equivalent = x::vec(a.x_axis())
                .and_then(|u| x::cross(&u, &x::vec(a.y_axis())?))
                .and_then(|normal| {
                    let nx = x::dot(&normal, &x::vec(z.x_axis())?)?;
                    let ny = x::dot(&normal, &x::vec(z.y_axis())?)?;
                    if !x::zero(&nx) || !x::zero(&ny) || !on_plane(array(z.origin()), other) {
                        return Some(false);
                    }
                    let orientation = x::dot(
                        &normal,
                        &x::cross(&x::vec(z.x_axis())?, &x::vec(z.y_axis())?)?,
                    )?;
                    Some(x::sign(&orientation).is_some_and(|v| v * sense * other_sense > 0))
                })
                .unwrap_or(false);
            if equivalent {
                group = Some(gi);
                break;
            }
        }
        if let Some(i) = group {
            let Some((_, _, faces)) = groups.get_mut(i) else {
                refuse!("a plane group is missing");
            };
            faces.push(f);
        } else {
            groups.push((f, sense, vec![f]));
        }
    }
    let mut assignments: Vec<Vec<usize>> = groups.iter().map(|_| Vec::new()).collect();
    for (id, alias) in source.aliases.iter().enumerate() {
        account.spend_core(k, 1)?;
        if alias.is_none() {
            continue;
        }
        let Some(triangle) = x::raw_triangle(&input.positions, &input.triangles, id) else {
            refuse!("an original source triangle is invalid");
        };
        let mut matched = None;
        for (gi, (f, sense, _)) in groups.iter().enumerate() {
            if !work(k, account, &mut budget)? {
                refuse!("the exact planar work budget was exhausted");
            }
            let Some(surface) = &b.face(*f)?.surface else {
                refuse!("an actual plane disappeared");
            };
            let SurfaceKind::Plane(plane) = surface.kind_with_nurb(k)? else {
                refuse!("an actual support changed kind");
            };
            if triangle.iter().all(|&p| on_plane(p, plane))
                && triangle_orientation(triangle, plane, *sense)
                && matched.replace(gi).is_some()
            {
                refuse!("an original triangle has ambiguous exact support assignment");
            }
        }
        let Some(gi) = matched else {
            refuse!("an original triangle is not in a same-oriented actual support plane");
        };
        let Some(list) = assignments.get_mut(gi) else {
            refuse!("a source support assignment is missing");
        };
        list.push(id);
    }
    let mut original_boundaries = Vec::new();
    for triangles in assignments {
        if triangles.is_empty() {
            refuse!("an actual support plane contains no original source 2-chain");
        }
        let mut edges: BTreeMap<(u32, u32), Vec<(u32, u32)>> = BTreeMap::new();
        for id in triangles {
            account.spend_core(k, 1)?;
            let Some(&Some([a, b, c])) = source.aliases.get(id) else {
                refuse!("an original retained triangle alias is missing");
            };
            for (u, v) in [(a, b), (b, c), (c, a)] {
                edges.entry((u.min(v), u.max(v))).or_default().push((u, v));
            }
        }
        let mut boundary = Vec::new();
        for uses in edges.values() {
            account.spend_core(k, 1)?;
            match *uses.as_slice() {
                [(u, v)] => boundary.push((u, v)),
                [(u, v), (x, y)] if u == y && v == x => {}
                _ => {
                    refuse!("the actual source planar 2-chain has invalid oriented incidence");
                }
            }
        }
        original_boundaries.push(boundary);
    }
    // A support-plane 2-chain may have disconnected components. It is not
    // a connected native CW patch. Prove native incidence per actual face,
    // then cancel only opposite uses in the SAME proved support class below.
    account.reserve_cells_core(k, b.face_list().len().saturating_mul(3))?;
    account.reserve_cells_core(k, groups.len())?;
    let mut support_groups = BTreeMap::new();
    for (group, (_, _, faces)) in groups.iter().enumerate() {
        for &f in faces {
            account.spend_core(k, 1)?;
            if support_groups.insert(f, group).is_some() {
                refuse!("an actual face has duplicate support attribution");
            }
        }
    }
    if support_groups.len() != b.face_list().len() {
        refuse!("an actual face has no support attribution");
    }
    let claims: Vec<_> = b
        .face_list()
        .iter()
        .map(|&f| TargetPatchClaim { faces: vec![f] })
        .collect();
    let complex = match target_complex_with_work(k, account, b, &claims)? {
        TargetCover::Proven(c) => c,
        TargetCover::Undecided(why) => {
            use super::target_complex::TargetRefusal;
            refuse!(match why {
                TargetRefusal::InvalidFacePartition => "native support face partition is invalid",
                TargetRefusal::MissingOrUnsureMaterialSide =>
                    "native support material side is undecided",
                TargetRefusal::UnsupportedPoleOrVertexLoop =>
                    "native support has an unsupported pole or vertex loop",
                TargetRefusal::InvalidNativeIncidence => "native target edge incidence is invalid",
                TargetRefusal::InvalidGroupBoundary { .. } =>
                    "native support group boundary is not simple",
                TargetRefusal::DisconnectedGroup { .. } =>
                    "coplanar support group contains disconnected native faces",
                TargetRefusal::WorkBudget => "native target incidence work budget was exceeded",
            });
        }
    };
    // Every actual edge/face trim must meet exactly. No tolerance-labelled gap is
    // treated as zero, and the Line's analytic definition is not replaced by its net.
    for (id, pair) in &complex.edges {
        account.spend_core(k, 1)?;
        let edge = b.edge(*id)?;
        let Some(curve) = &edge.curve else {
            refuse!("a native edge has no exact line");
        };
        let Some(ends) = affine_ends(curve, edge.interval, false) else {
            refuse!("a native boundary edge is not a complete exact affine segment");
        };
        let (Some(a), Some(z)) = crate::topology::edge::start_end_vertices(b, *id)? else {
            refuse!("a native edge endpoint is missing");
        };
        let points = [array(b.vertex(a)?.point), array(b.vertex(z)?.point)];
        if !ends.iter().zip(points).all(|(e, p)| x::equal_point(e, p)) {
            refuse!("a native line endpoint has nonzero geometric gap");
        }
        for (_, u) in pair {
            if !work(k, account, &mut budget)? {
                refuse!("the exact planar work budget was exhausted");
            }
            let Some(surface) = &b.face(u.face)?.surface else {
                refuse!("a native face surface is missing");
            };
            let SurfaceKind::Plane(plane) = surface.kind_with_nurb(k)? else {
                refuse!("a native face is not a plane");
            };
            let (Some(trim), _) = eu::uv_trim_curve(b, u.use_id)? else {
                refuse!("an actual native UV trim is missing");
            };
            let Some(uv) = affine_ends(trim, edge.interval, true) else {
                refuse!("an actual UV trim is not a complete affine segment");
            };
            let Some(image) = plane_trim_segment(plane, &uv) else {
                refuse!(
                    "an actual UV trim has no proved affine or monotone iso-clamped image on S"
                );
            };
            for (mapped, p) in image.iter().zip(points) {
                if !x::equal_point(mapped, p) {
                    refuse!("an actual face trim image on S has a nonzero edge gap");
                }
            }
        }
    }
    let mut native_boundaries: Vec<(usize, Vec<BoundarySegment>)> =
        groups.iter().map(|_| (0, Vec::new())).collect();
    // Count the actual chain once before allocating its storage. Repeated exact
    // growth would copy an already materialized boundary without its own charge.
    for pair in complex.edges.values() {
        account.spend_core(k, 1)?;
        let [(_, a), (_, z)] = pair;
        let (Some(&ga), Some(&gz)) = (support_groups.get(&a.face), support_groups.get(&z.face))
        else {
            refuse!("a native boundary use has no support attribution");
        };
        if ga == gz {
            continue;
        }
        for group in [ga, gz] {
            account.spend_core(k, 1)?;
            let Some((count, _)) = native_boundaries.get_mut(group) else {
                refuse!("a native support boundary group is missing");
            };
            let Some(next) = count.checked_add(1) else {
                refuse!("native support boundary count overflowed");
            };
            *count = next;
        }
    }
    for (count, boundary) in &mut native_boundaries {
        account.spend_core(k, 1)?;
        account.reserve_cells_core(k, *count)?;
        boundary
            .try_reserve_exact(*count)
            .map_err(|_| crate::SolidError::Unsupported {
                operation: "mesh_reconstruction::certificate::exact_planar",
                reason: "native support-chain storage could not be allocated",
            })?;
    }
    // ALL edge/S/UV checks above include internal coplanar seams. Only after
    // those checks can the verified opposite uses cancel in the support chain.
    for pair in complex.edges.values() {
        account.spend_core(k, 1)?;
        let [(_, a), (_, z)] = pair;
        let (Some(&ga), Some(&gz)) = (support_groups.get(&a.face), support_groups.get(&z.face))
        else {
            refuse!("a native boundary use has no support attribution");
        };
        if ga == gz {
            continue;
        }
        for (group, u) in [(ga, a), (gz, z)] {
            account.spend_core(k, 1)?;
            let Some((count, boundary)) = native_boundaries.get_mut(group) else {
                refuse!("a native support boundary group is missing");
            };
            if boundary.len() >= *count {
                refuse!("native support boundary exceeded its admitted inventory");
            }
            boundary.push((
                array(b.vertex(u.start)?.point),
                array(b.vertex(u.end)?.point),
            ));
        }
    }
    if original_boundaries.len() != native_boundaries.len() {
        refuse!("source and native support-group inventories differ");
    }
    for (boundary, (count, rebuilt)) in original_boundaries.iter().zip(&native_boundaries) {
        if rebuilt.len() != *count {
            refuse!("native support boundary differs from its admitted inventory");
        }
        account.spend_core(k, 1)?;
        let mut original = Vec::new();
        for &(a, b) in boundary {
            let (Some(a), Some(b)) = (source.position(a), source.position(b)) else {
                refuse!("an exact source rim alias is missing");
            };
            original.push((a, b));
        }
        if original.is_empty() || rebuilt.is_empty() {
            refuse!("an exact planar 2-chain has no finite boundary");
        }
        for &(a, b) in &original {
            if !covered(k, account, a, b, rebuilt, &mut budget)? {
                refuse!("the actual source oriented boundary chain differs from the native trim");
            }
        }
        for &(a, b) in rebuilt {
            if !covered(k, account, a, b, &original, &mut budget)? {
                refuse!(
                    "an actual native trim segment is not exactly covered by the source boundary"
                );
            }
        }
    }
    Ok(ExactPlanar::Proven)
}

#[cfg(test)]
mod affine_endpoint_regressions {
    use super::*;
    use crate::curve::line::Line;
    use crate::math::Point3;

    #[test]
    fn tiny_native_line_domain_is_not_replaced_by_analytic_ends() {
        use crate::nurbs::{
            b_spline_curve::BSplineCurve,
            crv_basic,
            math::{CPoint, NOW},
        };
        let start = Point3::new(10., 20., 30.);
        let tiny = Extent1d::from_min_max(0., 1e-12);
        let analytic = Extent1d::from_min_max(2., 3.);
        // from_points is deliberately lazy and a base edit can be a no-op.
        // Supply a STORED NURB with untouched tiny knots; borrowed=true avoids
        // any knot normalization, exactly as an imported native Line can carry.
        let net = crv_basic::Curve::new(
            vec![
                CPoint::new(10., 20., 30., NOW),
                CPoint::new(11., 20., 30., NOW),
            ],
            1,
            vec![0., 0., 1e-12, 1e-12],
        )
        .unwrap();
        let base = BSplineCurve::from_nurb(net, 3, true);
        let line = Line::from_parts(base, start, Vec3::new(1., 0., 0.), analytic, 1., false);
        assert_eq!(line.natural_interval().min(), tiny.min());
        assert_eq!(line.natural_interval().max(), tiny.max());
        assert!(crate::geom::tol::is_zero(line.natural_interval().length()));
        assert_eq!(line.convert_t_from_nurbs_to_step(tiny.min()), tiny.min());
        assert_eq!(line.evaluate_point(tiny.min()), start);
        let analytic_start =
            line.line_point() + analytic.min() * line.line_scale() * line.line_vector();
        assert_ne!(line.evaluate_point(tiny.min()), analytic_start);
        assert!(affine_ends(&Curve::from(line), tiny, false).is_none());
    }

    #[test]
    fn regular_native_line_retains_exact_affine_endpoint_proof() {
        let a = Point3::new(10.0, 20.0, 30.0);
        let b = Point3::new(11.0, 20.0, 30.0);
        let line = Line::from_points(a, b, 3);
        let interval = line.natural_interval();
        let ends = affine_ends(&Curve::from(line), interval, false).unwrap();
        assert!(x::equal_point(&ends[0], [a.x, a.y, a.z]));
        assert!(x::equal_point(&ends[1], [b.x, b.y, b.z]));
    }
    #[test]
    fn canonical_unbounded_line_certifies_its_whole_used_interval_in_both_senses() {
        use crate::math::Vec3;
        let origin = Point3::new(10., 20., 30.);
        // Normalizing an arbitrary input vector rounds its stored coefficients.
        // This canonical constructor has exact stored X and scale2, so its
        // independently derived integer endpoints have no normalization drift.
        let line = Line::create_canonical(origin, Vec3::new(2., 0., 0.));
        let used = Extent1d::from_raw(2., 5.);
        assert!(!line.is_bounded());
        assert_ne!(line.natural_interval().min(), used.min());
        let curve = Curve::from(line);
        for unbounded in [
            curve.natural_interval(),
            Extent1d::from_raw(0., crate::math::INFINITE_PARAMETER),
            Extent1d::from_raw(-crate::math::INFINITE_PARAMETER_SQRT, 5.),
        ] {
            assert!(!unbounded.is_bounded());
            assert!(affine_ends(&curve, unbounded, false).is_none());
        }
        let ends = affine_ends(&curve, used, false).unwrap();
        assert!(x::equal_point(&ends[0], [14., 20., 30.]));
        assert!(x::equal_point(&ends[1], [20., 20., 30.]));
        let uv = affine_ends(&curve, used, true).unwrap();
        assert!(x::equal_point(&uv[0], [14., 20., 0.]));
        assert!(x::equal_point(&uv[1], [20., 20., 0.]));
        // An import may carry finite coefficients independently of a cached
        // net. This non-axis stored affine law has exact integer data too.
        let stored = Line::from_parts(
            crate::nurbs::b_spline_curve::BSplineCurve::new(3),
            origin,
            Vec3::new(2., -3., 4.),
            Extent1d::from_raw(
                -crate::math::INFINITE_PARAMETER,
                crate::math::INFINITE_PARAMETER,
            ),
            1.,
            false,
        );
        let ends = affine_ends(&Curve::from(stored), used, false).unwrap();
        assert!(x::equal_point(&ends[0], [14., 14., 38.]));
        assert!(x::equal_point(&ends[1], [20., 5., 50.]));
        let reverse = Curve::from(Line::infinite(origin, Vec3::X, 3, true));
        let ends = affine_ends(&reverse, used, false).unwrap();
        assert!(x::equal_point(&ends[0], [8., 20., 30.]));
        assert!(x::equal_point(&ends[1], [5., 20., 30.]));
        assert!(affine_ends(&curve, Extent1d::from_raw(f64::NAN, 5.), false).is_none());
        assert!(affine_ends(&curve, Extent1d::from_raw(5., 2.), false).is_none());
        let bounded = Curve::from(Line::from_points(origin, Point3::new(20., 20., 30.), 3));
        assert!(affine_ends(&bounded, Extent1d::from_raw(0.2, 0.8), false).is_none());
    }
    #[test]
    fn actual_plane_iso_clamp_has_one_exact_oriented_image_segment() {
        use crate::{
            geom::extent2d::Extent2d,
            math::{Vec2, Vec3},
        };
        let mut plane = Plane::new(
            Point3::new(0., 0., 0.),
            Vec3::new(1., 0., 0.),
            Vec3::new(0., 1., 0.),
            Vec2::new(1., 1.),
            &Extent2d::from_bounds(0., 0., 5., 20.),
        );
        let uv = [
            x::point([5., -1.1102230246251565e-15, 0.]).unwrap(),
            x::point([5., 20., 0.]).unwrap(),
        ];
        assert!(!plane.is_out_of_bounds_enabled());
        let image = plane_trim_segment(&plane, &uv).unwrap();
        assert!(x::equal_point(&image[0], [5., 0., 0.]));
        assert!(x::equal_point(&image[1], [5., 20., 0.]));
        plane.set_out_of_bounds_enabled(true);
        let continued = plane_trim_segment(&plane, &uv).unwrap();
        assert!(!x::equal_point(&continued[0], [5., 0., 0.]));
    }
    #[test]
    fn noniso_clamp_cannot_be_replaced_by_clamped_endpoints() {
        use crate::{
            geom::extent2d::Extent2d,
            math::{Vec2, Vec3},
        };
        let plane = Plane::new(
            Point3::new(0., 0., 0.),
            Vec3::new(1., 0., 0.),
            Vec3::new(0., 1., 0.),
            Vec2::new(1., 1.),
            &Extent2d::from_bounds(0., 0., 5., 20.),
        );
        let uv = [
            x::point([-1., 0., 0.]).unwrap(),
            x::point([1., 2., 0.]).unwrap(),
        ];
        assert!(plane_trim_segment(&plane, &uv).is_none());
    }
    #[test]
    fn raw_noniso_trim_can_have_an_exact_iso_clamped_image() {
        use crate::{
            geom::extent2d::Extent2d,
            math::{Vec2, Vec3},
        };
        let plane = Plane::new(
            Point3::new(0., 0., 0.),
            Vec3::new(1., 0., 0.),
            Vec3::new(0., 1., 0.),
            Vec2::new(1., 1.),
            &Extent2d::from_bounds(0., 0., 5., 20.),
        );
        let uv = [
            x::point([5.000000000001, -1e-12, 0.]).unwrap(),
            x::point([5.000000000002, 20., 0.]).unwrap(),
        ];
        assert!(!x::zero(&x::sub(&uv[1][0], &uv[0][0]).unwrap()));
        assert!(!x::zero(&x::sub(&uv[1][1], &uv[0][1]).unwrap()));
        let image = plane_trim_segment(&plane, &uv).unwrap();
        assert!(x::equal_point(&image[0], [5., 0., 0.]));
        assert!(x::equal_point(&image[1], [5., 20., 0.]));
    }
}
