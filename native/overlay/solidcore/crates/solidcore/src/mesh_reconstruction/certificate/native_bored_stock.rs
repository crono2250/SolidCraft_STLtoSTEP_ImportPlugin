//! Canonical Native target for a rectangular blank with complete axial bores.
//! Geometry proof uses the original sewn body after normal export/reload.
//! Deviations: none. At most sixteen stacks, with bounded complete bands.
use super::super::work::MeshWork;
use super::analytic_ruling::{
    prove_native_radial_edges_with_work, prove_native_radial_values_with_work,
};
use super::bored_stock_proposal::{axes_for, perpendicular_bands_are_separate, BoredStockProposal};
use super::radial_curve::{prove_native_radial_cap_with_work, prove_native_radial_curve_with_work};
use super::radial_frame::AxialEndpointProposal;
use super::radial_source::RadialPatchClaim;
use super::rectangular_trim::prove_rectangular_trim_with_work;
use super::target_complex::{target_complex_with_work, TargetCover, TargetPatchClaim};
use crate::blend::fillet_section::interval::Ivl;
use crate::math::Vec3;
use crate::surface::surface::SurfaceKind;
use crate::topology::{edge, edgeuse::p1 as eu, face::p2 as face, Brep, EdgeId, FaceId};
use crate::{Kernel, Result, SolidError};
use std::collections::BTreeSet;

fn refused(reason: &'static str) -> SolidError {
    SolidError::Unsupported {
        operation: "mesh_reconstruction::certificate::native_bored_stock",
        reason,
    }
}

fn sum(a: f64, b: f64) -> Result<f64> {
    let c = Ivl::from(a) + Ivl::from(b);
    if !c.is_finite() {
        return Err(refused("native bored-stock bound overflow"));
    }
    Ok(c.hi)
}

fn native_clearance(
    w: &MeshWork,
    k: &Kernel,
    plan: &BoredStockProposal,
    margin: f64,
) -> Result<()> {
    let [lo, hi] = plan.bounds;
    let rad = |p: &RadialPatchClaim, x: f64| {
        let [r, s] = p.law.radius.map(Ivl::from);
        let [a, b] = p.law.height.map(Ivl::from);
        r + (s - r) * ((Ivl::from(x) - a) / (b - a)) + Ivl::from(margin)
    };
    for (i, own) in plan.bores.iter().enumerate() {
        for p in &own.bands {
            for (c, g) in axes_for(own.axis).into_iter().take(2).enumerate() {
                w.spend_core(k, 32)?;
                let radius = Ivl::from(p.law.radius[0].max(p.law.radius[1])) + Ivl::from(margin);
                let centre = Ivl::from(p.center[c]);
                for available in [centre - Ivl::from(lo[g]), Ivl::from(hi[g]) - centre] {
                    if !(available - radius - Ivl::from(margin)).is_positive() {
                        return Err(refused("native bore envelope may cross actual stock wall"));
                    }
                }
            }
            for earlier in plan.bores.iter().take(i) {
                for q in &earlier.bands {
                    w.spend_core(k, 64)?;
                    if own.axis != earlier.axis {
                        if !perpendicular_bands_are_separate(
                            [own.axis, earlier.axis],
                            [p, q],
                            [margin; 2],
                        ) {
                            return Err(refused("native perpendicular bore envelopes may overlap"));
                        }
                        continue;
                    }
                    let low = p.law.height[0].max(q.law.height[0]);
                    let high = p.law.height[1].min(q.law.height[1]);
                    if low > high {
                        continue;
                    }
                    let a = Ivl::from(p.center[0]) - Ivl::from(q.center[0]);
                    let b = Ivl::from(p.center[1]) - Ivl::from(q.center[1]);
                    let d = (a * a + b * b).sqrt();
                    for height in [low, high] {
                        if !(d - rad(p, height) - rad(q, height)).is_positive() {
                            return Err(refused("native analytic bore envelopes overlap"));
                        }
                    }
                }
            }
        }
    }
    Ok(())
}

fn void_use(
    k: &Kernel,
    work: &MeshWork,
    body: &Brep,
    id: FaceId,
) -> Result<crate::topology::FaceuseId> {
    work.spend_core(k, 8)?;
    let infinite = body
        .infinite_region()
        .ok_or_else(|| refused("native stock has no exterior"))?;
    let (Some(a), Some(b)) = face::faceuses(body, id)? else {
        return Err(refused("native stock face has incomplete use pair"));
    };
    let (Some(x), Some(y)) = (eu::faceuse_region(body, a)?, eu::faceuse_region(body, b)?) else {
        return Err(refused("native stock face has incomplete material regions"));
    };
    if x == infinite && y != infinite {
        Ok(a)
    } else if y == infinite && x != infinite {
        Ok(b)
    } else {
        Err(refused("native face does not border its one exterior"))
    }
}

pub(crate) fn prove_native_bored_stock_with_work(
    k: &Kernel,
    w: &MeshWork,
    body: &Brep,
    plan: &BoredStockProposal,
    allowance: f64,
) -> Result<f64> {
    use crate::mass::integrator::properties::region_material;
    use crate::topology::brep::p1::regions;
    if !allowance.is_finite() || allowance <= 0. {
        return Err(refused("native stock has no remaining distance allowance"));
    }
    native_clearance(w, k, plan, allowance)?;
    let bands: Vec<_> = plan
        .bores
        .iter()
        .flat_map(|b| b.bands.iter().map(|claim| (b.axis, claim)))
        .collect();
    let shoulder_count = plan
        .bores
        .iter()
        .map(|bore| bore.shoulders.len())
        .sum::<usize>();
    if body.face_list().len() != 6 + bands.len() + shoulder_count {
        return Err(refused(
            "native stock surface inventory differs from its source model",
        ));
    }
    let infinite = body
        .infinite_region()
        .ok_or_else(|| refused("missing stock infinite region"))?;
    let mut material = 0;
    let rs = regions(body, None)?;
    for &r in &rs {
        if region_material(body, r)? && r != infinite {
            material += 1;
        }
    }
    if rs.len() != 2 || material != 1 || region_material(body, infinite)? {
        return Err(refused(
            "native stock does not have one exterior and one material region",
        ));
    }
    let basis = [Vec3::X, Vec3::Y, Vec3::Z];
    let mut planes = [None; 6];
    let mut faces = vec![None; bands.len()];
    let mut shoulders = Vec::with_capacity(shoulder_count);
    for &id in body.face_list() {
        w.spend_core(k, 64)?;
        let s =
            face::surface(body, id)?.ok_or_else(|| refused("native stock face is undefined"))?;
        if s.has_kept_definition() {
            return Err(refused(
                "stock cannot replace a Native carried surface with a label",
            ));
        }
        match s.kind() {
            SurfaceKind::Plane(p) => {
                let frame = p.position();
                let q = frame.origin().to_array();
                let candidates = (0..6).filter(|&i| {
                    let a = i / 2;
                    q[a] == plan.bounds[i % 2][a]
                        && frame.x_axis().dot(basis[a]) == 0.
                        && frame.y_axis().dot(basis[a]) == 0.
                });
                let mut choices = candidates;
                match (choices.next(), choices.next()) {
                    (Some(i), None) => {
                        if planes[i].replace(id).is_some() {
                            return Err(refused("two Native faces claim the same stock Plane"));
                        }
                    }
                    (None, None)
                        if (0..3).any(|a| {
                            frame.x_axis().dot(basis[a]) == 0.
                                && frame.y_axis().dot(basis[a]) == 0.
                                && q[a] > plan.bounds[0][a]
                                && q[a] < plan.bounds[1][a]
                        }) =>
                    {
                        shoulders.push(id);
                    }
                    _ => {
                        return Err(refused(
                            "actual Native Plane does not match an outer wall or axial shoulder",
                        ))
                    }
                }
            }
            SurfaceKind::Cone(c) => {
                let position = c.rev().position();
                let origin = position.origin().to_array();
                let mut choices = bands.iter().enumerate().filter(|(_, (axis, band))| {
                    let [x, y, z] = axes_for(*axis).map(|i| origin[i]);
                    position.z_axis().cross(basis[*axis]).length() == 0.
                        && (x - band.center[0]).hypot(y - band.center[1]) <= allowance
                        && (z - band.law.height[0]).abs() <= allowance
                });
                let (Some((i, _)), None) = (choices.next(), choices.next()) else {
                    return Err(refused(
                        "actual conical band has an ambiguous source station",
                    ));
                };
                if faces[i].replace(id).is_some() {
                    return Err(refused("two actual bands claim the same source station"));
                }
            }
            _ => return Err(refused("unrelated Native surface in bored stock")),
        }
    }
    if shoulders.len() != shoulder_count {
        return Err(refused(
            "native stock did not preserve every shoulder Plane",
        ));
    }
    let shoulder_start = 6 + bands.len();
    let mut instances = planes
        .into_iter()
        .chain(faces)
        .map(|id| id.ok_or_else(|| refused("complete Native face inventory missing")))
        .collect::<Result<Vec<_>>>()?;
    instances.extend(shoulders);
    w.reserve_cells_core(k, instances.len().saturating_mul(2))?;
    let claims = instances
        .iter()
        .map(|&id| TargetPatchClaim { faces: vec![id] })
        .collect::<Vec<_>>();
    let target = match target_complex_with_work(k, w, body, &claims)? {
        TargetCover::Proven(c) => c,
        TargetCover::Undecided(_) => {
            return Err(refused("native stock has incomplete sewn topology"))
        }
    };

    let mut error = 0_f64;
    let mut radial_rims = Vec::new();
    for (&id, (axis, band)) in instances.iter().skip(6).zip(bands) {
        let s =
            face::surface(body, id)?.ok_or_else(|| refused("actual Native band disappeared"))?;
        let SurfaceKind::Cone(c) = s.kind() else {
            return Err(refused("actual Native band changed"));
        };
        let v = prove_native_radial_values_with_work(
            k,
            w,
            s,
            &plan.charts[axis],
            band.center,
            band.law,
            allowance,
        )?;
        let actual =
            prove_rectangular_trim_with_work(k, w, body, id, void_use(k, w, body, id)?)?
                .ok_or_else(|| refused("native bore does not cover its whole side rectangle"))?;
        let side = prove_native_radial_edges_with_work(
            k,
            w,
            &v,
            &actual,
            allowance.min(body.tolerance()),
        )?;
        error = error.max(sum(
            sum(v.definition_error_upper(), v.authority().distance_upper())?,
            side,
        )?);
        let r = super::native_radial_topology::side_rims(
            k,
            w,
            &actual,
            c.rev().swap_uv(),
            c.inside_out(),
        )?;
        if r[0].len() != 1 || r[1].len() != 1 {
            return Err(refused(
                "native bore band does not have two complete circular edges",
            ));
        }
        radial_rims.push(r);
    }
    let mut cap_rims: [Vec<(EdgeId, &RadialPatchClaim)>; 6] = core::array::from_fn(|_| Vec::new());
    let mut start = 0usize;
    let mut matched = BTreeSet::new();
    for bore in &plan.bores {
        let end = start
            .checked_add(bore.bands.len())
            .ok_or_else(|| refused("bore index overflow"))?;
        let rs = radial_rims
            .get(start..end)
            .ok_or_else(|| refused("Native bore inventory is incomplete"))?;
        for (join, pair) in rs.windows(2).enumerate() {
            let [a, b] = pair else {
                return Err(refused("missing native band neighbour"));
            };
            if bore
                .shoulders
                .iter()
                .any(|shoulder| shoulder.after_band == join)
            {
                let lower = &bore.bands[join];
                let upper = &bore.bands[join + 1];
                let lower_edge = *a[1]
                    .iter()
                    .next()
                    .ok_or_else(|| refused("missing lower shoulder edge"))?;
                let upper_edge = *b[0]
                    .iter()
                    .next()
                    .ok_or_else(|| refused("missing upper shoulder edge"))?;
                // Each actual annulus must use exactly the two adjoining
                // whole band edges. A same-height but unrelated face cannot match.
                let Some(paired) = target.edges.get(&lower_edge) else {
                    return Err(refused("native shoulder edge absent from target complex"));
                };
                let actual_index = paired
                    .iter()
                    .find_map(|&(i, _)| (i >= shoulder_start).then_some(i))
                    .ok_or_else(|| refused("native step edge does not adjoin an interior Plane"))?;
                if !matched.insert(actual_index) {
                    return Err(refused(
                        "same actual annulus was used for two source shoulders",
                    ));
                }
                error = error.max(prove_stock_shoulder(
                    k,
                    w,
                    body,
                    &plan.charts[bore.axis],
                    instances[actual_index],
                    &target.patches[actual_index],
                    [
                        (lower_edge, lower.law.radius[1]),
                        (upper_edge, upper.law.radius[0]),
                    ],
                    lower.center,
                    lower.law.height[1],
                    allowance,
                )?);
            } else if a[1] != b[0] {
                return Err(refused(
                    "native neighbouring bore bands do not share their exact rim",
                ));
            }
        }
        let a = rs
            .first()
            .and_then(|x| x[0].first())
            .copied()
            .zip(bore.bands.first())
            .ok_or_else(|| refused("missing native lower bore rim"))?;
        let b = rs
            .last()
            .and_then(|x| x[1].first())
            .copied()
            .zip(bore.bands.last())
            .ok_or_else(|| refused("missing native upper bore rim"))?;
        cap_rims[bore.axis * 2].push(a);
        cap_rims[bore.axis * 2 + 1].push(b);
        start = end;
    }
    if matched.len() != shoulder_count {
        return Err(refused("native stock has an unmatched interior Plane"));
    }
    for (i, (&id, actual)) in instances.iter().zip(&target.patches).take(6).enumerate() {
        let coordinate = i / 2;
        let [a, b] = [(coordinate + 1) % 3, (coordinate + 2) % 3];
        let level = plan.bounds[i % 2][coordinate];
        let [lo, hi] = plan.bounds;
        let corners = [
            [lo[a], lo[b]],
            [hi[a], lo[b]],
            [hi[a], hi[b]],
            [lo[a], hi[b]],
        ]
        .map(|[x, y]| {
            let mut p = [0.; 3];
            p[a] = x;
            p[b] = y;
            p[coordinate] = level;
            p
        });
        let s =
            face::surface(body, id)?.ok_or_else(|| refused("actual stock Plane disappeared"))?;
        let SurfaceKind::Plane(plane) = s.kind() else {
            return Err(refused("actual stock Plane changed"));
        };
        let mut outer = actual.rims.iter().filter(|rim| rim.len() == 4);
        let (Some(rect), None) = (outer.next(), outer.next()) else {
            return Err(refused("native stock outline must be one rectangle"));
        };
        let (planar_error, orientation) =
            prove_stock_outer_ring(k, w, body, plane, rect, corners, allowance)?;
        error = error.max(planar_error);
        let holes = &cap_rims[i];
        if actual.rims.len() != 1 + holes.len() {
            return Err(refused("native Plane lost or gained a complete hole"));
        }
        let mut visited = BTreeSet::new();
        for cycle in actual.rims.iter().filter(|r| r.len() != 4) {
            let [usage] = cycle.as_slice() else {
                return Err(refused("a native cap hole is not one whole circular edge"));
            };
            if !visited.insert(usage.edge) {
                return Err(refused("duplicate native cap hole"));
            }
            let (_, band) = holes
                .iter()
                .find(|(e, _)| *e == usage.edge)
                .ok_or_else(|| refused("native cap hole is not the same edge as its bore"))?;
            let (distance, sign) = prove_stock_circle(
                k,
                w,
                body,
                plane,
                usage,
                &plan.charts[coordinate],
                band.center,
                level,
                band.law.radius[i % 2],
                allowance,
            )?;
            if sign == orientation {
                return Err(refused(
                    "native through-hole loop does not subtract material from its cap",
                ));
            }
            error = error.max(distance);
        }
    }
    if error > allowance {
        return Err(refused(
            "complete native stock exceeds its boundary allowance",
        ));
    }
    Ok(error)
}

/// Whole actual planar stock rim against one fixed rectangle. The four native
/// vertices determine the corner assignment exactly. The full affine 3D edge
/// and every piece of the possibly clamped Plane trim image must follow the
/// same parameter segment inside the unchanged geometric zone.
fn prove_stock_outer_ring(
    k: &Kernel,
    work: &MeshWork,
    body: &crate::Brep,
    plane: &crate::surface::plane::Plane,
    loop_uses: &[super::target_complex::TargetEdgeUse],
    corners: [[f64; 3]; 4],
    allowance: f64,
) -> crate::Result<(f64, i32)> {
    use super::exact_geometry as x;
    use super::exact_planar::affine_ends;
    use super::hulls::{point_distance_upper, PointBox};
    use super::plane_trim_image::plane_trim_image_with_work;
    use crate::blend::fillet_section::interval::Ivl;
    use crate::topology::{edge, edgeuse::p1 as eu, vertex};
    use std::collections::BTreeSet;
    let [_, _, _, _] = loop_uses else {
        return Err(refused("stock outer loop must have exactly its four sides"));
    };
    let mut matched = BTreeSet::new();
    let mut orientation = None;
    let mut error = 0_f64;
    let enclose = |p: &x::P| -> Option<PointBox> {
        let [a, b, c] = p;
        Some([x::interval(a)?, x::interval(b)?, x::interval(c)?])
    };
    for item in loop_uses {
        work.spend_core(k, 2048)?;
        work.reserve_cells_core(k, 128)?;
        let a = vertex::point(body, item.start)?.to_array();
        let b = vertex::point(body, item.end)?.to_array();
        let start = corners
            .iter()
            .position(|&c| c == a)
            .ok_or_else(|| refused("stock outer vertex does not bind its exact rectangle"))?;
        let end = corners
            .iter()
            .position(|&c| c == b)
            .ok_or_else(|| refused("stock outer vertex does not bind its exact rectangle"))?;
        let sign = if (start + 1) % 4 == end {
            1
        } else if (end + 1) % 4 == start {
            -1
        } else {
            return Err(refused("stock outer boundary jumps across its rectangle"));
        };
        if !matched.insert(start) || orientation.replace(sign).is_some_and(|old| old != sign) {
            return Err(refused("stock outer loop does not go around exactly once"));
        }
        let interval = edge::interval(body, item.edge)?;
        let xyz = edge::curve(body, item.edge)?.ok_or_else(|| refused("stock line is absent"))?;
        let (Some(uv), _) = eu::uv_trim_curve(body, item.use_id)? else {
            return Err(refused("stock line lost its native UV trim"));
        };
        let mut world = affine_ends(xyz, interval, false)
            .ok_or_else(|| refused("stock edge is not a full affine physical line"))?;
        let mut param = affine_ends(uv, interval, true)
            .ok_or_else(|| refused("stock edge is not a full affine parametric trim"))?;
        if !item.forward {
            world.reverse();
            param.reverse();
        }
        let [s, t] = world.each_ref().map(enclose);
        let (Some(s), Some(t)) = (s, t) else {
            return Err(refused("stock full line endpoints are unbounded"));
        };
        let model_start = a.map(Ivl::from);
        let model_end = b.map(Ivl::from);
        let zone = allowance.min(edge::tolerance(body, item.edge)?.max(body.tolerance()));
        for (q, expected) in [(s, model_start), (t, model_end)] {
            error = error.max(point_distance_upper(q, expected)?);
            if error > allowance {
                return Err(refused(
                    "stock whole physical line exceeds its rectangle allowance",
                ));
            }
        }
        let plane_root = plane_trim_image_with_work(k, work, plane, &param)?;
        for knot in &plane_root.knots {
            let u = knot.parameter;
            let sample = |p: PointBox, q: PointBox| -> PointBox {
                core::array::from_fn(|j| p[j] + u * (q[j] - p[j]))
            };
            let model = sample(model_start, model_end);
            let curve = sample(s, t);
            let band = point_distance_upper(knot.point, model)?;
            let sewn = point_distance_upper(knot.point, curve)?;
            if sewn > zone || band > allowance {
                return Err(refused(
                    "stock complete affine trim exceeds its actual edge zone",
                ));
            }
            error = error.max(band).max(sewn);
        }
    }
    if matched.len() != 4 {
        return Err(refused("stock rectangle is missing a corner side"));
    }
    Ok((
        error,
        orientation.ok_or_else(|| refused("stock rectangle is not oriented"))?,
    ))
}

/// Full circular trim and its physical edge, using the same radial stock model.
fn prove_stock_circle(
    k: &Kernel,
    w: &MeshWork,
    body: &Brep,
    plane: &crate::surface::plane::Plane,
    usage: &super::target_complex::TargetEdgeUse,
    chart: &AxialEndpointProposal,
    center: [f64; 2],
    height: f64,
    radius: f64,
    allowance: f64,
) -> Result<(f64, i32)> {
    let interval = edge::interval(body, usage.edge)?;
    let curve =
        edge::curve(body, usage.edge)?.ok_or_else(|| refused("physical stock circle missing"))?;
    let (Some(trim), _) = eu::uv_trim_curve(body, usage.use_id)? else {
        return Err(refused("stock circular UV boundary missing"));
    };
    let radial = prove_native_radial_curve_with_work(
        k,
        w,
        curve,
        interval,
        usage.forward,
        chart,
        center,
        height,
        radius,
        allowance,
    )?;
    let (cap, sense) = prove_native_radial_cap_with_work(
        k,
        w,
        plane,
        trim,
        curve,
        interval,
        usage.forward,
        chart,
        center,
        height,
        radius,
        allowance.min(body.tolerance()),
    )?;
    if radial.sense != sense {
        return Err(refused(
            "stock cap and its physical edge traverse different senses",
        ));
    }
    Ok((cap.max(radial.world_error_upper), sense))
}

/// Verify a finite planar annulus joining two actual radial bands at a step.
fn prove_stock_shoulder(
    k: &Kernel,
    w: &MeshWork,
    body: &Brep,
    chart: &AxialEndpointProposal,
    id: FaceId,
    actual: &super::target_complex::TargetPatch,
    edges_and_radii: [(EdgeId, f64); 2],
    center: [f64; 2],
    height: f64,
    allowance: f64,
) -> Result<f64> {
    use crate::nurbs::b_spline_surface_n_lib::p2::OrientType;
    let s = face::surface(body, id)?.ok_or_else(|| refused("native shoulder plane missing"))?;
    let SurfaceKind::Plane(plane) = s.kind() else {
        return Err(refused("native shoulder is not an analytic Plane"));
    };
    let axis = Vec3::from_array(chart.columns[2]);
    let origin = Vec3::from_array(chart.origin);
    let frame = plane.position();
    if (frame.origin() - origin).dot(axis) != height
        || frame.x_axis().dot(axis) != 0.
        || frame.y_axis().dot(axis) != 0.
    {
        return Err(refused(
            "native shoulder Plane does not use the chosen join station",
        ));
    }
    let [a, b] = edges_and_radii;
    let delta = Ivl::from(a.1) - Ivl::from(b.1);
    let distance = if delta.is_positive() {
        delta.lo
    } else if delta.hi < 0. {
        -delta.hi
    } else {
        0.
    };
    if a.0 == b.0 || !(distance > (Ivl::from(2.) * Ivl::from(allowance)).hi) {
        return Err(refused(
            "native bore shoulder lacks two separate radial zones",
        ));
    }
    let [a, b] = if a.1 > b.1 { [a, b] } else { [b, a] };
    let mut world = 0_f64;
    let mut checked = BTreeSet::new();
    if actual.rims.len() != 2 {
        return Err(refused("bore step is not a complete native annulus"));
    }
    for row in &actual.rims {
        let [u] = row.as_slice() else {
            return Err(refused("annular shoulder has a split or unrelated rim"));
        };
        let radius = if u.edge == a.0 {
            a.1
        } else if u.edge == b.0 {
            b.1
        } else {
            return Err(refused(
                "native shoulder does not own the actual adjacent band edges",
            ));
        };
        if !checked.insert(u.edge) {
            return Err(refused("bore step reused an annular edge"));
        }
        let (error, sign) = prove_stock_circle(
            k, w, body, plane, u, chart, center, height, radius, allowance,
        )?;
        let face_direction = match body.faceuse(u.faceuse)?.orientation {
            OrientType::Same => 1,
            OrientType::Opposite => -1,
            OrientType::Unknown => {
                return Err(refused("stock shoulder has unknown material sense"))
            }
        };
        let plane_angle = frame.x_axis().cross(frame.y_axis()).dot(axis);
        if !plane_angle.is_finite() || plane_angle == 0. {
            return Err(refused("stock shoulder chart orientation unresolved"));
        }
        let external_sign = face_direction * if plane_angle > 0. { 1 } else { -1 };
        let want = if u.edge == a.0 {
            external_sign
        } else {
            -external_sign
        };
        if sign != want {
            return Err(refused(
                "native annular cap does not cover exactly its material band",
            ));
        }
        world = world.max(error);
    }
    // The entire annulus between two finite degree-one circles is mapped by
    // radial interpolation of their proven ordered boundaries.
    Ok(world)
}
