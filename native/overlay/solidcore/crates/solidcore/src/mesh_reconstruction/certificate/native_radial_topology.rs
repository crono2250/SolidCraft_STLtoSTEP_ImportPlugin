//! Complete finite Native side rectangle and actual end incidence for a frustum.
//!
//! The same immutable side definition supplies the all-root value authority and
//! the natural domain. Every actual 2D trim must cover the entire rectangle.
//! Identify the two physical end rings by that domain and the cone's height
//! reversal and UV swap. Then require the exact native edge sets on the two
//! planar caps, one void and one finite material region, and all faces covered.
//! This leaves the full cap/rim/edge geometry and their tolerance zones for
//! their own proof. It cannot authorize adoption on combinatorics alone.
//! Deviations: none. Shared MeshWork and complete target incidence.
use super::super::work::MeshWork;
use super::analytic_ruling::{prove_native_radial_values_with_work, NativeRadialValues};
use super::exact_geometry as x;
use super::radial_band::RadiusLaw;
use super::radial_frame::AxialEndpointProposal;
use super::rectangular_trim::{prove_rectangular_trim_with_work, RectangleTrim};
use super::target_complex::{target_complex_with_work, TargetCover, TargetPatchClaim};
use crate::mass::integrator::properties::region_material;
use crate::surface::surface::SurfaceKind;
use crate::topology::{
    brep::p1::regions, edgeuse::p1 as eu, face::p2 as face, Brep, EdgeId, FaceId,
};
use crate::{Kernel, Result, SolidError};
use std::collections::BTreeSet;

const OP: &str = "mesh_reconstruction::certificate::native_radial_topology";
fn refusal(reason: &'static str) -> SolidError {
    SolidError::Unsupported {
        operation: OP,
        reason,
    }
}

pub(crate) struct NativeRadialTopology<'a> {
    pub(crate) values: NativeRadialValues<'a>,
    pub(crate) rectangle: RectangleTrim<'a>,
    pub(crate) caps: [Option<FaceId>; 2],
    pub(crate) rims: [BTreeSet<EdgeId>; 2],
}

pub(super) fn side_rims(
    k: &Kernel,
    w: &MeshWork,
    rect: &RectangleTrim<'_>,
    height_u: bool,
    reverse_height: bool,
) -> Result<[BTreeSet<EdgeId>; 2]> {
    let [u0, u1, v0, v1] = rect.domain;
    let height = if height_u { [u0, u1] } else { [v0, v1] };
    let keys = height.map(x::scalar);
    let [Some(lo), Some(hi)] = keys else {
        return Err(refusal("Native rectangle height is not finite"));
    };
    let equal = |p: &x::E, q: &x::E| x::sub(p, q).is_some_and(|d| x::zero(&d));
    let mut low = BTreeSet::new();
    let mut high = BTreeSet::new();
    for edge in &rect.edges {
        w.spend_core(k, 256)?;
        w.reserve_cells_core(k, 128)?;
        let [[a, b, _], [c, d, _]] = &edge.ends;
        let (h0, h1) = if height_u { (a, c) } else { (b, d) };
        let at0 = equal(h0, &lo) && equal(h1, &lo);
        let at1 = equal(h0, &hi) && equal(h1, &hi);
        if at0 {
            if !low.insert(edge.edge) {
                return Err(refusal("a Native lower rim edge is repeated"));
            }
        } else if at1 && !high.insert(edge.edge) {
            return Err(refusal("a Native upper rim edge is repeated"));
        }
    }
    if !low.is_disjoint(&high) {
        return Err(refusal("Native end rims are missing or reuse an edge"));
    }
    Ok(if reverse_height {
        [high, low]
    } else {
        [low, high]
    })
}

pub(crate) fn prove_native_radial_topology_with_work<'a>(
    k: &'a Kernel,
    w: &MeshWork,
    b: &'a Brep,
    chart: &AxialEndpointProposal,
    axis_center: [f64; 2],
    law: RadiusLaw,
    allowance: f64,
) -> Result<NativeRadialTopology<'a>> {
    w.spend_core(k, 1)?;
    let [base, top] = law.radius;
    let pole = base == 0.;
    let cap_count = if pole { 1 } else { 2 };
    if base < 0. || top <= 0. || b.face_list().len() != 1 + cap_count {
        return Err(refusal(
            "Native radial solid does not have its one side and full end inventory",
        ));
    }
    // The face count is bounded up front. Verify standing region inventory
    // directly, including the infinite side. The final body validity guard
    // separately checks Region/Shell incidence under the shared work bound.
    let infinite = b
        .infinite_region()
        .ok_or_else(|| refusal("Native infinite region is absent"))?;
    let rs = regions(b, None)?;
    let [r0, r1] = rs.as_slice() else {
        return Err(refusal("a Native frustum needs one finite material region"));
    };
    let finite = if *r0 == infinite {
        *r1
    } else if *r1 == infinite {
        *r0
    } else {
        return Err(refusal("Native region inventory omits the infinite region"));
    };
    if region_material(b, infinite)? || !region_material(b, finite)? {
        return Err(refusal("Native frustum regions have incompatible material"));
    }
    let mut side = None;
    let mut caps = Vec::new();
    let mut claims = Vec::new();
    for &id in b.face_list() {
        w.spend_core(k, 16)?;
        w.reserve_cells_core(k, 8)?;
        let s =
            face::surface(b, id)?.ok_or_else(|| refusal("Native radial face has no definition"))?;
        match s.kind() {
            SurfaceKind::Cone(cone) if side.is_none() => side = Some((id, s, cone)),
            SurfaceKind::Plane(_) if !s.has_kept_definition() => caps.push(id),
            _ => return Err(refusal("Native body has unrelated or unsupported faces")),
        }
    }
    let (id, s, cone) = side.ok_or_else(|| refusal("Native cone side is absent"))?;
    claims.push(TargetPatchClaim { faces: vec![id] });
    if caps.len() != cap_count {
        return Err(refusal(
            "Native conical side has the wrong number of planar caps",
        ));
    }
    for &face in &caps {
        claims.push(TargetPatchClaim { faces: vec![face] });
    }
    let target = match target_complex_with_work(k, w, b, &claims)? {
        TargetCover::Proven(target) => target,
        TargetCover::Undecided(_) => return Err(refusal("Native frustum incidence is incomplete")),
    };
    let (side_patch, cap_patches) = target
        .patches
        .split_first()
        .ok_or_else(|| refusal("Native radial solid has no side patch"))?;
    if side_patch.rims.len() != cap_count || cap_patches.len() != cap_count {
        return Err(refusal(
            "Native radial side must share its exact finite rings",
        ));
    }
    let first_rim = side_patch
        .rims
        .first()
        .ok_or_else(|| refusal("Native radial side rim missing"))?;
    let side_use = first_rim
        .first()
        .ok_or_else(|| refusal("Native side rim is empty"))?
        .faceuse;
    if eu::faceuse_region(b, side_use)? != Some(infinite) {
        return Err(refusal("Native side must border the infinite void"));
    }
    let values = prove_native_radial_values_with_work(k, w, s, chart, axis_center, law, allowance)?;
    let rectangle = if pole {
        super::rectangular_trim::prove_implicit_pole_rectangle_with_work(
            k, w, b, id, side_use, &values,
        )?
        .map(|(rectangle, _)| rectangle)
    } else {
        prove_rectangular_trim_with_work(k, w, b, id, side_use)?
    }
    .ok_or_else(|| refusal("Native conical side does not use its complete trim rectangle"))?;
    if rectangle.domain != values.authority().domain() {
        return Err(refusal(
            "Native conical trim does not use its whole finite surface",
        ));
    }
    let rims = side_rims(k, w, &rectangle, cone.rev().swap_uv(), cone.inside_out())?;
    let [low, high] = &rims;
    if low.is_empty() != pole || high.is_empty() {
        return Err(refusal(
            "Native conical side cap or pole incidence is incomplete",
        ));
    }
    let mut result_caps = [None, None];
    for (&face, cap) in caps.iter().zip(cap_patches) {
        let [only] = cap.rims.as_slice() else {
            return Err(refusal("Native planar cap needs exactly one closed rim"));
        };
        let mut set = BTreeSet::new();
        for item in only {
            w.spend_core(k, 128)?;
            w.reserve_cells_core(k, 2)?;
            if eu::faceuse_region(b, item.faceuse)? != Some(infinite) || !set.insert(item.edge) {
                return Err(refusal("Native cap material or edge multiplicity differs"));
            }
        }
        let i = rims
            .iter()
            .position(|rim| rim == &set)
            .ok_or_else(|| refusal("Native cone and cap do not share their actual edge ring"))?;
        if result_caps[i].replace(face).is_some() {
            return Err(refusal("Native cap ring is covered more than once"));
        }
    }
    if result_caps.iter().flatten().count() != cap_count
        || result_caps[0].is_none() != pole
        || result_caps[1].is_none()
    {
        return Err(refusal(
            "Native exterior has an incomplete end disk inventory",
        ));
    }
    let caps = result_caps;
    Ok(NativeRadialTopology {
        values,
        rectangle,
        caps,
        rims,
    })
}

/// Write the two canonical seam uses during Native candidate construction.
/// The primitive's affine pcurves use length-normalized lines. A rounded
/// normalization can leave their endpoints short of the two exact trim corners.
/// The four stored uses choose correspondence only; the final canonical
/// candidate must pass the unchanged exact rectangle and complete 3D proofs.
pub(crate) fn construct_exact_cone_seams(
    k: &Kernel,
    work: &MeshWork,
    body: &mut Brep,
) -> Result<()> {
    work.spend_core(k, 1024)?;
    let mut conical_side = None;
    for &id in body.face_list() {
        work.spend_core(k, 1)?;
        let Some(surface) = face::surface(body, id)? else {
            return Err(refusal("Native primitive face is missing a surface"));
        };
        if matches!(surface.kind(), SurfaceKind::Cone(_)) {
            if conical_side.replace(id).is_some() {
                return Err(refusal("Native primitive has more than one conical side"));
            }
        }
    }
    let side = conical_side.ok_or_else(|| refusal("Native primitive has no conical side"))?;
    construct_exact_cone_seams_for_face(k, work, body, side)
}

/// Finish the full affine seams of this exact side in a freshly sewn candidate.
pub(super) fn construct_exact_cone_seams_for_face(
    k: &Kernel,
    work: &MeshWork,
    body: &mut Brep,
    side: FaceId,
) -> Result<()> {
    use super::rectangular_trim::rectangle_layout_claim_with_work;
    use crate::math::Vec3;
    use crate::nurbs::b_spline_curve::{BSplineCurve, BSplineCurveForm, CanonicalData, KnotType};
    use crate::nurbs::b_spline_surface_n_lib::p2::OrientType;
    let surface =
        face::surface(body, side)?.ok_or_else(|| refusal("Native primitive side is undefined"))?;
    let SurfaceKind::Cone(cone) = surface.kind() else {
        return Err(refusal("Native primitive side is not a cone"));
    };
    let height_u = cone.rev().swap_uv();
    let pole = cone.base_radius() == 0.;
    let infinite = body
        .infinite_region()
        .ok_or_else(|| refusal("Native primitive has no void"))?;
    let (first, second) = face::faceuses(body, side)?;
    let mut use_id = None;
    for id in [first, second].into_iter().flatten() {
        if eu::faceuse_region(body, id)? == Some(infinite) {
            use_id = Some(id);
        }
    }
    let use_id = use_id.ok_or_else(|| refusal("Native primitive side does not bound the void"))?;
    let loops = eu::faceuse_loopuses(body, use_id, false, None)?;
    let [l] = loops.as_slice() else {
        return Err(refusal(
            "fresh Native conical side has more or fewer than one loop",
        ));
    };
    let mut uses = Vec::new();
    if !crate::topology::loopuse::visit_edgeuses_bounded(body, *l, 8, |use_id| {
        work.reserve_cells_core(k, 1)?;
        uses.push(use_id);
        Ok(())
    })? || uses.len() != if pole { 3 } else { 4 }
    {
        return Err(refusal(
            "fresh Native conical side has a different full edge inventory",
        ));
    }
    // Sewing different analytic bands can invalidate UV trim caches. Use
    // the normal Native materialization before writing exact seam endpoints.
    for use_id in uses {
        work.spend_core(k, 256)?;
        if eu::uv_trim_curve(body, use_id)?.0.is_none() {
            crate::topology::edgeuse::p3::get_or_create_uv_trim_curve(
                k, body, use_id, false, false, true,
            )?
            .status?;
        }
        let e = body
            .edgeuse(use_id)?
            .edge
            .ok_or_else(|| refusal("Native side boundary edge is missing"))?;
        let at = body.edge(e)?.interval;
        let (Some(uv), _) = eu::uv_trim_curve(body, use_id)? else {
            return Err(refusal(
                "fresh Native conical side has no materialized UV trim",
            ));
        };
        if super::exact_planar::affine_ends(uv, at, true).is_none() {
            return Err(refusal(
                "fresh Native conical side UV evaluator is not completely affine",
            ));
        }
    }

    let layout = if pole {
        super::rectangular_trim::actual_affine_loop_with_work(k, work, body, side, use_id)?
    } else {
        rectangle_layout_claim_with_work(k, work, body, side, use_id)?
    }
    .ok_or_else(|| refusal("Native primitive is missing all affine boundary uses"))?;
    if layout.edges.len() != if pole { 3 } else { 4 } {
        return Err(refusal(
            "Native primitive has an unexpected number of side uses",
        ));
    }
    let [u0, u1, v0, v1] = layout.domain;
    let (height, profile) = if height_u {
        ([u0, u1], [v0, v1])
    } else {
        ([v0, v1], [u0, u1])
    };
    let h = usize::from(!height_u);
    let a = usize::from(height_u);
    let mut replacements = Vec::new();
    for edge in &layout.edges {
        let [start, end] = &edge.ends;
        let is_arc = |v: f64| {
            x::scalar(v).is_some_and(|value| {
                [&start[a], &end[a]]
                    .into_iter()
                    .all(|component| x::sub(component, &value).is_some_and(|v| x::zero(&v)))
            })
        };
        let turn = if is_arc(profile[0]) {
            profile[0]
        } else if is_arc(profile[1]) {
            profile[1]
        } else {
            continue;
        };
        let sign = x::sub(&end[h], &start[h])
            .and_then(|v| x::sign(&v))
            .ok_or_else(|| refusal("Native seam height extent is unresolved"))?;
        let [lo, hi] = match sign {
            1 => height,
            -1 => [height[1], height[0]],
            _ => return Err(refusal("Native seam has no positive extent")),
        };
        let coordinate = |height| {
            if height_u {
                Vec3::new(height, turn, 0.)
            } else {
                Vec3::new(turn, height, 0.)
            }
        };
        let (mut start, mut end) = (coordinate(lo), coordinate(hi));
        match body.edgeuse(edge.use_id)?.orientation {
            OrientType::Same => {}
            OrientType::Opposite => core::mem::swap(&mut start, &mut end),
            OrientType::Unknown => return Err(refusal("Native seam orientation is unknown")),
        }
        let interval = body.edge(edge.edge)?.interval;
        let curve = BSplineCurve::create_canonical(&CanonicalData {
            dim: 2,
            degree: 1,
            control_points: &[start, end],
            form: BSplineCurveForm::PolylineForm,
            knot_multiplicities: &[2, 2],
            knots: &[interval.min(), interval.max()],
            knot_type: KnotType::Unspecified,
            weights: None,
            trim: None,
        })?;
        replacements.push((edge.edge, edge.use_id, curve));
    }
    let [(a, _, _), (b, _, _)] = replacements.as_slice() else {
        return Err(refusal("Native primitive must have two seam uses"));
    };
    if a != b {
        return Err(refusal("Native primitive seam uses must refer to one edge"));
    }
    for (_, use_id, curve) in replacements {
        eu::set_uv_trim_curve(
            body,
            use_id,
            eu::UvTrimCurveArg::New(Box::new(curve.into())),
            0.,
            true,
            None,
        )?;
    }
    if !pole && prove_rectangular_trim_with_work(k, work, body, side, use_id)?.is_none() {
        return Err(refusal(
            "constructed Native seam did not complete the existing rims",
        ));
    }
    Ok(())
}

/// Complete ordinary frustum topology and geometry on the same canonical body.
/// Every physical rim is the unique shared cap edge and the conical side is
/// one exact finite parameter rectangle. A single outward material shell then
/// has the same two filled disks and one annular side as the source model.
pub(crate) fn prove_native_radial_boundary_with_work(
    k: &Kernel,
    w: &MeshWork,
    b: &Brep,
    chart: &AxialEndpointProposal,
    center: [f64; 2],
    law: RadiusLaw,
    allowance: f64,
) -> Result<f64> {
    use super::analytic_ruling::prove_native_radial_edges_with_work;
    use super::radial_curve::{
        prove_native_radial_cap_with_work, prove_native_radial_curve_with_work,
    };
    use crate::blend::fillet_section::interval::Ivl;
    use crate::nurbs::b_spline_surface_n_lib::p2::OrientType;
    use crate::topology::{edge, loopuse};
    if !allowance.is_finite()
        || allowance <= 0.
        || !b.tolerance().is_finite()
        || b.tolerance() <= 0.
    {
        return Err(refusal(
            "complete control budget for the frustum was exhausted",
        ));
    }
    let incidence = prove_native_radial_topology_with_work(k, w, b, chart, center, law, allowance)?;
    let actual_side = Ivl::from(incidence.values.definition_error_upper())
        + Ivl::from(incidence.values.authority().distance_upper());
    let side_gap = prove_native_radial_edges_with_work(
        k,
        w,
        &incidence.values,
        &incidence.rectangle,
        allowance.min(b.tolerance()),
    )?;
    let mut value = actual_side.hi;
    for (((cap, rim), height), radius) in incidence
        .caps
        .iter()
        .zip(&incidence.rims)
        .zip(law.height)
        .zip(law.radius)
    {
        w.spend_core(k, 1024)?;
        let Some(cap) = *cap else {
            continue;
        };
        let mut ids = rim.iter();
        let (Some(&edge_id), None) = (ids.next(), ids.next()) else {
            return Err(refusal(
                "Native finite cap requires one whole circular edge",
            ));
        };
        let s = face::surface(b, cap)?
            .ok_or_else(|| refusal("finite Native cap definition missing"))?;
        let SurfaceKind::Plane(plane) = s.kind() else {
            return Err(refusal("finite Native cap is not an ordinary plane"));
        };
        let (Some(a), Some(c)) = face::faceuses(b, cap)? else {
            return Err(refusal(
                "finite Native cap requires a complete face use pair",
            ));
        };
        let infinite = b
            .infinite_region()
            .ok_or_else(|| refusal("Native frustum exterior missing"))?;
        let use_id = if eu::faceuse_region(b, a)? == Some(infinite) {
            a
        } else if eu::faceuse_region(b, c)? == Some(infinite) {
            c
        } else {
            return Err(refusal("finite Native cap does not meet the exterior"));
        };
        let loops = eu::faceuse_loopuses(b, use_id, false, None)?;
        let [lu] = loops.as_slice() else {
            return Err(refusal(
                "finite Native cap must have its sole filled boundary",
            ));
        };
        let mut uses = Vec::new();
        if !loopuse::visit_edgeuses_bounded(b, *lu, 2, |id| {
            w.reserve_cells_core(k, 1)?;
            uses.push(id);
            Ok(())
        })? {
            return Err(refusal("finite Native cap has unexpected further uses"));
        }
        let [e] = uses.as_slice() else {
            return Err(refusal(
                "finite Native cap must use its full circular edge exactly once",
            ));
        };
        let usage = b.edgeuse(*e)?;
        if usage.edge != Some(edge_id) {
            return Err(refusal("finite Native cap uses an unrelated edge"));
        }
        let forward = match usage.orientation {
            OrientType::Same => true,
            OrientType::Opposite => false,
            OrientType::Unknown => return Err(refusal("finite Native cap orientation is unknown")),
        };
        let native_edge = edge::curve(b, edge_id)?
            .ok_or_else(|| refusal("Native cap edge lacks its physical evaluator"))?;
        let (Some(uv), _) = eu::uv_trim_curve(b, *e)? else {
            return Err(refusal("Native cap edge lacks its whole UV trim"));
        };
        let real_zone = edge::tolerance(b, edge_id)?.max(b.tolerance());
        if !real_zone.is_finite() {
            return Err(refusal("Native circular edge zone is not finite"));
        }
        let used = edge::interval(b, edge_id)?;
        let edge_bound = prove_native_radial_curve_with_work(
            k,
            w,
            native_edge,
            used,
            forward,
            chart,
            center,
            height,
            radius,
            allowance,
        )?;
        let (disk, orientation) = prove_native_radial_cap_with_work(
            k,
            w,
            plane,
            uv,
            native_edge,
            used,
            forward,
            chart,
            center,
            height,
            radius,
            allowance.min(real_zone),
        )?;
        if orientation != edge_bound.sense {
            return Err(refusal(
                "finite Native cap and shared physical edge have opposite radial traversal",
            ));
        }
        value = value.max(disk).max(edge_bound.world_error_upper);
    }
    let limit = Ivl::from(value) + Ivl::from(side_gap);
    if !limit.is_finite() || limit.hi > allowance {
        return Err(refusal(
            "whole finite Native boundary is outside its model allowance",
        ));
    }
    Ok(limit.hi)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::math::Vec3;
    use crate::primitive::api_primitives::create_cone;

    #[test]
    fn native_frustum_side_and_planes_share_two_complete_rims() {
        let mut k = Kernel::default();
        let mut b = create_cone(&mut k, Vec3::ZERO, 3., 2., 5.).unwrap();
        construct_exact_cone_seams(&k, &MeshWork::new(), &mut b).unwrap();
        let chart = AxialEndpointProposal {
            origin: [0.; 3],
            columns: [[1., 0., 0.], [0., 1., 0.], [0., 0., 1.]],
            rows: Vec::new(),
        };
        let proof = prove_native_radial_topology_with_work(
            &k,
            &MeshWork::new(),
            &b,
            &chart,
            [0.; 2],
            RadiusLaw {
                height: [0., 5.],
                radius: [3., 2.],
            },
            1e-6,
        );
        let proof = proof.unwrap();
        assert_ne!(proof.caps[0], proof.caps[1]);
        let complete = prove_native_radial_boundary_with_work(
            &k,
            &MeshWork::new(),
            &b,
            &chart,
            [0.; 2],
            RadiusLaw {
                height: [0., 5.],
                radius: [3., 2.],
            },
            1e-6,
        )
        .unwrap();
        assert!(complete <= 1e-6);
        assert!(proof.rims.iter().all(|rim| !rim.is_empty()));
        assert_eq!(proof.rectangle.domain, proof.values.authority().domain());
        for (index, ((cap, rim), radius)) in
            proof.caps.iter().zip(&proof.rims).zip([3., 2.]).enumerate()
        {
            use crate::nurbs::b_spline_surface_n_lib::p2::OrientType;
            use crate::topology::{edge, loopuse};
            let cap = cap.unwrap();
            let surface = face::surface(&b, cap).unwrap().unwrap();
            let SurfaceKind::Plane(plane) = surface.kind() else {
                panic!("cap must be a Plane");
            };
            let (first, second) = face::faceuses(&b, cap).unwrap();
            let void = [first, second]
                .into_iter()
                .flatten()
                .find(|&id| eu::faceuse_region(&b, id).unwrap() == b.infinite_region())
                .unwrap();
            let loops = eu::faceuse_loopuses(&b, void, false, None).unwrap();
            let [lu] = loops.as_slice() else {
                panic!("expected one full cap loop");
            };
            let uses = loopuse::edgeuses(&b, *lu, None, None).unwrap();
            let [id] = uses.as_slice() else {
                panic!("expected one full circular edge");
            };
            let e = b.edgeuse(*id).unwrap();
            let edge_id = e.edge.unwrap();
            assert!(rim.contains(&edge_id));
            let interval = edge::interval(&b, edge_id).unwrap();
            let xyz = edge::curve(&b, edge_id).unwrap().unwrap();
            let (uv, _) = eu::uv_trim_curve(&b, *id).unwrap();
            let forward = e.orientation == OrientType::Same;
            let height = [0., 5.][index];
            let ring = super::super::radial_curve::prove_native_radial_curve_with_work(
                &k,
                &MeshWork::new(),
                xyz,
                interval,
                forward,
                &chart,
                [0.; 2],
                height,
                radius,
                1e-6,
            )
            .unwrap();
            assert!(ring.world_error_upper <= 1e-6);
            let (cap, next_sense) = super::super::radial_curve::prove_native_radial_cap_with_work(
                &k,
                &MeshWork::new(),
                plane,
                uv.unwrap(),
                xyz,
                interval,
                forward,
                &chart,
                [0.; 2],
                height,
                radius,
                1e-6,
            )
            .unwrap();
            assert!(cap <= 1e-6 && next_sense == ring.sense);
        }
    }

    #[test]
    fn native_cone_completes_its_rectangle_at_one_real_pole() {
        let mut k = Kernel::default();
        let w = MeshWork::new();
        let mut b = create_cone(&mut k, Vec3::ZERO, 0., 4., 5.).unwrap();
        construct_exact_cone_seams(&k, &w, &mut b).unwrap();
        let chart = AxialEndpointProposal {
            origin: [0.; 3],
            columns: [[1., 0., 0.], [0., 1., 0.], [0., 0., 1.]],
            rows: Vec::new(),
        };
        let law = RadiusLaw {
            height: [0., 5.],
            radius: [0., 4.],
        };
        let proof =
            prove_native_radial_topology_with_work(&k, &w, &b, &chart, [0.; 2], law, 1e-6).unwrap();
        assert_eq!(proof.caps[0], None);
        assert!(proof.caps[1].is_some());
        assert_eq!(proof.rectangle.edges.len(), 3);
        assert!(
            prove_native_radial_boundary_with_work(&k, &w, &b, &chart, [0.; 2], law, 1e-6).unwrap()
                <= 1e-6
        );
    }
}
