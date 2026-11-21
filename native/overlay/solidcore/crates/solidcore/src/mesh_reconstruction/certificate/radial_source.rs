//! Finite source-side coverage under the polar (angle,height) projection.
//!
//! The SAME independently embedded retained source and whole-time affine model
//! are borrowed. Every selected triangle is counted once, internal edge uses
//! cancel oppositely, each vertex link is a disk/half-disk, and the patch is
//! connected with exactly the declared complete boundary circles. The radial
//! projection Jacobian is n dot (x,y,0)/rho^2; its numerator is AFFINE on every
//! triangle, so strict vertex enclosures prove its sign on the entire cell.
//! Complete boundary degree1 plus coherent positive local degree proves finite
//! annular coverage without missing or multiply covered sectors. A zero-radius
//! end is instead one actual source vertex with a complete degree1 disk star.
//!
//! The same-height radial correction is enclosed over EVERY triangle by the
//! separate Bernstein lemma, then lifted with the exact affine operator bound
//! and the original source motion ONCE. This source/model token is NOT proof of
//! Native target S, trims, CW/material, collars or canonical-body adoption.
//!
//! References: Lipman2014, doi:10.1137/130939754 (degree/global inversion);
//! the polar chart uses the displayed analytic Jacobian, not a PL angle fit.
//! Deviations: no recursion; unchanged original triangle/alias counts, MeshWork.
use super::super::angular_link::certify_angular_link;
use super::super::primitive_certificate::{cross, dot, sub, PointBox, Triangle};
use super::super::work::MeshWork;
use super::radial_band::{prove_radial_distance_with_work, RadiusLaw};
use super::radial_frame::AxialSourceView;
use crate::blend::fillet_section::interval::Ivl;
use crate::{Kernel, Result, SolidError};
use std::collections::{BTreeMap, BTreeSet};

const OP: &str = "mesh_reconstruction::certificate::radial_source";
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
fn size(n: usize, m: usize) -> Result<usize> {
    n.checked_mul(m)
        .ok_or_else(|| refused("radial source work/storage overflow"))
}
#[derive(Debug)]
pub(crate) struct RadialPatchClaim {
    pub(crate) triangles: Vec<usize>,
    pub(crate) center: [f64; 2],
    pub(crate) law: RadiusLaw,
    pub(crate) concave: bool,
}
pub(crate) struct SourceRadialPatch<'a, 'v, 'frame, 'raw> {
    source: &'a AxialSourceView<'v, 'frame, 'raw>,
    claim: &'a RadialPatchClaim,
    /// Directed ORIGINAL aliases of each complete boundary, never a fitted ring.
    rims: Vec<Vec<u32>>,
    pole: Option<u32>,
    local_upper: f64,
    world_upper: f64,
}
impl SourceRadialPatch<'_, '_, '_, '_> {
    pub(crate) fn source(&self) -> &AxialSourceView<'_, '_, '_> {
        self.source
    }
    pub(crate) fn claim(&self) -> &RadialPatchClaim {
        self.claim
    }
    pub(crate) fn rims(&self) -> &[Vec<u32>] {
        &self.rims
    }
    pub(crate) fn pole(&self) -> Option<u32> {
        self.pole
    }
    pub(crate) fn local_upper(&self) -> f64 {
        self.local_upper
    }
    pub(crate) fn world_upper(&self) -> f64 {
        self.world_upper
    }
}
fn coordinate(
    k: &Kernel,
    w: &MeshWork,
    s: &AxialSourceView<'_, '_, '_>,
    id: u32,
    center: [f64; 2],
) -> Result<(PointBox, [f64; 3])> {
    let row = s.row_with_work(k, w, id)?;
    let [u, v, h] = row;
    let [cx, cy] = center;
    // Exact equality of stored dyadics justifies an exact zero interval. No
    // tolerance-based snap is performed by a proof.
    let x = if u == cx {
        Ivl::from(0.)
    } else {
        Ivl::from(u) - Ivl::from(cx)
    };
    let y = if v == cy {
        Ivl::from(0.)
    } else {
        Ivl::from(v) - Ivl::from(cy)
    };
    Ok(([x, y, Ivl::from(h)], row))
}
type Links = BTreeMap<u32, BTreeMap<u32, BTreeSet<u32>>>;
fn connected<T: Copy + Ord>(
    k: &Kernel,
    w: &MeshWork,
    graph: &BTreeMap<T, BTreeSet<T>>,
) -> Result<bool> {
    let Some(seed) = graph.keys().next().copied() else {
        return Ok(false);
    };
    w.reserve_cells_core(k, size(graph.len(), 4)?)?;
    let mut pending = vec![seed];
    let mut seen = BTreeSet::new();
    while let Some(v) = pending.pop() {
        w.spend_core(
            k,
            size(
                graph
                    .len()
                    .checked_add(1)
                    .ok_or_else(|| refused("graph size overflow"))?,
                8,
            )?,
        )?;
        if !seen.insert(v) {
            continue;
        }
        let Some(adjacent) = graph.get(&v) else {
            return Ok(false);
        };
        for &a in adjacent {
            if !seen.contains(&a) {
                pending.push(a);
            }
        }
    }
    Ok(seen.len() == graph.len())
}
fn ring(k: &Kernel, w: &MeshWork, arcs: &mut BTreeMap<u32, u32>) -> Result<Vec<u32>> {
    let Some(start) = arcs.keys().next().copied() else {
        return Err(refused("radial boundary is empty"));
    };
    let mut out = Vec::new();
    let mut cursor = start;
    loop {
        w.spend_core(
            k,
            arcs.len()
                .checked_add(1)
                .ok_or_else(|| refused("ring count overflow"))?,
        )?;
        let Some(next) = arcs.remove(&cursor) else {
            return Err(refused("radial boundary chain is open"));
        };
        w.reserve_output_core(k, 1)?;
        out.push(cursor);
        if next == start {
            break;
        }
        if out.contains(&next) {
            return Err(refused("radial boundary revisits a non-start vertex"));
        }
        cursor = next;
    }
    Ok(out)
}
fn angular_degree(
    k: &Kernel,
    w: &MeshWork,
    s: &AxialSourceView<'_, '_, '_>,
    ids: &[u32],
    center: [f64; 2],
    expected: f64,
) -> Result<()> {
    let mut points = Vec::new();
    for &id in ids {
        w.reserve_cells_core(k, 4)?;
        let (p, _) = coordinate(k, w, s, id, center)?;
        let [x, y, _] = p;
        let p = [x, y, Ivl::from(0.)];
        points.push(p);
    }
    let z = [Ivl::from(0.), Ivl::from(0.), Ivl::from(1.)];
    certify_angular_link(k, w, &points, z).map_err(|e| match e {
        super::super::MeshError::Kernel(e) => e,
        _ => refused("complete radial boundary degree one was not established"),
    })?;
    let (Some(&a), Some(&b)) = (points.first(), points.get(1)) else {
        return Err(refused("radial ring too short"));
    };
    if !(dot(z, cross(a, b)) * Ivl::from(expected)).is_positive() {
        return Err(refused(
            "radial boundary has the wrong material orientation",
        ));
    }
    Ok(())
}

/// Establish complete finite source/model correspondence only. The caller
/// MUST still bind every original source face and every actual Native target
/// support/trim/edge/region to one common immutable model before adopting.
pub(crate) fn prove_source_radial_patch_with_work<'a, 'v, 'frame, 'raw>(
    k: &Kernel,
    w: &MeshWork,
    s: &'a AxialSourceView<'v, 'frame, 'raw>,
    c: &'a RadialPatchClaim,
    local_maximum: f64,
) -> Result<SourceRadialPatch<'a, 'v, 'frame, 'raw>> {
    w.spend_core(k, 32)?;
    if c.triangles.is_empty()
        || c.triangles.len() > s.world().retained_triangle_count()
        || !c.center.iter().all(|x| x.is_finite())
        || !c.law.valid()
        || !local_maximum.is_finite()
        || local_maximum < 0.
    {
        return Err(refused("invalid finite radial patch claim"));
    }
    let [lo, hi] = c.law.height;
    let [rlo, rhi] = c.law.radius;
    let pole_height = if rlo == 0. {
        Some(lo)
    } else if rhi == 0. {
        Some(hi)
    } else {
        None
    };
    let sense = if c.concave { -1. } else { 1. };
    let n = c.triangles.len();
    // Each selected triangle creates <=3 edge records,6 link arcs,3 coordinates
    // and one dual-graph node.128 slots cover records AND owning map/set headers.
    // Tree comparisons are bounded by the full selected inventory, not by an
    // assumed implementation-specific logarithmic height.
    let mut selected = BTreeSet::new();
    let mut edges: BTreeMap<(u32, u32), Vec<(u32, u32, usize)>> = BTreeMap::new();
    let mut links: Links = BTreeMap::new();
    let mut dual: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
    let mut vertices = BTreeSet::new();
    let mut pole = None;
    let mut upper = 0_f64;
    for &raw in &c.triangles {
        w.spend_core(
            k,
            size(
                n.checked_add(1)
                    .ok_or_else(|| refused("patch count overflow"))?,
                128,
            )?,
        )?;
        w.reserve_cells_core(k, 128)?;
        if !selected.insert(raw) {
            return Err(refused("radial source triangle selected more than once"));
        }
        let Some(Some(ids)) = s.world().retained_raw_triangle(raw) else {
            return Err(refused(
                "radial source selection is not an original retained triangle",
            ));
        };
        let [a, b, d] = ids;
        let pa = coordinate(k, w, s, a, c.center)?;
        let pb = coordinate(k, w, s, b, c.center)?;
        let pd = coordinate(k, w, s, d, c.center)?;
        let rows = [pa.1, pb.1, pd.1];
        let tri: Triangle = [pa.0, pb.0, pd.0];
        let normal = cross(sub(pb.0, pa.0), sub(pd.0, pa.0));
        for ((id, row), point) in ids.into_iter().zip(rows).zip(tri) {
            let [u, v, h] = row;
            if !(lo..=hi).contains(&h) {
                return Err(refused("source patch extends past declared finite heights"));
            }
            let is_pole = pole_height == Some(h) && [u, v] == c.center;
            if is_pole {
                if pole.is_some_and(|p| p != id) {
                    return Err(refused("radial pole has multiple original aliases"));
                }
                pole = Some(id);
            } else {
                if pole_height == Some(h) {
                    return Err(refused("zero-radius boundary is not one actual pole"));
                }
                let [x, y, _] = point;
                let jacobian = dot(normal, [x, y, Ivl::from(0.)]) * Ivl::from(sense);
                if !jacobian.is_finite() || !jacobian.is_positive() {
                    return Err(refused(
                        "whole-triangle polar projection has a fold or wrong material side",
                    ));
                }
            }
            vertices.insert(id);
        }
        let bound = prove_radial_distance_with_work(k, w, &tri, c.law, local_maximum)?;
        upper = upper.max(bound.upper());
        dual.entry(raw).or_default();
        for (from, to) in [(a, b), (b, d), (d, a)] {
            let entry = edges.entry((from.min(to), from.max(to))).or_default();
            entry.push((from, to, raw));
            if entry.len() > 2 {
                return Err(refused("radial patch has a nonmanifold edge"));
            }
        }
        for (v, x, y) in [(a, b, d), (b, d, a), (d, a, b)] {
            let link = links.entry(v).or_default();
            link.entry(x).or_default().insert(y);
            link.entry(y).or_default().insert(x);
        }
    }
    let mut boundary = BTreeMap::new();
    let mut incoming = BTreeSet::new();
    for uses in edges.values() {
        w.spend_core(
            k,
            size(
                n.checked_add(1)
                    .ok_or_else(|| refused("edge count overflow"))?,
                16,
            )?,
        )?;
        match uses.as_slice() {
            [(a, b, _)] => {
                if boundary.insert(*a, *b).is_some() || !incoming.insert(*b) {
                    return Err(refused("radial boundary branches or duplicates an edge"));
                }
            }
            [(a, b, f), (u, v, g)] if a == v && b == u && f != g => {
                dual.get_mut(f)
                    .ok_or_else(|| invariant("radial dual face missing"))?
                    .insert(*g);
                dual.get_mut(g)
                    .ok_or_else(|| invariant("radial dual face missing"))?
                    .insert(*f);
            }
            _ => return Err(refused("radial internal edges do not cancel oppositely")),
        }
    }
    if !connected(k, w, &dual)? {
        return Err(refused("radial patch is disconnected"));
    }
    let boundary_vertices: BTreeSet<_> = boundary.keys().copied().collect();
    if boundary_vertices != incoming {
        return Err(refused("radial boundary does not close"));
    }
    for (&vertex, link) in &links {
        w.spend_core(
            k,
            size(
                n.checked_add(1)
                    .ok_or_else(|| refused("link count overflow"))?,
                16,
            )?,
        )?;
        if !connected(k, w, link)? {
            return Err(refused("radial patch has a disconnected vertex link"));
        }
        let ones = link.values().filter(|v| v.len() == 1).count();
        if link.values().any(|v| v.is_empty() || v.len() > 2)
            || (boundary_vertices.contains(&vertex) && ones != 2)
            || (!boundary_vertices.contains(&vertex) && ones != 0)
        {
            return Err(refused(
                "radial patch is not a disk/half-disk at every vertex",
            ));
        }
    }
    let integer =
        |v: usize| i64::try_from(v).map_err(|_| refused("radial Euler inventory overflow"));
    let euler = integer(vertices.len())?
        .checked_sub(integer(edges.len())?)
        .and_then(|v| v.checked_add(i64::try_from(n).ok()?))
        .ok_or_else(|| refused("radial Euler sum overflow"))?;
    if (pole_height.is_some() && (pole.is_none() || euler != 1))
        || (pole_height.is_none() && (pole.is_some() || euler != 0))
    {
        return Err(refused(
            "radial source has the wrong complete finite surface topology",
        ));
    }
    let mut rims = Vec::new();
    let mut levels = BTreeSet::new();
    while !boundary.is_empty() {
        let ids = ring(k, w, &mut boundary)?;
        let first = *ids
            .first()
            .ok_or_else(|| refused("empty radial boundary"))?;
        let [_, _, h] = s.row_with_work(k, w, first)?;
        if h != lo && h != hi {
            return Err(refused("radial boundary is not a full finite end"));
        }
        let level = if h == lo { 0u8 } else { 1u8 };
        if !levels.insert(level) {
            return Err(refused("multiple radial boundary loops occupy one end"));
        }
        for &id in &ids {
            let [_, _, current_height] = s.row_with_work(k, w, id)?;
            if current_height != h {
                return Err(refused("radial boundary changes height"));
            }
        }
        angular_degree(
            k,
            w,
            s,
            &ids,
            c.center,
            if level == 0 { sense } else { -sense },
        )?;
        rims.push(ids);
    }
    if pole_height.is_some() {
        if rims.len() != 1 {
            return Err(refused(
                "a radial pole disk must have one complete regular boundary",
            ));
        }
        let p = pole.ok_or_else(|| invariant("proved radial disk pole missing"))?;
        if boundary_vertices.contains(&p) {
            return Err(refused(
                "the radial pole must have a complete interior star",
            ));
        }
        let link = links
            .get(&p)
            .ok_or_else(|| invariant("radial pole star missing"))?;
        let start = *link
            .keys()
            .next()
            .ok_or_else(|| refused("empty radial pole link"))?;
        let mut order = Vec::new();
        let mut current = start;
        let mut previous = None;
        loop {
            w.spend_core(
                k,
                size(
                    link.len()
                        .checked_add(1)
                        .ok_or_else(|| refused("pole link overflow"))?,
                    8,
                )?,
            )?;
            w.reserve_output_core(k, 1)?;
            order.push(current);
            let neighbours = link
                .get(&current)
                .ok_or_else(|| invariant("radial pole neighbour missing"))?;
            let next = *neighbours
                .iter()
                .find(|q| Some(**q) != previous)
                .ok_or_else(|| refused("radial pole link is open"))?;
            if next == start {
                break;
            }
            if order.contains(&next) {
                return Err(refused("radial pole link repeats"));
            }
            previous = Some(current);
            current = next;
        }
        // The link is already a single simple cycle. Its chosen traversal may
        // have either orientation; the separate triangle Jacobians bind material.
        let points: Vec<_> = order
            .iter()
            .map(|&id| coordinate(k, w, s, id, c.center).map(|(p, _)| p))
            .collect::<Result<_>>()?;
        certify_angular_link(k, w, &points, [Ivl::from(0.), Ivl::from(0.), Ivl::from(1.)])
            .map_err(|e| match e {
                super::super::MeshError::Kernel(e) => e,
                _ => refused("pole star has no degree-one radial link"),
            })?;
    } else if rims.len() != 2 || levels.len() != 2 {
        return Err(refused(
            "a finite radial annulus needs both complete boundaries",
        ));
    }
    w.spend_core(k, 0)?;
    Ok(SourceRadialPatch {
        source: s,
        claim: c,
        rims,
        pole,
        local_upper: upper,
        world_upper: s.world_error_upper(upper)?,
    })
}

#[cfg(test)]
mod tests {
    use super::super::super::{prepare_conversion, MeshInput};
    use super::super::radial_frame::{build_axial_model, AxialEndpointProposal};
    use super::super::source_motion::{prove_source_motion_with_work, SourceMotionVerdict};
    use super::super::source_topology::{validate_source_weld_with_work, SourceTopology};
    use super::*;

    fn input(apex: bool) -> (MeshInput, Vec<usize>) {
        let n = 32u32;
        let mut mesh = MeshInput {
            positions: Vec::new(),
            triangles: Vec::new(),
        };
        for (h, r) in [(0., 5.), (4., if apex { 0. } else { 3. })] {
            if r == 0. {
                mesh.positions.push([0., 0., h]);
                continue;
            }
            for i in 0..n {
                let a = std::f64::consts::TAU * f64::from(i) / f64::from(n);
                mesh.positions.push([r * a.cos(), r * a.sin(), h]);
            }
        }
        for i in 0..n {
            let j = (i + 1) % n;
            if apex {
                mesh.triangles.push([i, j, n]);
            } else {
                mesh.triangles.extend([[i, j, n + j], [i, n + j, n + i]]);
            }
        }
        let selected = (0..mesh.triangles.len()).collect();
        let c0 = u32::try_from(mesh.positions.len()).unwrap();
        mesh.positions.push([0., 0., 0.]);
        for i in 0..n {
            mesh.triangles.push([c0, (i + 1) % n, i]);
        }
        if !apex {
            let c1 = u32::try_from(mesh.positions.len()).unwrap();
            mesh.positions.push([0., 0., 4.]);
            for i in 0..n {
                mesh.triangles.push([c1, n + i, n + (i + 1) % n]);
            }
        }
        (mesh, selected)
    }
    fn check(
        apex: bool,
        pose: bool,
        change: impl FnOnce(&mut RadialPatchClaim),
    ) -> Result<(usize, bool, f64)> {
        let (mut input, selected) = input(apex);
        let origin = if pose { [10., 20., 30.] } else { [0.; 3] };
        let columns = if pose {
            [[0., 1., 0.], [0., 0., 1.], [1., 0., 0.]]
        } else {
            [[1., 0., 0.], [0., 1., 0.], [0., 0., 1.]]
        };
        if pose {
            for p in &mut input.positions {
                let [x, y, z] = *p;
                *p = [10. + z, 20. + x, 30. + y];
            }
        }
        let k = Kernel::default();
        let w = MeshWork::new();
        let prepared = prepare_conversion(&k, &input, 0.05, &[]).unwrap();
        let source = match validate_source_weld_with_work(
            &k,
            &w,
            &input.positions,
            &input.triangles,
            &prepared.weld,
        )
        .unwrap()
        {
            SourceTopology::Proven(p) => p,
            SourceTopology::Undecided(r) => panic!("source fixture: {r:?}"),
        };
        let mut rows = Vec::new();
        for i in 0..source.alias_count() {
            let [x, y, z] = source.position(u32::try_from(i).unwrap()).unwrap();
            rows.push(if pose {
                [y - 20., z - 30., x - 10.]
            } else {
                [x, y, z]
            });
        }
        let proposal = AxialEndpointProposal {
            origin,
            columns,
            rows,
        };
        let model = build_axial_model(&k, &w, source.alias_count(), &proposal).unwrap();
        let motion =
            match prove_source_motion_with_work(&k, &w, &source, model.points(), 0.05).unwrap() {
                SourceMotionVerdict::Proven(p) => p,
                SourceMotionVerdict::Undecided(r) => panic!("source motion fixture: {r}"),
            };
        let view = AxialSourceView::bind(&model, &motion).unwrap();
        let mut claim = RadialPatchClaim {
            triangles: selected,
            center: [0.; 2],
            law: RadiusLaw {
                height: [0., 4.],
                radius: [5., if apex { 0. } else { 3. }],
            },
            concave: false,
        };
        change(&mut claim);
        let proof = prove_source_radial_patch_with_work(&k, &w, &view, &claim, 0.05)?;
        assert!(std::ptr::eq(proof.source(), &view));
        assert!(std::ptr::eq(proof.claim(), &claim));
        assert!(proof.local_upper() <= 0.05);
        let solid =
            super::super::radial_solid_source::prove_source_radial_solid_with_work(&k, &w, &proof)?;
        assert_eq!(solid.filled_caps(), if apex { 1 } else { 2 });
        assert!(std::ptr::eq(solid.side(), &proof));
        Ok((
            proof.rims().len(),
            proof.pole().is_some(),
            proof.world_upper(),
        ))
    }
    #[test]
    fn complete_frustum_strip_covers_both_finite_rims() {
        let (rims, pole, error) = check(false, false, |_| {}).unwrap();
        assert_eq!(rims, 2);
        assert!(!pole);
        assert!(error > 0. && error < 0.05);
    }
    #[test]
    fn complete_cone_disk_retains_its_degree_one_apex_star() {
        let (rims, pole, error) = check(true, false, |_| {}).unwrap();
        assert_eq!(rims, 1);
        assert!(pole);
        assert!(error > 0. && error < 0.05);
    }
    #[test]
    fn source_only_axis_chooser_finds_frustum_and_reverses_for_a_real_apex() {
        use super::super::radial_proposal::propose_radial_solid_with_work;
        use super::super::source_view::ExactSourceView;
        use crate::math::Vec3;
        for apex in [false, true] {
            let (raw, side) = input(apex);
            let mut k = Kernel::default();
            let w = MeshWork::new();
            let prepared = prepare_conversion(&k, &raw, 0.05, &[]).unwrap();
            let source = match validate_source_weld_with_work(
                &k,
                &w,
                &raw.positions,
                &raw.triangles,
                &prepared.weld,
            )
            .unwrap()
            {
                SourceTopology::Proven(source) => source,
                SourceTopology::Undecided(r) => panic!("source proposal fixture: {r:?}"),
            };
            let proposal = propose_radial_solid_with_work(
                &k,
                &w,
                &ExactSourceView::original(&source),
                &[Vec3::Z],
                0.05,
            )
            .unwrap()
            .unwrap();
            assert_eq!(proposal.side.triangles, side);
            let [a, b] = proposal.side.law.radius;
            assert!((b - if apex { 5. } else { 3. }).abs() < 1e-10);
            assert!((a - if apex { 0. } else { 5. }).abs() < 1e-10);
            let model = build_axial_model(&k, &w, source.alias_count(), &proposal.chart).unwrap();
            let motion = match prove_source_motion_with_work(&k, &w, &source, model.points(), 0.05)
                .unwrap()
            {
                SourceMotionVerdict::Proven(motion) => motion,
                SourceMotionVerdict::Undecided(r) => panic!("proposed exact endpoint motion: {r}"),
            };
            let view = AxialSourceView::bind(&model, &motion).unwrap();
            let side =
                prove_source_radial_patch_with_work(&k, &w, &view, &proposal.side, 0.05).unwrap();
            let solid = super::super::radial_solid_source::prove_source_radial_solid_with_work(
                &k, &w, &side,
            )
            .unwrap();
            assert_eq!(solid.filled_caps(), if apex { 1 } else { 2 });
            let b = proposal.build_candidate(&mut k, &w).unwrap();
            assert_eq!(b.face_list().len(), if apex { 2 } else { 3 });
        }
    }

    #[test]
    fn placed_frustum_uses_the_same_original_source_motion() {
        let (rims, pole, error) = check(false, true, |_| {}).unwrap();
        assert_eq!(rims, 2);
        assert!(!pole);
        assert!(error < 0.05);
    }
    #[test]
    fn missing_side_triangle_is_not_an_annular_cover() {
        assert!(check(false, false, |c| {
            c.triangles.pop();
        })
        .is_err());
    }
    #[test]
    fn duplicate_side_triangle_and_wrong_material_side_are_refused() {
        assert!(check(false, false, |c| {
            c.triangles.push(c.triangles[0]);
        })
        .is_err());
        assert!(check(false, false, |c| {
            c.concave = true;
        })
        .is_err());
    }
}
