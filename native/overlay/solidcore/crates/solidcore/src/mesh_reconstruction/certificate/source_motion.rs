//! Whole-time fixed-complex source motion (not upstream).
//!
//! A proven exact-alias closed source2-manifold has circular vertex links and no
//! local cut points. EVERY retained triangle must stay nondegenerate, and EVERY
//! pair must meet only its declared shared simplex for ALL time. Continuous
//! vertex-linear trajectories then form a linear isotopy on the fixed complex.
//! Starbird1977, Flexible regular neighborhoods for complexes in E3, Thm3.1,
//! extends this family to a regular neighborhood. Its interior supplies the open
//! extension required by Edwards--Kirby1971, Cor1.2. Thus this precise closed
//! fixed-complex class has an ambient extension; a bilinear track is NOT assumed
//! piecewise linear merely because each time level is.
//! <https://topology.nipissingu.ca/tp/reprints/v02/tp02215.pdf>
//! <https://www.maths.gla.ac.uk/~mpowell/Edwards%20Kirby.pdf>
//!
//! The maximum vertex displacement bounds BOTH whole endpoint surfaces via the
//! same barycentric simplex coordinates. No sampled time/vertex residual grades
//! a surface. This token proves only SOURCE motion, never final native S/CW or
//! canonical-body adoption. Material/native region and full target proof remain.
//! Deviations: iterative dyadic time refinement, maximum depth24. All pairs are
//! proved or excluded by strictly disjoint whole-time swept boxes, using the shared
//! source BVH. Inclusive touching/unknown boxes always reach the original exact
//! predicate in its original surviving pair order. Shared limits are not increased.
use super::super::work::MeshWork;
use super::exact_geometry as x;
use super::hulls::{point_distance_upper, PointBox, Triangle};
use super::source_index::ConservativeIndex;
use super::source_topology::{
    exact_rays_separated, simplex_only, triangle_box_is_regular, SourceManifold,
};
use crate::blend::fillet_section::interval::Ivl;
use crate::{Kernel, Result, SolidError};
const OP: &str = "mesh_reconstruction::certificate::source_motion";
const MAX_DEPTH: u32 = 24;
// Same complete broad-phase visit bound used by source topology preflight.
const MAX_BROAD_VISITS: usize = 4_000_000;
fn invariant(reason: &'static str) -> SolidError {
    SolidError::PortInvariant {
        operation: OP,
        reason,
    }
}
fn arithmetic() -> SolidError {
    SolidError::Unsupported {
        operation: OP,
        reason: "exact source motion outside certified arithmetic range",
    }
}
pub(crate) struct SourceMotion<'a, 'raw> {
    source: &'a SourceManifold<'raw>,
    endpoints: &'a [x::P],
    distance_upper: f64,
    proved_time_cells: usize,
    pair_counts: MotionPairCounts,
}
impl<'a, 'raw> SourceMotion<'a, 'raw> {
    pub(crate) fn source(&self) -> &'a SourceManifold<'raw> {
        self.source
    }
    pub(crate) fn endpoints(&self) -> &'a [x::P] {
        self.endpoints
    }
    pub(crate) fn distance_upper(&self) -> f64 {
        self.distance_upper
    }
    pub(crate) fn pair_counts(&self) -> MotionPairCounts {
        self.pair_counts
    }
    pub(crate) fn proved_time_cells(&self) -> usize {
        self.proved_time_cells
    }
}
/// Diagnostic counts, never an acceptance proof or a timing comparison.
#[derive(Clone, Copy, Debug)]
pub(crate) struct MotionPairCounts {
    pub(crate) cartesian_pairs_per_cell: usize,
    pub(crate) pair_phase_cells: usize,
    pub(crate) broad_candidates: usize,
    pub(crate) exact_checks: usize,
}
pub(crate) enum SourceMotionVerdict<'a, 'raw> {
    Proven(SourceMotion<'a, 'raw>),
    Undecided(&'static str),
}
struct VertexMotion {
    start: x::P,
    delta: x::P,
    start_bounds: PointBox,
    delta_bounds: PointBox,
}
fn enclose(p: &x::P) -> Option<PointBox> {
    let [a, b, c] = p.each_ref().map(x::interval);
    Some([a?, b?, c?])
}
fn point_at(p: &VertexMotion, t: f64) -> Option<x::P> {
    let [a, b, c] = &p.start;
    let [da, db, dc] = &p.delta;
    Some([
        x::add(a, &x::scale(da, t)?)?,
        x::add(b, &x::scale(db, t)?)?,
        x::add(c, &x::scale(dc, t)?)?,
    ])
}
fn triangle(boxes: &[PointBox], ids: [u32; 3]) -> Option<Triangle> {
    let [a, b, c] = ids.map(|id| usize::try_from(id).ok().and_then(|i| boxes.get(i).copied()));
    Some([a?, b?, c?])
}
// Every ray is affine in time relative to the SAME shared vertex trajectory.
// Strict separation of all signed endpoint rays by ONE functional separates
// every whole triangle cone over the COMPLETE interval by convexity.
fn vertex_pair(
    k: &Kernel,
    work: &MeshWork,
    motions: &[VertexMotion],
    aid: [u32; 3],
    bid: [u32; 3],
    interval: [f64; 2],
) -> Result<bool> {
    let Some(shared) = aid.iter().find(|id| bid.contains(id)).copied() else {
        return Err(invariant(
            "shared-vertex motion pair lacks its declared vertex",
        ));
    };
    let get = |id: u32| usize::try_from(id).ok().and_then(|i| motions.get(i));
    let origin = get(shared).ok_or_else(|| invariant("source motion shared alias missing"))?;
    work.spend_core(k, 0)?;
    let mut rays = Vec::new();
    for (ids, positive) in [(aid, true), (bid, false)] {
        for id in ids {
            if id == shared {
                continue;
            }
            let p = get(id).ok_or_else(|| invariant("source motion alias missing"))?;
            for t in interval {
                work.spend_core(k, 1)?;
                work.reserve_cells_core(k, 1)?;
                let p = point_at(p, t).ok_or_else(arithmetic)?;
                let v = point_at(origin, t).ok_or_else(arithmetic)?;
                let ray = if positive {
                    x::difference(&p, &v)
                } else {
                    x::difference(&v, &p)
                }
                .ok_or_else(arithmetic)?;
                rays.push(ray);
            }
        }
    }
    if rays.len() != 8 {
        return Err(invariant(
            "one shared-vertex pair must have eight endpoint rays",
        ));
    }
    exact_rays_separated(k, work, &rays)
}
fn motion_boxes(
    k: &Kernel,
    work: &MeshWork,
    motions: &[VertexMotion],
    time: Ivl,
    boxes: &mut [PointBox],
) -> Result<()> {
    if boxes.len() != motions.len() {
        return Err(invariant("motion box inventory differs"));
    }
    work.spend_core(k, motions.len())?;
    for (point, motion) in boxes.iter_mut().zip(motions) {
        let [a, b, c] = motion.start_bounds;
        let [da, db, dc] = motion.delta_bounds;
        *point = [a + da * time, b + db * time, c + dc * time];
        if point.iter().any(|v| !v.is_finite()) {
            return Err(arithmetic());
        }
    }
    Ok(())
}
struct TimeCell {
    lo: f64,
    hi: f64,
    depth: u32,
}
/// Certify the complete linear motion of the SAME validated surface complex.
/// New points are exact expansion coordinates in original world coordinates;
/// no original triangle or alias incidence can be substituted by the caller.
pub(crate) fn prove_source_motion_with_work<'a, 'raw>(
    k: &Kernel,
    work: &MeshWork,
    source: &'a SourceManifold<'raw>,
    endpoints: &'a [x::P],
    tolerance: f64,
) -> Result<SourceMotionVerdict<'a, 'raw>> {
    work.spend_core(k, 0)?;
    if !tolerance.is_finite() || tolerance <= 0. || endpoints.len() != source.alias_count() {
        return Ok(SourceMotionVerdict::Undecided(
            "source motion alias/tolerance contract differs",
        ));
    }
    let anchor = source
        .aliases
        .iter()
        .flatten()
        .next()
        .and_then(|ids| ids.first())
        .copied()
        .and_then(|id| source.position(id))
        .and_then(x::point)
        .ok_or_else(|| invariant("proven retained source has no original anchor"))?;
    let mut motions = Vec::new();
    let mut boxes = Vec::new();
    let mut distance_upper = 0.0_f64;
    for (index, end) in endpoints.iter().enumerate() {
        work.spend_core(k, 1)?;
        let start = u32::try_from(index)
            .ok()
            .and_then(|id| source.position(id))
            .and_then(x::point)
            .ok_or_else(|| invariant("proven source alias missing"))?;
        let delta = x::difference(end, &start).ok_or_else(arithmetic)?;
        let start = x::difference(&start, &anchor).ok_or_else(arithmetic)?;
        let delta_bounds = enclose(&delta).ok_or_else(arithmetic)?;
        distance_upper =
            distance_upper.max(point_distance_upper(delta_bounds, [Ivl::from(0.); 3])?);
        work.reserve_cells_core(k, 2)?;
        boxes.push([Ivl::from(0.); 3]);
        motions.push(VertexMotion {
            start_bounds: enclose(&start).ok_or_else(arithmetic)?,
            start,
            delta,
            delta_bounds,
        });
    }
    if !distance_upper.is_finite() || distance_upper > tolerance {
        return Ok(SourceMotionVerdict::Undecided(
            "whole source-motion displacement bound exceeds tolerance",
        ));
    }
    let mut retained = Vec::new();
    for ids in source.aliases.iter().flatten() {
        work.reserve_cells_core(k, 1)?;
        retained.push(*ids);
    }
    if retained.len() != source.retained_count || retained.is_empty() {
        return Err(invariant("proven retained source inventory differs"));
    }
    let pair_count = retained
        .len()
        .checked_mul(retained.len().saturating_sub(1))
        .and_then(|n| n.checked_div(2))
        .ok_or_else(arithmetic)?;
    // A vertex follows one affine trajectory. Its coordinate interval over [0,1]
    // contains every time value; triangle barycentric convexity then puts EVERY
    // moving triangle inside its three-vertex interval hull. Strictly separated
    // swept boxes can never meet at any time. All other pairs retain old proof.
    motion_boxes(k, work, &motions, Ivl::new(0., 1.), &mut boxes)?;
    let mut swept = Vec::new();
    for &ids in &retained {
        work.spend_core(k, 1)?;
        work.reserve_cells_core(k, 1)?;
        swept.push(triangle(&boxes, ids).ok_or_else(|| invariant("swept aliases missing"))?);
    }
    let index = ConservativeIndex::swept(k, work, &swept)?;
    let mut broad_remaining = MAX_BROAD_VISITS;
    let mut pair_counts = MotionPairCounts {
        cartesian_pairs_per_cell: pair_count,
        pair_phase_cells: 0,
        broad_candidates: 0,
        exact_checks: 0,
    };
    let mut pending = Vec::new();
    work.reserve_cells_core(k, 1)?;
    pending.push(TimeCell {
        lo: 0.,
        hi: 1.,
        depth: 0,
    });
    let mut proved_time_cells = 0usize;
    while let Some(cell) = pending.pop() {
        motion_boxes(k, work, &motions, Ivl::new(cell.lo, cell.hi), &mut boxes)?;
        let mut complete = true;
        for &ids in &retained {
            work.spend_core(k, 1)?;
            let t = triangle(&boxes, ids)
                .ok_or_else(|| invariant("proven triangle aliases missing"))?;
            if !triangle_box_is_regular(&t) {
                complete = false;
                break;
            }
        }
        if complete {
            pair_counts.pair_phase_cells = pair_counts
                .pair_phase_cells
                .checked_add(1)
                .ok_or_else(arithmetic)?;
            'pairs: for (i, &aid) in retained.iter().enumerate() {
                let Some(candidates) = index.overlapping_later(k, work, i, &mut broad_remaining)?
                else {
                    return Ok(SourceMotionVerdict::Undecided(
                        "complete swept broad phase exhausted its visit bound",
                    ));
                };
                work.spend_core(k, candidates.len())?;
                pair_counts.broad_candidates = pair_counts
                    .broad_candidates
                    .checked_add(candidates.len())
                    .ok_or_else(arithmetic)?;
                // The shared query returns sorted ORIGINAL retained indices.
                // Thus the surviving pair predicate order is unchanged (i,j).
                for j in candidates {
                    work.spend_core(k, 0)?;
                    let &bid = retained
                        .get(j)
                        .ok_or_else(|| invariant("swept candidate triangle missing"))?;
                    pair_counts.exact_checks = pair_counts
                        .exact_checks
                        .checked_add(1)
                        .ok_or_else(arithmetic)?;
                    let count = aid.iter().filter(|id| bid.contains(id)).count();
                    let good = if count == 1 {
                        vertex_pair(k, work, &motions, aid, bid, [cell.lo, cell.hi])?
                    } else {
                        let a = triangle(&boxes, aid)
                            .ok_or_else(|| invariant("source motion first triangle missing"))?;
                        let b = triangle(&boxes, bid)
                            .ok_or_else(|| invariant("source motion second triangle missing"))?;
                        simplex_only(&a, aid, &b, bid)
                    };
                    if !good {
                        complete = false;
                        break 'pairs;
                    }
                }
            }
        }
        if complete {
            proved_time_cells = proved_time_cells.checked_add(1).ok_or_else(arithmetic)?;
            continue;
        }
        if cell.depth >= MAX_DEPTH {
            return Ok(SourceMotionVerdict::Undecided(
                "full-time source embedding remains undecided at refinement bound",
            ));
        }
        let middle = 0.5 * cell.lo + 0.5 * cell.hi;
        if !(cell.lo < middle && middle < cell.hi) {
            return Err(arithmetic());
        }
        let depth = cell.depth.checked_add(1).ok_or_else(arithmetic)?;
        work.reserve_cells_core(k, 2)?;
        pending.push(TimeCell {
            lo: middle,
            hi: cell.hi,
            depth,
        });
        pending.push(TimeCell {
            lo: cell.lo,
            hi: middle,
            depth,
        });
    }
    work.spend_core(k, 0)?;
    Ok(SourceMotionVerdict::Proven(SourceMotion {
        source,
        endpoints,
        distance_upper,
        proved_time_cells,
        pair_counts,
    }))
}

#[cfg(test)]
mod broadphase_tests {
    use super::super::super::types::MeshInput;
    use super::super::source_topology::{validate_source_weld_with_work, SourceTopology};
    use super::*;
    use crate::kernel::KernelOptions;
    use std::collections::BTreeMap;
    fn grid_box(n: u32) -> MeshInput {
        let mut vertices = BTreeMap::new();
        let mut mesh = MeshInput {
            positions: Vec::new(),
            triangles: Vec::new(),
        };
        let frames = [
            ([0, 0, 0], [0, 0, 1], [0, 1, 0]),
            ([n, 0, 0], [0, 1, 0], [0, 0, 1]),
            ([0, 0, 0], [1, 0, 0], [0, 0, 1]),
            ([0, n, 0], [0, 0, 1], [1, 0, 0]),
            ([0, 0, 0], [0, 1, 0], [1, 0, 0]),
            ([0, 0, n], [1, 0, 0], [0, 1, 0]),
        ];
        for (o, u, v) in frames {
            for i in 0..n {
                for j in 0..n {
                    let mut ids = Vec::new();
                    for (a, b) in [(i, j), (i + 1, j), (i + 1, j + 1), (i, j + 1)] {
                        let p = [
                            o[0] + a * u[0] + b * v[0],
                            o[1] + a * u[1] + b * v[1],
                            o[2] + a * u[2] + b * v[2],
                        ];
                        let id = *vertices.entry(p).or_insert_with(|| {
                            let id = u32::try_from(mesh.positions.len()).unwrap();
                            mesh.positions.push(p.map(f64::from));
                            id
                        });
                        ids.push(id);
                    }
                    mesh.triangles
                        .extend([[ids[0], ids[1], ids[2]], [ids[0], ids[2], ids[3]]]);
                }
            }
        }
        mesh
    }
    #[test]
    fn practical_subdivided_closed_motion_checks_local_swept_candidates_not_cartesian_pairs() {
        let k = Kernel::new(&KernelOptions::default());
        let w = MeshWork::new();
        let input = grid_box(12);
        assert_eq!(input.triangles.len(), 1728);
        let prepared =
            super::super::super::prepare::prepare_conversion_with_work(&k, &w, &input, 0.05, &[])
                .unwrap();
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
            SourceTopology::Undecided(why) => panic!("source: {why:?}"),
        };
        let endpoints: Vec<_> = (0..source.alias_count())
            .map(|id| {
                let mut p = x::point(source.position(u32::try_from(id).unwrap()).unwrap()).unwrap();
                p[0] = x::add(&p[0], &x::scalar(1. / 1024.).unwrap()).unwrap();
                p
            })
            .collect();
        let proof = match prove_source_motion_with_work(&k, &w, &source, &endpoints, 0.05).unwrap()
        {
            SourceMotionVerdict::Proven(p) => p,
            SourceMotionVerdict::Undecided(why) => panic!("motion: {why}"),
        };
        let counts = proof.pair_counts();
        assert_eq!(counts.cartesian_pairs_per_cell, 1_492_128);
        assert!(counts.exact_checks > 0);
        assert!(counts.exact_checks <= counts.broad_candidates);
        assert!(
            counts.exact_checks < counts.cartesian_pairs_per_cell / 8,
            "expected spatial root-cause reduction, got {counts:?}"
        );
        eprintln!(
            "whole-motion 1728-triangle counters: {counts:?}; proved_time_cells={}",
            proof.proved_time_cells()
        );
        assert!(core::ptr::eq(proof.source(), &raw const source));
        assert!(proof.distance_upper() >= 1. / 1024. && proof.distance_upper() < 0.001);
    }
}
