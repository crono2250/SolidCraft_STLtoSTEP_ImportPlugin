//! The existing AnalyticV1 reconstruction candidate engine and shared product planner.
//! Saved-generation geometry/order follows the pinned implementation. Its local checks
//! are candidate constraints, NOT the new generation's complete original/final proof.
//! Multi-axis cuts/caps currently lack original-source ancestry for final certification.
//!
//! Deviations: no upstream counterpart. No recursion.

use std::collections::BTreeMap;

use super::work::MeshWork;
use crate::kernel::Kernel;
use crate::math::{Vec2, Vec3};
use crate::prism::profile::{Loop2, Region2, Seg2};
use crate::{Brep, Result, SolidError};

use self::geometry::{
    circle, corners, distance_to_segment, nest_regions, normalize, polygon,
    ring_at_sharpest_corner, segment_length, MeshPlane, PlanarVector,
};

mod cap;
mod curves;
mod geometry;
mod native;
mod parts;

#[cfg(test)]
mod tests;

/// Owned source triangles used only by mesh reconstruction, never a solid's display mesh.
#[derive(Clone, Debug, Default)]
pub(super) struct TriMesh {
    pub(super) positions: Vec<Vec3>,
    pub(super) triangles: Vec<[u32; 3]>,
}

impl TriMesh {
    fn size(&self) -> f64 {
        mesh_size(&self.positions)
    }

    /// Signed source volume, in the same triangle order as the former split-corner measurement.
    fn volume(&self) -> f64 {
        let mut six = 0.;
        for &[a, b, c] in &self.triangles {
            if let (Some(a), Some(b), Some(c)) = (
                self.positions.get(a as usize),
                self.positions.get(b as usize),
                self.positions.get(c as usize),
            ) {
                six += a.dot(b.cross(*c));
            }
        }
        six / 6.
    }
}

/// Borrowed native source data; no copy, weld, orientation repair or proof flag.
#[derive(Clone, Copy)]
pub(super) struct MeshView<'a> {
    pub(super) positions: &'a [Vec3],
    pub(super) triangles: &'a [[u32; 3]],
}
impl MeshView<'_> {
    fn size(self) -> f64 {
        mesh_size(self.positions)
    }
}
impl TriMesh {
    fn view(&self) -> MeshView<'_> {
        MeshView {
            positions: &self.positions,
            triangles: &self.triangles,
        }
    }
}

/// Diagonal of the bounding box, used to scale the certification tolerances.
fn mesh_size(positions: &[Vec3]) -> f64 {
    let Some(&first) = positions.first() else {
        return 0.;
    };
    let (lo, hi) = positions.iter().fold((first, first), |(lo, hi), p| {
        (
            Vec3::new(lo.x.min(p.x), lo.y.min(p.y), lo.z.min(p.z)),
            Vec3::new(hi.x.max(p.x), hi.y.max(p.y), hi.z.max(p.z)),
        )
    });
    (hi - lo).length()
}

/// Maximum input triangle count. A mesh may also carry up to three vertices per triangle of this limit.
pub const MAX_TRIANGLES: usize = 50_000;
const MAX_BOUNDARY: usize = 8192;
/// Nesting certification runs two planar booleans per pair of boundary loops,
/// so the loop count (not the segment count) bounds its cost: 50 loops (an
/// outline with 49 holes) is at most 1225 pairs and 2450 booleans.
const MAX_LOOPS: usize = 50;

/// A malformed mesh or a reconstruction that fails a certificate.
fn invalid(message: &'static str) -> SolidError {
    SolidError::invalid_input("reconstruct mesh", message)
}

/// Replay the saved AnalyticV1 candidate construction/order. Its historical
/// local constraints do not replace CertifiedV2 canonical original-source proof.
/// Returns `None` when the existing candidate search produces no supported fit.
///
/// # Errors
/// Returns an error for malformed input, a tolerance outside 0.000001–1 mm, exceeded work
/// budgets, or a failed construction or validation of a certified candidate.
pub fn reconstruct(
    k: &mut Kernel,
    positions: &[Vec3],
    triangles: &[[u32; 3]],
    tolerance: f64,
) -> Result<Option<Brep>> {
    let work = MeshWork::new();
    reconstruct_with_work(k, &work, positions, triangles, tolerance)
}

/// Replay AnalyticV1 using the SAME caller-owned complete-workflow ledger.
/// The standalone `reconstruct` convenience creates one ledger; Ops multi-stage
/// input/record handoffs call this entry and retain its authoritative budget state.
/// This changes no candidate arithmetic, construction order or saved face order.
///
/// # Errors
/// Original malformed-input/native failures, cancellation and shared-work exhaustion.
pub fn reconstruct_with_work(
    k: &mut Kernel,
    work: &MeshWork,
    positions: &[Vec3],
    triangles: &[[u32; 3]],
    tolerance: f64,
) -> Result<Option<Brep>> {
    work.spend_core(k, 0)?;
    if !tolerance.is_finite() || !(1e-6..=1.).contains(&tolerance) {
        return Err(invalid("tolerance must be between 0.000001 and 1 mm"));
    }
    check_budget(positions, triangles)?;
    work.spend_core(
        k,
        positions
            .len()
            .checked_add(triangles.len())
            .ok_or_else(|| invalid("input work count overflow"))?,
    )?;
    let mesh = weld(k, work, positions, triangles, tolerance)?;
    work.spend_core(k, 0)?;
    let mut edges: BTreeMap<(u32, u32), (usize, i32)> = BTreeMap::new();
    let mut axes: BTreeMap<(i64, i64, i64), (Vec3, f64)> = BTreeMap::new();
    for &[a, b, c] in &mesh.triangles {
        work.spend_core(k, 1)?;
        let (Some(pa), Some(pb), Some(pc)) = (
            mesh.positions.get(a as usize),
            mesh.positions.get(b as usize),
            mesh.positions.get(c as usize),
        ) else {
            return Err(invalid("triangle refers to a missing vertex"));
        };
        let cross = (*pb - *pa).cross(*pc - *pa);
        // Welding dropped the triangles of no area.
        let Some(mut n) = normalize(cross) else {
            return Err(invalid("degenerate triangle"));
        };
        for (a, b) in [(a, b), (b, c), (c, a)] {
            let entry = edges.entry((a.min(b), a.max(b))).or_default();
            entry.0 += 1;
            entry.1 += if a < b { 1 } else { -1 };
        }
        if n.x < -1e-8 || (n.x.abs() <= 1e-8 && (n.y < -1e-8 || (n.y.abs() <= 1e-8 && n.z < 0.))) {
            n = -n;
        }
        let key = (
            (n.x * 1e7).round() as i64,
            (n.y * 1e7).round() as i64,
            (n.z * 1e7).round() as i64,
        );
        let entry = axes.entry(key).or_insert((n, 0.));
        entry.1 += cross.length();
    }
    if edges
        .values()
        .any(|&(count, balance)| count != 2 || balance != 0)
    {
        return Err(invalid(
            "mesh must be closed and consistently oriented, with two triangles per edge",
        ));
    }
    let mut axes: Vec<_> = axes.into_values().collect();
    axes.sort_by(|a, b| b.1.total_cmp(&a.1));
    for &(axis, _) in axes.iter().take(16) {
        if let Some(result) = extrusion(k, work, &mesh, axis, tolerance)? {
            return Ok(Some(result));
        }
    }
    parts::reconstruct(k, work, &mesh, tolerance)
}

fn check_budget(positions: &[Vec3], triangles: &[[u32; 3]]) -> Result<()> {
    if triangles.len() > MAX_TRIANGLES {
        return Err(invalid(
            "mesh exceeds the conversion limit of 50000 triangles",
        ));
    }
    if positions.len() > MAX_TRIANGLES * 3 {
        return Err(invalid(
            "mesh exceeds the conversion limit of 150000 vertices",
        ));
    }
    Ok(())
}

/// Merge nearby source vertices, discard degenerate triangles and unused vertices, and enforce bounded welding work.
fn weld(
    k: &Kernel,
    work: &MeshWork,
    source_positions: &[Vec3],
    source_triangles: &[[u32; 3]],
    tolerance: f64,
) -> Result<TriMesh> {
    check_budget(source_positions, source_triangles)?;
    let size = mesh_size(source_positions);
    let epsilon = (size.max(1.) * 1e-7).min(tolerance * 0.01).max(1e-9);
    if !epsilon.is_finite()
        || source_positions.iter().any(|p| {
            [p.x, p.y, p.z]
                .iter()
                .any(|v| !v.is_finite() || v.abs() >= 1e9 || (v / epsilon).abs() > 1e15)
        })
    {
        return Err(invalid("mesh coordinates exceed the conversion budget"));
    }
    let key = |p: Vec3| {
        (
            (p.x / epsilon).floor() as i64,
            (p.y / epsilon).floor() as i64,
            (p.z / epsilon).floor() as i64,
        )
    };
    let mut grid = BTreeMap::<_, Vec<u32>>::new();
    let mut positions: Vec<Vec3> = Vec::new();
    let mut remap = Vec::new();
    let mut comparisons = 0usize;
    for &p in source_positions {
        work.spend_core(k, 1)?;
        let k = key(p);
        let mut found = None;
        for dx in -1..=1 {
            for dy in -1..=1 {
                for dz in -1..=1 {
                    for &i in grid
                        .get(&(k.0 + dx, k.1 + dy, k.2 + dz))
                        .into_iter()
                        .flatten()
                    {
                        comparisons += 1;
                        if comparisons > 8_000_000 {
                            return Err(invalid("vertex welding exceeds its work budget"));
                        }
                        if positions
                            .get(i as usize)
                            .is_some_and(|q| q.distance(p) <= epsilon)
                        {
                            found = Some(i);
                            break;
                        }
                    }
                }
            }
        }
        let i = if let Some(i) = found {
            i
        } else {
            let i = u32::try_from(positions.len()).map_err(|_| invalid("too many vertices"))?;
            positions.push(p);
            grid.entry(k).or_default().push(i);
            i
        };
        remap.push(i);
    }
    // A triangle of no area (its corners on one line, or welded into one another) adds no
    // surface, so it is dropped rather than refused (#4561); the closed-manifold check that
    // follows still refuses a mesh that needed it to close. Only the vertices the kept triangles
    // use stay, so a dropped triangle's corner cannot widen the part's extent.
    let mut used: Vec<Option<u32>> = vec![None; positions.len()];
    let mut kept_positions: Vec<Vec3> = Vec::new();
    let mut triangles = Vec::new();
    for &[a, b, c] in source_triangles {
        work.spend_core(k, 1)?;
        let (Some(&a), Some(&b), Some(&c)) = (
            remap.get(a as usize),
            remap.get(b as usize),
            remap.get(c as usize),
        ) else {
            return Err(invalid("missing triangle vertex"));
        };
        let (Some(&pa), Some(&pb), Some(&pc)) = (
            positions.get(a as usize),
            positions.get(b as usize),
            positions.get(c as usize),
        ) else {
            return Err(invalid("missing triangle vertex"));
        };
        if normalize((pb - pa).cross(pc - pa)).is_none() {
            continue;
        }
        let mut keep = |i: u32| -> Result<u32> {
            let slot = used
                .get_mut(i as usize)
                .ok_or_else(|| invalid("missing triangle vertex"))?;
            if let Some(k) = *slot {
                return Ok(k);
            }
            let k =
                u32::try_from(kept_positions.len()).map_err(|_| invalid("too many vertices"))?;
            kept_positions.push(
                positions
                    .get(i as usize)
                    .copied()
                    .ok_or_else(|| invalid("missing triangle vertex"))?,
            );
            *slot = Some(k);
            Ok(k)
        };
        triangles.push([keep(a)?, keep(b)?, keep(c)?]);
    }
    if triangles.is_empty() {
        return Err(invalid("the mesh has no triangle of any area"));
    }
    let mut mesh = TriMesh {
        positions: kept_positions,
        triangles,
    };
    // Welding can join formerly separate patches, so make their winding consistent
    // before testing manifoldness and orient a closed shell outward.
    parts::orient(&mut mesh);
    work.spend_core(k, 0)?;
    Ok(mesh)
}

/// Certify matching caps and straight walls before building an analytic prism with valid nesting and volume.
/// One untrusted source-only ordinary extrusion event, in the original loop order.
/// This contains no native result and no acceptance status.
pub(super) struct PrismProposal {
    frame: crate::eval::Frame,
    height: f64,
    raw: Vec<Loop2>,
    fitted: Vec<Loop2>,
    cap_loops: Vec<Vec<u32>>,
    epsilon: f64,
    size: f64,
}
impl PrismProposal {
    pub(super) fn into_plan(
        self,
        k: &Kernel,
        work: &MeshWork,
    ) -> Result<super::prismatic::PrismaticPlan> {
        work.spend_core(k, 0)?;
        let n = self.raw.len();
        work.spend_core(
            k,
            n.checked_mul(n)
                .ok_or_else(|| invalid("nesting work overflow"))?,
        )?;
        work.reserve_cells_core(
            k,
            n.checked_mul(3)
                .ok_or_else(|| invalid("nesting storage overflow"))?,
        )?;
        let mut parents = Vec::new();
        parents
            .try_reserve_exact(n)
            .map_err(|_| invalid("cannot allocate cap parent claims"))?;
        for (i, inner) in self.raw.iter().enumerate() {
            work.spend_core(k, 0)?;
            let mut parent = None;
            for (j, outer) in self.raw.iter().enumerate() {
                if i != j && geometry::contains_loop(outer, inner)? {
                    let area = outer.signed_area()?.value.abs();
                    if parent.is_none_or(|(_, old)| area < old) {
                        parent = Some((j, area));
                    }
                }
            }
            parents.push(parent.map(|(j, _)| j));
        }
        let raw_refs = self
            .raw
            .iter()
            .try_fold(0usize, |n, lp| n.checked_add(lp.segs.len()))
            .ok_or_else(|| invalid("raw profile count overflow"))?;
        let fitted_refs = self
            .fitted
            .iter()
            .try_fold(0usize, |n, lp| n.checked_add(lp.segs.len()))
            .ok_or_else(|| invalid("fitted profile count overflow"))?;
        work.reserve_cells_core(
            k,
            fitted_refs
                .checked_add(
                    n.checked_mul(3)
                        .ok_or_else(|| invalid("region storage overflow"))?,
                )
                .ok_or_else(|| invalid("region storage overflow"))?,
        )?;
        let public_refs = raw_refs
            .checked_add(fitted_refs)
            .and_then(|m| m.checked_mul(2))
            .and_then(|m| m.checked_add(n))
            .ok_or_else(|| invalid("plan output count overflow"))?;
        work.reserve_output_core(k, public_refs)?;
        let regions = nest_regions(&self.raw, &self.fitted)?
            .ok_or_else(|| invalid("unresolved cap nesting"))?;
        work.spend_core(k, 0)?;
        Ok(super::prismatic::PrismaticPlan {
            tool: super::PrismTool {
                frame: self.frame,
                regions,
                start: 0.,
                end: self.height,
            },
            nesting: super::ProfileNesting {
                raw: self.raw,
                fitted: self.fitted,
                epsilon: self.epsilon,
                size: self.size,
            },
            cap_loops: self.cap_loops,
            cap_loop_parents: parents,
        })
    }
}

/// The ONE ordinary product proposal used by old replay and new complete acceptance.
pub(super) fn propose_prism_with_work(
    k: &Kernel,
    work: &MeshWork,
    mesh: MeshView<'_>,
    axis: Vec3,
    tolerance: f64,
) -> Result<Option<PrismProposal>> {
    work.spend_core(k, 0)?;
    check_budget(mesh.positions, mesh.triangles)?;
    let refs = mesh
        .positions
        .len()
        .checked_mul(3)
        .and_then(|n| {
            mesh.triangles
                .len()
                .checked_mul(3)
                .and_then(|m| n.checked_add(m))
        })
        .ok_or_else(|| invalid("proposal storage overflow"))?;
    // Logical planning records: projected points/keys/cap aliases (<=3V),
    // plus both cap-edge maps (<=3T). This is not byte/allocator accounting.
    work.reserve_cells_core(k, refs)?;
    type Boundary = BTreeMap<(i64, i64), Vec<(i64, i64)>>;
    let (lo, hi) = mesh
        .positions
        .iter()
        .map(|p| p.dot(axis))
        .fold((f64::INFINITY, f64::NEG_INFINITY), |(lo, hi), h| {
            (lo.min(h), hi.max(h))
        });
    let height = hi - lo;
    let size = mesh.size();
    let epsilon = (size.max(1.) * 1e-7).min(tolerance * 0.01).max(1e-9);
    if height <= epsilon {
        return Ok(None);
    }
    let Some(plane) = MeshPlane::from_normal(axis * lo, axis) else {
        return Ok(None);
    };
    let mut caps = [BTreeMap::<(u32, u32), usize>::new(), BTreeMap::new()];
    for triangle in mesh.triangles {
        work.spend_core(k, 1)?;
        let [a, b, c] = *triangle;
        let (Some(pa), Some(pb), Some(pc)) = (
            mesh.positions.get(a as usize),
            mesh.positions.get(b as usize),
            mesh.positions.get(c as usize),
        ) else {
            return Err(invalid("missing triangle vertex"));
        };
        let hs = [pa.dot(axis), pb.dot(axis), pc.dot(axis)];
        let cap = if hs.iter().all(|h| (h - lo).abs() <= epsilon) {
            0
        } else if hs.iter().all(|h| (h - hi).abs() <= epsilon) {
            1
        } else {
            // STL stores coordinates as f32. Test the projected triangle's
            // distance from a line rather than amplifying that rounding into
            // an angular error on narrow side triangles.
            let [a, b, c] = [
                plane.to_local(*pa),
                plane.to_local(*pb),
                plane.to_local(*pc),
            ];
            let length = a.dist(b).max(b.dist(c)).max(c.dist(a));
            if (b - a).cross(c - a).abs() > epsilon * 3. * length {
                return Ok(None);
            }
            continue;
        };
        let Some(edges) = caps.get_mut(cap) else {
            return Ok(None);
        };
        for (a, b) in [(a, b), (b, c), (c, a)] {
            *edges.entry((a.min(b), a.max(b))).or_default() += 1;
        }
    }
    let raw_key = |p: Vec2| {
        (
            (p.x / epsilon).floor() as i64,
            (p.y / epsilon).floor() as i64,
        )
    };
    let mut positions = BTreeMap::<(i64, i64), Vec2>::new();
    let mut projected = Vec::new();
    for p in mesh.positions {
        work.spend_core(k, 1)?;
        let p = plane.to_local(*p);
        let k = raw_key(p);
        let mut canonical = None;
        for dx in -1..=1 {
            for dy in -1..=1 {
                let candidate = (k.0 + dx, k.1 + dy);
                if positions
                    .get(&candidate)
                    .is_some_and(|q| q.distance(p) <= epsilon)
                {
                    canonical = Some(candidate);
                }
            }
        }
        let canonical = canonical.unwrap_or(k);
        positions.entry(canonical).or_insert(p);
        projected.push(canonical);
    }
    let boundary = |cap: usize| -> Option<Boundary> {
        let count = caps.get(cap)?.len();
        work.reserve_cells_core(k, count.checked_mul(4)?).ok()?;
        let mut adjacency = Boundary::new();
        for (&(a, b), &count) in caps.get(cap)? {
            if count == 2 {
                continue;
            }
            if count != 1 {
                return None;
            }
            let (a, b) = (*projected.get(a as usize)?, *projected.get(b as usize)?);
            if a == b {
                return None;
            }
            adjacency.entry(a).or_default().push(b);
            adjacency.entry(b).or_default().push(a);
        }
        for neighbours in adjacency.values_mut() {
            neighbours.sort_unstable();
        }
        Some(adjacency)
    };
    let pair = (boundary(0), boundary(1));
    work.spend_core(k, 0)?;
    let (Some(mut adjacency), Some(mut other)) = pair else {
        return Ok(None);
    };
    // Clipping a triangle at a shoulder can introduce different collinear nodes
    // on the two caps. Compare their actual polygon edges, not tessellation counts.
    let simplify = |graph: &mut Boundary| -> Option<()> {
        if graph.len() > MAX_BOUNDARY || graph.values().any(|v| v.len() != 2) {
            return None;
        }
        // Initial nodes plus at most two appended neighbours per removed node.
        work.reserve_cells_core(k, graph.len().checked_mul(3)?)
            .ok()?;
        let mut pending: std::collections::VecDeque<_> = graph.keys().copied().collect();
        while let Some(key) = pending.pop_front() {
            work.spend_core(k, 1).ok()?;
            let Some(neighbours) = graph.get(&key) else {
                continue;
            };
            let (Some(&a), Some(&b)) = (neighbours.first(), neighbours.get(1)) else {
                return None;
            };
            if a == b {
                return None;
            }
            let (pa, pb, p) = (
                *positions.get(&a)?,
                *positions.get(&b)?,
                *positions.get(&key)?,
            );
            if distance_to_segment(&Seg2::Line { a: pa, b: pb }, p) > epsilon * 3. {
                continue;
            }
            if graph.get(&a)?.contains(&b) {
                continue;
            }
            graph.remove(&key);
            for (from, to) in [(a, b), (b, a)] {
                let adjacent = graph.get_mut(&from)?;
                let slot = adjacent.iter_mut().find(|v| **v == key)?;
                *slot = to;
                adjacent.sort_unstable();
                pending.push_back(from);
            }
        }
        Some(())
    };
    let simplified = simplify(&mut adjacency).is_some() && simplify(&mut other).is_some();
    work.spend_core(k, 0)?;
    if !simplified {
        return Ok(None);
    }
    if adjacency != other
        || adjacency.is_empty()
        || adjacency.len() > MAX_BOUNDARY
        || adjacency.values().any(|n| n.len() != 2)
    {
        return Ok(None);
    }
    // Every side vertex must lie on an unchanged straight extrusion of the cap.
    // This excludes twisted, tapered and stepped meshes before fitting any circles.
    let point = |k: (i64, i64)| Vec2::new(k.0 as f64 * epsilon, k.1 as f64 * epsilon);
    work.reserve_cells_core(k, adjacency.len())?;
    let boundary_segments: Vec<_> = adjacency
        .iter()
        .flat_map(|(&a, bs)| {
            bs.iter()
                .filter(move |&&b| a < b)
                .map(move |&b| (point(a), point(b)))
        })
        .collect();
    if mesh.positions.len().saturating_mul(boundary_segments.len()) > 32_000_000 {
        return Err(invalid("boundary certification exceeds its work budget"));
    }
    for p in mesh.positions {
        work.spend_core(
            k,
            boundary_segments
                .len()
                .checked_add(1)
                .ok_or_else(|| invalid("boundary work overflow"))?,
        )?;
        let h = p.dot(axis);
        if (h - lo).abs() <= epsilon || (h - hi).abs() <= epsilon {
            continue;
        }
        let p = plane.to_local(*p);
        if !boundary_segments
            .iter()
            .any(|&(a, b)| distance_to_segment(&Seg2::Line { a, b }, p) <= epsilon * 3.)
        {
            return Ok(None);
        }
    }
    let mut loops = Vec::new();
    let mut raw_loops = Vec::new();
    let mut cap_loops = Vec::new();
    let mut cap_vertices = BTreeMap::new();
    for (i, p) in mesh.positions.iter().enumerate() {
        work.spend_core(k, 1)?;
        if (p.dot(axis) - lo).abs() <= epsilon {
            let key = *projected
                .get(i)
                .ok_or_else(|| invalid("missing cap projection"))?;
            cap_vertices
                .entry(key)
                .or_insert(u32::try_from(i).map_err(|_| invalid("cap alias overflow"))?);
        }
    }
    while let Some((&start, _)) = adjacency.first_key_value() {
        let mut current = start;
        let mut previous = None;
        let mut chain = Vec::new();
        let mut source_loop = Vec::new();
        for _ in 0..=MAX_BOUNDARY {
            work.spend_core(k, 1)?;
            work.reserve_cells_core(k, 2)?;
            let Some(neighbours) = adjacency.remove(&current) else {
                return Ok(None);
            };
            chain.push(
                positions
                    .get(&current)
                    .copied()
                    .unwrap_or_else(|| point(current)),
            );
            source_loop.push(
                *cap_vertices
                    .get(&current)
                    .ok_or_else(|| invalid("missing cap source alias"))?,
            );
            let next = neighbours.into_iter().find(|n| Some(*n) != previous);
            let Some(next) = next else { return Ok(None) };
            if next == start {
                break;
            }
            previous = Some(current);
            current = next;
        }
        if chain.len() < 3 || current == start {
            return Ok(None);
        }
        let fit_work = chain
            .len()
            .checked_mul(
                chain
                    .len()
                    .checked_add(1)
                    .ok_or_else(|| invalid("profile work overflow"))?,
            )
            .and_then(|n| n.checked_mul(2))
            .ok_or_else(|| invalid("profile work overflow"))?;
        // The unchanged partial-arc fitter has its original 4M inner-work guard;
        // collinear elimination is at most n*(n+1)/2 visits. This upper charge is
        // for THIS bounded data job, not permission for native evaluator memory.
        work.spend_core(
            k,
            fit_work
                .checked_add(fit_work.min(4_000_000))
                .ok_or_else(|| invalid("profile work overflow"))?,
        )?;
        work.reserve_cells_core(
            k,
            chain
                .len()
                .checked_mul(6)
                .and_then(|n| n.checked_add(1))
                .ok_or_else(|| invalid("profile storage overflow"))?,
        )?;
        cap_loops.push(source_loop);
        raw_loops.push(polygon(&chain));
        loops.push(fit_loop(&chain, tolerance, epsilon));
    }
    work.spend_core(k, 0)?;
    Ok(Some(PrismProposal {
        frame: plane.frame(),
        height,
        raw: raw_loops,
        fitted: loops,
        cap_loops,
        epsilon,
        size,
    }))
}

/// Existing AnalyticV1 saved-generation build/check ordering. These checks are not
/// the new generation's complete canonical original-source certificate.
fn extrusion(
    k: &mut Kernel,
    work: &MeshWork,
    mesh: &TriMesh,
    axis: Vec3,
    tolerance: f64,
) -> Result<Option<Brep>> {
    let Some(p) = propose_prism_with_work(k, work, mesh.view(), axis, tolerance)? else {
        return Ok(None);
    };
    let PrismProposal {
        frame,
        height,
        raw,
        fitted,
        epsilon,
        size,
        ..
    } = p;
    certify_nesting(k, &raw, &fitted, epsilon, size)?;
    let Some(regions) = nest_regions(&raw, &fitted)? else {
        return Ok(None);
    };
    let mut body = native::extrude(k, &frame, &regions, height)?;
    if !native::is_valid(k, &mut body)? {
        return Err(invalid("reconstructed solid did not pass validity checks"));
    }
    let perimeter: f64 = fitted
        .iter()
        .flat_map(|lp| &lp.segs)
        .map(segment_length)
        .sum();
    let original = mesh.volume();
    let rebuilt = native::volume(k, &mut body)?;
    if !original.is_finite()
        || original <= 0.
        || (rebuilt - original).abs() > perimeter * height * tolerance + epsilon * size.powi(2)
    {
        return Err(invalid(
            "reconstructed volume is inconsistent with the source mesh",
        ));
    }
    work.spend_core(k, 0)?;
    Ok(Some(body))
}

/// Candidate ranking only; original material/source proof is independent.
pub(super) fn ranked_axes_with_work(
    k: &Kernel,
    work: &MeshWork,
    mesh: &TriMesh,
) -> Result<Vec<Vec3>> {
    work.spend_core(k, mesh.triangles.len())?;
    work.reserve_cells_core(
        k,
        mesh.triangles
            .len()
            .checked_mul(3)
            .ok_or_else(|| invalid("axis storage overflow"))?,
    )?;
    Ok(parts::axes(mesh)
        .into_iter()
        .map(|(axis, _)| axis)
        .collect())
}

/// Build the selected original-order profile with the existing kernel builder.
/// This is a candidate, never an adoption token; final canonical proof is mandatory.
pub(super) fn build_prism_with_work(
    k: &mut Kernel,
    work: &MeshWork,
    tool: &super::PrismTool,
) -> Result<Brep> {
    work.spend_core(k, 0)?;
    if tool.start != 0. || tool.regions.len() > MAX_BOUNDARY {
        return Err(invalid("invalid selected analytic product"));
    }
    let mut refs = 0usize;
    for region in &tool.regions {
        work.spend_core(k, 0)?;
        if region.holes.len() >= MAX_BOUNDARY {
            return Err(invalid("selected profile loop budget"));
        }
        for lp in region.loops() {
            work.spend_core(k, 0)?;
            refs = refs
                .checked_add(lp.segs.len())
                .ok_or_else(|| invalid("selected profile count overflow"))?;
            if refs > MAX_BOUNDARY {
                return Err(invalid("selected profile boundary budget"));
            }
        }
    }
    work.spend_core(k, refs)?;
    work.reserve_cells_core(
        k,
        refs.checked_mul(2)
            .ok_or_else(|| invalid("selected profile storage overflow"))?,
    )?;
    let answer = native::extrude(k, &tool.frame, &tool.regions, tool.end);
    if matches!(&answer, Err(SolidError::PortInvariant { .. })) {
        return answer;
    }
    work.spend_core(k, 0)?;
    answer
}

/// Reject fitted boundaries that cross or change containment, with a cap on pairwise Boolean work.
fn certify_nesting(
    k: &mut Kernel,
    raw: &[Loop2],
    fitted: &[Loop2],
    epsilon: f64,
    size: f64,
) -> Result<()> {
    if raw.len() > MAX_LOOPS {
        return Err(invalid(
            "mesh is too complex to convert (at most 50 boundary loops are supported)",
        ));
    }
    let mut work = 0usize;
    for (i, a) in raw.iter().enumerate() {
        for (j, b) in raw.iter().enumerate().skip(i + 1) {
            work = work.saturating_add(a.segs.len().saturating_mul(b.segs.len()));
            if work > 16_000_000 {
                return Err(invalid("loop certification exceeds its work budget"));
            }
            let (ab, ba) = (
                geometry::contains_loop(a, b)?,
                geometry::contains_loop(b, a)?,
            );
            if ab && ba {
                return Err(invalid("overlapping boundary loops"));
            }
            for (a, b) in [
                (a, b),
                (
                    fitted
                        .get(i)
                        .ok_or_else(|| invalid("missing fitted loop"))?,
                    fitted
                        .get(j)
                        .ok_or_else(|| invalid("missing fitted loop"))?,
                ),
            ] {
                let region = |l: &Loop2| -> Result<Region2> {
                    Ok(Region2 {
                        outer: geometry::ccw(l)?,
                        holes: Vec::new(),
                    })
                };
                let area = native::intersection_area(
                    k,
                    &region(a)?,
                    &region(b)?,
                    epsilon.clamp(1e-9, 1.),
                )?;
                let expected = if ab {
                    b.signed_area()?.value.abs()
                } else if ba {
                    a.signed_area()?.value.abs()
                } else {
                    0.
                };
                if (area - expected).abs() > epsilon * size.max(1.) * 10. {
                    return Err(invalid("conversion would cross or merge boundary loops"));
                }
            }
        }
    }
    Ok(())
}

/// Recover full circles or partial arcs only after sample and chord checks; otherwise retain polygon corners.
pub(super) fn fit_loop(points: &[Vec2], tolerance: f64, epsilon: f64) -> Loop2 {
    // Fit a complete circular boundary only with enough samples to distinguish it
    // from a polygon. Certify the chord deviation, not just the vertex residual.
    if points.len() >= 12 {
        let (Some(&a), Some(&b), Some(&c)) = (
            points.first(),
            points.get(points.len() / 3),
            points.get(2 * points.len() / 3),
        ) else {
            return polygon(points);
        };
        let u = b - a;
        let v = c - a;
        let d = 2. * u.cross(v);
        if d.abs() > epsilon * epsilon {
            let center = a + Vec2::new(
                v.y * u.len2() - u.y * v.len2(),
                u.x * v.len2() - v.x * u.len2(),
            )
            .divided_by(d);
            let radius = center.dist(a);
            if radius.is_finite()
                && radius > epsilon
                && points
                    .iter()
                    .all(|p| (center.dist(*p) - radius).abs() <= epsilon * 3.)
            {
                let mut sweep = 0.;
                let mut direction = 0f64;
                let valid = points
                    .iter()
                    .zip(points.iter().cycle().skip(1))
                    .all(|(a, b)| {
                        let signed = ((*a - center).cross(*b - center))
                            .atan2((*a - center).dot(*b - center));
                        if direction == 0. {
                            direction = signed.signum();
                        }
                        if signed * direction <= 0. {
                            return false;
                        }
                        sweep += signed;
                        let angle = signed.abs();
                        angle <= std::f64::consts::PI / 6. + 1e-8
                            && radius * (1. - (angle * 0.5).cos()) + epsilon * 10. <= tolerance
                    });
                if valid && (sweep.abs() - std::f64::consts::TAU).abs() <= 1e-7 {
                    return circle(center, radius);
                }
            }
        }
    }
    let mut points = points.to_vec();
    let linear_tolerance = epsilon / points.len().max(1) as f64;
    loop {
        let n = points.len();
        if n <= 3 {
            break;
        }
        let remove = corners(&points).position(|(a, b, c)| {
            distance_to_segment(&Seg2::Line { a, b: c }, b) <= linear_tolerance
        });
        let Some(index) = remove else { break };
        let mut at = 0;
        points.retain(|_| {
            let keep = at != index;
            at += 1;
            keep
        });
    }
    fit_partial_arcs(&points, tolerance, epsilon)
}

/// A circular arc through both actual endpoints, independently certified against every
/// source vertex and chord. Short polygon corners and coarse facets are not rounded.
fn partial_arc(points: &[Vec2], tolerance: f64, epsilon: f64) -> Option<Seg2> {
    if points.len() < 5 {
        return None;
    }
    let first = *points.first()?;
    let last = *points.last()?;
    let chord = last - first;
    let length = chord.len();
    if length <= epsilon * 10. {
        return None;
    }
    let mean = points
        .iter()
        .copied()
        .fold(Vec2::ZERO, |a, b| a + b)
        .divided_by(points.len() as f64);
    let (mut xx, mut xy, mut yy, mut xq, mut yq) = (0., 0., 0., 0., 0.);
    for p in points {
        let d = *p - mean;
        let q = d.len2();
        xx += d.x * d.x;
        xy += d.x * d.y;
        yy += d.y * d.y;
        xq += d.x * q;
        yq += d.y * q;
    }
    let determinant = xx * yy - xy * xy;
    if determinant.abs() <= (xx + yy).powi(2) * 1e-10 {
        return None;
    }
    let seed = mean + Vec2::new(yy * xq - xy * yq, xx * yq - xy * xq).divided_by(2. * determinant);
    let normal = Vec2::new(-chord.y, chord.x).divided_by(length);
    let middle = (first + last) * 0.5;
    let center = middle + normal * (seed - middle).dot(normal);
    let radius = center.dist(first);
    if !radius.is_finite() || radius <= epsilon {
        return None;
    }
    let residual = points
        .iter()
        .map(|p| (p.dist(center) - radius).abs())
        .fold(0., f64::max);
    if residual > epsilon * 5. {
        return None;
    }
    let mut sweep = 0.;
    let mut direction = 0.;
    for (&a, &b) in points.iter().zip(points.iter().skip(1)) {
        let (a, b) = (a - center, b - center);
        let angle = a.cross(b).atan2(a.dot(b));
        if direction == 0. {
            direction = angle.signum();
        }
        if angle * direction <= 0.
            || angle.abs() > std::f64::consts::PI / 6. + 1e-8
            || radius * (1. - (angle * 0.5).cos()) + residual + epsilon * 10. > tolerance
        {
            return None;
        }
        sweep += angle;
    }
    if sweep.abs() < 0.04 || sweep.abs() > std::f64::consts::TAU - 0.01 {
        return None;
    }
    let start = (first - center).y.atan2((first - center).x);
    Some(Seg2::Arc {
        center,
        radius,
        start,
        sweep,
    })
}

/// Replace certified circular runs while keeping their actual endpoints and the remaining polygon edges.
fn fit_partial_arcs(points: &[Vec2], tolerance: f64, epsilon: f64) -> Loop2 {
    let n = points.len();
    if n < 5 {
        return polygon(points);
    }
    let ring = ring_at_sharpest_corner(points);
    let mut at = 0;
    let mut work = 0usize;
    let mut segs = Vec::new();
    while at < n {
        let mut fitted = None;
        for end in at + 4..=n {
            work = work.saturating_add((end - at + 1) * 2);
            if work > 4_000_000 {
                return polygon(points);
            }
            let Some(run) = ring.get(at..=end) else { break };
            let Some(arc) = partial_arc(run, tolerance, epsilon) else {
                break;
            };
            fitted = Some((end, arc));
        }
        if let Some((end, arc)) = fitted {
            segs.push(arc);
            at = end;
        } else {
            let (Some(&a), Some(&b)) = (ring.get(at), ring.get(at + 1)) else {
                return polygon(points);
            };
            segs.push(Seg2::Line { a, b });
            at += 1;
        }
    }
    Loop2 { segs }
}
