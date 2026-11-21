//! The main faceted fallback as native topology/construction planning; no display geometry.
type GroupedEdgeUses = BTreeMap<(usize, (u32, u32)), Vec<(u32, u32)>>;

use super::numeric::Vec3Numeric;
use super::source::SourceMesh;
use super::types::{invalid, MeshInput, Result};
use crate::math::Vec3;
use std::collections::BTreeMap;
const COPLANAR: f64 = 1e-7;
#[derive(Clone, Copy, Debug)]
/// A directed exact edge of a faceted construction candidate.
pub enum NativeEdge {
    /// A straight directed segment.
    Line {
        /// First endpoint.
        a: Vec3,
        /// Second endpoint.
        b: Vec3,
    },
}
#[derive(Clone, Debug)]
/// All boundary loops of one coplanar source group.
pub struct FacetedFace {
    /// Complete directed boundary loops of one candidate face.
    pub loops: Vec<Vec<NativeEdge>>,
    /// Planning normal; final orientation is independently checked.
    pub normal: Vec3,
    /// Original indexed input triangle IDs, preserving attribution.
    pub source_triangles: Vec<u32>,
}
#[derive(Clone, Debug)]
/// Faceted construction plan, not a source-equivalence proof.
pub struct FacetedPlan {
    /// Candidate planar faces in deterministic construction order.
    pub faces: Vec<FacetedFace>,
}
impl FacetedPlan {
    /// Move the original triangle-ID groups after building this exact plan's candidate.
    /// These are untrusted correspondence claims: only the final actual-body/source
    /// certificate can verify complete geometric, topological and material agreement.
    /// No source IDs or inner geometry buffers are cloned or renumbered.
    ///
    /// # Errors
    /// Shared workflow work/output exhaustion or native cancellation, before allocation.
    pub fn into_source_patch_claims_with_work(
        self,
        k: &crate::Kernel,
        work: &super::MeshWork,
    ) -> Result<Vec<Vec<u32>>> {
        work.check(k)?;
        work.spend(k, self.faces.len())?;
        work.reserve_output(k, self.faces.len())?;
        let mut groups = Vec::new();
        for face in self.faces {
            work.check(k)?;
            groups.push(face.source_triangles);
        }
        work.check(k)?;
        Ok(groups)
    }
}

/// Standalone single-job convenience; multi-stage callers share one `MeshWork`.
pub fn faceted_plan(k: &crate::Kernel, input: &MeshInput, tolerance: f64) -> Result<FacetedPlan> {
    let work_budget = super::work::MeshWork::new();
    faceted_plan_with_work(k, &work_budget, input, tolerance)
}

/// Group coplanar source triangles and retain their complete directed boundaries using the same complete-workflow budget.
pub fn faceted_plan_with_work(
    k: &crate::Kernel,
    work_budget: &super::work::MeshWork,
    input: &MeshInput,
    tolerance: f64,
) -> Result<FacetedPlan> {
    work_budget.check(k)?;
    let answer = (|| {
        super::regions::checked_tolerance(tolerance)?;
        super::source::admit_conversion(input)?;
        let mesh =
            super::source::weld_with_work(k, work_budget, &SourceMesh::checked(input)?, tolerance)?;
        faceted_plan_of(k, work_budget, &mesh)
    })();
    work_budget.check(k)?;
    answer
}
fn faceted_plan_of(
    k: &crate::Kernel,
    work_budget: &super::work::MeshWork,
    mesh: &SourceMesh,
) -> Result<FacetedPlan> {
    let at = |i: u32| mesh.positions.get(i as usize).copied();
    // Every side of the closed, consistently oriented mesh joins two triangles, which the
    // checks in `convert_prismatic_mesh` have already certified; the faceted path relies on it.
    let mut touching: BTreeMap<(u32, u32), Vec<usize>> = BTreeMap::new();
    for (i, t) in mesh.triangles.iter().enumerate() {
        for (a, b) in [(t[0], t[1]), (t[1], t[2]), (t[2], t[0])] {
            touching.entry((a.min(b), a.max(b))).or_default().push(i);
        }
    }
    if touching.values().any(|ts| ts.len() != 2) {
        return Err(invalid(
            "mesh must be closed and consistently oriented, with two triangles per edge",
        ));
    }
    // Coplanar groups grow from a seed triangle's plane, never from the neighbour's own, so a
    // chain of triangles each nearly on the next one's plane cannot drift off the group's
    // plane: the whole group stays within COPLANAR of one plane.
    let mut groups = vec![usize::MAX; mesh.triangles.len()];
    let mut planes: Vec<(Vec3, f64)> = Vec::new();
    let mut queue: Vec<usize> = Vec::new();
    let work = super::work::Work::with_budget(k, work_budget)?;
    for seed in 0..mesh.triangles.len() {
        work.spend(1)?;
        if *groups
            .get(seed)
            .ok_or_else(|| invalid("missing facet group"))?
            != usize::MAX
        {
            continue;
        }
        let [a, b, c] = mesh
            .triangles
            .get(seed)
            .copied()
            .ok_or_else(|| invalid("missing source triangle"))?;
        let (Some(pa), Some(pb), Some(pc)) = (at(a), at(b), at(c)) else {
            return Err(invalid("missing triangle vertex"));
        };
        let Some(n) = (pb - pa).cross(pc - pa).normalized() else {
            return Err(invalid("degenerate triangle"));
        };
        let group = planes.len();
        planes.push((n, n.dot(pa)));
        *groups
            .get_mut(seed)
            .ok_or_else(|| invalid("missing facet group"))? = group;
        queue.push(seed);
        while let Some(t) = queue.pop() {
            work.spend(1)?;
            let [a, b, c] = mesh
                .triangles
                .get(t)
                .copied()
                .ok_or_else(|| invalid("missing source triangle"))?;
            for (a, b) in [(a, b), (b, c), (c, a)] {
                for &u in touching.get(&(a.min(b), a.max(b))).into_iter().flatten() {
                    if *groups
                        .get(u)
                        .ok_or_else(|| invalid("missing facet group"))?
                        != usize::MAX
                    {
                        continue;
                    }
                    let (n, d) = planes
                        .get(group)
                        .copied()
                        .ok_or_else(|| invalid("missing facet plane"))?;
                    if mesh
                        .triangles
                        .get(u)
                        .ok_or_else(|| invalid("missing source triangle"))?
                        .iter()
                        .all(|&v| at(v).is_some_and(|p| (n.dot(p) - d).abs() <= COPLANAR))
                    {
                        *groups
                            .get_mut(u)
                            .ok_or_else(|| invalid("missing facet group"))? = group;
                        queue.push(u);
                    }
                }
            }
        }
    }
    // A group's boundary sides are those its triangles use once: the partner triangle belongs
    // to another group. The mesh's own winding directs them, which orients each face's loops
    // about its outward normal.
    let mut uses = GroupedEdgeUses::new();
    for (i, t) in mesh.triangles.iter().enumerate() {
        for (a, b) in [(t[0], t[1]), (t[1], t[2]), (t[2], t[0])] {
            uses.entry((
                *groups
                    .get(i)
                    .ok_or_else(|| invalid("missing facet group"))?,
                (a.min(b), a.max(b)),
            ))
            .or_default()
            .push((a, b));
        }
    }
    let mut faces: Vec<Vec<(u32, u32)>> = vec![Vec::new(); planes.len()];
    for ((group, _), directed) in &uses {
        if directed.len() == 1 {
            faces
                .get_mut(*group)
                .ok_or_else(|| invalid("missing facet boundary"))?
                .push(
                    *directed
                        .first()
                        .ok_or_else(|| invalid("missing directed boundary"))?,
                );
        }
    }
    // The triangle that runs each directed side, for the boundary walk's turn around a vertex.
    let mut owner: BTreeMap<(u32, u32), usize> = BTreeMap::new();
    for (i, t) in mesh.triangles.iter().enumerate() {
        for (a, b) in [(t[0], t[1]), (t[1], t[2]), (t[2], t[0])] {
            owner.insert((a, b), i);
        }
    }
    let mut specs = Vec::new();
    for (group, sides) in faces.iter().enumerate() {
        let (normal, _) = planes
            .get(group)
            .copied()
            .ok_or_else(|| invalid("missing faceted plane"))?;
        let loops = face_loops(
            sides,
            normal,
            &mesh.positions,
            &mesh.triangles,
            &owner,
            &work,
        )?;
        let mut source_triangles = Vec::new();
        for (triangle_id, assigned) in groups.iter().enumerate() {
            if *assigned == group {
                if let Some(Some(source)) = mesh.source_triangles.get(triangle_id) {
                    source_triangles.push(*source);
                }
            }
        }
        specs.push(FacetedFace {
            loops,
            normal,
            source_triangles,
        });
    }
    Ok(FacetedPlan { faces: specs })
}

/// One group's boundary loops as face wire edges: each directed side is followed by rotating
/// from its triangle around the shared vertex through the group's interior triangles until the
/// next boundary side leaves it, which keeps a loop on one strand of material even where
/// several strands meet at a vertex. Each side becomes exactly one edge — the two faces that
/// share a rim run it in opposite directions, so fusing collinear runs of vertices greedily
/// could leave each face with a different subset and edges that pair with nothing. Points that
/// coincide within 1e-9 mm are fused (sewing could not tell the ends apart anyway), and the
/// loop that runs counter-clockwise comes first, where sewing reads the face's outward
/// direction from it.
fn face_loops(
    sides: &[(u32, u32)],
    normal: Vec3,
    positions: &[Vec3],
    triangles: &[[u32; 3]],
    owner: &BTreeMap<(u32, u32), usize>,
    work: &super::work::Work<'_>,
) -> Result<Vec<Vec<NativeEdge>>> {
    let at = |i: u32| {
        positions
            .get(i as usize)
            .copied()
            .ok_or_else(|| invalid("missing triangle vertex"))
    };
    let boundary: std::collections::BTreeSet<(u32, u32)> = sides.iter().copied().collect();
    let mut used: std::collections::BTreeSet<(u32, u32)> = std::collections::BTreeSet::new();
    let mut chains: Vec<Vec<Vec3>> = Vec::new();
    for &(start_side, into) in sides {
        if used.contains(&(start_side, into)) {
            continue;
        }
        used.insert((start_side, into));
        let (mut previous, mut current) = (start_side, into);
        let mut chain = vec![at(previous)?];
        loop {
            work.spend(1)?;
            chain.push(at(current)?);
            if chain.len() > sides.len() + 1 {
                return Err(invalid("a planar group's boundary does not close"));
            }
            // Rotate from the incoming side's triangle around `current` through the triangles
            // between the two boundary sides that meet there; interior sides are shared with a
            // neighbour of the same group, so the walk stays on this group's material.
            let mut side = (previous, current);
            let mut spin = 0usize;
            let next = loop {
                work.spend(1)?;
                spin += 1;
                if spin > triangles.len() {
                    return Err(invalid("a vertex with no way around its triangles"));
                }
                let Some(&t) = owner.get(&side) else {
                    return Err(invalid("a side without its triangle"));
                };
                let [x, y, z] = triangles
                    .get(t)
                    .copied()
                    .ok_or_else(|| invalid("missing incident triangle"))?;
                let third = if x != side.0 && x != side.1 {
                    x
                } else if y != side.0 && y != side.1 {
                    y
                } else {
                    z
                };
                if boundary.contains(&(current, third)) {
                    break third;
                }
                side = (third, current);
            };
            used.insert((current, next));
            previous = current;
            if next == start_side {
                break;
            }
            current = next;
        }
        if chain.len() < 3 {
            return Err(invalid("a planar group's boundary has no loop"));
        }
        chains.push(chain);
    }
    let mut loops: Vec<Vec<NativeEdge>> = Vec::new();
    for chain in &mut chains {
        loop {
            let n = chain.len();
            if n <= 3 {
                break;
            }
            let remove = (0..n).find(|&i| {
                chain
                    .get(i)
                    .zip(chain.get((i + n - 1) % n))
                    .is_some_and(|(p, q)| p.dist(*q) <= 1e-9)
                    || chain
                        .get(i)
                        .zip(chain.get((i + 1) % n))
                        .is_some_and(|(p, q)| p.dist(*q) <= 1e-9)
            });
            let Some(i) = remove else { break };
            *chain = std::mem::take(chain)
                .into_iter()
                .enumerate()
                .filter_map(|(index, p)| (index != i).then_some(p))
                .collect();
        }
        let wire: Vec<NativeEdge> = chain
            .iter()
            .zip(chain.iter().skip(1).chain(chain.first()))
            .map(|(&a, &b)| NativeEdge::Line { a, b })
            .collect();
        loops.push(wire);
    }
    // The outer loop runs counter-clockwise about the outward normal and comes first: sewing
    // takes the face's outward direction from the first loop's plane.
    let signed = |wire: &Vec<NativeEdge>| -> f64 {
        wire.iter()
            .map(|e| match e {
                NativeEdge::Line { a, b } => a.cross(*b),
            })
            .fold(Vec3::ZERO, |sum, cross| sum + cross)
            .dot(normal)
    };
    let outer = loops
        .iter()
        .enumerate()
        .find(|(_, l)| signed(l) > 0.)
        .map(|(i, _)| i);
    let Some(outer) = outer else {
        return Err(invalid("a planar group's boundary does not enclose it"));
    };
    if outer != 0 {
        let first = loops
            .first()
            .cloned()
            .ok_or_else(|| invalid("missing outer face loop"))?;
        let chosen = loops
            .get(outer)
            .cloned()
            .ok_or_else(|| invalid("missing selected outer face loop"))?;
        *loops
            .first_mut()
            .ok_or_else(|| invalid("missing outer face loop"))? = chosen;
        *loops
            .get_mut(outer)
            .ok_or_else(|| invalid("missing selected outer face loop"))? = first;
    }
    Ok(loops)
}
