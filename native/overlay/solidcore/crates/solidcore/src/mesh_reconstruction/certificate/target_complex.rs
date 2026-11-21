//! Recomputes the oriented final B-rep support-patch complex (not upstream).
//!
//! Candidate face grouping is a claim. This verifies an exact partition of actual
//! native faces, reads the void-side face uses from region material flags, verifies
//! every native edge has exactly two opposite material-boundary uses, cancels only
//! within a candidate patch, and recovers all remaining closed oriented simple rims.
//! Finite void cavities use their OWN void-side use, never a guessed infinite-region
//! normal. Cached display topology is not used.
//!
//! This proves combinatorics of the claimed grouping only. It is NOT proof that grouped
//! faces share a support, that any source patch maps to them, or that its actual trim
//! geometry/nesting/degree and movement tubes preserve material. Those geometric checks
//! must consume this immutable native complex before reconstruction acceptance.
//!
//! Deviations: none. No recursion; at most 8192 faces and 262,144 edge uses/edges.
//! Every face/loop/edge/component loop polls cancellation. Missing/unsure/unsupported
//! topology refuses; no geometry, seam or pole is silently omitted.
use super::super::work::MeshWork;
use crate::kernel::Kernel;
use crate::mass::integrator::properties::region_material;
use crate::nurbs::b_spline_surface_n_lib::p2::OrientType;
use crate::topology::{edge, edgeuse::p1 as eu, face::p2 as face, loopuse};
use crate::topology::{Brep, EdgeId, EdgeuseId, FaceId, FaceuseId, VertexId};
use crate::{Result, SolidError};
use std::collections::{BTreeMap, BTreeSet};

const OP: &str = "mesh_reconstruction::certificate::target_complex";
pub(crate) const MAX_FACES: usize = 8192;
const MAX_USES: usize = 262_144;
/// A plan-derived assignment only; the verifier never trusts its supporting geometry.
pub(crate) struct TargetPatchClaim {
    pub(crate) faces: Vec<FaceId>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum TargetRefusal {
    InvalidFacePartition,
    MissingOrUnsureMaterialSide,
    UnsupportedPoleOrVertexLoop,
    InvalidNativeIncidence,
    InvalidGroupBoundary { patch: usize },
    DisconnectedGroup { patch: usize },
    WorkBudget,
}
pub(crate) enum TargetCover<'a> {
    Proven(TargetComplex<'a>),
    Undecided(TargetRefusal),
}
#[derive(Clone, Copy)]
pub(crate) struct TargetEdgeUse {
    pub(crate) edge: EdgeId,
    pub(crate) use_id: EdgeuseId,
    pub(crate) face: FaceId,
    pub(crate) faceuse: FaceuseId,
    pub(crate) start: VertexId,
    pub(crate) end: VertexId,
    pub(crate) forward: bool,
}
pub(crate) struct TargetPatch {
    pub(crate) faces: Vec<FaceId>,
    pub(crate) rims: Vec<Vec<TargetEdgeUse>>,
}
pub(crate) struct TargetComplex<'a> {
    rebuilt: &'a Brep,
    _claims: &'a [TargetPatchClaim],
    pub(crate) patches: Vec<TargetPatch>,
    /// Exactly one pair for each actual boundary edge, retained across groups.
    pub(crate) edges: BTreeMap<EdgeId, [(usize, TargetEdgeUse); 2]>,
}
impl<'a> TargetComplex<'a> {
    /// The same immutable final B-rep whose incidence was independently checked.
    pub(crate) fn brep(&self) -> &'a Brep {
        self.rebuilt
    }
}

fn missing(reason: &'static str) -> SolidError {
    SolidError::query_failed(OP, reason)
}
fn start_vertex(b: &Brep, u: EdgeuseId) -> Result<VertexId> {
    let vu = b
        .edgeuse(u)?
        .vertexuse
        .ok_or_else(|| missing("a boundary edge use has no vertex use"))?;
    b.vertexuse(vu)?
        .vertex
        .ok_or_else(|| missing("a boundary vertex use has no vertex"))
}
fn void_use(b: &Brep, f: FaceId) -> Result<Option<FaceuseId>> {
    let (Some(a), Some(c)) = face::faceuses(b, f)? else {
        return Ok(None);
    };
    let (Some(ar), Some(cr)) = (eu::faceuse_region(b, a)?, eu::faceuse_region(b, c)?) else {
        return Ok(None);
    };
    let (am, cm) = (region_material(b, ar)?, region_material(b, cr)?);
    Ok(match (am, cm) {
        (false, true) => Some(a),
        (true, false) => Some(c),
        _ => None,
    })
}
type ExtractedComplex = (
    Vec<TargetPatch>,
    BTreeMap<EdgeId, [(usize, TargetEdgeUse); 2]>,
);
fn extract(
    k: &Kernel,
    work: &MeshWork,
    b: &Brep,
    claims: &[TargetPatchClaim],
) -> Result<core::result::Result<ExtractedComplex, TargetRefusal>> {
    macro_rules! refuse {
        ($why:expr) => {
            return Ok(Err($why))
        };
    }
    if b.face_list().is_empty()
        || b.face_list().len() > MAX_FACES
        || claims.is_empty()
        || claims.len() > b.face_list().len()
    {
        refuse!(TargetRefusal::InvalidFacePartition);
    }
    let actual: BTreeSet<_> = b.face_list().iter().copied().collect();
    let mut partition = BTreeMap::new();
    for (pi, claim) in claims.iter().enumerate() {
        work.spend_core(k, 1)?;
        if claim.faces.is_empty() || claim.faces.len() > MAX_FACES {
            refuse!(TargetRefusal::InvalidFacePartition);
        }
        for &f in &claim.faces {
            if !actual.contains(&f) || partition.insert(f, pi).is_some() {
                refuse!(TargetRefusal::InvalidFacePartition);
            }
        }
    }
    if partition.len() != actual.len() {
        refuse!(TargetRefusal::InvalidFacePartition);
    }
    let mut uses: BTreeMap<EdgeId, Vec<(usize, TargetEdgeUse)>> = BTreeMap::new();
    let mut count = 0_usize;
    let mut face_neighbors: BTreeMap<FaceId, Vec<FaceId>> = BTreeMap::new();
    for &f in b.face_list() {
        work.spend_core(k, 1)?;
        face_neighbors.entry(f).or_default();
        let Some(&group) = partition.get(&f) else {
            refuse!(TargetRefusal::InvalidFacePartition);
        };
        let Some(fu) = void_use(b, f)? else {
            refuse!(TargetRefusal::MissingOrUnsureMaterialSide);
        };
        for lu in eu::faceuse_loopuses(b, fu, false, None)? {
            work.spend_core(k, 1)?;
            let loop_uses = loopuse::edgeuses(b, lu, None, None)?;
            if loop_uses.is_empty() {
                refuse!(TargetRefusal::UnsupportedPoleOrVertexLoop);
            }
            for u in loop_uses {
                work.spend_core(k, 1)?;
                if count >= MAX_USES {
                    refuse!(TargetRefusal::WorkBudget);
                }
                count += 1;
                work.reserve_cells_core(k, 1)?;
                let record = b.edgeuse(u)?;
                let Some(edge_id) = record.edge else {
                    refuse!(TargetRefusal::InvalidNativeIncidence);
                };
                let (Some(a), Some(z)) = edge::start_end_vertices(b, edge_id)? else {
                    refuse!(TargetRefusal::InvalidNativeIncidence);
                };
                let forward = match record.orientation {
                    OrientType::Same => true,
                    OrientType::Opposite => false,
                    OrientType::Unknown => {
                        refuse!(TargetRefusal::InvalidNativeIncidence);
                    }
                };
                let (start, end) = if forward { (a, z) } else { (z, a) };
                let Some(next) = record.ccw else {
                    refuse!(TargetRefusal::InvalidNativeIncidence);
                };
                if start_vertex(b, u)? != start || start_vertex(b, next)? != end {
                    refuse!(TargetRefusal::InvalidNativeIncidence);
                }
                let item = TargetEdgeUse {
                    edge: edge_id,
                    use_id: u,
                    face: f,
                    faceuse: fu,
                    start,
                    end,
                    forward,
                };
                let entry = uses.entry(edge_id).or_default();
                entry.push((group, item));
                if entry.len() > 2 {
                    refuse!(TargetRefusal::InvalidNativeIncidence);
                }
            }
        }
    }
    let mut boundaries: Vec<Vec<TargetEdgeUse>> = claims.iter().map(|_| Vec::new()).collect();
    let mut edges = BTreeMap::new();
    for (id, list) in uses {
        work.spend_core(k, 1)?;
        let [(ga, a), (gb, buse)] = list.as_slice() else {
            refuse!(TargetRefusal::InvalidNativeIncidence);
        };
        if a.forward == buse.forward || a.start != buse.end || a.end != buse.start {
            refuse!(TargetRefusal::InvalidNativeIncidence);
        }
        edges.insert(id, [(*ga, *a), (*gb, *buse)]);
        if ga == gb {
            if let Some(n) = face_neighbors.get_mut(&a.face) {
                n.push(buse.face);
            } else {
                refuse!(TargetRefusal::InvalidNativeIncidence);
            }
            if let Some(n) = face_neighbors.get_mut(&buse.face) {
                n.push(a.face);
            } else {
                refuse!(TargetRefusal::InvalidNativeIncidence);
            }
        } else {
            let Some(aa) = boundaries.get_mut(*ga) else {
                refuse!(TargetRefusal::InvalidFacePartition);
            };
            aa.push(*a);
            let Some(bb) = boundaries.get_mut(*gb) else {
                refuse!(TargetRefusal::InvalidFacePartition);
            };
            bb.push(*buse);
        }
    }
    let mut patches = Vec::new();
    for ((pi, claim), boundary) in claims.iter().enumerate().zip(boundaries) {
        work.spend_core(k, 1)?;
        let Some(&first) = claim.faces.first() else {
            refuse!(TargetRefusal::InvalidFacePartition);
        };
        let mut seen = BTreeSet::new();
        let mut stack = vec![first];
        while let Some(f) = stack.pop() {
            work.spend_core(k, 1)?;
            if !seen.insert(f) {
                continue;
            }
            let Some(adj) = face_neighbors.get(&f) else {
                refuse!(TargetRefusal::InvalidNativeIncidence);
            };
            for &next in adj {
                stack.push(next);
            }
        }
        if seen.len() != claim.faces.len() {
            refuse!(TargetRefusal::DisconnectedGroup { patch: pi });
        }
        // A simple oriented support-patch rim has one incoming and one outgoing use
        // at each boundary vertex. Periodic interior seams were cancelled above;
        // a genuine closed circular edge is retained as a one-edge rim.
        let mut incoming = BTreeSet::new();
        let mut outgoing = BTreeMap::new();
        for u in boundary {
            if !incoming.insert(u.end) || outgoing.insert(u.start, u).is_some() {
                refuse!(TargetRefusal::InvalidGroupBoundary { patch: pi });
            }
        }
        if incoming.len() != outgoing.len() || incoming.iter().any(|v| !outgoing.contains_key(v)) {
            refuse!(TargetRefusal::InvalidGroupBoundary { patch: pi });
        }
        let mut rims = Vec::new();
        let mut visited = BTreeSet::new();
        for &start in outgoing.keys() {
            work.spend_core(k, 1)?;
            if visited.contains(&start) {
                continue;
            }
            let mut rim = Vec::new();
            let mut point = start;
            loop {
                work.spend_core(k, 1)?;
                if visited.len() >= MAX_USES {
                    refuse!(TargetRefusal::WorkBudget);
                }
                if !visited.insert(point) {
                    if point == start {
                        break;
                    }
                    refuse!(TargetRefusal::InvalidGroupBoundary { patch: pi });
                }
                let Some(&u) = outgoing.get(&point) else {
                    refuse!(TargetRefusal::InvalidGroupBoundary { patch: pi });
                };
                rim.push(u);
                point = u.end;
            }
            rims.push(rim);
        }
        patches.push(TargetPatch {
            faces: claim.faces.clone(),
            rims,
        });
    }
    Ok(Ok((patches, edges)))
}
/// Recompute structural target incidence. Geometry/support/nesting/local-degree proof
/// remains mandatory: this return value must not be used directly as acceptance.
pub(crate) fn target_complex_with_work<'a>(
    k: &Kernel,
    work: &MeshWork,
    b: &'a Brep,
    claims: &'a [TargetPatchClaim],
) -> Result<TargetCover<'a>> {
    match extract(k, work, b, claims) {
        Ok(Ok((patches, edges))) => Ok(TargetCover::Proven(TargetComplex {
            rebuilt: b,
            _claims: claims,
            patches,
            edges,
        })),
        Ok(Err(why)) => Ok(TargetCover::Undecided(why)),
        Err(e) if e.is_cancelled() => Err(e),
        Err(SolidError::UnsureRegion { .. }) => Ok(TargetCover::Undecided(
            TargetRefusal::MissingOrUnsureMaterialSide,
        )),
        Err(e) if super::errors::expected(&e) => Ok(TargetCover::Undecided(
            TargetRefusal::InvalidNativeIncidence,
        )),
        Err(e) => Err(e),
    }
}
