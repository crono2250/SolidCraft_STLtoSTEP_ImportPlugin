//! Recomputes original-source oriented face-cell patches from untrusted IDs (not upstream).
//! No support, final-face order, nesting, material or geometric acceptance is inferred.
//! Deviations: none; iterative bounded source graph walks share one `MeshWork`.
type OriginalEdgeUses = BTreeMap<(u32, u32), Vec<(usize, u32, u32)>>;

use super::super::work::MeshWork;
use super::source_topology::SourceManifold;
use crate::{Kernel, Result};
use std::collections::{BTreeMap, BTreeSet};
pub(crate) struct SourceCellPatch {
    pub(crate) triangles: Vec<usize>,
    pub(crate) vertices: BTreeSet<u32>,
    pub(crate) boundary: BTreeSet<(u32, u32)>,
    pub(crate) rims: Vec<Vec<u32>>,
}
pub(crate) struct SourceCellComplex<'a, 'raw> {
    _source: &'a SourceManifold<'raw>,
    pub(crate) patches: Vec<SourceCellPatch>,
}
pub(crate) enum SourceCellsCover<'a, 'raw> {
    Proven(SourceCellComplex<'a, 'raw>),
    Undecided(&'static str),
}
pub(crate) fn source_cells_with_work<'a, 'raw>(
    k: &Kernel,
    work: &MeshWork,
    source: &'a SourceManifold<'raw>,
    claims: &[Vec<u32>],
) -> Result<SourceCellsCover<'a, 'raw>> {
    macro_rules! refuse {
        ($why:expr) => {
            return Ok(SourceCellsCover::Undecided($why))
        };
    }
    work.spend_core(k, 0)?;
    if claims.is_empty() || claims.len() > source.retained_count {
        refuse!("source-cell groups are empty or oversized");
    }
    let mut seen = BTreeSet::new();
    let mut patches = Vec::new();
    for claim in claims {
        work.spend_core(k, 1)?;
        if claim.is_empty() || claim.len() > source.retained_count {
            refuse!("a source-cell group is empty or oversized");
        }
        let mut edges = OriginalEdgeUses::new();
        let mut adjacency: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
        let mut vertices = BTreeSet::new();
        let mut triangles = Vec::new();
        for &raw in claim {
            work.spend_core(k, 1)?;
            let Ok(id) = usize::try_from(raw) else {
                refuse!("an original source-cell id does not fit this host");
            };
            let Some(&Some([a, b, c])) = source.aliases.get(id) else {
                refuse!("a source-cell claim names an omitted or missing triangle");
            };
            if !seen.insert(id) {
                refuse!("original source cells are not partitioned exactly once");
            }
            work.reserve_cells_core(k, 4)?;
            triangles.push(id);
            vertices.extend([a, b, c]);
            adjacency.insert(id, Vec::new());
            for (u, v) in [(a, b), (b, c), (c, a)] {
                edges
                    .entry((u.min(v), u.max(v)))
                    .or_default()
                    .push((id, u, v));
            }
        }
        let mut boundary = BTreeSet::new();
        for uses in edges.values() {
            work.spend_core(k, 1)?;
            match *uses.as_slice() {
                [(_, u, v)] => {
                    boundary.insert((u, v));
                }
                [(a, u, v), (b, x, y)] if u == y && v == x => {
                    let Some(aa) = adjacency.get_mut(&a) else {
                        refuse!("a source-cell neighbor is missing");
                    };
                    aa.push(b);
                    let Some(bb) = adjacency.get_mut(&b) else {
                        refuse!("a source-cell neighbor is missing");
                    };
                    bb.push(a);
                }
                _ => {
                    refuse!("source-cell incidence does not cancel as an oriented 2-chain");
                }
            }
        }
        let Some(&first) = triangles.first() else {
            refuse!("a source-cell patch has no triangle");
        };
        let mut visited = BTreeSet::new();
        let mut pending = vec![first];
        while let Some(id) = pending.pop() {
            work.spend_core(k, 1)?;
            if !visited.insert(id) {
                continue;
            }
            let Some(neighbors) = adjacency.get(&id) else {
                refuse!("a source-cell adjacency is missing");
            };
            pending.extend(neighbors);
        }
        if visited.len() != triangles.len() {
            refuse!("a source-cell patch is not edge-connected");
        }
        if boundary.len() < 3 {
            refuse!("a finite face-cell patch has no complete boundary");
        }
        let mut outgoing = BTreeMap::new();
        let mut incoming = BTreeSet::new();
        for &(u, v) in &boundary {
            work.spend_core(k, 1)?;
            if u == v || outgoing.insert(u, v).is_some() || !incoming.insert(v) {
                refuse!("source-cell boundary is not a union of disjoint simple cycles");
            }
        }
        if outgoing.len() != incoming.len() || incoming.iter().any(|v| !outgoing.contains_key(v)) {
            refuse!("a source-cell boundary is open");
        }
        let mut walked = BTreeSet::new();
        let mut rims = Vec::new();
        for &start in outgoing.keys() {
            work.spend_core(k, 1)?;
            if walked.contains(&start) {
                continue;
            }
            let mut v = start;
            let mut rim = Vec::new();
            loop {
                work.spend_core(k, 1)?;
                if !walked.insert(v) {
                    if v == start {
                        break;
                    }
                    refuse!("source-cell boundary cycles share vertices");
                }
                rim.push(v);
                let Some(&next) = outgoing.get(&v) else {
                    refuse!("a source-cell boundary successor is absent");
                };
                v = next;
            }
            if rim.len() < 3 {
                refuse!("a source-cell rim has fewer than three corners");
            }
            work.reserve_output_core(k, rim.len())?;
            rims.push(rim);
        }
        patches.push(SourceCellPatch {
            triangles,
            vertices,
            boundary,
            rims,
        });
    }
    if seen.len() != source.retained_count {
        refuse!("some original retained source cells have no patch");
    }
    work.spend_core(k, 0)?;
    Ok(SourceCellsCover::Proven(SourceCellComplex {
        _source: source,
        patches,
    }))
}
