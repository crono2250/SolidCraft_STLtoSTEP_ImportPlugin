//! Exact indexed source partition for separate closed solids.
//!
//! Weld only bit-equal original positions (signed zeros denote one point).
//! Shared points connect components; a vertex-touching pinch still goes to the
//! single-solid validity gate. Distinct components only qualify when one
//! axis separates their whole tolerance-expanded boxes. Each child still
//! requires original-source, Native topology and whole geometry certification.
//! Deviations: none. Bounded iterative components with one shared MeshWork.
use super::{types::invalid, MeshError, MeshInput, MeshWork, Result};
use crate::blend::fillet_section::interval::Ivl;
use crate::Kernel;
use std::collections::BTreeMap;

fn root(parent: &mut [usize], mut i: usize, k: &Kernel, w: &MeshWork) -> Result<usize> {
    loop {
        w.spend(k, 1)?;
        let p = *parent
            .get(i)
            .ok_or_else(|| invalid("mesh connectivity index missing"))?;
        if p == i {
            return Ok(i);
        }
        let next = *parent
            .get(p)
            .ok_or_else(|| invalid("mesh connectivity parent missing"))?;
        *parent
            .get_mut(i)
            .ok_or_else(|| invalid("mesh connectivity index missing"))? = next;
        i = next;
    }
}

fn join(
    parent: &mut [usize],
    rank: &mut [usize],
    a: usize,
    b: usize,
    k: &Kernel,
    w: &MeshWork,
) -> Result<()> {
    let a = root(parent, a, k, w)?;
    let b = root(parent, b, k, w)?;
    if a == b {
        return Ok(());
    }
    let x = *rank
        .get(a)
        .ok_or_else(|| invalid("mesh connectivity rank missing"))?;
    let y = *rank
        .get(b)
        .ok_or_else(|| invalid("mesh connectivity rank missing"))?;
    let (from, to) = if x >= y { (b, a) } else { (a, b) };
    *parent
        .get_mut(from)
        .ok_or_else(|| invalid("mesh connectivity parent missing"))? = to;
    if x == y {
        *rank
            .get_mut(to)
            .ok_or_else(|| invalid("mesh connectivity rank missing"))? += 1;
    }
    Ok(())
}

fn position(input: &MeshInput, v: u32) -> Result<[f64; 3]> {
    input
        .positions
        .get(v as usize)
        .copied()
        .filter(|p| p.iter().all(|v| v.is_finite()))
        .ok_or_else(|| invalid("original disconnected mesh vertex is invalid"))
}

struct Piece {
    lower: [f64; 3],
    upper: [f64; 3],
    aliases: BTreeMap<u32, u32>,
    input: MeshInput,
}
impl Piece {
    fn new() -> Self {
        Self {
            lower: [f64::INFINITY; 3],
            upper: [f64::NEG_INFINITY; 3],
            aliases: BTreeMap::new(),
            input: MeshInput {
                positions: Vec::new(),
                triangles: Vec::new(),
            },
        }
    }

    fn push(&mut self, source: &MeshInput, ids: [u32; 3], k: &Kernel, w: &MeshWork) -> Result<()> {
        let mut tri = [0_u32; 3];
        for (to, from) in tri.iter_mut().zip(ids) {
            w.spend(k, 1024)?;
            w.reserve_cells(k, 8)?;
            let p = position(source, from)?;
            let selected = match self.aliases.get(&from).copied() {
                Some(id) => id,
                None => {
                    let id = u32::try_from(self.input.positions.len())
                        .map_err(|_| invalid("disconnected mesh child is too large"))?;
                    for ((lo, hi), x) in self.lower.iter_mut().zip(&mut self.upper).zip(p) {
                        *lo = lo.min(x);
                        *hi = hi.max(x);
                    }
                    self.input.positions.push(p);
                    self.aliases.insert(from, id);
                    id
                }
            };
            *to = selected;
        }
        w.reserve_output(k, 3)?;
        self.input.triangles.push(tri);
        Ok(())
    }
}

/// Separate complete source components in deterministic first-triangle order.
/// A single component retains the original arrays and route.
///
/// # Errors
/// Invalid or touching components, cancellation or workflow exhaustion.
pub fn disjoint_component_meshes_with_work(
    k: &Kernel,
    w: &MeshWork,
    input: &MeshInput,
    tolerance: f64,
) -> Result<Option<Vec<MeshInput>>> {
    w.check(k)?;
    super::regions::checked_tolerance(tolerance)?;
    super::source::admit_conversion(input)?;
    let count = input.triangles.len();
    w.reserve_cells(
        k,
        count
            .checked_mul(4)
            .ok_or_else(|| invalid("mesh connectivity size overflow"))?,
    )?;
    let mut parent = (0..count).collect::<Vec<_>>();
    let mut rank = vec![0; count];
    let mut owner = BTreeMap::new();
    for (id, tri) in input.triangles.iter().enumerate() {
        for &v in tri {
            w.spend(k, 1024)?;
            let key = position(input, v)?.map(|v| if v == 0. { 0 } else { v.to_bits() });
            match owner.entry(key) {
                std::collections::btree_map::Entry::Vacant(row) => {
                    w.reserve_cells(k, 5)?;
                    row.insert(id);
                }
                std::collections::btree_map::Entry::Occupied(row) => {
                    join(&mut parent, &mut rank, id, *row.get(), k, w)?
                }
            }
        }
    }
    let mut roots = BTreeMap::new();
    let mut assignment = Vec::new();
    for i in 0..count {
        let set = root(&mut parent, i, k, w)?;
        let n = roots.len();
        w.spend(k, 1024)?;
        let id = *roots.entry(set).or_insert(n);
        assignment.push(id);
    }
    if roots.len() < 2 {
        return Ok(None);
    }
    w.reserve_cells(k, roots.len().saturating_mul(16))?;
    let mut pieces = (0..roots.len()).map(|_| Piece::new()).collect::<Vec<_>>();
    for (tri, id) in input.triangles.iter().zip(assignment) {
        pieces
            .get_mut(id)
            .ok_or_else(|| invalid("component assignment disappeared"))?
            .push(input, *tri, k, w)?;
    }
    let doubled = Ivl::from(2.) * Ivl::from(tolerance);
    for (i, a) in pieces.iter().enumerate() {
        for b in pieces.iter().take(i) {
            w.spend(k, 32)?;
            let separate = (0..3).any(|coord| {
                ((Ivl::from(a.lower[coord]) - Ivl::from(b.upper[coord])) - doubled).is_positive()
                    || ((Ivl::from(b.lower[coord]) - Ivl::from(a.upper[coord])) - doubled)
                        .is_positive()
            });
            if !separate {
                return Err(MeshError::Refused {
                    stage: "component reconstruction",
                    detail:
                        "the complete tolerance-expanded solid bounds are not strictly separate"
                            .into(),
                });
            }
        }
    }
    w.check(k)?;
    Ok(Some(pieces.into_iter().map(|p| p.input).collect()))
}
