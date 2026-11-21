//! A bounded deterministic spatial index of the exact input triangles (not upstream).
//!
//! ONE BVH builder supports two different consumers. Closest-point queries are hints
//! only and never certify distance. Complete overlap queries exclude ONLY boxes with
//! a strict separating coordinate interval. They return every touching/overlapping or
//! unknown pair, in original triangle order; exhausted visits never become empty success.
//! Source topology supplies static outward boxes; `SourceMotion` supplies WHOLE-time
//! swept boxes. A broad exclusion proves disjointness, never a distance or body result.
//!
//! Deviations: none. No recursion: build/query work waits in explicit bounded vectors.

use super::super::work::MeshWork;
use crate::blend::fillet_section::interval::Ivl;
use crate::geom::geom_utility::p2::triangle_point_distance;
use crate::kernel::Kernel;
use crate::math::Point3;
use crate::{Result, SolidError};

use super::hulls::{PointBox, Triangle};

const OP: &str = "mesh_reconstruction::certificate::source_index";
/// Source triangles this reconstruction family admits, before allocating an index.
const MAX_TRIANGLES: usize = 200_000;
const LEAF_TRIANGLES: usize = 8;
/// A hint query never needs to search the whole index to remain a sound proof aid.
const MAX_HINT_VISITS: usize = 4096;
const HINTS: usize = 4;

fn invalid(reason: &'static str) -> SolidError {
    SolidError::invalid_input(OP, reason)
}

#[derive(Clone, Copy)]
struct Bounds {
    lo: [f64; 3],
    hi: [f64; 3],
}

impl Bounds {
    fn empty() -> Self {
        Self {
            lo: [f64::INFINITY; 3],
            hi: [f64::NEG_INFINITY; 3],
        }
    }
    fn include(&mut self, other: Self) {
        for ((lo, hi), (&a, &b)) in self
            .lo
            .iter_mut()
            .zip(&mut self.hi)
            .zip(other.lo.iter().zip(&other.hi))
        {
            *lo = lo.min(a);
            *hi = hi.max(b);
        }
    }
    fn unknown() -> Self {
        Self {
            lo: [f64::NEG_INFINITY; 3],
            hi: [f64::INFINITY; 3],
        }
    }
    fn from_triangle(triangle: &Triangle) -> Option<Self> {
        let mut bounds = Self::empty();
        for p in triangle {
            for ((lo, hi), c) in bounds.lo.iter_mut().zip(&mut bounds.hi).zip(p) {
                if !c.is_finite() || c.lo > c.hi {
                    return None;
                }
                *lo = lo.min(c.lo);
                *hi = hi.max(c.hi);
            }
        }
        Some(bounds)
    }
    fn of_triangle(triangle: &Triangle) -> Result<Self> {
        Self::from_triangle(triangle)
            .ok_or_else(|| invalid("a source coordinate enclosure is not finite"))
    }
    fn axis(self) -> usize {
        self.lo
            .iter()
            .zip(&self.hi)
            .enumerate()
            .max_by(|(_, (a, b)), (_, (c, d))| (**b - **a).total_cmp(&(**d - **c)))
            .map_or(0, |(i, _)| i)
    }
    fn centre(self, axis: usize) -> f64 {
        match (self.lo.get(axis), self.hi.get(axis)) {
            (Some(&a), Some(&b)) if a.is_finite() && b.is_finite() => 0.5 * a + 0.5 * b,
            _ => 0.0,
        }
    }
    /// A numerical search score, NOT a certified distance bound.
    fn score(self, point: Point3) -> f64 {
        let point = [point.x, point.y, point.z];
        self.lo
            .iter()
            .zip(&self.hi)
            .zip(point)
            .map(|((&a, &b), p)| {
                let d = (a - p).max(p - b).max(0.0);
                d * d
            })
            .sum()
    }
}

#[derive(Clone, Copy)]
enum NodeKind {
    Leaf { first: usize, end: usize },
    Branch { left: usize, right: usize },
}
struct Node {
    bounds: Bounds,
    kind: NodeKind,
}

/// One deterministic BVH over supplied conservative boxes. A separation is
/// used ONLY with strict interval gaps; touching/unknown boxes always survive.
/// `SourceMotion` supplies whole-time swept triangle boxes, not endpoint samples.
pub(crate) struct ConservativeIndex {
    boxes: Vec<Bounds>,
    order: Vec<usize>,
    nodes: Vec<Node>,
}
/// Exact raw source remains borrowed; this index never substitutes mesh geometry.
pub(crate) struct SourceIndex<'a> {
    positions: &'a [[f64; 3]],
    triangles: &'a [[u32; 3]],
    origin: [f64; 3],
    tree: ConservativeIndex,
}
impl<'a> SourceIndex<'a> {
    pub(crate) fn new(
        k: &Kernel,
        work: &MeshWork,
        positions: &'a [[f64; 3]],
        triangles: &'a [[u32; 3]],
        origin: Point3,
    ) -> Result<Self> {
        if triangles.is_empty() || triangles.len() > MAX_TRIANGLES {
            return Err(invalid(
                "source triangle count is outside the reconstruction limit",
            ));
        }
        let origin = [origin.x, origin.y, origin.z];
        if !origin.iter().all(|x| x.is_finite()) {
            return Err(invalid("source translation is not finite"));
        }
        let mut boxes = Vec::new();
        for i in 0..triangles.len() {
            work.spend_core(k, 1)?;
            work.reserve_cells_core(k, 1)?;
            boxes.push(Bounds::of_triangle(&triangle_about(
                positions, triangles, origin, i,
            )?)?);
        }
        Ok(Self {
            positions,
            triangles,
            origin,
            tree: ConservativeIndex::from_bounds(k, work, boxes)?,
        })
    }

    /// The exact stored source triangle, translated by an exactly stored origin, enclosed
    /// outward. Out-of-range and non-finite input never becomes a default point.
    pub(crate) fn triangle(&self, triangle: usize) -> Result<Triangle> {
        triangle_about(self.positions, self.triangles, self.origin, triangle)
    }

    fn try_hint(&self, i: usize, p: Point3, best: &mut Vec<(f64, usize)>) -> Result<()> {
        let triangle = self.triangle(i)?;
        let pt = |p: PointBox| {
            let [x, y, z] = p;
            Point3::new(
                0.5 * x.lo + 0.5 * x.hi,
                0.5 * y.lo + 0.5 * y.hi,
                0.5 * z.lo + 0.5 * z.hi,
            )
        };
        let [a, b, c] = triangle.map(pt);
        let distance = match triangle_point_distance(a, b, c, p) {
            Ok(d) => d.distance,
            Err(e) if super::errors::expected(&e) => f64::INFINITY,
            Err(e) => return Err(e),
        };
        if distance.is_finite() && !best.iter().any(|(_, j)| *j == i) {
            best.push((distance * distance, i));
            best.sort_unstable_by(|a, b| a.0.total_cmp(&b.0).then_with(|| a.1.cmp(&b.1)));
            best.truncate(HINTS);
        }
        Ok(())
    }

    pub(crate) fn overlapping_later(
        &self,
        k: &Kernel,
        work: &MeshWork,
        triangle: usize,
        remaining: &mut usize,
    ) -> Result<Option<Vec<usize>>> {
        self.tree.overlapping_later(k, work, triangle, remaining)
    }

    /// At most four source triangles near the point, by a bounded numerical search.
    /// The caller must still prove its full patch bound against each returned triangle.
    pub(crate) fn hints(
        &self,
        k: &Kernel,
        work: &MeshWork,
        point: PointBox,
        seed: Option<usize>,
    ) -> Result<Vec<usize>> {
        if !point.iter().all(|x| x.is_finite()) {
            return Err(invalid("a source hint point is not finite"));
        }
        let mid = |x: Ivl| 0.5 * x.lo + 0.5 * x.hi;
        let [x, y, z] = point;
        let p = Point3::new(mid(x), mid(y), mid(z));
        let mut best: Vec<(f64, usize)> = Vec::new();
        if let Some(seed) = seed.filter(|i| *i < self.triangles.len()) {
            self.try_hint(seed, p, &mut best)?;
        }
        let mut stack = vec![0];
        let mut visits = 0;
        while let Some(node) = stack.pop() {
            work.spend_core(k, 1)?;
            if visits >= MAX_HINT_VISITS {
                break;
            }
            visits += 1;
            let node = self
                .tree
                .nodes
                .get(node)
                .ok_or_else(|| invalid("a source search node is missing"))?;
            // Numeric ordering/pruning only chooses hints. Missing a triangle can make
            // the independent upper-bound proof decline, never make a wrong one pass.
            let worst = best
                .last()
                .filter(|_| best.len() == HINTS)
                .map_or(f64::INFINITY, |x| x.0);
            if node.bounds.score(p) > worst {
                continue;
            }
            match node.kind {
                NodeKind::Leaf { first, end } => {
                    for &i in self
                        .tree
                        .order
                        .get(first..end)
                        .ok_or_else(|| invalid("source search range is invalid"))?
                    {
                        self.try_hint(i, p, &mut best)?;
                    }
                }
                NodeKind::Branch { left, right } => {
                    let l = self
                        .tree
                        .nodes
                        .get(left)
                        .ok_or_else(|| invalid("source branch is missing"))?
                        .bounds
                        .score(p);
                    let r = self
                        .tree
                        .nodes
                        .get(right)
                        .ok_or_else(|| invalid("source branch is missing"))?
                        .bounds
                        .score(p);
                    if l <= r {
                        stack.push(right);
                        stack.push(left);
                    } else {
                        stack.push(left);
                        stack.push(right);
                    }
                }
            }
        }
        Ok(best.into_iter().map(|(_, i)| i).collect())
    }
}

impl ConservativeIndex {
    fn from_bounds(k: &Kernel, work: &MeshWork, boxes: Vec<Bounds>) -> Result<Self> {
        if boxes.is_empty() || boxes.len() > MAX_TRIANGLES {
            return Err(invalid(
                "source triangle count is outside the reconstruction limit",
            ));
        }
        let mut index = Self {
            boxes,
            order: Vec::new(),
            nodes: Vec::new(),
        };
        for i in 0..index.boxes.len() {
            work.spend_core(k, 1)?;
            work.reserve_cells_core(k, 1)?;
            index.order.push(i);
        }
        let mut root = Bounds::empty();
        for b in &index.boxes {
            work.spend_core(k, 1)?;
            root.include(*b);
        }
        work.reserve_cells_core(k, 1)?;
        index.nodes.push(Node {
            bounds: root,
            kind: NodeKind::Leaf {
                first: 0,
                end: index.boxes.len(),
            },
        });
        work.reserve_cells_core(k, 1)?;
        let mut pending_nodes = vec![(0, 0, index.boxes.len())];
        let max_nodes = index
            .boxes
            .len()
            .checked_mul(2)
            .ok_or_else(|| invalid("source node count overflowed"))?;
        while let Some((node, first, end)) = pending_nodes.pop() {
            work.spend_core(k, 1)?;
            let count = end
                .checked_sub(first)
                .ok_or_else(|| invalid("a source node has an invalid range"))?;
            if count <= LEAF_TRIANGLES {
                continue;
            }
            let axis = index
                .nodes
                .get(node)
                .ok_or_else(|| invalid("a source node is missing"))?
                .bounds
                .axis();
            let slice = index
                .order
                .get_mut(first..end)
                .ok_or_else(|| invalid("source node range is outside its triangles"))?;
            work.spend_core(k, count)?;
            slice.sort_unstable_by(|a, b| {
                let x = index.boxes.get(*a).map_or(0.0, |b| b.centre(axis));
                let y = index.boxes.get(*b).map_or(0.0, |b| b.centre(axis));
                x.total_cmp(&y).then_with(|| a.cmp(b))
            });
            let middle = first + count / 2;
            let mut children = Vec::new();
            for (a, b) in [(first, middle), (middle, end)] {
                if index.nodes.len() >= max_nodes {
                    return Err(invalid("source node count exceeded its proved bound"));
                }
                let mut bounds = Bounds::empty();
                for &i in index
                    .order
                    .get(a..b)
                    .ok_or_else(|| invalid("a source child range is invalid"))?
                {
                    work.spend_core(k, 1)?;
                    bounds.include(
                        *index
                            .boxes
                            .get(i)
                            .ok_or_else(|| invalid("a source triangle box is missing"))?,
                    );
                }
                let child = index.nodes.len();
                work.reserve_cells_core(k, 1)?;
                index.nodes.push(Node {
                    bounds,
                    kind: NodeKind::Leaf { first: a, end: b },
                });
                work.reserve_cells_core(k, 2)?;
                pending_nodes.push((child, a, b));
                children.push(child);
            }
            let [Some(&left), Some(&right)] = [children.first(), children.get(1)] else {
                return Err(invalid("source split lacks two children"));
            };
            index
                .nodes
                .get_mut(node)
                .ok_or_else(|| invalid("a source node is missing"))?
                .kind = NodeKind::Branch { left, right };
        }
        Ok(index)
    }
    /// Every triangle argument is an outward enclosure for its WHOLE motion.
    /// Invalid/reversed/nonfinite ranges become universal boxes, never exclusion.
    pub(crate) fn swept(k: &Kernel, work: &MeshWork, triangles: &[Triangle]) -> Result<Self> {
        if triangles.is_empty() || triangles.len() > MAX_TRIANGLES {
            return Err(invalid(
                "source triangle count is outside the reconstruction limit",
            ));
        }
        let mut boxes = Vec::new();
        for t in triangles {
            work.spend_core(k, 1)?;
            work.reserve_cells_core(k, 1)?;
            boxes.push(Bounds::from_triangle(t).unwrap_or_else(Bounds::unknown));
        }
        Self::from_bounds(k, work, boxes)
    }
    /// All later source triangles whose outward boxes overlap this one's box.
    /// Unlike `hints`, this is a complete broad phase: no numerical distance pruning
    /// or truncated candidate list. Budget exhaustion returns None, never an empty list.
    pub(crate) fn overlapping_later(
        &self,
        k: &Kernel,
        work: &MeshWork,
        triangle: usize,
        remaining: &mut usize,
    ) -> Result<Option<Vec<usize>>> {
        let target = *self
            .boxes
            .get(triangle)
            .ok_or_else(|| invalid("overlap query triangle missing"))?;
        let disjoint = |a: Bounds, b: Bounds| {
            a.lo.iter()
                .zip(&a.hi)
                .zip(b.lo.iter().zip(&b.hi))
                .any(|((&al, &ah), (&bl, &bh))| ah < bl || bh < al)
        };
        let mut result = Vec::new();
        work.reserve_cells_core(k, 1)?;
        let mut stack = vec![0];
        while let Some(node) = stack.pop() {
            work.spend_core(k, 1)?;
            if *remaining == 0 {
                return Ok(None);
            }
            *remaining -= 1;
            let node = self
                .nodes
                .get(node)
                .ok_or_else(|| invalid("an overlap node is missing"))?;
            if disjoint(target, node.bounds) {
                continue;
            }
            match node.kind {
                NodeKind::Leaf { first, end } => {
                    for &i in self
                        .order
                        .get(first..end)
                        .ok_or_else(|| invalid("an overlap range is invalid"))?
                    {
                        work.spend_core(k, 1)?;
                        if i <= triangle {
                            continue;
                        }
                        if *remaining == 0 {
                            return Ok(None);
                        }
                        *remaining -= 1;
                        if !disjoint(
                            target,
                            *self
                                .boxes
                                .get(i)
                                .ok_or_else(|| invalid("overlap triangle box missing"))?,
                        ) {
                            work.reserve_cells_core(k, 1)?;
                            result.push(i);
                        }
                    }
                }
                NodeKind::Branch { left, right } => {
                    work.reserve_cells_core(k, 2)?;
                    stack.push(right);
                    stack.push(left);
                }
            }
        }
        work.spend_core(k, result.len())?;
        result.sort_unstable();
        work.spend_core(k, 0)?;
        Ok(Some(result))
    }
}
fn triangle_about(
    positions: &[[f64; 3]],
    triangles: &[[u32; 3]],
    origin: [f64; 3],
    triangle: usize,
) -> Result<Triangle> {
    let ids = triangles
        .get(triangle)
        .ok_or_else(|| invalid("a source triangle is missing"))?;
    let mut corners = Vec::new();
    for &id in ids {
        let id = usize::try_from(id)
            .map_err(|_| invalid("a source vertex index does not fit this machine"))?;
        let point = positions
            .get(id)
            .ok_or_else(|| invalid("a source triangle refers to a missing vertex"))?;
        if !point.iter().all(|x| x.is_finite()) {
            return Err(invalid("a source vertex is not finite"));
        }
        let [x, y, z] = *point;
        let [ox, oy, oz] = origin;
        corners.push([
            Ivl::from(x) - Ivl::from(ox),
            Ivl::from(y) - Ivl::from(oy),
            Ivl::from(z) - Ivl::from(oz),
        ]);
    }
    let [Some(a), Some(b), Some(c)] = [corners.first(), corners.get(1), corners.get(2)] else {
        return Err(invalid("a source triangle lacks three corners"));
    };
    Ok([*a, *b, *c])
}

#[cfg(test)]
mod swept_tests {
    use super::*;
    use crate::kernel::KernelOptions;
    fn slab(x: f64) -> Triangle {
        [[Ivl::new(x, x + 1.), Ivl::from(0.), Ivl::from(0.)]; 3]
    }
    #[test]
    fn shared_complete_index_keeps_touch_unknown_and_original_pair_order() {
        let k = Kernel::new(&KernelOptions::default());
        let w = MeshWork::new();
        let mut boxes = vec![
            slab(0.),
            slab(100.),
            slab(1.),
            slab(40.),
            slab(-1.),
            slab(0.5),
            slab(10.),
            slab(200.),
            slab(300.),
        ];
        boxes[8][0][0] = Ivl {
            lo: f64::NAN,
            hi: f64::NAN,
        };
        let index = ConservativeIndex::swept(&k, &w, &boxes).unwrap();
        let mut remaining = 1000;
        assert_eq!(
            index
                .overlapping_later(&k, &w, 0, &mut remaining)
                .unwrap()
                .unwrap(),
            vec![2, 4, 5, 8]
        );
        let mut exhausted = 0;
        assert!(index
            .overlapping_later(&k, &w, 0, &mut exhausted)
            .unwrap()
            .is_none());
        // Reversed finite intervals are unknown, not an empty geometric box.
        boxes[8][0][0] = Ivl { lo: 5., hi: 4. };
        let index = ConservativeIndex::swept(&k, &w, &boxes).unwrap();
        let mut remaining = 1000;
        assert!(index
            .overlapping_later(&k, &w, 1, &mut remaining)
            .unwrap()
            .unwrap()
            .contains(&8));
    }
    #[test]
    fn whole_motion_overlap_cannot_be_pruned_from_disjoint_endpoint_boxes() {
        let k = Kernel::new(&KernelOptions::default());
        let w = MeshWork::new();
        // Two triangles swap x intervals. Both endpoint pairs are separated,
        // but their WHOLE-time swept x ranges overlap and must reach exact proof.
        let boxes = [[[Ivl::new(0., 11.), Ivl::new(0., 1.), Ivl::from(0.)]; 3]; 2];
        let index = ConservativeIndex::swept(&k, &w, &boxes).unwrap();
        let mut remaining = 100;
        assert_eq!(
            index
                .overlapping_later(&k, &w, 0, &mut remaining)
                .unwrap()
                .unwrap(),
            vec![1]
        );
    }
    #[test]
    fn shared_complete_index_preserves_original_cancellation_and_work_failure() {
        let mut k = Kernel::new(&KernelOptions::default());
        let w = MeshWork::new();
        let index = ConservativeIndex::swept(&k, &w, &[slab(0.), slab(10.)]).unwrap();
        let exhausted = MeshWork::new();
        assert!(!exhausted.try_spend(usize::MAX));
        assert!(index
            .overlapping_later(&k, &exhausted, 0, &mut 100)
            .is_err());
        let cancel = crate::kernel::CancelToken::new();
        k.set_cancel_token(cancel.clone());
        cancel.cancel();
        assert!(index
            .overlapping_later(&k, &w, 0, &mut 100)
            .unwrap_err()
            .is_cancelled());
    }
}
