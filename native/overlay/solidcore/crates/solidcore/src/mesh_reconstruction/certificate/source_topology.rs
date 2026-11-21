//! Verifies exact-source alias and embedded closed-manifold claims (not upstream).
//!
//! STL duplicates vertex records. Equal-coordinate aliases are a representation change;
//! merging merely nearby points is a geometric edit and is NOT proved harmless by a weld
//! radius. This first certificate accepts only the exact-coordinate quotient, verifies
//! original triangle coverage/winding, two opposite uses of every edge, a single circular
//! link at every vertex, and complete pairwise non-intersection except shared simplices.
//! It neither fills holes nor trusts synthetic fans or a caller's incidence report.
//!
//! Pair exclusion uses interval-enclosed separating planes and exact dual-cone sums
//! for a shared vertex. Numerical axes may steer a
//! proof, but the complete vertex half-space inequalities establish it. All potentially
//! overlapping pairs are enumerated by the source index's outward boxes; missed/uncertain
//! pairs or exhausted budgets refuse. No triangle samples establish non-intersection.
//!
//! This is NOT a final reconstruction-acceptance token: final B-rep correspondence and
//! oriented shell nesting/material sides still must be proved. Signed component volumes
//! are retained for that verifier, not compared to a guessed component/genus count.
//!
//! The proofs use vertex links and complete separating-plane inequalities directly;
//! interval arithmetic reuses native outward Ivl operations. No sampled intersection
//! oracle or external geometry implementation is used.
//!
//! Deviations: none. No recursion; at most 200,000 source triangles/600,000 raw vertices,
//! 4,000,000 broad-phase node/leaf visits and 1,000,000 actual pair proofs. Budget refusal
//! never accepts. Every graph, triangle and pair loop polls kernel cancellation.

use super::super::types::WeldClaim;
use super::super::work::MeshWork;
use super::hulls::{PointBox, Triangle};
use super::source_index::SourceIndex;
use crate::blend::fillet_section::interval::Ivl;
use crate::kernel::Kernel;
use crate::math::Point3;
use crate::Result;
use std::collections::{BTreeMap, BTreeSet};

const OP: &str = "mesh_reconstruction::certificate::source_topology";
const MAX_TRIANGLES: usize = 200_000;
const MAX_VERTICES: usize = 600_000;
const MAX_BROAD: usize = 4_000_000;
const MAX_PAIRS: usize = 1_000_000;

/// Why the bounded source embedding and exact alias proof could not be established.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SourceRefusal {
    /// A purported original-source correspondence is malformed.
    InvalidClaim(&'static str),
    /// A proposed alias would move an original source coordinate.
    InexactWeld {
        /// The raw input vertex index.
        vertex: usize,
    },
    /// A retained edge does not have exactly two opposite uses.
    NonManifoldEdge,
    /// A retained vertex does not have one complete circular link.
    NonManifoldVertex {
        /// The exact-alias vertex index.
        vertex: u32,
    },
    /// Full triangle interiors could not be proved disjoint beyond their common simplex.
    IntersectionUnproved {
        /// First raw input triangle index.
        a: usize,
        /// Second raw input triangle index.
        b: usize,
    },
    /// A lower-dimensional facet lacks a proof of exact redundancy.
    DegenerateTriangle {
        /// The raw input triangle index.
        triangle: usize,
    },
    /// A shell's enclosed oriented volume could not be established.
    ComponentVolumeUnproved,
    /// The bounded source proof exhausted its assigned work.
    WorkBudget,
}
pub(crate) enum SourceTopology<'a> {
    Proven(SourceManifold<'a>),
    Undecided(SourceRefusal),
}
/// Immutable exact-source geometric quotient, not proof of a reconstructed body.
pub(crate) struct SourceManifold<'a> {
    positions: &'a [[f64; 3]],
    triangles: &'a [[u32; 3]],
    claim: &'a WeldClaim,
    /// Original triangle order: None only for an independently proved exact
    /// lower-dimensional facet fully covered by retained source geometry.
    pub(super) aliases: Vec<Option<[u32; 3]>>,
    pub(super) retained_count: usize,
    pub(super) components: Vec<Vec<usize>>,
    pub(super) signed_volumes: Vec<Ivl>,
}

impl SourceManifold<'_> {
    pub(crate) fn alias_count(&self) -> usize {
        self.claim.vertices.len()
    }

    /// Read exactly the original raw triangle proved by this immutable source token.
    pub(crate) fn original_triangle(&self, id: usize) -> Option<[[f64; 3]; 3]> {
        super::exact_geometry::raw_triangle(self.positions, self.triangles, id)
    }
    pub(crate) fn position(&self, alias: u32) -> Option<[f64; 3]> {
        self.claim
            .vertices
            .get(usize::try_from(alias).ok()?)
            .map(|v| v.position)
    }
}

fn sub(a: PointBox, b: PointBox) -> PointBox {
    let [ax, ay, az] = a;
    let [bx, by, bz] = b;
    [ax - bx, ay - by, az - bz]
}
fn cross(a: PointBox, b: PointBox) -> PointBox {
    let [ax, ay, az] = a;
    let [bx, by, bz] = b;
    [ay * bz - az * by, az * bx - ax * bz, ax * by - ay * bx]
}
fn dot(a: PointBox, b: PointBox) -> Ivl {
    let [ax, ay, az] = a;
    let [bx, by, bz] = b;
    ax * bx + ay * by + az * bz
}
fn nonzero(a: Ivl) -> bool {
    a.is_finite() && (a.lo > 0.0 || a.hi < 0.0)
}
fn edges(t: &Triangle) -> [PointBox; 3] {
    let [a, b, c] = *t;
    [sub(b, a), sub(c, b), sub(a, c)]
}
fn normal(t: &Triangle) -> PointBox {
    let [a, b, c] = *t;
    cross(sub(b, a), sub(c, a))
}
/// A nonzero normal component over the complete boxes proves every triangle regular.
pub(super) fn triangle_box_is_regular(triangle: &Triangle) -> bool {
    normal(triangle).into_iter().any(nonzero)
}
fn axes(a: &Triangle, b: &Triangle) -> Vec<PointBox> {
    let ea = edges(a);
    let eb = edges(b);
    let na = normal(a);
    let nb = normal(b);
    let mut axes = vec![na, nb];
    for &e in &ea {
        for &f in &eb {
            axes.push(cross(e, f));
        }
        axes.push(cross(na, e));
    }
    for &f in &eb {
        axes.push(cross(nb, f));
    }
    let ca = centre(a);
    let cb = centre(b);
    axes.push(sub(ca, cb));
    axes
}
fn centre(t: &Triangle) -> PointBox {
    let [a, b, c] = *t;
    let one = Ivl::from(1.0 / 3.0);
    [
        (a[0] + b[0] + c[0]) * one,
        (a[1] + b[1] + c[1]) * one,
        (a[2] + b[2] + c[2]) * one,
    ]
}
fn projection(t: &Triangle, axis: PointBox) -> Option<Ivl> {
    let mut lo = f64::INFINITY;
    let mut hi = f64::NEG_INFINITY;
    for &p in t {
        let q = dot(p, axis);
        if !q.is_finite() {
            return None;
        }
        lo = lo.min(q.lo);
        hi = hi.max(q.hi);
    }
    Some(Ivl::new(lo, hi))
}

/// Prove that two exact triangles meet only in their declared common simplex.
/// False means unproved, not a claimed intersection. IDs are the validated exact alias
/// quotient; all coordinates remain the original raw triangle coordinates.
pub(super) fn simplex_only(a: &Triangle, aid: [u32; 3], b: &Triangle, bid: [u32; 3]) -> bool {
    let mut common = Vec::new();
    for (i, &id) in aid.iter().enumerate() {
        if let Some(j) = bid.iter().position(|&x| x == id) {
            common.push((i, j));
        }
    }
    match common.as_slice() {
        [] => axes(a, b)
            .into_iter()
            .any(|axis| match (projection(a, axis), projection(b, axis)) {
                (Some(x), Some(y)) => x.hi < y.lo || y.hi < x.lo,
                _ => false,
            }),
        &[(i, j)] => {
            let (Some(&origin), Some(_)) = (a.get(i), b.get(j)) else {
                return false;
            };
            axes(a, b).into_iter().any(|axis| {
                let aa: Vec<_> = a
                    .iter()
                    .enumerate()
                    .filter(|(v, _)| *v != i)
                    .map(|(_, p)| dot(sub(*p, origin), axis))
                    .collect();
                let bb: Vec<_> = b
                    .iter()
                    .enumerate()
                    .filter(|(v, _)| *v != j)
                    .map(|(_, p)| dot(sub(*p, origin), axis))
                    .collect();
                aa.iter().chain(&bb).all(|q| q.is_finite())
                    && ((aa.iter().all(|q| q.lo > 0.0) && bb.iter().all(|q| q.hi < 0.0))
                        || (aa.iter().all(|q| q.hi < 0.0) && bb.iter().all(|q| q.lo > 0.0)))
            })
        }
        &[(i, j), (m, n)] => {
            let (Some(&origin), Some(&end)) = (a.get(i), a.get(m)) else {
                return false;
            };
            let Some(&at) = a
                .iter()
                .enumerate()
                .find(|(v, _)| *v != i && *v != m)
                .map(|(_, p)| p)
            else {
                return false;
            };
            let Some(&bt) = b
                .iter()
                .enumerate()
                .find(|(v, _)| *v != j && *v != n)
                .map(|(_, p)| p)
            else {
                return false;
            };
            // Distinct supporting planes meet along this exact common edge. In the
            // coplanar case, opposite radial half-planes also meet only in that edge.
            if nonzero(dot(normal(a), sub(bt, origin))) {
                return true;
            }
            dot(
                cross(sub(end, origin), sub(at, origin)),
                cross(sub(end, origin), sub(bt, origin)),
            )
            .hi < 0.0
        }
        _ => false,
    }
}

/// A shared-vertex star needs a strictly separating functional on FOUR signed
/// rays. A single edge/normal SAT axis need not be strict, even on a box corner.
/// Collect exact WEAK separators instead. Their sum is strict iff every ray has
/// a positive dot for at least one retained candidate; every other dot is >=0.
/// Thus every convex point away from the declared common vertex lies on opposite
/// sides. Nonnegative zero tests use native exact expansions, never an epsilon.
pub(super) fn vertex_cones_separated(
    k: &Kernel,
    work: &MeshWork,
    a: [[f64; 3]; 3],
    aid: [u32; 3],
    b: [[f64; 3]; 3],
    bid: [u32; 3],
) -> Result<bool> {
    use super::exact_geometry as x;
    work.spend_core(k, 0)?;
    let mut common = Vec::new();
    for (i, &id) in aid.iter().enumerate() {
        if let Some(j) = bid.iter().position(|&v| v == id) {
            work.reserve_cells_core(k, 1)?;
            common.push((i, j));
        }
    }
    let [(i, j)] = common.as_slice() else {
        return Ok(false);
    };
    let Some(origin) = a.get(*i).copied().and_then(x::point) else {
        return Ok(false);
    };
    if !b
        .get(*j)
        .copied()
        .is_some_and(|p| x::equal_point(&origin, p))
    {
        return Ok(false);
    }
    let mut rays = Vec::new();
    for (v, p) in a.into_iter().enumerate() {
        work.spend_core(k, 1)?;
        if v == *i {
            continue;
        }
        let Some(ray) = x::point(p).and_then(|p| x::difference(&p, &origin)) else {
            return Ok(false);
        };
        work.reserve_cells_core(k, 1)?;
        rays.push(ray);
    }
    for (v, p) in b.into_iter().enumerate() {
        work.spend_core(k, 1)?;
        if v == *j {
            continue;
        }
        let Some(ray) = x::point(p).and_then(|p| x::difference(&origin, &p)) else {
            return Ok(false);
        };
        work.reserve_cells_core(k, 1)?;
        rays.push(ray);
    }
    if rays.len() != 4 {
        return Ok(false);
    }
    exact_rays_separated(k, work, &rays)
}

/// A bounded collection of signed exact rays uses the same weak-dual-cone proof.
/// Four rays describe a static vertex pair; eight describe both endpoints of a
/// vertex-linear motion interval. A sum of retained weak separators is strict on
/// every ray, so it is strict on their entire positive hull, not only endpoints.
pub(super) fn exact_rays_separated(
    k: &Kernel,
    work: &MeshWork,
    rays: &[super::exact_geometry::P],
) -> Result<bool> {
    use super::exact_geometry as x;
    work.spend_core(k, 0)?;
    if rays.is_empty() || rays.len() > 8 {
        return Ok(false);
    }
    let mut candidates = Vec::new();
    for ray in rays {
        work.spend_core(k, 1)?;
        work.reserve_cells_core(k, 1)?;
        candidates.push(ray.clone());
    }
    let mut span_normal = None;
    for (i, a) in rays.iter().enumerate() {
        for b in rays.iter().skip(i + 1) {
            work.spend_core(k, 1)?;
            let Some(n) = x::cross(a, b) else {
                return Ok(false);
            };
            if span_normal.is_none() && n.iter().any(|c| !x::zero(c)) {
                work.reserve_cells_core(k, 1)?;
                span_normal = Some(n.clone());
            }
            work.reserve_cells_core(k, 1)?;
            candidates.push(n);
        }
    }
    // A coplanar star has lineality in the normal direction: pair crosses
    // alone vanish on ALL rays. In this rank-two event, normal-cross-ray
    // gives the actual extremal weak functionals INSIDE their common plane.
    if let Some(normal) = span_normal {
        let mut coplanar = true;
        for ray in rays {
            work.spend_core(k, 1)?;
            let Some(sign) = x::dot(&normal, ray).and_then(|d| x::sign(&d)) else {
                return Ok(false);
            };
            coplanar &= sign == 0;
        }
        if coplanar {
            for ray in rays {
                work.spend_core(k, 1)?;
                let Some(axis) = x::cross(&normal, ray) else {
                    return Ok(false);
                };
                work.reserve_cells_core(k, 1)?;
                candidates.push(axis);
            }
        }
    }
    let mut positive = [false; 8];
    for axis in candidates {
        for orientation in [1., -1.] {
            let mut signs = [0; 8];
            for (slot, ray) in signs.iter_mut().zip(rays) {
                work.spend_core(k, 1)?;
                let Some(sign) = x::dot(&axis, ray)
                    .and_then(|v| x::scale(&v, orientation))
                    .and_then(|v| x::sign(&v))
                else {
                    return Ok(false);
                };
                *slot = sign;
            }
            if signs.iter().take(rays.len()).any(|&s| s < 0) {
                continue;
            }
            for (positive, &s) in positive.iter_mut().zip(&signs) {
                *positive |= s > 0;
            }
        }
    }
    Ok(positive.into_iter().take(rays.len()).all(|p| p))
}

fn raw_id(value: u32) -> Option<usize> {
    usize::try_from(value).ok()
}
fn exact_key(point: [f64; 3]) -> [u64; 3] {
    point.map(|v| if v == 0.0 { 0 } else { v.to_bits() })
}
fn cycle_same(a: [u32; 3], b: [u32; 3]) -> bool {
    a == b || a == [b[1], b[2], b[0]] || a == [b[2], b[0], b[1]]
}

/// Validate the proposed weld against the exact input arrays and prove an embedded,
/// consistently oriented closed source manifold. This deliberately refuses radius-only
/// welding. Such a weld needs a separate bounded non-crossing isotopy proof.
pub(crate) fn validate_source_weld_with_work<'a>(
    k: &Kernel,
    work: &MeshWork,
    positions: &'a [[f64; 3]],
    triangles: &'a [[u32; 3]],
    claim: &'a WeldClaim,
) -> Result<SourceTopology<'a>> {
    macro_rules! refuse {
        ($why:expr) => {
            return Ok(SourceTopology::Undecided($why))
        };
    }
    macro_rules! bad {
        ($why:expr) => {
            refuse!(SourceRefusal::InvalidClaim($why))
        };
    }
    if triangles.is_empty()
        || triangles.len() > MAX_TRIANGLES
        || positions.len() > MAX_VERTICES
        || claim.vertices.len() > positions.len()
        || claim.triangles.is_empty()
        || claim.triangles.len() > triangles.len()
        || claim.original_triangles.len() != claim.triangles.len()
    {
        bad!("source/claim counts are invalid or outside the proof budget");
    }
    if !(claim.tolerance.is_finite() && claim.tolerance >= 0.0) {
        bad!("the proposed weld tolerance is invalid");
    }
    let mut raw_alias: Vec<Option<u32>> = positions.iter().map(|_| None).collect();
    let mut keys = BTreeMap::new();
    for (vi, vertex) in claim.vertices.iter().enumerate() {
        work.spend_core(k, 1)?;
        let Ok(alias) = u32::try_from(vi) else {
            bad!("an alias index does not fit u32");
        };
        if vertex.raw_vertices.is_empty() || !vertex.position.iter().all(|x| x.is_finite()) {
            bad!("an alias is empty or not finite");
        }
        if keys.insert(exact_key(vertex.position), alias).is_some() {
            bad!("an exact source point occurs in different alias classes");
        }
        for &raw in &vertex.raw_vertices {
            let Some(raw) = raw_id(raw) else {
                bad!("a raw vertex id does not fit this machine");
            };
            let Some(point) = positions.get(raw) else {
                bad!("a claimed raw vertex is missing");
            };
            if !point.iter().all(|x| x.is_finite()) || *point != vertex.position {
                refuse!(SourceRefusal::InexactWeld { vertex: vi });
            }
            let Some(slot) = raw_alias.get_mut(raw) else {
                bad!("a raw alias slot is missing");
            };
            if slot.replace(alias).is_some() {
                bad!("a raw vertex occurs in more than one alias claim");
            }
        }
    }
    let mut ordered: Vec<Option<[u32; 3]>> = triangles.iter().map(|_| None).collect();
    for (welded, raw) in claim.triangles.iter().zip(&claim.original_triangles) {
        work.spend_core(k, 1)?;
        let Some(raw) = raw.and_then(raw_id) else {
            bad!("a synthetic or missing triangle cannot certify the original source");
        };
        let Some(&original) = triangles.get(raw) else {
            bad!("a claimed original triangle is missing");
        };
        let mut aliases = Vec::new();
        for id in original {
            let Some(id) = raw_id(id) else {
                bad!("a source vertex id does not fit this machine");
            };
            let Some(Some(alias)) = raw_alias.get(id) else {
                bad!("an original triangle vertex has no alias");
            };
            aliases.push(*alias);
        }
        let [Some(&a), Some(&b), Some(&c)] = [aliases.first(), aliases.get(1), aliases.get(2)]
        else {
            bad!("a triangle lacks aliases");
        };
        let aliases = [a, b, c];
        if !cycle_same(aliases, *welded) {
            bad!("the weld changed a source triangle's oriented incidence");
        }
        let Some(slot) = ordered.get_mut(raw) else {
            bad!("an original triangle slot is missing");
        };
        if slot.replace(aliases).is_some() {
            bad!("an original triangle occurs more than once");
        }
    }
    // A dropped raw facet is not waived by area epsilon. Prove exact collinearity
    // and its complete convex hull's containment in ONE retained exact triangle.
    // This first sufficient case preserves the existing redundant-edge regression;
    // a more general union coverage may still conservatively refuse.
    let retained_count = ordered.iter().filter(|t| t.is_some()).count();
    let mut disposition_work = 0_usize;
    for (i, alias) in ordered.iter().enumerate() {
        work.spend_core(k, 1)?;
        if alias.is_some() {
            continue;
        }
        let Some(raw) = super::exact_geometry::raw_triangle(positions, triangles, i) else {
            bad!("an omitted raw triangle is invalid");
        };
        if !super::exact_geometry::collinear(raw) {
            refuse!(SourceRefusal::DegenerateTriangle { triangle: i });
        }
        let mut covered = false;
        for (j, retained) in ordered.iter().enumerate() {
            if retained.is_none() {
                continue;
            }
            work.spend_core(k, 1)?;
            if disposition_work >= MAX_PAIRS {
                refuse!(SourceRefusal::WorkBudget);
            }
            disposition_work += 1;
            let Some(support) = super::exact_geometry::raw_triangle(positions, triangles, j) else {
                bad!("a retained raw triangle is invalid");
            };
            if raw
                .iter()
                .all(|&p| super::exact_geometry::in_triangle(p, support))
            {
                covered = true;
                break;
            }
        }
        if !covered {
            refuse!(SourceRefusal::DegenerateTriangle { triangle: i });
        }
    }
    let aliases = ordered;
    let Some(&[x, y, z]) = positions.first() else {
        bad!("the source has no vertices");
    };
    let origin = Point3::new(x, y, z);
    let source = match SourceIndex::new(k, work, positions, triangles, origin) {
        Ok(v) => v,
        Err(crate::SolidError::InvalidInput { .. }) => {
            bad!("the exact source index could not be prepared");
        }
        Err(e) => return Err(e),
    };
    let mut edge_uses: BTreeMap<(u32, u32), Vec<(usize, bool)>> = BTreeMap::new();
    let mut links: BTreeMap<u32, BTreeMap<u32, Vec<u32>>> = BTreeMap::new();
    for (i, alias) in aliases.iter().enumerate() {
        work.spend_core(k, 1)?;
        let Some([a, b, c]) = *alias else {
            continue;
        };
        let n = normal(&source.triangle(i)?);
        let squared = dot(n, n);
        if a == b || b == c || a == c || !squared.is_finite() || squared.lo <= 0.0 {
            refuse!(SourceRefusal::DegenerateTriangle { triangle: i });
        }
        for (u, v) in [(a, b), (b, c), (c, a)] {
            let key = (u.min(v), u.max(v));
            let uses = edge_uses.entry(key).or_default();
            uses.push((i, u < v));
            if uses.len() > 2 {
                refuse!(SourceRefusal::NonManifoldEdge);
            }
        }
        for (v, p, q) in [(a, b, c), (b, c, a), (c, a, b)] {
            let link = links.entry(v).or_default();
            link.entry(p).or_default().push(q);
            link.entry(q).or_default().push(p);
        }
    }
    let mut neighbors: Vec<Vec<usize>> = triangles.iter().map(|_| Vec::new()).collect();
    for uses in edge_uses.values() {
        work.spend_core(k, 1)?;
        let [(a, oa), (b, ob)] = uses.as_slice() else {
            refuse!(SourceRefusal::NonManifoldEdge);
        };
        if oa == ob {
            refuse!(SourceRefusal::NonManifoldEdge);
        }
        let Some(an) = neighbors.get_mut(*a) else {
            bad!("an edge triangle is missing");
        };
        an.push(*b);
        let Some(bn) = neighbors.get_mut(*b) else {
            bad!("an edge triangle is missing");
        };
        bn.push(*a);
    }
    for (&v, link) in &links {
        work.spend_core(k, 1)?;
        if link.values().any(|n| n.len() != 2 || n.first() == n.get(1)) {
            refuse!(SourceRefusal::NonManifoldVertex { vertex: v });
        }
        let Some(&start) = link.keys().next() else {
            refuse!(SourceRefusal::NonManifoldVertex { vertex: v });
        };
        let mut visited = BTreeSet::new();
        let mut stack = vec![start];
        while let Some(point) = stack.pop() {
            work.spend_core(k, 1)?;
            if !visited.insert(point) {
                continue;
            }
            let Some(neighbors) = link.get(&point) else {
                refuse!(SourceRefusal::NonManifoldVertex { vertex: v });
            };
            for &n in neighbors {
                stack.push(n);
            }
        }
        if visited.len() != link.len() {
            refuse!(SourceRefusal::NonManifoldVertex { vertex: v });
        }
    }
    let mut remaining = MAX_BROAD;
    let mut pair_count = 0_usize;
    for i in 0..triangles.len() {
        work.spend_core(k, 1)?;
        if !aliases.get(i).is_some_and(Option::is_some) {
            continue;
        }
        let Some(pairs) = source.overlapping_later(k, work, i, &mut remaining)? else {
            refuse!(SourceRefusal::WorkBudget);
        };
        for j in pairs {
            work.spend_core(k, 1)?;
            if pair_count >= MAX_PAIRS {
                refuse!(SourceRefusal::WorkBudget);
            }
            pair_count += 1;
            let (Some(&Some(aid)), Some(&Some(bid))) = (aliases.get(i), aliases.get(j)) else {
                continue;
            };
            let common = aid.iter().filter(|id| bid.contains(id)).count();
            let separated = if common == 1 {
                // Fixed four-ray exact algebra, bounded before allocating candidates.
                work.spend_core(k, 256)?;
                let (Some(a), Some(b)) = (
                    super::exact_geometry::raw_triangle(positions, triangles, i),
                    super::exact_geometry::raw_triangle(positions, triangles, j),
                ) else {
                    bad!("an authoritative source pair is missing");
                };
                vertex_cones_separated(k, work, a, aid, b, bid)?
            } else {
                simplex_only(&source.triangle(i)?, aid, &source.triangle(j)?, bid)
            };
            if !separated {
                refuse!(SourceRefusal::IntersectionUnproved { a: i, b: j });
            }
        }
    }
    let mut seen = BTreeSet::new();
    let mut components = Vec::new();
    let mut signed_volumes = Vec::new();
    for i in 0..triangles.len() {
        if seen.contains(&i) || !aliases.get(i).is_some_and(Option::is_some) {
            continue;
        }
        let mut component = Vec::new();
        let mut stack = vec![i];
        let mut volume = Ivl::from(0.0);
        while let Some(t) = stack.pop() {
            work.spend_core(k, 1)?;
            if !seen.insert(t) {
                continue;
            }
            let [a, b, c] = source.triangle(t)?;
            volume = volume + dot(a, cross(b, c)) / Ivl::from(6.0);
            component.push(t);
            let Some(adjacent) = neighbors.get(t) else {
                bad!("a component triangle is missing");
            };
            for &n in adjacent {
                stack.push(n);
            }
        }
        if !nonzero(volume) {
            refuse!(SourceRefusal::ComponentVolumeUnproved);
        }
        component.sort_unstable();
        components.push(component);
        signed_volumes.push(volume);
    }
    Ok(SourceTopology::Proven(SourceManifold {
        positions,
        triangles,
        claim,
        aliases,
        retained_count,
        components,
        signed_volumes,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    fn separated(a: [[f64; 3]; 3], aid: [u32; 3], b: [[f64; 3]; 3], bid: [u32; 3]) -> bool {
        vertex_cones_separated(&Kernel::default(), &MeshWork::new(), a, aid, b, bid).unwrap()
    }
    fn p(x: f64, y: f64, z: f64) -> PointBox {
        [x, y, z].map(Ivl::from)
    }
    #[test]
    fn separated_completetriangles_are_excluded() {
        let a = [p(0., 0., 0.), p(2., 0., 0.), p(0., 2., 0.)];
        let b = [p(0., 0., 1.), p(2., 0., 1.), p(0., 2., 1.)];
        assert!(simplex_only(&a, [0, 1, 2], &b, [3, 4, 5]));
    }
    #[test]
    fn a_coplanar_crossing_is_not_certified_by_vertex_samples() {
        let a = [p(-2., -1., 0.), p(2., -1., 0.), p(0., 2., 0.)];
        let b = [p(-2., 1., 0.), p(2., 1., 0.), p(0., -2., 0.)];
        assert!(!simplex_only(&a, [0, 1, 2], &b, [3, 4, 5]));
    }
    #[test]
    fn opposite_sides_share_only_their_declared_edge() {
        let a = [p(0., 0., 0.), p(2., 0., 0.), p(0., 2., 0.)];
        let b = [p(2., 0., 0.), p(0., 0., 0.), p(0., -2., 0.)];
        assert!(simplex_only(&a, [0, 1, 2], &b, [1, 0, 3]));
    }
    #[test]
    fn same_side_common_edge_does_not_hide_overlap() {
        let a = [p(0., 0., 0.), p(2., 0., 0.), p(0., 2., 0.)];
        let b = [p(2., 0., 0.), p(0., 0., 0.), p(0., 1., 0.)];
        assert!(!simplex_only(&a, [0, 1, 2], &b, [1, 0, 3]));
    }
    #[test]
    fn box_vertex_requires_a_combination_of_weak_separating_axes() {
        let a = [[0., 0., 0.], [20., 10., 0.], [20., 0., 0.]];
        let b = [[0., 0., 0.], [20., 0., 5.], [0., 0., 5.]];
        assert!(separated(a, [0, 2, 1], b, [0, 5, 4]));
    }
    #[test]
    fn an_undeclared_shared_ray_cannot_pass_the_vertex_cone_proof() {
        let a = [[0., 0., 0.], [1., 0., 0.], [0., 1., 0.]];
        let b = [[0., 0., 0.], [0.5, 0., 0.], [0., 0., 1.]];
        assert!(!separated(a, [0, 1, 2], b, [0, 3, 4]));
    }
    #[test]
    fn coplanar_opposite_fans_use_in_plane_dual_functionals() {
        let a = [[0., 0., 0.], [10., 5., 0.], [20., 0., 0.]];
        let b = [[20., 10., 0.], [10., 5., 0.], [0., 10., 0.]];
        assert!(separated(a, [0, 8, 1], b, [2, 8, 3]));
    }

    fn with_motion_source(
        input: &super::super::super::MeshInput,
        run: impl FnOnce(&mut Kernel, &MeshWork, &SourceManifold<'_>, &WeldClaim),
    ) {
        let mut k = Kernel::default();
        let work = MeshWork::new();
        let prepared =
            super::super::super::prepare_conversion_with_work(&k, &work, input, 0.05, &[]).unwrap();
        let before_positions = input.positions.clone();
        let before_triangles = input.triangles.clone();
        let source = match validate_source_weld_with_work(
            &k,
            &work,
            &input.positions,
            &input.triangles,
            &prepared.weld,
        )
        .unwrap()
        {
            SourceTopology::Proven(source) => source,
            SourceTopology::Undecided(why) => panic!("{why:?}"),
        };
        run(&mut k, &work, &source, &prepared.weld);
        assert_eq!(input.positions, before_positions);
        assert_eq!(input.triangles, before_triangles);
    }
    fn motion_endpoints(
        claim: &WeldClaim,
        raw_endpoints: &[[f64; 3]],
    ) -> Vec<super::super::exact_geometry::P> {
        claim
            .vertices
            .iter()
            .map(|vertex| {
                // Alias order is NOT original STL vertex order.
                let raw = *vertex.raw_vertices.first().unwrap() as usize;
                super::super::exact_geometry::point(raw_endpoints[raw]).unwrap()
            })
            .collect()
    }
    #[test]
    fn fixed_complex_source_motion_covers_whole_translated_box_and_preserves_source() {
        use super::super::source_motion::{prove_source_motion_with_work, SourceMotionVerdict};
        let input = super::super::super::tests::box_mesh(2., 3., 4.);
        let ends: Vec<_> = input
            .positions
            .iter()
            .map(|&[x, y, z]| [x + 1. / 64., y, z])
            .collect();
        with_motion_source(&input, |k, work, source, claim| {
            let endpoints = motion_endpoints(claim, &ends);
            let proof =
                match prove_source_motion_with_work(k, work, source, &endpoints, 0.05).unwrap() {
                    SourceMotionVerdict::Proven(proof) => proof,
                    SourceMotionVerdict::Undecided(why) => panic!("{why}"),
                };
            assert!(core::ptr::eq(proof.source(), source));
            assert!(core::ptr::eq(
                proof.endpoints().as_ptr(),
                endpoints.as_ptr()
            ));
            assert!(proof.distance_upper() >= 1. / 64. && proof.distance_upper() < 0.016);
            assert!(proof.proved_time_cells() > 0);
        });
    }
    #[test]
    fn fixed_complex_motion_proves_shared_noisy_vertices_without_radius_welding() {
        use super::super::source_motion::{prove_source_motion_with_work, SourceMotionVerdict};
        let mut input = super::super::super::tests::box_mesh(2., 3., 4.);
        let ends = input.positions.clone();
        input.positions[6][2] += 1. / 256.;
        with_motion_source(&input, |k, work, source, claim| {
            let endpoints = motion_endpoints(claim, &ends);
            let proof =
                match prove_source_motion_with_work(k, work, source, &endpoints, 0.05).unwrap() {
                    SourceMotionVerdict::Proven(proof) => proof,
                    SourceMotionVerdict::Undecided(why) => panic!("{why}"),
                };
            assert!(proof.distance_upper() >= 1. / 256. && proof.distance_upper() < 0.004);
        });
    }
    #[test]
    fn valid_motion_endpoints_do_not_hide_a_collapsed_intermediate_surface() {
        use super::super::source_motion::{prove_source_motion_with_work, SourceMotionVerdict};
        let input = super::super::super::tests::box_mesh(2., 3., 4.);
        let ends: Vec<_> = input
            .positions
            .iter()
            .map(|&[x, y, z]| [-x, y, z])
            .collect();
        // Both endpoints embed a box; t=1/2 collapses its entire x extent.
        with_motion_source(&input, |k, work, source, claim| {
            let endpoints = motion_endpoints(claim, &ends);
            assert!(matches!(
                prove_source_motion_with_work(k, work, source, &endpoints, 10.).unwrap(),
                SourceMotionVerdict::Undecided(_)
            ));
        });
    }
    #[test]
    fn two_components_cannot_swap_through_each_other_even_with_valid_endpoints() {
        use super::super::source_motion::{prove_source_motion_with_work, SourceMotionVerdict};
        let first = super::super::super::tests::box_mesh(1., 1., 1.);
        let mut input = first.clone();
        input
            .positions
            .extend(first.positions.iter().map(|&[x, y, z]| [x + 4., y, z]));
        input
            .triangles
            .extend(first.triangles.iter().map(|t| t.map(|id| id + 8)));
        let ends: Vec<_> = input
            .positions
            .iter()
            .enumerate()
            .map(|(i, &[x, y, z])| [if i < 8 { x + 4. } else { x - 4. }, y, z])
            .collect();
        with_motion_source(&input, |k, work, source, claim| {
            let endpoints = motion_endpoints(claim, &ends);
            assert!(matches!(
                prove_source_motion_with_work(k, work, source, &endpoints, 5.).unwrap(),
                SourceMotionVerdict::Undecided(_)
            ));
        });
    }
    #[test]
    fn source_motion_checks_alias_contract_and_preserves_budget_and_cancellation_types() {
        use super::super::source_motion::{prove_source_motion_with_work, SourceMotionVerdict};
        let input = super::super::super::tests::box_mesh(2., 3., 4.);
        let ends = input.positions.clone();
        with_motion_source(&input, |k, work, source, claim| {
            let endpoints = motion_endpoints(claim, &ends);
            assert!(matches!(
                prove_source_motion_with_work(k, work, source, &[], 0.05).unwrap(),
                SourceMotionVerdict::Undecided(_)
            ));
            let exhausted = MeshWork::new();
            assert!(!exhausted.try_spend(usize::MAX));
            assert!(
                prove_source_motion_with_work(k, &exhausted, source, &endpoints, 0.05).is_err()
            );
            assert!(matches!(
                exhausted.check(k),
                Err(super::super::super::MeshError::BudgetExceeded { .. })
            ));
            let token = crate::kernel::CancelToken::new();
            k.set_cancel_token(token.clone());
            token.cancel();
            let Err(error) = prove_source_motion_with_work(k, work, source, &endpoints, 0.05)
            else {
                panic!("cancelled source motion must return the original cancellation");
            };
            assert!(error.is_cancelled());
        });
    }

    struct LayeredFixture {
        input: super::super::super::MeshInput,
        caps: [Vec<usize>; 3],
        walls: Vec<super::super::layered_source::WallClaim>,
    }
    /// Actual boundary of a finite union of unit voxels:5x3x2 stock, a full
    /// square through-hole at(3,1), and a square upper pocket at(1,1).
    /// This is procedural original source data, not a mesh fabricated as a proof.
    fn layered_fixture(upper_addition: bool) -> LayeredFixture {
        use super::super::layered_source::WallClaim;
        let occupied = |x: i32, y: i32, z: i32| {
            (0..5).contains(&x)
                && (0..3).contains(&y)
                && (0..2).contains(&z)
                && (x, y) != (3, 1)
                && !((x, y) == (1, 1) && z == if upper_addition { 0 } else { 1 })
        };
        let mut points = BTreeMap::<[i32; 3], u32>::new();
        let mut positions = Vec::new();
        let mut triangles = Vec::new();
        let mut caps: [Vec<usize>; 3] = core::array::from_fn(|_| Vec::new());
        let mut walls = Vec::new();
        for z in 0..2 {
            for y in 0..3 {
                for x in 0..5 {
                    if !occupied(x, y, z) {
                        continue;
                    }
                    for (offset, quad) in [
                        (
                            [-1, 0, 0],
                            [[x, y + 1, z], [x, y, z], [x, y, z + 1], [x, y + 1, z + 1]],
                        ),
                        (
                            [1, 0, 0],
                            [
                                [x + 1, y, z],
                                [x + 1, y + 1, z],
                                [x + 1, y + 1, z + 1],
                                [x + 1, y, z + 1],
                            ],
                        ),
                        (
                            [0, -1, 0],
                            [[x, y, z], [x + 1, y, z], [x + 1, y, z + 1], [x, y, z + 1]],
                        ),
                        (
                            [0, 1, 0],
                            [
                                [x + 1, y + 1, z],
                                [x, y + 1, z],
                                [x, y + 1, z + 1],
                                [x + 1, y + 1, z + 1],
                            ],
                        ),
                        (
                            [0, 0, -1],
                            [[x, y, z], [x, y + 1, z], [x + 1, y + 1, z], [x + 1, y, z]],
                        ),
                        (
                            [0, 0, 1],
                            [
                                [x, y, z + 1],
                                [x + 1, y, z + 1],
                                [x + 1, y + 1, z + 1],
                                [x, y + 1, z + 1],
                            ],
                        ),
                    ] {
                        let [dx, dy, dz] = offset;
                        if occupied(x + dx, y + dy, z + dz) {
                            continue;
                        }
                        let ids = quad.map(|point| {
                            *points.entry(point).or_insert_with(|| {
                                let id = u32::try_from(positions.len()).unwrap();
                                positions.push(point.map(f64::from));
                                id
                            })
                        });
                        let [a, b, c, d] = ids;
                        let first = triangles.len();
                        triangles.extend([[a, b, c], [a, c, d]]);
                        if dz == 0 {
                            walls.push(WallClaim {
                                triangles: vec![first, first + 1],
                                corners: ids,
                                interval: [z as usize, z as usize + 1],
                            });
                        } else {
                            let level = usize::try_from(quad[0][2]).unwrap();
                            caps[level].extend([first, first + 1]);
                        }
                    }
                }
            }
        }
        LayeredFixture {
            input: super::super::super::MeshInput {
                positions,
                triangles,
            },
            caps,
            walls,
        }
    }
    fn layered_claim(
        fixture: &LayeredFixture,
        weld: &WeldClaim,
    ) -> super::super::layered_source::LayeredClaim {
        use super::super::layered_source::{LayeredClaim, WallClaim};
        let mut raw_alias = vec![None; fixture.input.positions.len()];
        for (alias, v) in weld.vertices.iter().enumerate() {
            for &raw in &v.raw_vertices {
                raw_alias[raw as usize] = Some(alias as u32);
            }
        }
        let alias = |raw: u32| raw_alias[raw as usize].unwrap();
        let mut representatives = BTreeMap::new();
        let mut columns = Vec::new();
        for (id, v) in weld.vertices.iter().enumerate() {
            let [x, y, _] = v.position;
            let rep = *representatives
                .entry([x.to_bits(), y.to_bits()])
                .or_insert(id as u32);
            columns.push(Some(rep));
        }
        let level_aliases = [0., 1., 2.].map(|level| {
            u32::try_from(
                weld.vertices
                    .iter()
                    .position(|v| v.position[2] == level)
                    .unwrap(),
            )
            .unwrap()
        });
        LayeredClaim {
            axis: 2,
            level_aliases,
            columns,
            caps: fixture.caps.clone(),
            walls: fixture
                .walls
                .iter()
                .map(|w| WallClaim {
                    triangles: w.triangles.clone(),
                    corners: w.corners.map(alias),
                    interval: w.interval,
                })
                .collect(),
        }
    }
    fn layered_is_proven(
        k: &Kernel,
        work: &MeshWork,
        source: &SourceManifold<'_>,
        claim: &super::super::layered_source::LayeredClaim,
    ) -> bool {
        use super::super::layered_source::{analyze_layered_source_with_work, LayeredVerdict};
        match analyze_layered_source_with_work(
            k,
            work,
            super::super::source_view::ExactSourceView::original(source),
            claim,
        )
        .unwrap()
        {
            LayeredVerdict::Proven(p) => {
                assert!(core::ptr::eq(p.view().source(), source));
                assert!(core::ptr::eq(p.claim(), claim));
                true
            }
            LayeredVerdict::Undecided(_) => false,
        }
    }
    #[test]
    fn complete_two_slab_source_has_a_real_pocket_floor_and_polygonal_through_hole() {
        let fixture = layered_fixture(false);
        with_motion_source(&fixture.input, |k, work, source, weld| {
            let claim = layered_claim(&fixture, weld);
            assert!(!claim.caps[1].is_empty());
            assert!(layered_is_proven(k, work, source, &claim));
            // This SAME source is not relabeled as a one-translation/two-level prism.
            assert!(super::super::source_prism::prove_source_prism_with_work(
                k,
                work,
                super::super::source_view::ExactSourceView::original(source),
                &super::super::exact_geometry::point([0., 0., 1.]).unwrap()
            )
            .unwrap()
            .is_none());
        });
    }
    #[test]
    fn omitted_floor_extra_wall_and_duplicate_original_triangle_are_not_complete_ownership() {
        let fixture = layered_fixture(false);
        with_motion_source(&fixture.input, |k, work, source, weld| {
            let claim = layered_claim(&fixture, weld);
            let mut omitted = claim.clone();
            omitted.caps[1].pop();
            assert!(!layered_is_proven(k, work, source, &omitted));
            let mut extra = claim.clone();
            extra.walls.push(extra.walls[0].clone());
            assert!(!layered_is_proven(k, work, source, &extra));
            let mut duplicate = claim.clone();
            duplicate.caps[0][0] = duplicate.caps[0][1];
            assert!(!layered_is_proven(k, work, source, &duplicate));
        });
    }
    #[test]
    fn wrong_cap_owner_column_identity_and_wall_orientation_do_not_certify() {
        let fixture = layered_fixture(false);
        with_motion_source(&fixture.input, |k, work, source, weld| {
            let claim = layered_claim(&fixture, weld);
            let mut owner = claim.clone();
            core::mem::swap(&mut owner.caps[0][0], &mut owner.walls[0].triangles[0]);
            assert!(!layered_is_proven(k, work, source, &owner));
            let mut column = claim.clone();
            let first = column.columns.iter().flatten().copied().next().unwrap();
            let other = column
                .columns
                .iter()
                .flatten()
                .copied()
                .find(|&v| v != first)
                .unwrap();
            let index = column
                .columns
                .iter()
                .position(|&v| v == Some(first))
                .unwrap();
            column.columns[index] = Some(other);
            assert!(!layered_is_proven(k, work, source, &column));
            let mut reverse = claim.clone();
            let [a, b, c, d] = reverse.walls[0].corners;
            reverse.walls[0].corners = [b, a, d, c];
            assert!(!layered_is_proven(k, work, source, &reverse));
        });
    }
    #[test]
    fn an_outward_upper_addition_is_not_a_nested_monotone_pocket() {
        let fixture = layered_fixture(true);
        with_motion_source(&fixture.input, |k, work, source, weld| {
            let claim = layered_claim(&fixture, weld);
            assert!(!layered_is_proven(k, work, source, &claim));
        });
    }
    #[test]
    fn layered_source_uses_the_same_proven_motion_view_without_new_weld_or_source_mask() {
        use super::super::layered_source::{analyze_layered_source_with_work, LayeredVerdict};
        use super::super::source_motion::{prove_source_motion_with_work, SourceMotionVerdict};
        let mut fixture = layered_fixture(false);
        let endpoints = fixture.input.positions.clone();
        fixture.input.positions[0][2] += 1. / 256.;
        with_motion_source(&fixture.input, |k, work, source, weld| {
            let claim = layered_claim(&fixture, weld);
            assert!(!layered_is_proven(k, work, source, &claim));
            let exact = motion_endpoints(weld, &endpoints);
            let motion = match prove_source_motion_with_work(k, work, source, &exact, 0.05).unwrap()
            {
                SourceMotionVerdict::Proven(p) => p,
                SourceMotionVerdict::Undecided(why) => panic!("{why}"),
            };
            let answer = analyze_layered_source_with_work(
                k,
                work,
                super::super::source_view::ExactSourceView::motion(&motion),
                &claim,
            )
            .unwrap();
            match answer {
                LayeredVerdict::Proven(p) => {
                    assert!(core::ptr::eq(p.view().source(), source));
                    assert_eq!(
                        p.view().prior_motion_upper().to_bits(),
                        motion.distance_upper().to_bits()
                    );
                }
                LayeredVerdict::Undecided(why) => panic!("{why}"),
            }
        });
    }
    #[test]
    fn layered_source_keeps_cumulative_budget_and_native_cancel_precedence() {
        use super::super::layered_source::analyze_layered_source_with_work;
        let fixture = layered_fixture(false);
        with_motion_source(&fixture.input, |k, work, source, weld| {
            let claim = layered_claim(&fixture, weld);
            assert!(work.reserve_cells_core(k, 2_000_000).is_err());
            assert!(analyze_layered_source_with_work(
                k,
                work,
                super::super::source_view::ExactSourceView::original(source),
                &claim
            )
            .is_err());
            assert!(matches!(
                work.check(k),
                Err(super::super::super::MeshError::BudgetExceeded { .. })
            ));
            let token = crate::kernel::CancelToken::new();
            k.set_cancel_token(token.clone());
            token.cancel();
            let error = match analyze_layered_source_with_work(
                k,
                work,
                super::super::source_view::ExactSourceView::original(source),
                &claim,
            ) {
                Err(e) => e,
                Ok(_) => panic!("cancel was not preserved"),
            };
            assert!(error.is_cancelled());
        });
    }
}
