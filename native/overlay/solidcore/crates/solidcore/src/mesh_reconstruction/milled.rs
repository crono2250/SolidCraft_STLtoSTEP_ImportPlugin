//! Native machining-direction, section and profile planning. Modelling recipes live in ops.
use super::frame::FrameGeometry;
use super::numeric::{Bounds3, Vec2Numeric, Vec3Numeric};
use super::profile::drop_collinear;
use super::source::SourceMesh;
use super::types::{invalid, MeshError, MeshInput, PrismTool, Result};
use crate::eval::Frame;
use crate::math::{Vec2, Vec3};
use crate::prism::profile::{Loop2, Region2, Seg2};
use std::collections::BTreeMap;
const MAX_DIRECTIONS: usize = 6;
const MAX_CANDIDATES: usize = 48;
const MAX_LEVELS: usize = 64;
const MAX_SAMPLES: usize = 12;
const MAX_FIT_POINTS: usize = 4096;
const MAX_SECTION_POINTS: usize = 60_000;
const MAX_PLANNED_SEGMENTS: usize = 200_000;
struct Tri {
    v: [u32; 3],
    n: Vec3,
    area: f64,
}
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Role {
    Wall,
    Floor,
    Other,
}
#[derive(Clone, Debug)]
/// Source sections inside one machining slab.
pub struct SlabSections {
    /// Lower source level along the machining direction.
    pub lo: f64,
    /// Upper source level along the machining direction.
    pub hi: f64,
    /// Source section candidates used to plan this slab.
    pub sections: Vec<Vec<Region2>>,
}
#[derive(Clone, Debug)]
/// Geometry and candidate sections for one machining direction.
pub struct MilledSetup {
    /// Local profile frame.
    pub frame: Frame,
    /// Lowest source level in this frame.
    pub lo: f64,
    /// Highest source level in this frame.
    pub hi: f64,
    /// Computed extension beyond the source stock.
    pub margin: f64,
    /// Planar boolean tolerance computed from the source scale.
    pub boolean_tolerance: f64,
    /// Requested reconstruction tolerance.
    pub geometry_tolerance: f64,
    /// Profile fitting snap distance.
    pub snap: f64,
    /// Computed source-level comparison allowance.
    pub epsilon: f64,
    /// Source extent used by the planning policy.
    pub size: f64,
    /// Source slab/section candidates in level order.
    pub slabs: Vec<SlabSections>,
}
#[derive(Clone, Debug)]
/// One constant planar shadow over an axial run.
pub struct SlabShadow {
    /// Lower run level.
    pub lo: f64,
    /// Upper run level.
    pub hi: f64,
    /// Planar material regions, including their holes.
    pub regions: Vec<Region2>,
}
/// The old cap-loop nesting checks remain proof obligations, not caller-provided certificates.
#[derive(Clone, Debug)]
pub struct ProfileNesting {
    /// Original closed polygonal loops.
    pub raw: Vec<Loop2>,
    /// Candidate fitted loops in corresponding order.
    pub fitted: Vec<Loop2>,
    /// Source-scale nesting comparison allowance.
    pub epsilon: f64,
    /// Source extent used to bound nesting work.
    pub size: f64,
}
#[derive(Clone, Debug)]
/// Fitted slab candidates with all outstanding nesting obligations.
pub struct FittedShadowRuns {
    /// Fitted planar runs, not accepted final solids.
    pub runs: Vec<SlabShadow>,
    /// Every outstanding loop-nesting obligation.
    pub nesting: Vec<ProfileNesting>,
}
fn triangles(mesh: &SourceMesh) -> Result<Vec<Tri>> {
    mesh.triangles
        .iter()
        .map(|t| {
            let [a, b, c] = *t;
            let (Some(pa), Some(pb), Some(pc)) = (
                mesh.positions.get(a as usize),
                mesh.positions.get(b as usize),
                mesh.positions.get(c as usize),
            ) else {
                return Err(invalid("triangle refers to a missing vertex"));
            };
            let cross = (*pb - *pa).cross(*pc - *pa);
            // A zero-area sliver keeps the mesh closed but faces nowhere.
            let n = cross.normalized().unwrap_or(Vec3::ZERO);
            Ok(Tri {
                v: *t,
                n,
                area: cross.len() * 0.5,
            })
        })
        .collect()
}

fn point(mesh: &SourceMesh, i: u32) -> Vec3 {
    mesh.positions
        .get(i as usize)
        .copied()
        .unwrap_or(Vec3::ZERO)
}

/// One sign per line: the direction with a positive leading coordinate.
fn canonical(d: Vec3) -> Vec3 {
    if d.x < -1e-9 || (d.x.abs() <= 1e-9 && (d.y < -1e-9 || (d.y.abs() <= 1e-9 && d.z < 0.))) {
        -d
    } else {
        d
    }
}

/// Directions worth trying, best first: face normals (floors) and the lines where
/// neighbouring faces meet (walls; the facets of a cylinder meet along its axis).
fn candidate_directions(tris: &[Tri]) -> Vec<Vec3> {
    let mut bins = BTreeMap::<(i64, i64, i64), (Vec3, f64)>::new();
    let mut add = |d: Vec3, w: f64| {
        let d = canonical(d);
        let key = (
            (d.x * 400.).round() as i64,
            (d.y * 400.).round() as i64,
            (d.z * 400.).round() as i64,
        );
        let entry = bins.entry(key).or_insert((Vec3::ZERO, 0.));
        entry.0 += d * w;
        entry.1 += w;
    };
    let mut sides = BTreeMap::<(u32, u32), Vec<usize>>::new();
    for (i, t) in tris.iter().enumerate() {
        add(t.n, t.area);
        let [a, b, c] = t.v;
        for (a, b) in [(a, b), (b, c), (c, a)] {
            sides.entry((a.min(b), a.max(b))).or_default().push(i);
        }
    }
    for pair in sides.values() {
        let [i, j] = pair.as_slice() else { continue };
        let (Some(a), Some(b)) = (tris.get(*i), tris.get(*j)) else {
            continue;
        };
        let c = a.n.cross(b.n);
        if c.len() > 0.004 {
            if let Some(c) = c.normalized() {
                add(c, a.area.min(b.area));
            }
        }
    }
    let mut bins: Vec<(Vec3, f64)> = bins
        .into_values()
        .filter_map(|(sum, w)| Some((sum.normalized()?, w)))
        .collect();
    bins.sort_by(|a, b| b.1.total_cmp(&a.1));
    let close = 1f64.to_radians().cos();
    let mut clusters: Vec<(Vec3, f64)> = Vec::new();
    for (d, w) in bins.into_iter().take(20_000) {
        if let Some(c) = clusters
            .iter_mut()
            .find(|c| c.0.normalized().is_some_and(|cd| cd.dot(d).abs() > close))
        {
            let sign = if c.0.dot(d) < 0. { -1. } else { 1. };
            c.0 += d * (w * sign);
            c.1 += w;
        } else if clusters.len() < 256 {
            clusters.push((d * w, w));
        }
    }
    clusters.sort_by(|a, b| b.1.total_cmp(&a.1));
    // Model axes stay exact: an STL of an axis-aligned part keeps its planes axis-aligned.
    let snap_axis = |d: Vec3| {
        let near = 0.02f64.to_radians().cos();
        [Vec3::X, Vec3::Y, Vec3::Z]
            .into_iter()
            .find(|a| d.dot(*a).abs() > near)
            .unwrap_or(d)
    };
    let mut out: Vec<Vec3> = Vec::new();
    for (sum, _) in clusters {
        let Some(d) = sum.normalized() else { continue };
        let d = canonical(snap_axis(d));
        if !out.iter().any(|o| o.dot(d).abs() > close) {
            out.push(d);
        }
        if out.len() >= MAX_CANDIDATES {
            break;
        }
    }
    out
}

fn heights(mesh: &SourceMesh, t: &Tri, d: Vec3) -> [f64; 3] {
    let [a, b, c] = t.v;
    [
        point(mesh, a).dot(d),
        point(mesh, b).dot(d),
        point(mesh, c).dot(d),
    ]
}

/// How a triangle lies relative to direction `d`, within `snap`.
fn role(mesh: &SourceMesh, t: &Tri, d: Vec3, snap: f64) -> Role {
    let h = heights(mesh, t, d);
    let (lo, hi) = (h[0].min(h[1]).min(h[2]), h[0].max(h[1]).max(h[2]));
    if hi - lo <= snap {
        return Role::Floor;
    }
    let [a, b, c] = t.v;
    let (pa, pb, pc) = (point(mesh, a), point(mesh, b), point(mesh, c));
    let longest = pa.dist(pb).max(pb.dist(pc)).max(pc.dist(pa));
    // Twice the projected area over the longest side: the projected triangle's height.
    let projected = (pb - pa).cross(pc - pa).dot(d).abs();
    if projected <= snap * longest {
        Role::Wall
    } else {
        Role::Other
    }
}

/// The fewest directions (greedily) that explain every triangle as a wall or a floor.
fn choose_directions(
    mesh: &SourceMesh,
    tris: &[Tri],
    candidates: &[Vec3],
    snap: f64,
    total: f64,
) -> Result<Vec<Vec3>> {
    let roles: Vec<Vec<bool>> = candidates
        .iter()
        .map(|d| {
            tris.iter()
                .map(|t| role(mesh, t, *d, snap) != Role::Other)
                .collect()
        })
        .collect();
    let mut explained = vec![false; tris.len()];
    let mut chosen: Vec<Vec3> = Vec::new();
    let mut used = vec![false; candidates.len()];
    while chosen.len() < MAX_DIRECTIONS {
        let mut best: Option<(usize, f64)> = None;
        for (c, r) in roles.iter().enumerate() {
            if used.get(c).copied().unwrap_or(true) {
                continue;
            }
            let gain: f64 = tris
                .iter()
                .zip(r)
                .zip(&explained)
                .filter(|((_, ok), done)| **ok && !**done)
                .map(|((t, _), _)| t.area)
                .sum();
            if best.is_none_or(|(_, g)| gain > g) {
                best = Some((c, gain));
            }
        }
        let Some((c, gain)) = best else { break };
        if gain <= total * 1e-9 {
            break;
        }
        if let Some(u) = used.get_mut(c) {
            *u = true;
        }
        if let (Some(d), Some(r)) = (candidates.get(c), roles.get(c)) {
            chosen.push(*d);
            for (e, ok) in explained.iter_mut().zip(r) {
                *e |= *ok;
            }
        }
    }
    let unexplained: f64 = tris
        .iter()
        .zip(&explained)
        .filter(|(_, e)| !**e)
        .map(|(t, _)| t.area)
        .sum();
    if unexplained > total * 1e-4 {
        return Err(MeshError::Refused{stage:"milled direction coverage",detail:format!(
            "{:.1}% of the surface is not parallel or square to {} machining directions (drill points, spheres, sloped or freeform faces); only milled and constant-section parts convert",
            unexplained / total * 100.,
            chosen.len().max(1)
        )});
    }
    if chosen.is_empty() {
        return Err(MeshError::Refused {
            stage: "milled machining directions",
            detail: "no machining direction found".into(),
        });
    }
    Ok(chosen)
}

fn direction_setup(
    k: &crate::Kernel,
    work_budget: &super::work::MeshWork,
    mesh: &SourceMesh,
    tris: &[Tri],
    plane: Frame,
    tolerance: f64,
    epsilon: f64,
    snap: f64,
    size: f64,
    planned_segments: &mut usize,
) -> Result<MilledSetup> {
    let d = plane.normal();
    let (lo, hi) = mesh
        .positions
        .iter()
        .map(|p| p.dot(d))
        .fold((f64::INFINITY, f64::NEG_INFINITY), |(lo, hi), h| {
            (lo.min(h), hi.max(h))
        });
    if !crate::geom::certified::above(hi - lo, tolerance) {
        return Err(MeshError::Refused {
            stage: "milled analytic thickness",
            detail: "the part is thinner than the tolerance".into(),
        });
    }
    let roles: Vec<Role> = tris.iter().map(|t| role(mesh, t, d, snap)).collect();
    let ranges: Vec<(f64, f64)> = tris
        .iter()
        .map(|t| {
            let h = heights(mesh, t, d);
            (h[0].min(h[1]).min(h[2]), h[0].max(h[1]).max(h[2]))
        })
        .collect();
    // Floor levels, merged within the tolerance; the part's extremes stay exact.
    let mut raw: Vec<f64> = tris
        .iter()
        .zip(&roles)
        .zip(&ranges)
        .filter(|((_, r), _)| **r == Role::Floor)
        .map(|(_, (a, b))| (a + b) * 0.5)
        .collect();
    raw.push(lo);
    raw.push(hi);
    raw.sort_by(f64::total_cmp);
    let mut levels: Vec<f64> = Vec::new();
    let mut group: Vec<f64> = Vec::new();
    let flush = |group: &mut Vec<f64>, levels: &mut Vec<f64>| {
        if group.is_empty() {
            return;
        }
        let value = if group.iter().any(|h| *h <= lo) {
            lo
        } else if group.iter().any(|h| *h >= hi) {
            hi
        } else {
            group.iter().sum::<f64>() / group.len() as f64
        };
        levels.push(value);
        group.clear();
    };
    for h in raw {
        if group.last().is_some_and(|g| h - g > tolerance) {
            flush(&mut group, &mut levels);
        }
        group.push(h);
    }
    flush(&mut group, &mut levels);
    if levels.len() > MAX_LEVELS {
        return Err(invalid(&format!(
            "too many depth levels along one direction ({}; at most {MAX_LEVELS})",
            levels.len()
        )));
    }
    let vertex_heights: Vec<f64> = {
        let mut v: Vec<f64> = mesh.positions.iter().map(|p| p.dot(d)).collect();
        v.sort_by(f64::total_cmp);
        v
    };
    let btol = (snap * 0.5).clamp(1e-9, 1.);
    // (start, end, shadow) for each run of slabs with the same shadow.
    let mut slabs = Vec::new();
    for pair in levels.windows(2) {
        k.check_cancelled("mesh_reconstruction::milled_setup")?;
        let [l0, l1] = pair else { continue };
        let (l0, l1) = (*l0, *l1);
        let varying = tris
            .iter()
            .zip(&roles)
            .zip(&ranges)
            .any(|((_, r), (a, b))| *r != Role::Wall && *a < l1 - snap && *b > l0 + snap);
        let samples: Vec<f64> = if varying {
            let delta = (snap * 2.).min((l1 - l0) * 0.25);
            let mut inner: Vec<f64> = Vec::new();
            let from = vertex_heights.partition_point(|h| *h <= l0 + delta);
            for h in vertex_heights
                .iter()
                .skip(from)
                .take_while(|h| **h < l1 - delta)
            {
                if inner.last().is_none_or(|last| h - last > snap) {
                    inner.push(*h);
                }
            }
            let keep = MAX_SAMPLES - 2;
            let step = inner.len().div_ceil(keep).max(1);
            let mut s = vec![l0 + delta, l1 - delta];
            s.extend(inner.iter().step_by(step));
            s
        } else {
            vec![(l0 + l1) * 0.5]
        };
        let mut sections = Vec::new();
        for h in samples {
            let regions = section(k, mesh, tris, &ranges, &plane, d, h, epsilon, snap * 0.2)?;
            let count: usize = regions
                .iter()
                .flat_map(Region2::loops)
                .map(|lp| lp.segs.len())
                .sum();
            work_budget.reserve_output(k, count)?;
            *planned_segments = planned_segments.saturating_add(count);
            if *planned_segments > MAX_PLANNED_SEGMENTS {
                return Err(MeshError::BudgetExceeded {
                    stage: "milled planned segment references",
                    limit: MAX_PLANNED_SEGMENTS,
                });
            }
            sections.push(regions);
        }
        slabs.push(SlabSections {
            lo: l0,
            hi: l1,
            sections,
        });
    }
    Ok(MilledSetup {
        frame: plane,
        lo,
        hi,
        margin: (size * 0.01).max(1.),
        boolean_tolerance: btol,
        geometry_tolerance: tolerance,
        snap,
        epsilon,
        size,
        slabs,
    })
}
fn section(
    k: &crate::Kernel,
    mesh: &SourceMesh,
    tris: &[Tri],
    ranges: &[(f64, f64)],
    plane: &Frame,
    d: Vec3,
    h: f64,
    epsilon: f64,
    collinear: f64,
) -> Result<Vec<Region2>> {
    let above = |i: u32| point(mesh, i).dot(d) > h;
    let cross = |a: u32, b: u32| -> Vec2 {
        // Interpolate from the lower index so both triangles at an edge get the same point.
        let (a, b) = (a.min(b), a.max(b));
        let (pa, pb) = (point(mesh, a), point(mesh, b));
        let (ha, hb) = (pa.dot(d), pb.dot(d));
        let t = if (hb - ha).abs() > 0. {
            ((h - ha) / (hb - ha)).clamp(0., 1.)
        } else {
            0.5
        };
        plane.to_local(pa + (pb - pa) * t)
    };
    // Each segment runs from the side the boundary leaves the slab above (in the triangle's
    // winding) to the side it enters it: material on its left seen from +d.
    let mut next = BTreeMap::<(u32, u32), ((u32, u32), Vec2)>::new();
    for (t, (lo, hi)) in tris.iter().zip(ranges) {
        k.check_cancelled("mesh_reconstruction::section")?;
        if *hi <= h || *lo > h {
            continue;
        }
        let [a, b, c] = t.v;
        let mut down = None;
        let mut up = None;
        for (p, q) in [(a, b), (b, c), (c, a)] {
            match (above(p), above(q)) {
                (true, false) => down = Some((p.min(q), p.max(q))),
                (false, true) => up = Some((p.min(q), p.max(q))),
                _ => {}
            }
        }
        let (Some(from), Some(to)) = (down, up) else {
            continue;
        };
        if next.insert(from, (to, cross(from.0, from.1))).is_some() {
            return Err(invalid("the mesh crosses itself"));
        }
        if next.len() > MAX_SECTION_POINTS {
            return Err(invalid("a section exceeds its geometry budget"));
        }
    }
    let mut loops: Vec<Vec<Vec2>> = Vec::new();
    while let Some((&start, _)) = next.first_key_value() {
        let mut current = start;
        let mut points = Vec::new();
        loop {
            let Some((to, p)) = next.remove(&current) else {
                return Err(invalid("a section is not closed"));
            };
            if points.last().is_none_or(|q: &Vec2| q.dist(p) > epsilon) {
                points.push(p);
            }
            current = to;
            if current == start {
                break;
            }
        }
        while points.len() > 1
            && points
                .first()
                .zip(points.last())
                .is_some_and(|(a, b)| a.dist(*b) <= epsilon)
        {
            points.pop();
        }
        // Faces crossed by the section leave runs of collinear points (one per triangle).
        let points = drop_collinear(&points, collinear);
        if points.len() >= 3 {
            loops.push(points);
        }
    }
    let mut accepted = Vec::new();
    for points in loops {
        let lp = super::profile::polygon(&points);
        let area = lp.signed_area()?;
        if area.value.abs() > epsilon * epsilon + area.bound {
            accepted.push(lp);
        }
    }
    super::outline::nest_oriented_loops(accepted)
}
struct Shared<'a> {
    work: &'a super::work::Work<'a>,
    points: Vec<Vec2>,
    circles: Vec<(Vec2, f64)>,
}

impl<'a> Shared<'a> {
    fn new(work: &'a super::work::Work<'a>) -> Self {
        Self {
            work,
            points: Vec::new(),
            circles: Vec::new(),
        }
    }
    fn point(&mut self, p: Vec2, within: f64) -> Result<Vec2> {
        self.work.spend(self.points.len().saturating_add(1))?;
        if let Some(q) = self.points.iter().find(|q| q.dist(p) <= within) {
            return Ok(*q);
        }
        if self.points.len() < 100_000 {
            self.points.push(p);
        }
        Ok(p)
    }

    fn circle(&mut self, c: Vec2, r: f64, within: f64) -> Result<(Vec2, f64)> {
        self.work.spend(self.circles.len().saturating_add(1))?;
        if let Some(k) = self
            .circles
            .iter()
            .find(|(q, s)| q.dist(c) <= within && (s - r).abs() <= within)
        {
            return Ok(*k);
        }
        if self.circles.len() < 100_000 {
            self.circles.push((c, r));
        }
        Ok((c, r))
    }

    fn snap(&mut self, lp: Loop2, within: f64) -> Result<Loop2> {
        let segs = lp
            .segs
            .into_iter()
            .map(|s| {
                Ok(match s {
                    Seg2::Line { a, b } => Seg2::Line {
                        a: self.point(a, within)?,
                        b: self.point(b, within)?,
                    },
                    Seg2::Arc {
                        center,
                        radius,
                        start,
                        sweep,
                    } => {
                        let (center, radius) = self.circle(center, radius, within)?;
                        Seg2::Arc {
                            center,
                            radius,
                            start,
                            sweep,
                        }
                    }
                    other => other,
                })
            })
            .collect::<Result<Vec<_>>>()?;
        Ok(Loop2 {
            segs: super::profile::close_gaps(segs),
        })
    }
}

/// Standalone single-job convenience; multi-stage callers share one `MeshWork`.
pub fn milled_setups(
    k: &crate::Kernel,
    input: &MeshInput,
    tolerance: f64,
) -> Result<Vec<MilledSetup>> {
    let work_budget = super::work::MeshWork::new();
    milled_setups_with_work(k, &work_budget, input, tolerance)
}

/// Plan machining frames and source sections, without building a body using the same complete-workflow budget.
pub fn milled_setups_with_work(
    k: &crate::Kernel,
    work_budget: &super::work::MeshWork,
    input: &MeshInput,
    tolerance: f64,
) -> Result<Vec<MilledSetup>> {
    work_budget.check(k)?;
    let answer = (|| {
        super::regions::checked_tolerance(tolerance)?;
        work_budget.spend(
            k,
            input
                .positions
                .len()
                .saturating_add(input.triangles.len().saturating_mul(3)),
        )?;
        let mesh = SourceMesh::checked(input)?;
        let mut bounds = Bounds3::new();
        for p in &mesh.positions {
            bounds.add_point(*p);
        }
        let size = bounds.size().len().max(1.);
        let epsilon = (size * 1e-7).min(tolerance * 0.01).max(1e-9);
        let snap = (tolerance * 0.1).max(epsilon * 3.);
        let tris = triangles(&mesh)?;
        let total: f64 = tris.iter().map(|t| t.area).sum();
        if !crate::geom::certified::above(total, 0.) {
            return Err(invalid("empty mesh"));
        }
        let work = super::work::Work::with_budget(k, work_budget)?;
        work.spend(tris.len().saturating_mul(MAX_CANDIDATES))?;
        let candidates = candidate_directions(&tris);
        let directions = choose_directions(&mesh, &tris, &candidates, snap, total)?;
        let mut setups = Vec::new();
        let mut planned_segments = 0usize;
        for d in &directions {
            work.spend(tris.len().saturating_mul(MAX_LEVELS * MAX_SAMPLES))?;
            let across = directions.iter().copied().find(|e| e.dot(*d).abs() < 1e-6);
            let frame = across
                .and_then(|e| Frame::new(Vec3::ZERO, e, d.cross(e)))
                .or_else(|| Frame::from_normal(Vec3::ZERO, *d))
                .ok_or_else(|| invalid("degenerate machining direction"))?;
            setups.push(direction_setup(
                k,
                work_budget,
                &mesh,
                &tris,
                frame,
                tolerance,
                epsilon,
                snap,
                size,
                &mut planned_segments,
            )?);
        }
        Ok(setups)
    })();
    work_budget.check(k)?;
    answer
}

/// Every result is still a candidate until all returned nesting obligations and the final
/// full-domain source/B-rep certificate have succeeded.
/// Standalone single-job convenience; multi-stage callers share one `MeshWork`.
pub fn fit_shadow_runs(
    k: &crate::Kernel,
    setup: &MilledSetup,
    raw: Vec<SlabShadow>,
) -> Result<FittedShadowRuns> {
    let work_budget = super::work::MeshWork::new();
    fit_shadow_runs_with_work(k, &work_budget, setup, raw)
}

/// Fit all runs of one machining direction with shared corner and circle candidates using the same complete-workflow budget.
pub fn fit_shadow_runs_with_work(
    k: &crate::Kernel,
    work_budget: &super::work::MeshWork,
    setup: &MilledSetup,
    raw: Vec<SlabShadow>,
) -> Result<FittedShadowRuns> {
    work_budget.check(k)?;
    let answer = (|| {
        let references: usize = raw
            .iter()
            .flat_map(|s| &s.regions)
            .flat_map(Region2::loops)
            .map(|lp| lp.segs.len())
            .sum();
        work_budget.spend(k, references)?;
        work_budget.reserve_output(k, references.saturating_mul(4))?;
        if references > MAX_PLANNED_SEGMENTS {
            return Err(MeshError::BudgetExceeded {
                stage: "fitted shadow segment references",
                limit: MAX_PLANNED_SEGMENTS,
            });
        }
        if raw.len() > MAX_LEVELS {
            return Err(MeshError::BudgetExceeded {
                stage: "milled shadow runs",
                limit: MAX_LEVELS,
            });
        }
        let work = super::work::Work::with_budget(k, work_budget)?;
        let mut shared = Shared::new(&work);
        let mut runs = Vec::new();
        let mut nesting = Vec::new();
        for slab in raw {
            let mut raw_loops = Vec::new();
            let mut fitted = Vec::new();
            let mut regions = Vec::new();
            for region in &slab.regions {
                let points = loop_points(&region.outer, setup.snap)?;
                work.spend(points.len().saturating_mul(points.len().saturating_add(1)))?;
                let raw_outer = super::profile::polygon(&points);
                let outer = shared.snap(
                    super::profile::fit_profile(&points, setup.geometry_tolerance, setup.snap),
                    setup.snap,
                )?;
                let mut holes = Vec::new();
                for hole in &region.holes {
                    let points = loop_points(hole, setup.snap)?;
                    work.spend(points.len().saturating_mul(points.len().saturating_add(1)))?;
                    let fit = shared.snap(
                        super::profile::fit_profile(&points, setup.geometry_tolerance, setup.snap),
                        setup.snap,
                    )?;
                    raw_loops.push(super::profile::polygon(&points));
                    fitted.push(fit.clone());
                    holes.push(ccw(&fit)?.reversed());
                }
                raw_loops.push(raw_outer);
                fitted.push(outer.clone());
                regions.push(Region2 {
                    outer: ccw(&outer)?,
                    holes,
                });
            }
            nesting.push(ProfileNesting {
                raw: raw_loops,
                fitted,
                epsilon: setup.epsilon,
                size: setup.size,
            });
            runs.push(SlabShadow {
                lo: slab.lo,
                hi: slab.hi,
                regions,
            });
        }
        Ok(FittedShadowRuns { runs, nesting })
    })();
    work_budget.check(k)?;
    answer
}
fn ccw(lp: &Loop2) -> Result<Loop2> {
    let area = lp.signed_area()?;
    match area.sign() {
        Some(true) => Ok(lp.clone()),
        Some(false) => Ok(lp.reversed()),
        None => Err(MeshError::Undecided {
            stage: "profile orientation",
            work: lp.segs.len(),
        }),
    }
}
/// Only line/arc shadows are generated here. Unsupported segments refuse, never sample.
fn loop_points(lp: &Loop2, tolerance: f64) -> Result<Vec<Vec2>> {
    let mut points = Vec::new();
    for seg in &lp.segs {
        match *seg {
            Seg2::Line { a, .. } => points.push(a),
            Seg2::Arc { radius, sweep, .. } => {
                if !(radius > 0. && radius.is_finite() && tolerance > 0. && tolerance.is_finite()) {
                    return Err(invalid("invalid shadow arc"));
                }
                let step = if tolerance >= radius {
                    std::f64::consts::PI
                } else {
                    2. * (1. - tolerance / radius).clamp(-1., 1.).acos()
                };
                if !(step > 0. && step.is_finite()) {
                    return Err(MeshError::Undecided {
                        stage: "shadow arc subdivision",
                        work: points.len(),
                    });
                }
                let count = (sweep.abs() / step).ceil().max(1.);
                if count > MAX_SECTION_POINTS as f64
                    || points.len().saturating_add(count as usize) > MAX_SECTION_POINTS
                {
                    return Err(MeshError::BudgetExceeded {
                        stage: "shadow arc points",
                        limit: MAX_SECTION_POINTS,
                    });
                }
                let count = count as usize;
                for i in 0..count {
                    points.push(seg.point_at(i as f64 / count as f64));
                }
            }
            _ => {
                return Err(invalid(
                    "mesh reconstruction shadows must be lines or circular arcs",
                ))
            }
        }
    }
    Ok(points)
}
/// Native exact area decisions with the original quantitative pocket threshold.
pub fn keep_fresh_tool(
    region: &Region2,
    difference: &[Region2],
    boolean_tolerance: f64,
) -> Result<bool> {
    let parent = region.signed_area()?;
    let mut left = 0.;
    let mut uncertainty = 0.;
    for r in difference {
        let a = r.signed_area()?;
        left += a.value;
        uncertainty += a.bound;
    }
    let threshold = parent.value * 1e-6 + boolean_tolerance;
    let bound = uncertainty + parent.bound * 1e-6;
    if left - bound > threshold {
        return Ok(true);
    }
    if left + bound <= threshold {
        return Ok(false);
    }
    Err(MeshError::Undecided {
        stage: "pocket depth eligibility",
        work: difference.len(),
    })
}
/// The caller supplies the open-end intersection, native code owns span calculations.
pub fn pocket_tool(
    setup: &MilledSetup,
    floor: f64,
    from_top: bool,
    regions: Vec<Region2>,
) -> PrismTool {
    let (start, end) = if from_top {
        (floor, setup.hi + setup.margin)
    } else {
        (setup.lo - setup.margin, floor)
    };
    PrismTool {
        frame: setup.frame.clone(),
        regions,
        start,
        end,
    }
}
fn material_bounds(regions: &[Region2]) -> Option<(Vec2, Vec2)> {
    let mut lo = Vec2::new(f64::INFINITY, f64::INFINITY);
    let mut hi = Vec2::new(f64::NEG_INFINITY, f64::NEG_INFINITY);
    for s in regions.iter().flat_map(|r| &r.outer.segs) {
        let (a, b) = match s {
            Seg2::Line { a, b } => (*a, *b),
            Seg2::Arc { center, radius, .. } if radius.is_finite() && *radius > 0. => (
                *center - Vec2::new(*radius, *radius),
                *center + Vec2::new(*radius, *radius),
            ),
            _ => return None,
        };
        if ![a.x, a.y, b.x, b.y].iter().all(|v| v.is_finite()) {
            return None;
        }
        lo.x = lo.x.min(a.x).min(b.x);
        lo.y = lo.y.min(a.y).min(b.y);
        hi.x = hi.x.max(a.x).max(b.x);
        hi.y = hi.y.max(a.y).max(b.y);
    }
    // Enclose the rounding of center +/- radius as well.
    lo.x = -crate::geom::certified::next_up(-lo.x);
    lo.y = -crate::geom::certified::next_up(-lo.y);
    hi.x = crate::geom::certified::next_up(hi.x);
    hi.y = crate::geom::certified::next_up(hi.y);
    (lo.x <= hi.x && lo.y <= hi.y).then_some((lo, hi))
}

/// Match the same cyclic sequence of boundaries. For line segments, endpoint bounds
/// also bound every point on the segment. Arcs include centre, radius and angular bounds;
/// other curves use exact equality only.
pub(crate) fn same_loop(a: &Loop2, b: &Loop2, distance: f64) -> bool {
    // A full circle's start is arbitrary; the kernel may split it at another seam.
    let circle = |l: &Loop2| -> Option<(Vec2, f64, f64)> {
        let Some(Seg2::Arc { center, radius, .. }) = l.segs.first() else {
            return None;
        };
        let mut total = 0.;
        let sign = match l.segs.first()? {
            Seg2::Arc { sweep, .. } => sweep.signum(),
            _ => return None,
        };
        for (s, next) in l.segs.iter().zip(l.segs.iter().cycle().skip(1)) {
            let Seg2::Arc {
                center: c,
                radius: r,
                sweep,
                ..
            } = s
            else {
                return None;
            };
            if center.dist(*c) + (radius - r).abs() > distance
                || sweep.signum() != sign
                || s.end().dist(next.start()) > distance
            {
                return None;
            }
            total += sweep;
        }
        ((total.abs() - std::f64::consts::TAU).abs() <= 8. * f64::EPSILON * l.segs.len() as f64)
            .then_some((*center, *radius, total.signum()))
    };
    if let (Some((a, r, sign)), Some((b, s, other))) = (circle(a), circle(b)) {
        return sign == other && a.dist(b) + (r - s).abs() <= distance;
    }
    if a.segs.len() != b.segs.len() || a.segs.is_empty() {
        return false;
    }
    let matching = |a: &Seg2, b: &Seg2| match (a, b) {
        (Seg2::Line { a, b }, Seg2::Line { a: c, b: d }) => {
            a.dist(*c) <= distance && b.dist(*d) <= distance
        }
        (
            Seg2::Arc {
                center: a,
                radius: r,
                start: t,
                sweep: u,
            },
            Seg2::Arc {
                center: b,
                radius: s,
                start: v,
                sweep: w,
            },
        ) => {
            let angle = (t - v + std::f64::consts::PI).rem_euclid(std::f64::consts::TAU)
                - std::f64::consts::PI;
            a.dist(*b) + (r - s).abs() + r.abs().max(s.abs()) * (angle.abs() + (u - w).abs())
                <= distance
        }
        _ => a == b,
    };
    let Some(first) = a.segs.first() else {
        return false;
    };
    b.segs
        .iter()
        .enumerate()
        .filter(|(_, s)| matching(first, s))
        .take(8)
        .any(|(start, _)| {
            a.segs
                .iter()
                .zip(b.segs.iter().cycle().skip(start))
                .all(|(a, b)| matching(a, b))
        })
}

/// Geometric helpers below consume whole line/arc extents and bounded area sums; ops only
/// selects and sequences requests. A missing interval decision refuses rather than samples.
fn segment_length(s: &Seg2) -> Result<f64> {
    match *s {
        Seg2::Line { a, b } => Ok(a.dist(b)),
        Seg2::Arc { radius, sweep, .. }
            if radius.is_finite() && radius > 0. && sweep.is_finite() =>
        {
            Ok(radius * sweep.abs())
        }
        _ => Err(invalid("only line/arc machining profiles are supported")),
    }
}
fn area_sum(regions: &[Region2]) -> Result<(f64, f64)> {
    let (mut value, mut bound) = (0., 0.);
    for region in regions {
        let area = region.signed_area()?;
        value += area.value;
        bound += area.bound;
    }
    bound += crate::nurbs::math::gamma(regions.len() + 1) * value.abs();
    Ok((value, bound))
}
fn perimeter(regions: &[Region2]) -> Result<f64> {
    let mut length = 0.;
    for s in regions
        .iter()
        .flat_map(Region2::loops)
        .flat_map(|lp| &lp.segs)
    {
        length += segment_length(s)?;
    }
    if !length.is_finite() {
        return Err(invalid("profile perimeter is not finite"));
    }
    Ok(length)
}
/// Decide whether consecutive axial runs share a level boundary.
pub fn can_merge_runs(previous: &SlabShadow, next: &SlabShadow, tolerance: f64) -> Result<bool> {
    if ![previous.hi, next.lo, tolerance]
        .iter()
        .all(|v| v.is_finite())
    {
        return Err(invalid("run heights must be finite"));
    }
    Ok((previous.hi - next.lo).abs() <= tolerance)
}
/// Some decides without a planar boolean; None asks ops for both directed differences.
pub fn same_shadow(
    a: &[Region2],
    b: &[Region2],
    snap: f64,
    boolean_tolerance: f64,
) -> Result<Option<bool>> {
    if a.len() == b.len()
        && a.iter().zip(b).all(|(a, b)| {
            same_loop(&a.outer, &b.outer, snap)
                && a.holes.len() == b.holes.len()
                && a.holes
                    .iter()
                    .zip(&b.holes)
                    .all(|(a, b)| same_loop(a, b, snap))
        })
    {
        return Ok(Some(true));
    }
    let (aa, ab) = area_sum(a)?;
    let (ba, bb) = area_sum(b)?;
    let limit = perimeter(a)? * snap + perimeter(b)? * snap + boolean_tolerance;
    if (aa - ba).abs() - ab - bb > limit {
        return Ok(Some(false));
    }
    Ok(None)
}
/// Check both exact boolean differences against the shadow comparison allowance.
pub fn shadow_differences_agree(
    a: &[Region2],
    b: &[Region2],
    ab: &[Region2],
    ba: &[Region2],
    snap: f64,
    boolean_tolerance: f64,
) -> Result<bool> {
    let limit = (perimeter(a)? + perimeter(b)?) * snap + boolean_tolerance;
    for difference in [ab, ba] {
        let (v, e) = area_sum(difference)?;
        if v - e > limit {
            return Ok(false);
        }
        if v + e > limit {
            return Err(MeshError::Undecided {
                stage: "shadow difference",
                work: difference.len(),
            });
        }
    }
    Ok(true)
}
/// Reject uncertain area signs and retain non-sliver pocket regions.
pub fn filter_pocket_regions(regions: Vec<Region2>, tolerance: f64) -> Result<Vec<Region2>> {
    let mut out = Vec::new();
    for region in regions {
        let area = region.signed_area()?;
        let threshold = perimeter(std::slice::from_ref(&region))? * tolerance * 0.5;
        if area.value - area.bound > threshold {
            out.push(region);
        } else if area.value + area.bound > threshold {
            return Err(MeshError::Undecided {
                stage: "pocket sliver",
                work: region.outer.segs.len(),
            });
        }
    }
    Ok(out)
}
/// Validate bounded planar boolean outputs before further planning.
pub fn filter_planar_result(regions: Vec<Region2>, tolerance: f64) -> Result<Vec<Region2>> {
    let degenerate = |lp: &Loop2| -> Result<bool> {
        if lp.segs.is_empty() {
            return Ok(true);
        }
        let area = lp.signed_area()?;
        let mut length = 0.;
        for s in &lp.segs {
            length += segment_length(s)?;
        }
        let limit = length * tolerance;
        if area.value.abs() + area.bound <= limit {
            return Ok(true);
        }
        if area.value.abs() - area.bound > limit {
            return Ok(false);
        }
        Err(MeshError::Undecided {
            stage: "planar sliver",
            work: lp.segs.len(),
        })
    };
    let mut out = Vec::new();
    for mut r in regions {
        if degenerate(&r.outer)? {
            continue;
        }
        let mut holes = Vec::new();
        for h in r.holes {
            if !degenerate(&h)? {
                holes.push(h);
            }
        }
        r.holes = holes;
        out.push(r);
    }
    Ok(out)
}
/// Copy profile regions while closing only the existing profile endpoint policy.
pub fn seal_regions(regions: &[Region2]) -> Vec<Region2> {
    let seal = |lp: &Loop2| Loop2 {
        segs: super::profile::close_gaps(lp.segs.clone()),
    };
    regions
        .iter()
        .map(|r| Region2 {
            outer: seal(&r.outer),
            holes: r.holes.iter().map(seal).collect(),
        })
        .collect()
}
/// Order precomputed axial tools by their machining depth.
pub fn order_tools_deepest_first(tools: &mut [PrismTool]) {
    tools.sort_by(|a, b| (b.end - b.start).total_cmp(&(a.end - a.start)));
}
/// Form a stock extrusion request from a planned setup and outline.
pub fn stock_tool(setup: &MilledSetup, outline: &[Region2]) -> PrismTool {
    PrismTool {
        frame: setup.frame.clone(),
        regions: seal_regions(outline),
        start: setup.lo,
        end: setup.hi,
    }
}
/// Exact conservative stock cutter bounds: arc supports use their complete circle enclosure.
pub fn outside_stock_tool(setup: &MilledSetup, regions: &[Region2]) -> PrismTool {
    PrismTool {
        frame: setup.frame.clone(),
        regions: seal_regions(regions),
        start: setup.lo - setup.margin,
        end: setup.hi + setup.margin,
    }
}
/// Compute a containing planar stock rectangle for the supplied regions.
pub fn stock_rectangle(outline: &[Region2]) -> Result<Region2> {
    let (lo, hi) =
        material_bounds(outline).ok_or_else(|| invalid("unsupported or empty outline bounds"))?;
    Ok(Region2 {
        outer: super::profile::polygon(&[lo, Vec2::new(hi.x, lo.y), hi, Vec2::new(lo.x, hi.y)]),
        holes: Vec::new(),
    })
}
/// Requested exact planar intersections for the original topology/nesting obligations.
#[derive(Clone, Debug)]
pub struct NestingIntersection {
    /// First planar intersection operand.
    pub a: Region2,
    /// Second planar intersection operand.
    pub b: Region2,
    expected: f64,
    expected_bound: f64,
    /// The enforced count or work limit.
    limit: f64,
    /// Tolerance for this exact planar boolean request.
    pub boolean_tolerance: f64,
}
/// Enumerate every exact planar intersection needed to verify loop nesting.
pub fn nesting_intersections(obligation: &ProfileNesting) -> Result<Vec<NestingIntersection>> {
    if obligation.raw.len() > 50 {
        return Err(MeshError::BudgetExceeded {
            stage: "profile nesting loops",
            limit: 50,
        });
    }
    if obligation.raw.len() != obligation.fitted.len() {
        return Err(invalid("profile nesting correspondence is incomplete"));
    }
    let mut requests = Vec::new();
    let mut work = 0usize;
    let hold = |a: &Loop2, b: &Loop2| -> Result<bool> {
        let p = b
            .segs
            .first()
            .ok_or_else(|| invalid("empty nesting loop"))?
            .start();
        a.holds(p).ok_or(MeshError::Undecided {
            stage: "loop containment",
            work: a.segs.len(),
        })
    };
    for (i, a) in obligation.raw.iter().enumerate() {
        for (j, b) in obligation.raw.iter().enumerate().skip(i + 1) {
            work = work.saturating_add(a.segs.len().saturating_mul(b.segs.len()));
            if work > 16_000_000 {
                return Err(MeshError::BudgetExceeded {
                    stage: "profile nesting work",
                    limit: 16_000_000,
                });
            }
            let (ab, ba) = (hold(a, b)?, hold(b, a)?);
            if ab && ba {
                return Err(invalid("overlapping boundary loops"));
            }
            let fa = obligation
                .fitted
                .get(i)
                .ok_or_else(|| invalid("missing fitted loop"))?;
            let fb = obligation
                .fitted
                .get(j)
                .ok_or_else(|| invalid("missing fitted loop"))?;
            for (a, b) in [(a, b), (fa, fb)] {
                let expected = if ab {
                    b.signed_area()?
                } else if ba {
                    a.signed_area()?
                } else {
                    crate::prism::profile::Area {
                        value: 0.,
                        bound: 0.,
                    }
                };
                requests.push(NestingIntersection {
                    a: Region2 {
                        outer: ccw(a)?,
                        holes: Vec::new(),
                    },
                    b: Region2 {
                        outer: ccw(b)?,
                        holes: Vec::new(),
                    },
                    expected: expected.value.abs(),
                    expected_bound: expected.bound,
                    limit: obligation.epsilon * obligation.size.max(1.) * 10.,
                    boolean_tolerance: obligation.epsilon.clamp(1e-9, 1.),
                });
            }
        }
    }
    Ok(requests)
}
/// Verify one planar intersection against its bounded nesting expectation.
pub fn check_nesting_intersection(
    request: &NestingIntersection,
    overlap: &[Region2],
) -> Result<()> {
    let (area, bound) = area_sum(overlap)?;
    let deviation = (area - request.expected).abs();
    if deviation + bound + request.expected_bound <= request.limit {
        return Ok(());
    }
    if deviation - bound - request.expected_bound > request.limit {
        return Err(invalid("conversion would cross or merge boundary loops"));
    }
    Err(MeshError::Undecided {
        stage: "profile nesting intersection",
        work: overlap.len(),
    })
}

/// Standalone single-job convenience; multi-stage callers share one `MeshWork`.
pub fn section_outline(
    k: &crate::Kernel,
    input: &MeshInput,
    frame: &Frame,
    tolerance: f64,
) -> Result<FittedShadowRuns> {
    let work_budget = super::work::MeshWork::new();
    section_outline_with_work(k, &work_budget, input, frame, tolerance)
}

/// Fit a closed source section at the explicit plane using the same complete-workflow budget.
pub fn section_outline_with_work(
    k: &crate::Kernel,
    work_budget: &super::work::MeshWork,
    input: &MeshInput,
    frame: &Frame,
    tolerance: f64,
) -> Result<FittedShadowRuns> {
    work_budget.check(k)?;
    let answer = (|| {
        super::regions::checked_tolerance(tolerance)?;
        let mesh =
            super::source::weld_with_work(k, work_budget, &SourceMesh::checked(input)?, tolerance)?;
        let mut bounds = Bounds3::new();
        for p in &mesh.positions {
            bounds.add_point(*p);
        }
        let size = bounds.size().len().max(1.);
        let epsilon = (size * 1e-7).min(tolerance * 0.01).max(1e-9);
        let snap = (tolerance * 0.1).max(epsilon * 3.);
        let tris = triangles(&mesh)?;
        let d = frame.normal();
        let ranges: Vec<_> = tris
            .iter()
            .map(|t| {
                let h = heights(&mesh, t, d);
                (h[0].min(h[1]).min(h[2]), h[0].max(h[1]).max(h[2]))
            })
            .collect();
        let height = Vec3::from_array(frame.origin).dot(d);
        let regions = section(
            k,
            &mesh,
            &tris,
            &ranges,
            frame,
            d,
            height,
            epsilon,
            snap * 0.2,
        )?;
        let setup = MilledSetup {
            frame: frame.clone(),
            lo: height,
            hi: height,
            margin: 0.,
            boolean_tolerance: (snap * 0.5).clamp(1e-9, 1.),
            geometry_tolerance: tolerance,
            snap,
            epsilon,
            size,
            slabs: Vec::new(),
        };
        fit_shadow_runs_with_work(
            k,
            work_budget,
            &setup,
            vec![SlabShadow {
                lo: height,
                hi: height,
                regions,
            }],
        )
    })();
    work_budget.check(k)?;
    answer
}

pub use super::budgeted::{
    can_merge_runs_with_work, check_nesting_intersection_with_work, filter_planar_result_with_work,
    filter_pocket_regions_with_work, keep_fresh_tool_with_work, nesting_intersections_with_work,
    order_tools_deepest_first_with_work, outside_stock_tool_with_work, pocket_tool_with_work,
    same_shadow_with_work, seal_regions_with_work, shadow_differences_agree_with_work,
    stock_rectangle_with_work, stock_tool_with_work,
};
