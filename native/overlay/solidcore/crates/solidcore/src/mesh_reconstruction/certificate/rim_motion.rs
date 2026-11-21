//! Whole-level-set embedding proof for a polygon-to-rational rim homotopy.
//!
//! Each model edge is a COMPLETE positive-weight rational Bezier curve `Q_i(t)`.
//! Its source is the affine edge `P_i(t)`, with exact joins in each complete loop.
//! We prove H_i(s,t)=(1-s)P_i(t)+s `Q_i(t)` is an embedded, coherently joined
//! closed family for EVERY s in [0,1], with different loops always disjoint:
//! (1) a strictly positive full Bernstein derivative numerator along the source
//! edge makes each `H_i(s`,.) injective; (2) nonincident edges' complete swept
//! control hulls are separated; (3) adjacent edges have strict opposite halfplanes
//! relative to their interpolated shared join J(s). Thus no crossing, touching,
//! local reversal, or change of nesting can occur between the endpoint profiles.
//!
//! This is a sufficient model-motion certificate, NOT an actual B-rep adoption
//! token. Consumers must bind the exact model controls to complete actual curve
//! roots and unchanged native balls/tubes/bands. Approximate endpoint overlap is
//! NEVER a join. A finite distance bound or two embedded endpoint loops alone
//! would not prove this theorem. Full filled-cap and final-material binding are
//! still separate. No samples or floating zero tolerances enter this proof.
//!
//! Deviations: none. No recursion. Degree <=8, <=8192 edges and shared `MeshWork`.
use super::super::work::MeshWork;
use super::exact_geometry as x;
use crate::blend::fillet_section::interval::Ivl;
use crate::{Kernel, Result};

type H = [x::E; 3]; // exact (X,Y,W), with W strictly positive
#[derive(Clone)]
pub(crate) struct RationalControl {
    pub(crate) xy: [x::E; 2],
    pub(crate) weight: x::E,
}
pub(crate) struct MotionEdge {
    pub(crate) source: [[x::E; 2]; 2],
    pub(crate) target: Vec<RationalControl>,
}
pub(crate) struct RimMotion<'a> {
    /// Immutable model/source identity. No cloned or changed controls can use it.
    loops: &'a [Vec<MotionEdge>],
    distance_upper: f64,
}
impl<'a> RimMotion<'a> {
    pub(crate) fn loops(&self) -> &'a [Vec<MotionEdge>] {
        self.loops
    }
    /// Full same-parameter displacement in these exact 2D coordinates. A
    /// non-isometric 2D-to-world lift must charge its own proved metric factor.
    pub(crate) fn distance_upper(&self) -> f64 {
        self.distance_upper
    }
}
pub(crate) enum RimMotionVerdict<'a> {
    Proven(RimMotion<'a>),
    Undecided(&'static str),
}
fn raw(p: &[x::E; 2]) -> Option<H> {
    let [a, b] = p;
    if x::sign(a).is_none() || x::sign(b).is_none() {
        return None;
    }
    Some([a.clone(), b.clone(), x::scalar(1.)?])
}
fn control(p: &RationalControl) -> H {
    let [a, b] = &p.xy;
    [a.clone(), b.clone(), p.weight.clone()]
}
fn valid(p: &H) -> bool {
    let [_, _, w] = p;
    p.iter().all(|e| x::sign(e).is_some()) && x::sign(w) == Some(1)
}
fn eq(a: &H, b: &H) -> bool {
    let [ax, ay, aw] = a;
    let [bx, by, bw] = b;
    [(ax, bx), (ay, by)].into_iter().all(|(a, b)| {
        x::mul(a, bw)
            .and_then(|v| x::sub(&v, &x::mul(b, aw)?))
            .is_some_and(|v| x::zero(&v))
    })
}
/// A projective difference, multiplied by the positive product of weights.
fn difference(a: &H, b: &H) -> Option<[x::E; 2]> {
    let [ax, ay, aw] = a;
    let [bx, by, bw] = b;
    Some([
        x::sub(&x::mul(ax, bw)?, &x::mul(bx, aw)?)?,
        x::sub(&x::mul(ay, bw)?, &x::mul(by, aw)?)?,
    ])
}
fn dot(a: &[x::E; 2], b: &[x::E; 2]) -> Option<x::E> {
    let [ax, ay] = a;
    let [bx, by] = b;
    x::add(&x::mul(ax, bx)?, &x::mul(ay, by)?)
}
fn neg(a: &[x::E; 2]) -> Option<[x::E; 2]> {
    let [a, b] = a;
    Some([x::scale(a, -1.)?, x::scale(b, -1.)?])
}
fn perp(a: &[x::E; 2]) -> Option<[x::E; 2]> {
    let [a, b] = a;
    Some([x::scale(b, -1.)?, a.clone()])
}
fn zero(a: &[x::E; 2]) -> bool {
    a.iter().all(x::zero)
}
/// All coefficients of d/dt dot(D,Q(t)) have strictly positive numerators.
/// For each Bernstein product coefficient the omitted binomial denominator is
/// positive and common to both terms, so its exact sign needs NO division.
fn forward(k: &Kernel, work: &MeshWork, edge: &MotionEdge) -> Result<bool> {
    let [Some(a), Some(b)] = edge.source.each_ref().map(raw) else {
        return Ok(false);
    };
    let Some(d) = difference(&b, &a) else {
        return Ok(false);
    };
    if zero(&d) || !(2..=9).contains(&edge.target.len()) {
        return Ok(false);
    }
    let n = edge.target.len().saturating_sub(1);
    let mut h = Vec::new();
    for c in &edge.target {
        work.spend_core(k, 1)?;
        let c = control(c);
        if !valid(&c) {
            return Ok(false);
        }
        let [cx, cy, cw] = c;
        let Some(v) = dot(&d, &[cx, cy]) else {
            return Ok(false);
        };
        work.reserve_cells_core(k, 1)?;
        h.push((v, cw));
    }
    // Equal positive weights make the rational denominator constant. Cancel
    // that SAME positive factor from every existing elevated Bernstein
    // coefficient before multiplying its small expansion tails. Equality is
    // coefficient-wise, not a rounded value or a tolerance; variable weights
    // retain the original quotient-derivative construction below.
    let Some((_, weight)) = h.first() else {
        return Ok(false);
    };
    let mut common_weight = true;
    for (_, other) in &h {
        work.spend_core(k, weight.len())?;
        work.spend_core(k, other.len())?;
        common_weight &= weight == other;
    }
    let Some(degree) = n.checked_mul(2).and_then(|v| v.checked_sub(1)) else {
        return Ok(false);
    };
    for out in 0..=degree {
        let mut sum = vec![0.];
        for i in 0..n {
            let Some(j) = out.checked_sub(i).filter(|&j| j <= n) else {
                continue;
            };
            work.spend_core(k, 1)?;
            let (Some((hi, wi)), Some((hz, wz)), Some((hj, wj))) =
                (h.get(i), h.get(i + 1), h.get(j))
            else {
                return Ok(false);
            };
            // Native Pascal table coefficients are exact integers; the proven
            // degree <=8 puts these rows far inside its supported 18x18 domain.
            // A native table error is an internal error, never ordinary refusal.
            let coefficient =
                crate::nurbs::bezier::binomial(n - 1, i)? * crate::nurbs::bezier::binomial(n, j)?;
            let Some(v) = x::sub(hz, hi)
                .and_then(|dh| {
                    if common_weight {
                        Some(dh)
                    } else {
                        x::mul(&dh, wj).and_then(|a| x::sub(&a, &x::mul(hj, &x::sub(wz, wi)?)?))
                    }
                })
                .and_then(|a| x::scale(&a, coefficient))
                .and_then(|a| x::add(&sum, &a))
            else {
                return Ok(false);
            };
            sum = v;
        }
        if x::sign(&sum) != Some(1) {
            return Ok(false);
        }
    }
    Ok(true)
}
fn enclosure(e: &x::E) -> Option<Ivl> {
    let mut v = Ivl::from(0.);
    for &term in e {
        v = v.add_ulp(Ivl::from(term));
    }
    v.is_finite().then_some(v)
}
/// Bound the ENTIRE numerator Q(t)-P(t) in degree n+1 Bernstein form.
/// Product/elevation integer coefficients are reused from the native Pascal
/// table; exact expansion expressions are interval-enclosed only at the final
/// coefficient bound. This is not a corner residual or a sampled curve fit.
fn displacement(k: &Kernel, work: &MeshWork, edge: &MotionEdge) -> Result<Option<f64>> {
    let [a, b] = &edge.source;
    let Some(n) = edge
        .target
        .len()
        .checked_sub(1)
        .filter(|&n| (1..=8).contains(&n))
    else {
        return Ok(None);
    };
    let mut lower = f64::INFINITY;
    for control in &edge.target {
        work.spend_core(k, 1)?;
        let Some(w) = enclosure(&control.weight) else {
            return Ok(None);
        };
        if !w.is_positive() {
            return Ok(None);
        }
        lower = lower.min(w.lo);
    }
    let mut worst = 0.0_f64;
    for out in 0..=n + 1 {
        let mut numerator = [vec![0.], vec![0.]];
        for (source_index, source) in [a, b].into_iter().enumerate() {
            let Some(i) = out.checked_sub(source_index).filter(|&i| i <= n) else {
                continue;
            };
            let Some(control) = edge.target.get(i) else {
                return Ok(None);
            };
            let coefficient = crate::nurbs::bezier::binomial(n, i)?;
            for ((sum, h), p) in numerator.iter_mut().zip(&control.xy).zip(source) {
                work.spend_core(k, 1)?;
                let Some(value) = x::mul(&control.weight, p)
                    .and_then(|p| x::sub(h, &p))
                    .and_then(|v| x::scale(&v, coefficient))
                    .and_then(|v| x::add(sum, &v))
                else {
                    return Ok(None);
                };
                *sum = value;
            }
        }
        let scale = Ivl::from(crate::nurbs::bezier::binomial(n + 1, out)?);
        let [Some(a), Some(b)] = numerator.each_ref().map(enclosure) else {
            return Ok(None);
        };
        let [a, b] = [a / scale, b / scale].map(|v| Ivl::from(v.lo.abs().max(v.hi.abs())));
        let bound = ((a * a + b * b).sqrt() / Ivl::from(lower)).hi;
        if !bound.is_finite() || bound < 0. {
            return Ok(None);
        }
        worst = worst.max(bound);
    }
    Ok(Some(worst))
}
fn hull(k: &Kernel, work: &MeshWork, edge: &MotionEdge) -> Result<Option<Vec<H>>> {
    let [Some(a), Some(b)] = edge.source.each_ref().map(raw) else {
        return Ok(None);
    };
    work.reserve_cells_core(k, 2)?;
    let mut out = vec![a, b];
    for c in &edge.target {
        work.spend_core(k, 1)?;
        let c = control(c);
        if !valid(&c) {
            return Ok(None);
        }
        work.reserve_cells_core(k, 1)?;
        out.push(c);
    }
    Ok(Some(out))
}
// Every endpoint and EVERY positive homogeneous target control participates.
// Positive rational weights place the complete target curve in this convex hull;
// adding the source endpoints contains every linear homotopy level as well.
// This is a whole-domain enclosure, never an endpoint sample or fitted epsilon.
struct SweptHull {
    controls: Vec<H>,
    bounds: Option<[Ivl; 2]>,
}
fn hull_enclosure(k: &Kernel, work: &MeshWork, points: &[H]) -> Result<Option<[Ivl; 2]>> {
    work.reserve_cells_core(k, 5)?;
    let mut result: Option<[Ivl; 2]> = None;
    for point in points {
        work.spend_core(k, 32)?;
        for coordinate in point {
            work.spend_core(k, coordinate.len())?;
        }
        let [x, y, w] = point;
        let Some(w) = enclosure(w).filter(|w| w.is_positive()) else {
            return Ok(None);
        };
        let (Some(x), Some(y)) = (enclosure(x), enclosure(y)) else {
            return Ok(None);
        };
        let [x, y] = [x / w, y / w];
        if !x.is_finite() || !y.is_finite() {
            return Ok(None);
        }
        let union = |a: Ivl, b: Ivl| Ivl::new(a.lo.min(b.lo), a.hi.max(b.hi));
        result = Some(match result {
            Some([a, b]) => [union(a, x), union(b, y)],
            None => [x, y],
        });
    }
    Ok(result)
}
fn enclosures_disjoint(a: Option<[Ivl; 2]>, b: Option<[Ivl; 2]>) -> bool {
    match (a, b) {
        (Some(a), Some(b)) => a.iter().zip(&b).any(|(a, b)| a.hi < b.lo || b.hi < a.lo),
        _ => false,
    }
}

/// Whole convex hull intervals along one exact axis are STRICTLY disjoint.
fn axis_separates(a: &[H], b: &[H], axis: &[x::E; 2]) -> Option<bool> {
    if zero(axis) {
        return Some(false);
    }
    let projected = |p: &H| {
        let [a, b, w] = p;
        Some((dot(axis, &[a.clone(), b.clone()])?, w.clone()))
    };
    let range = |points: &[H]| -> Option<[(x::E, x::E); 2]> {
        let first = projected(points.first()?)?;
        let mut lo = first.clone();
        let mut hi = first;
        for p in points.iter().skip(1) {
            let v = projected(p)?;
            let compare = |a: &(x::E, x::E), b: &(x::E, x::E)| {
                x::sub(&x::mul(&a.0, &b.1)?, &x::mul(&b.0, &a.1)?).and_then(|v| x::sign(&v))
            };
            if compare(&v, &lo)? < 0 {
                lo = v.clone();
            }
            if compare(&v, &hi)? > 0 {
                hi = v;
            }
        }
        Some([lo, hi])
    };
    let [alo, ahi] = range(a)?;
    let [blo, bhi] = range(b)?;
    let lt = |a: &(x::E, x::E), b: &(x::E, x::E)| {
        x::sub(&x::mul(&a.0, &b.1)?, &x::mul(&b.0, &a.1)?)
            .and_then(|v| x::sign(&v))
            .map(|v| v < 0)
    };
    Some(lt(&ahi, &blo)? || lt(&bhi, &alo)?)
}
fn separated(k: &Kernel, work: &MeshWork, a: &[H], b: &[H]) -> Result<bool> {
    // SAT candidates from every pair in each hull. In addition to polygon-edge
    // normals, use pair directions to cover collinear/point hull degeneracies.
    for points in [a, b] {
        for (i, p) in points.iter().enumerate() {
            for q in points.iter().skip(i + 1) {
                work.spend_core(k, 1)?;
                let Some(d) = difference(q, p) else {
                    return Ok(false);
                };
                let Some(n) = perp(&d) else { return Ok(false) };
                for axis in [&d, &n] {
                    work.spend_core(k, a.len().saturating_add(b.len()))?;
                    if axis_separates(a, b, axis) == Some(true) {
                        return Ok(true);
                    }
                }
            }
        }
    }
    Ok(false)
}
fn adjacent(k: &Kernel, work: &MeshWork, a: &MotionEdge, b: &MotionEdge) -> Result<bool> {
    let (Some(ap), Some(bp)) = (
        a.source.last().and_then(raw),
        b.source.first().and_then(raw),
    ) else {
        return Ok(false);
    };
    let (Some(aq), Some(bq)) = (a.target.last().map(control), b.target.first().map(control)) else {
        return Ok(false);
    };
    if !eq(&ap, &bp) || !eq(&aq, &bq) {
        return Ok(false);
    }
    let mut rays = Vec::new();
    for (edge, sp, tp, reverse) in [(a, &ap, &aq, false), (b, &bp, &bq, true)] {
        let Some(h) = hull(k, work, edge)? else {
            return Ok(false);
        };
        for (i, p) in h.iter().enumerate() {
            work.spend_core(k, 1)?;
            let Some(mut r) = difference(p, if i < 2 { sp } else { tp }) else {
                return Ok(false);
            };
            if reverse {
                let Some(v) = neg(&r) else { return Ok(false) };
                r = v;
            }
            if !zero(&r) {
                work.reserve_cells_core(k, 1)?;
                rays.push(r);
            }
        }
    }
    if rays.is_empty() {
        return Ok(false);
    }
    // In two dimensions the feasible strict dual cone is bounded by normals
    // perpendicular to input rays. Sum all exact weak support functionals. If
    // each ray is positive on at least one, the sum is strictly positive on ALL.
    work.reserve_cells_core(k, rays.len())?;
    let mut covered = vec![false; rays.len()];
    for r in &rays {
        work.spend_core(k, 1)?;
        let Some(n) = perp(r) else { return Ok(false) };
        let Some(nn) = neg(&n) else { return Ok(false) };
        for n in [n, nn, r.clone()] {
            work.reserve_cells_core(k, rays.len())?;
            let mut signs = Vec::new();
            for v in &rays {
                work.spend_core(k, 1)?;
                let Some(s) = dot(&n, v).and_then(|v| x::sign(&v)) else {
                    return Ok(false);
                };
                signs.push(s);
            }
            if signs.iter().all(|&s| s >= 0) {
                for (yes, s) in covered.iter_mut().zip(signs) {
                    *yes |= s > 0;
                }
            }
        }
    }
    Ok(covered.iter().all(|v| *v))
}
/// Complete closed model loops. Source and target controls must already use ONE
/// exact common planar coordinate system. No incomplete root partition can be
/// certified by passing only a subset here: actual membership/cover is separate.
pub(crate) fn prove_rim_motion_with_work<'a>(
    k: &Kernel,
    work: &MeshWork,
    loops: &'a [Vec<MotionEdge>],
) -> Result<RimMotionVerdict<'a>> {
    macro_rules! refuse {
        ($reason:expr) => {
            return Ok(RimMotionVerdict::Undecided($reason))
        };
    }
    work.spend_core(k, 0)?;
    let Some(count) = loops.iter().try_fold(0usize, |a, b| a.checked_add(b.len())) else {
        refuse!("model rim size overflow")
    };
    if loops.is_empty() || count > 8192 || loops.iter().any(|v| v.len() < 3) {
        refuse!("model loops need three through 8192 edges")
    }
    let mut hulls = Vec::new();
    let mut distance_upper = 0.0_f64;
    for edges in loops {
        let mut row = Vec::new();
        for (i, e) in edges.iter().enumerate() {
            work.spend_core(k, 1)?;
            if !forward(k, work, e)? {
                refuse!("a full rational edge cannot prove a forward graph")
            }
            let Some(bound) = displacement(k, work, e)? else {
                refuse!("a full rational displacement has no finite enclosure")
            };
            distance_upper = distance_upper.max(bound);
            let Some(next) = edges.get(i + 1).or_else(|| edges.first()) else {
                refuse!("model loop next edge missing")
            };
            if !adjacent(k, work, e, next)? {
                refuse!(
                    "whole adjacent swept branches lack exact coherent joins or separated sectors"
                )
            }
            let Some(h) = hull(k, work, e)? else {
                refuse!("a complete model control hull is invalid")
            };
            let bounds = hull_enclosure(k, work, &h)?;
            work.reserve_cells_core(k, 1)?;
            row.push(SweptHull {
                controls: h,
                bounds,
            });
        }
        work.reserve_cells_core(k, 1)?;
        hulls.push(row);
    }
    for (li, edges) in hulls.iter().enumerate() {
        for (ei, a) in edges.iter().enumerate() {
            for (lj, other) in hulls.iter().enumerate().skip(li) {
                for (ej, b) in other.iter().enumerate() {
                    if li == lj && (ej <= ei || ej == ei + 1 || (ei == 0 && ej + 1 == edges.len()))
                    {
                        continue;
                    }
                    work.spend_core(k, 5)?;
                    // A strict outward box separation already proves the same
                    // complete swept-hull predicate. Overlap/uncertainty retains
                    // the existing exact SAT path and every original refusal.
                    if !enclosures_disjoint(a.bounds, b.bounds)
                        && !separated(k, work, &a.controls, &b.controls)?
                    {
                        refuse!("nonincident complete swept control hulls are not proved disjoint")
                    }
                }
            }
        }
    }
    work.spend_core(k, 0)?;
    Ok(RimMotionVerdict::Proven(RimMotion {
        loops,
        distance_upper,
    }))
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::KernelOptions;
    /// Q(t)=(0*(1-t)+W*t)/W=t for the SAME positive W=1+2^-500.
    /// Its derivative is identically one; multiplying the two tiny expansion
    /// tails is unnecessary and outside the existing exact-product range.
    #[test]
    fn constant_positive_weight_preserves_a_full_linear_forward_graph() {
        let k = Kernel::new(&KernelOptions::default());
        let tiny = 2.0_f64.powi(-500);
        assert!(crate::geom::expansion::product(tiny, tiny).is_none());
        let weight = x::add(&x::scalar(1.).unwrap(), &x::scalar(tiny).unwrap()).unwrap();
        let mut edge = MotionEdge {
            source: [
                [x::scalar(0.).unwrap(), x::scalar(0.).unwrap()],
                [x::scalar(1.).unwrap(), x::scalar(0.).unwrap()],
            ],
            target: vec![
                RationalControl {
                    xy: [x::scalar(0.).unwrap(), x::scalar(0.).unwrap()],
                    weight: weight.clone(),
                },
                RationalControl {
                    xy: [weight.clone(), x::scalar(0.).unwrap()],
                    weight,
                },
            ],
        };
        assert!(forward(&k, &MeshWork::new(), &edge).unwrap());
        edge.target.reverse();
        assert!(!forward(&k, &MeshWork::new(), &edge).unwrap());
    }
    /// The cubic differences [1,-0.1,1] have a positive degree-elevated
    /// derivative certificate. Common-weight cancellation must retain the SAME
    /// elevated Bernstein test, not replace it by a stricter low-degree test.
    #[test]
    fn common_weight_curve_keeps_the_degree_elevated_forward_certificate() {
        let k = Kernel::new(&KernelOptions::default());
        let edge = MotionEdge {
            source: [
                [x::scalar(0.).unwrap(), x::scalar(0.).unwrap()],
                [x::scalar(1.9).unwrap(), x::scalar(0.).unwrap()],
            ],
            target: vec![c(0., 0., 1.), c(1., 0., 1.), c(0.9, 0., 1.), c(1.9, 0., 1.)],
        };
        assert!(forward(&k, &MeshWork::new(), &edge).unwrap());
    }

    fn c(x: f64, y: f64, w: f64) -> RationalControl {
        RationalControl {
            xy: [x::scalar(x * w).unwrap(), x::scalar(y * w).unwrap()],
            weight: x::scalar(w).unwrap(),
        }
    }
    fn exact(p: [f64; 2]) -> [x::E; 2] {
        p.map(|v| x::scalar(v).unwrap())
    }
    fn line(a: [f64; 2], b: [f64; 2], shift: [f64; 2]) -> MotionEdge {
        MotionEdge {
            source: [exact(a), exact(b)],
            target: vec![
                c(a[0] + shift[0], a[1] + shift[1], 1.),
                c(b[0] + shift[0], b[1] + shift[1], 1.),
            ],
        }
    }
    fn square(center: f64, shift: f64) -> Vec<MotionEdge> {
        let p = [
            [center - 1., -1.],
            [center + 1., -1.],
            [center + 1., 1.],
            [center - 1., 1.],
        ];
        (0..4)
            .map(|i| line(p[i], p[(i + 1) % 4], [shift, 0.125]))
            .collect()
    }
    #[test]
    fn cached_whole_hull_bounds_include_interior_controls_and_refuse_touching() {
        let k = Kernel::default();
        let work = MeshWork::new();
        let bowed = MotionEdge {
            source: [exact([0., 0.]), exact([1., 0.])],
            target: vec![c(0., 0., 1.), c(0.5, 10., 0.5), c(1., 0., 1.)],
        };
        let a = hull(&k, &work, &bowed).unwrap().unwrap();
        let inside = hull(&k, &work, &line([0.4, 5.], [0.6, 5.], [0., 0.]))
            .unwrap()
            .unwrap();
        let far = hull(&k, &work, &line([0.4, 20.], [0.6, 20.], [0., 0.]))
            .unwrap()
            .unwrap();
        let ab = hull_enclosure(&k, &work, &a).unwrap();
        let ib = hull_enclosure(&k, &work, &inside).unwrap();
        let fb = hull_enclosure(&k, &work, &far).unwrap();
        assert!(
            !enclosures_disjoint(ab, ib),
            "endpoints alone would falsely separate"
        );
        assert!(!separated(&k, &work, &a, &inside).unwrap());
        assert!(enclosures_disjoint(ab, fb));
        assert!(separated(&k, &work, &a, &far).unwrap());
        let first = Some([Ivl::new(0., 1.), Ivl::new(0., 1.)]);
        let touch = Some([Ivl::new(1., 2.), Ivl::new(0., 1.)]);
        assert!(!enclosures_disjoint(first, touch));
        assert!(!enclosures_disjoint(first, None));
        let invalid = [[vec![1.], vec![2.], vec![-1.]]];
        assert!(hull_enclosure(&k, &work, &invalid).unwrap().is_none());
    }

    #[test]
    fn translated_closed_joins_are_proved_for_every_homotopy_level() {
        let k = Kernel::new(&KernelOptions::default());
        let w = MeshWork::new();
        let loops = vec![square(0., 0.25)];
        match prove_rim_motion_with_work(&k, &w, &loops).unwrap() {
            RimMotionVerdict::Proven(p) => {
                assert!(core::ptr::eq(p.loops(), loops.as_slice()));
                assert!(p.distance_upper() >= (0.25_f64 * 0.25 + 0.125 * 0.125).sqrt());
                assert!(p.distance_upper() < 0.28);
            }
            RimMotionVerdict::Undecided(e) => panic!("{e}"),
        }
    }
    #[test]
    fn complete_positive_rational_quarters_move_a_polygon_to_a_curved_loop() {
        let k = Kernel::new(&KernelOptions::default());
        let w = MeshWork::new();
        let d = core::f64::consts::FRAC_1_SQRT_2;
        let p = [[1., 0.], [0., 1.], [-1., 0.], [0., -1.]];
        let m = [[1., 1.], [-1., 1.], [-1., -1.], [1., -1.]];
        let edges = (0..4)
            .map(|i| {
                let a = p[i];
                let b = p[(i + 1) % 4];
                MotionEdge {
                    source: [exact(a), exact(b)],
                    target: vec![c(a[0], a[1], 1.), c(m[i][0], m[i][1], d), c(b[0], b[1], 1.)],
                }
            })
            .collect();
        let loops = vec![edges];
        match prove_rim_motion_with_work(&k, &w, &loops).unwrap() {
            RimMotionVerdict::Proven(proof) => {
                assert!(proof.distance_upper() > 0.29);
                assert!(proof.distance_upper() < 0.6);
            }
            RimMotionVerdict::Undecided(e) => panic!("{e}"),
        }
    }
    #[test]
    fn disjoint_end_profiles_do_not_hide_crossing_intermediate_loops() {
        let k = Kernel::new(&KernelOptions::default());
        let w = MeshWork::new();
        let loops = vec![square(-3., 6.), square(3., -6.)];
        assert!(matches!(
            prove_rim_motion_with_work(&k, &w, &loops).unwrap(),
            RimMotionVerdict::Undecided(_)
        ));
    }
    #[test]
    fn exact_nonrepresentable_source_split_remains_a_coherent_source_chain() {
        let k = Kernel::new(&KernelOptions::default());
        let work = MeshWork::new();
        let mut edges = square(0., 0.25);
        let source_join = [
            x::add(&x::scalar(0.5).unwrap(), &x::scalar(1e-20).unwrap()).unwrap(),
            x::scalar(-1.).unwrap(),
        ];
        // Expansion coordinates retain the exact affine source split instead
        // of silently rounding it to one f64 before the topology proof.
        let model_join = RationalControl {
            xy: [
                x::add(&source_join[0], &x::scalar(0.25).unwrap()).unwrap(),
                x::scalar(-0.875).unwrap(),
            ],
            weight: x::scalar(1.).unwrap(),
        };
        let a = MotionEdge {
            source: [exact([-1., -1.]), source_join.clone()],
            target: vec![c(-0.75, -0.875, 1.), model_join.clone()],
        };
        let b = MotionEdge {
            source: [source_join, exact([1., -1.])],
            target: vec![model_join, c(1.25, -0.875, 1.)],
        };
        edges.remove(0);
        edges.insert(0, b);
        edges.insert(0, a);
        assert!(matches!(
            prove_rim_motion_with_work(&k, &work, &[edges]).unwrap(),
            RimMotionVerdict::Proven(_)
        ));
    }
    #[test]
    fn approximate_join_overlap_is_not_exact_coherence() {
        let k = Kernel::new(&KernelOptions::default());
        let w = MeshWork::new();
        let mut edges = square(0., 0.);
        edges[1].target[0].xy[0] = x::scalar(1. + 1e-12).unwrap();
        assert!(matches!(
            prove_rim_motion_with_work(&k, &w, &[edges]).unwrap(),
            RimMotionVerdict::Undecided(_)
        ));
    }
}
