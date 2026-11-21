//! Exact sewn rational-model endpoints with a whole actual-curve error bound.
//!
//! A restricted actual root Piece already encloses ALL homogeneous coefficient
//! error from its complete parameter restriction. Choose its stored coefficients
//! as the model's interior controls, retain their relative weights, and replace
//! only endpoint projective positions by two chosen exact rational joins. The
//! result is ONE exact positive-weight rational model curve, not overlapping
//! endpoint intervals. A common positive homogeneous scale avoids every division:
//! endpoint0 = J0.xyz * oldW0 * J1.w, W0 = oldW0 * J0.w * J1.w;
//! endpoint1 is analogous. Interior homogeneous controls multiply J0.w*J1.w.
//! When BOTH join weights exactly equal the projected original endpoint weights,
//! every old control has that SAME positive common factor. The construction then
//! omits the factor before forming it: interiors keep their projected controls,
//! endpoints keep the SAME joins. This preserves the complete parametric curve,
//! including arbitrary internal rational weights and unequal endpoint weights.
//!
//! Exact model coefficients are enclosed for native Bernstein paired-curve
//! algebra; the whole normalized-parameter bound includes actual restriction,
//! rounded model enclosure, and endpoint sewing. No sampled residual certifies
//! the fit. A returned span alone proves NO native membership, complete partition,
//! actual vertex/tube allowance, planar model, embedding, or final material.
//!
//! Deviations: none. No recursion; degree1..8 and shared `MeshWork`.
use super::super::work::MeshWork;
use super::exact_geometry as x;
use super::hulls::paired_curve_upper;
use crate::blend::fillet_section::interval::Ivl;
use crate::offset::construction::bernstein::Bernstein2;
use crate::query::distance_bound::Piece;
use crate::{Kernel, Result, SolidError};

pub(crate) struct ProjectivePoint {
    pub(crate) xyz: x::P,
    pub(crate) w: x::E,
}
pub(crate) struct SewnCurve<'a> {
    actual: &'a Piece,
    controls: Vec<ProjectivePoint>,
    enclosure: Box<Piece>,
    distance_upper: f64,
}
impl<'a> SewnCurve<'a> {
    pub(crate) fn actual(&self) -> &'a Piece {
        self.actual
    }
    pub(crate) fn controls(&self) -> &[ProjectivePoint] {
        &self.controls
    }
    pub(crate) fn enclosure(&self) -> &Piece {
        &self.enclosure
    }
    pub(crate) fn distance_upper(&self) -> f64 {
        self.distance_upper
    }
}
pub(crate) enum SewnCurveVerdict<'a> {
    Proven(SewnCurve<'a>),
    Undecided(&'static str),
}
use super::exact_geometry::interval;
fn approximate(e: &x::E) -> Option<(f64, f64)> {
    let v = interval(e)?;
    let center = 0.5 * v.lo + 0.5 * v.hi;
    if !center.is_finite() {
        return None;
    }
    let d = v - Ivl::from(center);
    let error = d.lo.abs().max(d.hi.abs());
    (error.is_finite()).then_some((center, error))
}
fn scaled(p: &ProjectivePoint, factor: &x::E) -> Option<ProjectivePoint> {
    let [a, b, c] = &p.xyz;
    Some(ProjectivePoint {
        xyz: [x::mul(a, factor)?, x::mul(b, factor)?, x::mul(c, factor)?],
        w: x::mul(&p.w, factor)?,
    })
}
const OP: &str = "mesh_reconstruction::certificate::sewn_curve";
fn count_overflow() -> SolidError {
    SolidError::Unsupported {
        operation: OP,
        reason: "sewn model payload count overflow",
    }
}
/// Guard initialized logical coefficient/vector slots, never byte estimates.
/// Native grow uses six TwoSum operations plus bounded loop/update/finite scans;
/// sixteen work units per written coefficient/header covers these expressions.
/// Existing calls/counters below are retained; this is an additional ledger.
fn charge(k: &Kernel, work: &MeshWork, slots: usize) -> Result<()> {
    work.spend_core(k, 0)?;
    let steps = slots.checked_mul(16).ok_or_else(count_overflow)?;
    work.spend_core(k, steps)?;
    work.reserve_cells_core(k, slots)
}
/// scale(m) writes at most3m²+2m coefficient slots and4m+1 Vec headers.
/// Exact-zero compaction is in-place and can only reduce this upper bound.
fn scale_slots(m: usize) -> Result<usize> {
    m.checked_mul(m)
        .and_then(|v| v.checked_mul(3))
        .and_then(|v| m.checked_mul(6).and_then(|m| v.checked_add(m)))
        .and_then(|v| v.checked_add(1))
        .ok_or_else(count_overflow)
}
/// sub(a[m],b[n]) clones m, then writes m+j for every j=1..n:
/// m+nm+n(n+1)/2 coefficient slots and n+1 Vec headers, all before allocation.
fn subtraction_slots(m: usize, n: usize) -> Result<usize> {
    let triangle = n
        .checked_add(1)
        .and_then(|v| n.checked_mul(v))
        .and_then(|v| v.checked_div(2))
        .ok_or_else(count_overflow)?;
    m.checked_add(m.checked_mul(n).ok_or_else(count_overflow)?)
        .and_then(|v| v.checked_add(triangle))
        .and_then(|v| v.checked_add(n))
        .and_then(|v| v.checked_add(1))
        .ok_or_else(count_overflow)
}
/// Choose a homogeneous construction event BEFORE forming any common product.
/// This is equality of exact projected MODEL endpoint weights, not a label,
/// dehomogenized point coincidence, constant-weight claim or tolerance test.
/// Unproved equality selects the original formula before either model is built.
fn same_endpoint_gauge(
    k: &Kernel,
    work: &MeshWork,
    actual_weight: &Bernstein2,
    degree: usize,
    delta: Option<&x::E>,
    joins: [&ProjectivePoint; 2],
) -> Result<bool> {
    work.spend_core(k, 0)?;
    let [first, last] = joins;
    let mut same = true;
    for (index, join) in [(0, first), (degree, last)] {
        work.spend_core(k, 1)?;
        let Some(&value) = actual_weight.coefficients().get(index) else {
            return Ok(false);
        };
        let endpoint_weight = if let Some(delta) = delta {
            charge(k, work, scale_slots(delta.len())?)?;
            x::scale(delta, value)
        } else {
            charge(k, work, 2)?; // scalar coefficient and its Vec header.
            x::scalar(value)
        };
        let Some(endpoint_weight) = endpoint_weight else {
            return Ok(false);
        };
        charge(
            k,
            work,
            subtraction_slots(join.w.len(), endpoint_weight.len())?,
        )?;
        let equal = x::sub(&join.w, &endpoint_weight).is_some_and(|v| x::zero(&v));
        same &= equal;
    }
    Ok(same)
}
fn clone_join_with_work(
    k: &Kernel,
    work: &MeshWork,
    p: &ProjectivePoint,
) -> Result<ProjectivePoint> {
    work.spend_core(k, 0)?;
    let slots = p
        .xyz
        .iter()
        .chain(core::iter::once(&p.w))
        .try_fold(5usize, |n, e| n.checked_add(e.len()))
        .ok_or_else(count_overflow)?;
    charge(k, work, slots)?; // all coefficients, four Vec headers and the point slot.
    Ok(ProjectivePoint {
        xyz: p.xyz.clone(),
        w: p.w.clone(),
    })
}

/// Joins and actual coefficients must use the SAME translated 3D frame. Chosen
/// join coordinates are steering; the resulting full distance bound must fit the
/// unchanged actual native allowances before any consumer can accept this model.
fn sew_impl<'a>(
    k: &Kernel,
    work: &MeshWork,
    actual: &'a Piece,
    joins: [&ProjectivePoint; 2],
    projection: Option<&PlaneProjection<'_>>,
) -> Result<SewnCurveVerdict<'a>> {
    macro_rules! refuse {
        ($reason:expr) => {
            return Ok(SewnCurveVerdict::Undecided($reason))
        };
    }
    work.spend_core(k, 0)?;
    let [_, _, _, actual_weight] = &actual.h;
    let [join0, join1] = joins;
    let (degree, other) = actual_weight.degrees();
    if !(1..=8).contains(&degree)
        || other != 0
        || !actual.err.is_finite()
        || actual.err < 0.
        || actual.h.iter().any(|h| h.degrees() != (degree, 0))
    {
        refuse!("actual root is not a complete bounded degree1..8 curve")
    }
    for j in joins {
        work.spend_core(k, 1)?;
        if x::sign(&j.w) != Some(1) || j.xyz.iter().any(|v| x::sign(v).is_none()) {
            refuse!("a chosen projective join is not finite positive")
        }
    }
    let delta = if let Some(plane) = projection.as_ref() {
        let Some(delta) = x::dot(plane.normal, plane.direction) else {
            refuse!("source plane projection is outside exact arithmetic")
        };
        if x::sign(&delta) != Some(1) {
            refuse!("source projection direction is not positively transverse")
        }
        for join in joins {
            let Some(on) = x::dot(plane.normal, &join.xyz)
                .and_then(|v| x::sub(&v, &x::mul(plane.low, &join.w)?))
            else {
                refuse!("chosen plane join is outside exact arithmetic")
            };
            if !x::zero(&on) {
                refuse!("a chosen exact join leaves the common source plane")
            }
        }
        Some(delta)
    } else {
        None
    };
    let same_gauge = same_endpoint_gauge(k, work, actual_weight, degree, delta.as_ref(), joins)?;
    let common = if same_gauge {
        // Let C=join0.w*join1.w mathematically. Both weights are positive;
        // C need not be representable to cancel it. If projected endpoint
        // weights equal their joins, the OLD endpoint factors equal C too.
        // Bernstein linearity makes every old homogeneous curve C times this
        // one for ALL parameters. No internal-weight equality is required.
        None
    } else {
        let Some(common) = x::mul(&join0.w, &join1.w) else {
            refuse!("join common scale is outside exact arithmetic")
        };
        Some(common)
    };
    let mut controls = Vec::new();
    for i in 0..=degree {
        work.spend_core(k, 1)?;
        let mut raw = Vec::new();
        for polynomial in &actual.h {
            let Some(&v) = polynomial.coefficients().get(i) else {
                refuse!("actual root coefficient is missing")
            };
            let Some(v) = x::scalar(v) else {
                refuse!("actual root coefficient is nonfinite")
            };
            raw.push(v);
        }
        let [Some(a), Some(b), Some(c), Some(w)] =
            [raw.first(), raw.get(1), raw.get(2), raw.get(3)]
        else {
            refuse!("actual root lacks homogeneous coordinates")
        };
        // Enclosure positivity of the ACTUAL root is checked again by the paired
        // bound. These chosen model center weights are independently positive.
        if x::sign(w) != Some(1) {
            refuse!("chosen model weight is not strictly positive")
        }
        let p = ProjectivePoint {
            xyz: [a.clone(), b.clone(), c.clone()],
            w: w.clone(),
        };
        let p = if let (Some(plane), Some(delta)) = (projection.as_ref(), delta.as_ref()) {
            let Some(residual) =
                x::dot(plane.normal, &p.xyz).and_then(|v| x::sub(&v, &x::mul(plane.low, &p.w)?))
            else {
                refuse!("model projection plane residual is outside exact arithmetic")
            };
            let mut projected = Vec::new();
            for (h, d) in p.xyz.iter().zip(plane.direction) {
                let Some(v) = x::mul(delta, h).and_then(|v| x::sub(&v, &x::mul(d, &residual)?))
                else {
                    refuse!("model projection is outside exact arithmetic")
                };
                projected.push(v);
            }
            let [Some(a), Some(b), Some(c)] =
                [projected.first(), projected.get(1), projected.get(2)]
            else {
                refuse!("projected model lacks coordinates")
            };
            let Some(w) = x::mul(delta, &p.w) else {
                refuse!("projected model weight is outside exact arithmetic")
            };
            ProjectivePoint {
                xyz: [a.clone(), b.clone(), c.clone()],
                w,
            }
        } else {
            p
        };
        let p = if let Some(common) = common.as_ref() {
            // Original construction event, including its exact operation order
            // and all range refusals. No failed-proof retry chooses this path.
            let chosen_weight = p.w.clone();
            let Some(mut p) = scaled(&p, common) else {
                refuse!("model common scaling is outside exact arithmetic")
            };
            if i == 0 || i == degree {
                let (join, other) = if i == 0 {
                    (join0, join1)
                } else {
                    (join1, join0)
                };
                let Some(factor) = x::mul(&chosen_weight, &other.w) else {
                    refuse!("sewn endpoint scale is outside exact arithmetic")
                };
                let Some(endpoint) = scaled(join, &factor) else {
                    refuse!("sewn projective endpoint is outside exact arithmetic")
                };
                p = endpoint;
            }
            p
        } else if i == 0 {
            clone_join_with_work(k, work, join0)?
        } else if i == degree {
            clone_join_with_work(k, work, join1)?
        } else {
            p
        };
        work.reserve_cells_core(k, 1)?;
        controls.push(p);
    }
    let Some(enclosure) = enclose_controls_with_work(k, work, &controls, actual)? else {
        refuse!("exact sewn model has no complete coefficient enclosure")
    };
    let distance_upper = paired_curve_upper(actual, &enclosure, 0., 0.)?;
    work.spend_core(k, 0)?;
    Ok(SewnCurveVerdict::Proven(SewnCurve {
        actual,
        controls,
        enclosure: Box::new(enclosure),
        distance_upper,
    }))
}
/// Enclose an EXACT positive rational model net using native Bernstein data.
/// The returned Piece's `err` includes every exact coefficient's enclosure error;
/// its centers are never silently taken as the exact model. Parameter metadata
/// donor binds coordinates only; callers must still bind model/object semantics.
pub(crate) fn enclose_controls_with_work(
    k: &Kernel,
    work: &MeshWork,
    controls: &[ProjectivePoint],
    actual: &Piece,
) -> Result<Option<Piece>> {
    work.spend_core(k, 0)?;
    let Some(degree) = controls
        .len()
        .checked_sub(1)
        .filter(|&n| (1..=8).contains(&n))
    else {
        return Ok(None);
    };
    if controls.iter().any(|c| x::sign(&c.w) != Some(1)) {
        return Ok(None);
    }
    let mut coefficient_columns: [Vec<f64>; 4] = core::array::from_fn(|_| Vec::new());
    let mut error = 0.0_f64;
    for p in controls {
        work.spend_core(k, 1)?;
        for (i, e) in p.xyz.iter().chain(core::iter::once(&p.w)).enumerate() {
            let Some((center, err)) = approximate(e) else {
                return Ok(None);
            };
            let Some(column) = coefficient_columns.get_mut(i) else {
                return Ok(None);
            };
            work.reserve_cells_core(k, 1)?;
            column.push(center);
            error = error.max(err);
        }
    }
    let [a, b, c, w] = coefficient_columns;
    let enclosure = Piece {
        h: [
            Bernstein2::new(degree, 0, a)?,
            Bernstein2::new(degree, 0, b)?,
            Bernstein2::new(degree, 0, c)?,
            Bernstein2::new(degree, 0, w)?,
        ],
        err: error,
        lower: 0.,
        depth: actual.depth,
        uv: actual.uv,
        parameter_ends: actual.parameter_ends,
    };
    work.spend_core(k, 0)?;
    Ok(Some(enclosure))
}
struct PlaneProjection<'a> {
    normal: &'a x::P,
    low: &'a x::E,
    direction: &'a x::P,
}
/// Sew without moving interior model controls off their chosen actual centers.
pub(crate) fn sew_curve_with_work<'a>(
    k: &Kernel,
    work: &MeshWork,
    actual: &'a Piece,
    joins: [&ProjectivePoint; 2],
) -> Result<SewnCurveVerdict<'a>> {
    sew_impl(k, work, actual, joins, None)
}
/// A complete model in ONE exact plane N dot P=low. Project ALL homogeneous
/// controls along positively transverse D, then sew exact joins in that plane.
/// This is not projection of just the endpoints. Paired-curve full-span bounds
/// include the whole actual-to-projected/sewn model error; unchanged actual
/// allowances must be checked separately. Relative rational weights are retained.
pub(crate) fn project_sew_curve_with_work<'a>(
    k: &Kernel,
    work: &MeshWork,
    actual: &'a Piece,
    joins: [&ProjectivePoint; 2],
    normal: &x::P,
    low: &x::E,
    direction: &x::P,
) -> Result<SewnCurveVerdict<'a>> {
    sew_impl(
        k,
        work,
        actual,
        joins,
        Some(&PlaneProjection {
            normal,
            low,
            direction,
        }),
    )
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::KernelOptions;
    fn point(x: f64, y: f64, w: f64) -> ProjectivePoint {
        ProjectivePoint {
            xyz: x::point([x * w, y * w, 0.]).unwrap(),
            w: x::scalar(w).unwrap(),
        }
    }
    fn line() -> Piece {
        Piece {
            h: [
                Bernstein2::new(1, 0, vec![0., 2.]).unwrap(),
                Bernstein2::new(1, 0, vec![0., 0.]).unwrap(),
                Bernstein2::new(1, 0, vec![0., 0.]).unwrap(),
                Bernstein2::new(1, 0, vec![1., 1.]).unwrap(),
            ],
            err: 0.,
            lower: 0.,
            depth: 0,
            uv: [0., 1., 0., 0.],
            parameter_ends: [Ivl::from(0.), Ivl::from(1.), Ivl::from(0.), Ivl::from(0.)],
        }
    }
    #[test]
    fn complete_sewing_bound_covers_both_moved_endpoints_and_every_interior_point() {
        let k = Kernel::new(&KernelOptions::default());
        let work = MeshWork::new();
        let actual = line();
        let a = point(0., 0.125, 2.);
        let b = point(2., 0.125, 3.);
        let proof = match sew_curve_with_work(&k, &work, &actual, [&a, &b]).unwrap() {
            SewnCurveVerdict::Proven(p) => p,
            SewnCurveVerdict::Undecided(e) => panic!("{e}"),
        };
        assert!(core::ptr::eq(proof.actual(), &raw const actual));
        assert!(proof.distance_upper() >= 0.125 && proof.distance_upper() < 0.126);
        for (c, j) in [(&proof.controls()[0], &a), (&proof.controls()[1], &b)] {
            for (h, jh) in c.xyz.iter().zip(&j.xyz) {
                assert!(x::zero(
                    &x::sub(&x::mul(h, &j.w).unwrap(), &x::mul(jh, &c.w).unwrap()).unwrap()
                ));
            }
        }
        assert!(proof.enclosure().err >= 0.);
    }
    #[test]
    fn complete_projected_model_is_exactly_planar_with_real_interior_error() {
        let k = Kernel::new(&KernelOptions::default());
        let work = MeshWork::new();
        let mut actual = line();
        actual.h[2] = Bernstein2::new(1, 0, vec![0.125, 0.125]).unwrap();
        let a = point(0., 0., 2.);
        let b = point(2., 0., 3.);
        let n = x::point([0., 0., 1.]).unwrap();
        let low = x::scalar(0.).unwrap();
        let d = x::point([0., 0., 5.]).unwrap();
        let proof = match project_sew_curve_with_work(&k, &work, &actual, [&a, &b], &n, &low, &d)
            .unwrap()
        {
            SewnCurveVerdict::Proven(p) => p,
            SewnCurveVerdict::Undecided(e) => panic!("{e}"),
        };
        for control in proof.controls() {
            assert!(x::zero(&x::dot(&n, &control.xyz).unwrap()));
        }
        assert!(proof.distance_upper() >= 0.125 && proof.distance_upper() < 0.126);
    }
    #[test]
    fn negative_join_weights_cannot_create_a_model_certificate() {
        let k = Kernel::new(&KernelOptions::default());
        let work = MeshWork::new();
        let actual = line();
        let a = point(0., 0., -1.);
        let b = point(2., 0., 1.);
        assert!(matches!(
            sew_curve_with_work(&k, &work, &actual, [&a, &b]).unwrap(),
            SewnCurveVerdict::Undecided(_)
        ));
    }

    fn rational_piece() -> Piece {
        Piece {
            h: [
                Bernstein2::new(2, 0, vec![0., 3., 10.]).unwrap(),
                Bernstein2::new(2, 0, vec![0., 3., 0.]).unwrap(),
                Bernstein2::new(2, 0, vec![0., 0., 0.]).unwrap(),
                Bernstein2::new(2, 0, vec![2., 3., 5.]).unwrap(),
            ],
            err: 0.,
            lower: 0.,
            depth: 0,
            uv: [0., 1., 0., 0.],
            parameter_ends: [Ivl::from(0.), Ivl::from(1.), Ivl::from(0.), Ivl::from(0.)],
        }
    }
    fn exact_control(piece: &Piece, i: usize) -> ProjectivePoint {
        let [a, b, c, w] = piece
            .h
            .each_ref()
            .map(|p| x::scalar(*p.coefficients().get(i).unwrap()).unwrap());
        ProjectivePoint { xyz: [a, b, c], w }
    }
    fn exact_equal(a: &x::E, b: &x::E) -> bool {
        x::sub(a, b).is_some_and(|d| x::zero(&d))
    }
    #[test]
    fn tiny_positive_common_factor_is_removed_before_out_of_range_cubic_scale() {
        let k = Kernel::default();
        let work = MeshWork::new();
        let actual = line();
        let tiny = 2_f64.powi(-330);
        // C=tiny² is positive/representable; OLD final scaling tiny*C is not
        // in geom::expansion::product's proven range. The curve is exactly2t.
        assert!(x::mul(&x::scalar(tiny).unwrap(), &x::scalar(tiny * tiny).unwrap()).is_none());
        let a = point(0., 0., tiny);
        let b = point(2., 0., tiny);
        let n = x::point([0., 0., 1.]).unwrap();
        let low = x::scalar(0.).unwrap();
        let d = x::point([0., 0., tiny]).unwrap();
        let proof = match project_sew_curve_with_work(&k, &work, &actual, [&a, &b], &n, &low, &d)
            .unwrap()
        {
            SewnCurveVerdict::Proven(p) => p,
            SewnCurveVerdict::Undecided(e) => panic!("{e}"),
        };
        assert!(core::ptr::eq(proof.actual(), &actual));
        for (i, p) in proof.controls().iter().enumerate() {
            assert!(exact_equal(&p.w, &x::scalar(tiny).unwrap()));
            for (h, input) in p.xyz.iter().zip(actual.h.iter().take(3)) {
                let expected = x::scale(
                    &x::scalar(*input.coefficients().get(i).unwrap()).unwrap(),
                    tiny,
                )
                .unwrap();
                assert!(exact_equal(h, &expected));
            }
        }
        assert!(proof.distance_upper().is_finite() && proof.distance_upper() < 1e-10);
    }
    #[test]
    fn a_positive_weight_with_a_tiny_exact_tail_keeps_the_same_complete_model() {
        let k = Kernel::default();
        let work = MeshWork::new();
        let actual = line();
        let w = x::add(
            &x::scalar(1.).unwrap(),
            &x::scalar(2_f64.powi(-500)).unwrap(),
        )
        .unwrap();
        assert!(x::mul(&w, &w).is_none()); // cannot first form the old common.
        let a = ProjectivePoint {
            xyz: x::point([0., 0., 0.]).unwrap(),
            w: w.clone(),
        };
        let b = ProjectivePoint {
            xyz: [
                x::scale(&w, 2.).unwrap(),
                x::scalar(0.).unwrap(),
                x::scalar(0.).unwrap(),
            ],
            w: w.clone(),
        };
        let n = x::point([0., 0., 1.]).unwrap();
        let d = [x::scalar(0.).unwrap(), x::scalar(0.).unwrap(), w];
        let proof = match project_sew_curve_with_work(
            &k,
            &work,
            &actual,
            [&a, &b],
            &n,
            &x::scalar(0.).unwrap(),
            &d,
        )
        .unwrap()
        {
            SewnCurveVerdict::Proven(p) => p,
            SewnCurveVerdict::Undecided(e) => panic!("{e}"),
        };
        assert!(exact_equal(&proof.controls().first().unwrap().w, &a.w));
        assert!(exact_equal(&proof.controls().last().unwrap().w, &b.w));
        assert!(proof.distance_upper().is_finite() && proof.distance_upper() < 1e-10);
    }
    #[test]
    fn nonuniform_rational_weights_and_distinct_matching_join_weights_share_one_gauge() {
        let k = Kernel::default();
        let work = MeshWork::new();
        let actual = rational_piece();
        let a = exact_control(&actual, 0);
        let b = exact_control(&actual, 2);
        let common = x::mul(&a.w, &b.w).unwrap();
        let proof = match sew_curve_with_work(&k, &work, &actual, [&a, &b]).unwrap() {
            SewnCurveVerdict::Proven(p) => p,
            SewnCurveVerdict::Undecided(e) => panic!("{e}"),
        };
        for (i, new) in proof.controls().iter().enumerate() {
            let original = exact_control(&actual, i);
            assert!(exact_equal(&new.w, &original.w)); //2,3,5, not20,30,50.
            let old = if i == 0 || i == 2 {
                let (join, other) = if i == 0 { (&a, &b) } else { (&b, &a) };
                scaled(join, &x::mul(&original.w, &other.w).unwrap()).unwrap()
            } else {
                scaled(&original, &common).unwrap()
            };
            for (old, new) in old
                .xyz
                .iter()
                .chain(core::iter::once(&old.w))
                .zip(new.xyz.iter().chain(core::iter::once(&new.w)))
            {
                assert!(exact_equal(old, &x::mul(new, &common).unwrap()));
            }
        }
        assert!(proof.distance_upper().is_finite() && proof.distance_upper() < 1e-10);
    }
    #[test]
    fn virtual_cut_matches_restricted_endpoint_weights_instead_of_assuming_one() {
        let k = Kernel::default();
        let work = MeshWork::new();
        let actual = rational_piece().restricted_u(0.25, 0.75).unwrap();
        let a = exact_control(&actual, 0);
        let b = exact_control(&actual, 2);
        assert!(!exact_equal(&a.w, &x::scalar(1.).unwrap()));
        assert!(!exact_equal(&b.w, &x::scalar(1.).unwrap()));
        assert!(!exact_equal(&a.w, &b.w));
        let proof = match sew_curve_with_work(&k, &work, &actual, [&a, &b]).unwrap() {
            SewnCurveVerdict::Proven(p) => p,
            SewnCurveVerdict::Undecided(e) => panic!("{e}"),
        };
        for (i, p) in proof.controls().iter().enumerate() {
            let original = exact_control(&actual, i);
            assert!(exact_equal(&p.w, &original.w));
            for (a, b) in p.xyz.iter().zip(&original.xyz) {
                assert!(exact_equal(a, b));
            }
        }
        assert!(proof.distance_upper().is_finite() && proof.distance_upper() < 1e-8);
    }
    #[test]
    fn any_mismatched_endpoint_weight_preserves_the_original_complete_formula() {
        let k = Kernel::default();
        let actual = rational_piece();
        for (wa, wb) in [(2., 11.), (7., 5.), (7., 11.)] {
            let a = point(0., 0., wa);
            let b = point(2., 0., wb);
            let common = x::mul(&a.w, &b.w).unwrap();
            let proof = match sew_curve_with_work(&k, &MeshWork::new(), &actual, [&a, &b]).unwrap()
            {
                SewnCurveVerdict::Proven(p) => p,
                SewnCurveVerdict::Undecided(e) => panic!("{e}"),
            };
            for (i, p) in proof.controls().iter().enumerate() {
                let original = exact_control(&actual, i);
                assert!(exact_equal(&p.w, &x::mul(&original.w, &common).unwrap()));
            }
        }
    }
    #[test]
    fn zero_weights_refuse_and_reversal_keeps_the_same_reversed_rational_curve() {
        let k = Kernel::default();
        let actual = rational_piece();
        let zero = point(0., 0., 0.);
        let end = exact_control(&actual, 2);
        assert!(matches!(
            sew_curve_with_work(&k, &MeshWork::new(), &actual, [&zero, &end]).unwrap(),
            SewnCurveVerdict::Undecided(_)
        ));
        let mut zero_actual = line();
        zero_actual.h[3] = Bernstein2::new(1, 0, vec![1., 0.]).unwrap();
        let start = point(0., 0., 1.);
        let finish = point(2., 0., 1.);
        assert!(matches!(
            sew_curve_with_work(&k, &MeshWork::new(), &zero_actual, [&start, &finish]).unwrap(),
            SewnCurveVerdict::Undecided(_)
        ));
        let reverse = Piece {
            h: actual.h.each_ref().map(|p| {
                Bernstein2::new(2, 0, p.coefficients().iter().copied().rev().collect()).unwrap()
            }),
            err: actual.err,
            lower: actual.lower,
            depth: actual.depth,
            uv: actual.uv,
            parameter_ends: actual.parameter_ends,
        };
        let a = exact_control(&reverse, 0);
        let b = exact_control(&reverse, 2);
        let proof = match sew_curve_with_work(&k, &MeshWork::new(), &reverse, [&a, &b]).unwrap() {
            SewnCurveVerdict::Proven(p) => p,
            SewnCurveVerdict::Undecided(e) => panic!("{e}"),
        };
        for (i, p) in proof.controls().iter().enumerate() {
            let input = exact_control(&reverse, i);
            assert!(exact_equal(&p.w, &input.w));
            for (a, b) in p.xyz.iter().zip(&input.xyz) {
                assert!(exact_equal(a, b));
            }
        }
    }
    #[test]
    fn gauge_preflight_uses_the_same_cumulative_cells_and_preserves_cancel() {
        let k = Kernel::default();
        let work = MeshWork::new();
        work.reserve_cells_core(&k, 1_999_500).unwrap();
        let actual = line();
        let mut a = point(0., 0., 1.);
        let mut b = point(2., 0., 1.);
        // Full retained zero tails are legal exact data; do not compact inputs
        // before accounting. Two 128-by-1 subtractions alone exceed500 cells.
        for p in [&mut a, &mut b] {
            p.w = vec![0.; 128];
            *p.w.last_mut().unwrap() = 1.;
        }
        assert!(sew_curve_with_work(&k, &work, &actual, [&a, &b]).is_err());
        assert!(matches!(
            work.check(&k),
            Err(super::super::super::MeshError::BudgetExceeded { .. })
        ));
        let token = crate::kernel::CancelToken::new();
        let mut k = Kernel::default();
        k.set_cancel_token(token.clone());
        token.cancel();
        let error = match sew_curve_with_work(&k, &work, &actual, [&a, &b]) {
            Err(e) => e,
            Ok(_) => panic!("cancel was not preserved"),
        };
        assert!(error.is_cancelled());
    }
}
