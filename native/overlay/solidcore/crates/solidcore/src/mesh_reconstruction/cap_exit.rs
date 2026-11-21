//! Whole-polynomial certificate of one regular exit from an actual native ball.
use super::actual_roots::ActualRoot;
use super::certificate::{curve_cap_bound, CurveCapBound, PointBox};
use super::{MeshError, MeshWork};
use crate::query::distance_bound::Piece;
use crate::Kernel;
const OP: &str = "mesh_reconstruction::profile_cap_exit";
type Result<T> = core::result::Result<T, MeshError>;
fn unsure(n: usize) -> MeshError {
    MeshError::Undecided { stage: OP, work: n }
}
pub(crate) struct CapExit<'a> {
    pub(crate) actual: &'a ActualRoot,
    pub(crate) vertex: PointBox,
    pub(crate) radius: f64,
    /// The actual curve has exactly one sphere crossing in this bracket; all
    /// earlier parameters are strictly inside and all later ones strictly outside.
    pub(crate) bracket: [f64; 2],
}
fn bound(
    k: &Kernel,
    work: &MeshWork,
    piece: &Piece,
    vertex: PointBox,
    radius: f64,
    a: f64,
    b: f64,
) -> Result<CurveCapBound> {
    work.reserve_cells(k, 1)?;
    work.spend(k, 1)?;
    let part = piece.restricted_u(a, b)?;
    Ok(curve_cap_bound(&part, vertex, radius, 0.)?)
}
/// Positive weights and WHOLE interval phi bounds prove coverage; point signs
/// are steering only. Opposite endpoints plus strict phi derivative prove one
/// crossing, never a sampled normal. The native radius is not widened.
pub(crate) fn unique_cap_exit<'a>(
    k: &Kernel,
    work: &MeshWork,
    actual: &'a ActualRoot,
    vertex: PointBox,
    radius: f64,
) -> Result<CapExit<'a>> {
    work.check(k)?;
    let all = bound(k, work, &actual.piece, vertex, radius, 0., 1.)?;
    let [at_start, at_end] = all.endpoints;
    if !(at_start.hi < 0. && at_end.lo > 0.) {
        return Err(unsure(0));
    }
    let (mut a, mut b) = (0., 1.);
    for iteration in 0..48 {
        work.spend(k, 1)?;
        if a > 0. && b < 1. {
            let before = bound(k, work, &actual.piece, vertex, radius, 0., a)?;
            let after = bound(k, work, &actual.piece, vertex, radius, b, 1.)?;
            let crossing = bound(k, work, &actual.piece, vertex, radius, a, b)?;
            let [left, right] = crossing.endpoints;
            if before.numerator.hi < 0.
                && after.numerator.lo > 0.
                && left.hi < 0.
                && right.lo > 0.
                && crossing.derivative.lo > 0.
            {
                work.check(k)?;
                return Ok(CapExit {
                    actual,
                    vertex,
                    radius,
                    bracket: [a, b],
                });
            }
        }
        let middle = 0.5 * a + 0.5 * b;
        if !(a < middle && middle < b) {
            return Err(unsure(iteration));
        }
        // The entire interval proof above decides acceptance. These certified
        // endpoint signs merely choose a candidate bracket to prove next time.
        let point = bound(k, work, &actual.piece, vertex, radius, 0., middle)?.endpoints;
        let [_, point] = point;
        if point.hi < 0. {
            a = middle;
            continue;
        }
        if point.lo > 0. {
            b = middle;
            continue;
        }
        // An exact dyadic crossing may enclose zero at the midpoint. Choose
        // distinct quarter points rather than pretending the enclosure's sign.
        let left = 0.5 * a + 0.5 * middle;
        let right = 0.5 * middle + 0.5 * b;
        if !(a < left && left < right && right < b) {
            return Err(unsure(iteration));
        }
        let [_, lp] = bound(k, work, &actual.piece, vertex, radius, 0., left)?.endpoints;
        let [_, rp] = bound(k, work, &actual.piece, vertex, radius, 0., right)?.endpoints;
        if lp.hi < 0. && rp.lo > 0. {
            a = left;
            b = right;
        } else {
            return Err(unsure(iteration));
        }
    }
    Err(unsure(48))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::blend::fillet_section::interval::Ivl;
    use crate::curve::curve::Curve;
    use crate::nurbs::b_spline_curve::BSplineCurve;
    use crate::nurbs::crv_basic::Curve as Nurb;
    use crate::nurbs::math::{CPoint, NOW};
    fn curve(x: &[f64]) -> Curve {
        let degree = x.len() - 1;
        let knots = std::iter::repeat_n(0., degree + 1)
            .chain(std::iter::repeat_n(1., degree + 1))
            .collect();
        let controls = x.iter().map(|&x| CPoint::new(x, 0., 0., NOW)).collect();
        Curve::from(BSplineCurve::from_nurb(
            Nurb::new(controls, degree, knots).unwrap(),
            3,
            true,
        ))
    }
    #[test]
    fn exact_dyadic_sphere_exit_does_not_depend_on_a_sample_sign() {
        let k = Kernel::default();
        let work = MeshWork::new();
        let curve = curve(&[0., 1.]);
        let roots = super::super::actual_roots::actual_roots(&k, &work, &curve, true).unwrap();
        let root = roots.first().unwrap();
        let proof = unique_cap_exit(&k, &work, root, [Ivl::from(0.); 3], 0.125).unwrap();
        let [a, b] = proof.bracket;
        assert!(a < 0.125 && 0.125 < b);
    }
    #[test]
    fn endpoint_straddling_with_an_earlier_excursion_cannot_prove_one_exit() {
        let k = Kernel::default();
        let work = MeshWork::new();
        let curve = curve(&[0., 3., -3., 1.]);
        let roots = super::super::actual_roots::actual_roots(&k, &work, &curve, true).unwrap();
        assert!(
            unique_cap_exit(&k, &work, roots.first().unwrap(), [Ivl::from(0.); 3], 0.125).is_err()
        );
    }
}
