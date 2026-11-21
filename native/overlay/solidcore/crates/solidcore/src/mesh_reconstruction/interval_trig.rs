//! Shared outward sine/cosine enclosures for native geometric certificates.
//! Taylor polynomials use outward interval arithmetic; the next term bounds the alternating
//! remainder after degree 41/40. For |x|<=16 the omitted tails decrease monotonically.
//! Larger finite angles return the rigorous full [-1,1] range, not an unproved libm reduction.
//! Certificate owners may subdivide/refuse undecided ranges without changing tolerances.
use crate::blend::fillet_section::interval::Ivl;

/// Sine and cosine over the ENTIRE finite radian interval, including interior extrema.
/// None for a malformed/nonfinite interval. No endpoint sampling is used.
pub(crate) fn sin_cos(angle: Ivl) -> Option<(Ivl, Ivl)> {
    if !angle.is_finite() {
        return None;
    }
    let unit = Ivl::new(-1., 1.);
    if angle.mag() > 16. {
        return Some((unit, unit));
    }
    let x2 = angle.mul_ulp(angle);
    let minus = Ivl::from(-1.);
    let (mut st, mut sine) = (angle, angle);
    let (mut ct, mut cosine) = (Ivl::from(1.), Ivl::from(1.));
    for n in 1..=20usize {
        st = st
            .mul_ulp(x2)
            .mul_ulp(minus)
            .div_ulp(Ivl::from(((2 * n) * (2 * n + 1)) as f64));
        sine = sine.add_ulp(st);
        ct = ct
            .mul_ulp(x2)
            .mul_ulp(minus)
            .div_ulp(Ivl::from(((2 * n - 1) * (2 * n)) as f64));
        cosine = cosine.add_ulp(ct);
    }
    let sr = st.mul_ulp(x2).div_ulp(Ivl::from(f64::from(42 * 43))).mag();
    let cr = ct.mul_ulp(x2).div_ulp(Ivl::from(f64::from(41 * 42))).mag();
    let sine = sine.add_ulp(Ivl::new(-sr, sr));
    let cosine = cosine.add_ulp(Ivl::new(-cr, cr));
    if !sine.is_finite() || !cosine.is_finite() {
        return Some((unit, unit));
    }
    let clamp = |v: Ivl| {
        let (lo, hi) = (v.lo.max(-1.), v.hi.min(1.));
        if lo <= hi {
            Ivl::new(lo, hi)
        } else {
            unit
        }
    };
    Some((clamp(sine), clamp(cosine)))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn interval_straddling_zero_keeps_the_interior_cosine_maximum() {
        let (s, c) = sin_cos(Ivl::new(-0.2, 0.2)).unwrap();
        assert!(s.lo < 0. && s.hi > 0.);
        assert!(c.lo <= 1. && c.hi >= 1.);
        let (s, c) = sin_cos(Ivl::from(0.)).unwrap();
        assert!(s.lo <= 0. && s.hi >= 0.);
        assert!(c.lo <= 1. && c.hi >= 1.);
    }
    #[test]
    fn a_half_turn_interval_cannot_be_replaced_by_its_endpoints() {
        let (s, c) = sin_cos(Ivl::new(-3.1415926535897936, 3.1415926535897936)).unwrap();
        assert!(s.lo <= -1. && s.hi >= 1.);
        assert!(c.lo <= -1. && c.hi >= 1.);
        assert_eq!(
            sin_cos(Ivl::new(100., 101.)).unwrap(),
            (Ivl::new(-1., 1.), Ivl::new(-1., 1.))
        );
        assert!(sin_cos(Ivl::whole()).is_none());
    }
}
