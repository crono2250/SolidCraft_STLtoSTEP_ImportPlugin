//! Small proof expressions over the kernel's exact expansion arithmetic (not upstream).
//! No numerical zero tolerance: arithmetic outside expansion's proven range refuses.
//! Deviations: none. No recursion. All expressions here have fixed algebraic degree.
use crate::geom::expansion as e;
use crate::math::Vec3;
pub(crate) type E = Vec<f64>;
pub(crate) type P = [E; 3];
fn finite(mut v: E) -> Option<E> {
    if !v.iter().all(|x| x.is_finite()) {
        return None;
    }
    // Native grow-expansion intentionally retains zero coefficients. Deep exact
    // projective constructions would multiply those redundant zeros at every
    // subsequent product, even on the reported integer native-box workflow.
    // Removing EXACT zeros changes neither a bit of any nonzero component nor
    // its order/value/sign. This is representation compaction, never epsilon
    // pruning, rounded recomputation, or weakening of native product range guards.
    v.retain(|&coefficient| coefficient != 0.);
    if v.is_empty() {
        v.push(0.);
    }
    Some(v)
}
/// Enclose every coefficient of an exact expansion with native outward arithmetic.
/// No coefficient is sampled, rounded away, or used as an approximate predicate.
pub(crate) fn interval(e: &E) -> Option<crate::blend::fillet_section::interval::Ivl> {
    use crate::blend::fillet_section::interval::Ivl;
    let mut value = Ivl::from(0.);
    for &term in e {
        value = value.add_ulp(Ivl::from(term));
    }
    value.is_finite().then_some(value)
}
pub(crate) fn scalar(x: f64) -> Option<E> {
    x.is_finite().then(|| vec![x])
}
pub(crate) fn point(p: [f64; 3]) -> Option<P> {
    let [x, y, z] = p;
    Some([scalar(x)?, scalar(y)?, scalar(z)?])
}
pub(crate) fn add(a: &E, b: &E) -> Option<E> {
    finite(e::add(a, b))
}
pub(crate) fn sub(a: &E, b: &E) -> Option<E> {
    finite(e::sub(a, b))
}
pub(crate) fn mul(a: &E, b: &E) -> Option<E> {
    let mut sum = Vec::new();
    for &x in b {
        sum = add(&sum, &e::scale(a, x)?)?;
    }
    Some(sum)
}
pub(crate) fn scale(a: &E, x: f64) -> Option<E> {
    finite(e::scale(a, x)?)
}
pub(crate) fn difference(a: &P, b: &P) -> Option<P> {
    let [ax, ay, az] = a;
    let [bx, by, bz] = b;
    Some([sub(ax, bx)?, sub(ay, by)?, sub(az, bz)?])
}
pub(crate) fn cross(a: &P, b: &P) -> Option<P> {
    let [ax, ay, az] = a;
    let [bx, by, bz] = b;
    Some([
        sub(&mul(ay, bz)?, &mul(az, by)?)?,
        sub(&mul(az, bx)?, &mul(ax, bz)?)?,
        sub(&mul(ax, by)?, &mul(ay, bx)?)?,
    ])
}
pub(crate) fn dot(a: &P, b: &P) -> Option<E> {
    let [ax, ay, az] = a;
    let [bx, by, bz] = b;
    add(&add(&mul(ax, bx)?, &mul(ay, by)?)?, &mul(az, bz)?)
}
pub(crate) fn sign(a: &E) -> Option<i32> {
    a.iter().all(|x| x.is_finite()).then(|| e::sign(a))
}
pub(crate) fn zero(a: &E) -> bool {
    sign(a) == Some(0)
}
pub(crate) fn equal_point(a: &P, b: [f64; 3]) -> bool {
    point(b)
        .and_then(|b| difference(a, &b))
        .is_some_and(|v| v.iter().all(zero))
}
pub(crate) fn collinear(t: [[f64; 3]; 3]) -> bool {
    let [a, b, c] = t;
    point(a)
        .and_then(|a| cross(&difference(&point(b)?, &a)?, &difference(&point(c)?, &a)?))
        .is_some_and(|n| n.iter().all(zero))
}
pub(crate) fn in_triangle(p: [f64; 3], t: [[f64; 3]; 3]) -> bool {
    let [a, b, c] = t;
    let Some((p, a, b, c)) = point(p).and_then(|p| Some((p, point(a)?, point(b)?, point(c)?)))
    else {
        return false;
    };
    let Some(n) = difference(&b, &a).and_then(|ab| cross(&ab, &difference(&c, &a)?)) else {
        return false;
    };
    if dot(&n, &n).and_then(|x| sign(&x)).is_none_or(|s| s <= 0) {
        return false;
    }
    if !difference(&p, &a)
        .and_then(|ap| dot(&n, &ap))
        .is_some_and(|d| zero(&d))
    {
        return false;
    }
    for (u, v) in [(&a, &b), (&b, &c), (&c, &a)] {
        let Some(area) = difference(v, u)
            .and_then(|uv| cross(&uv, &difference(&p, u)?))
            .and_then(|cross| dot(&cross, &n))
        else {
            return false;
        };
        if sign(&area).is_none_or(|s| s < 0) {
            return false;
        }
    }
    true
}
pub(crate) fn same_line(a: [f64; 3], b: [f64; 3], p: [f64; 3]) -> bool {
    collinear([a, b, p])
}
pub(crate) fn vec(v: Vec3) -> Option<P> {
    point([v.x, v.y, v.z])
}

/// Checked untouched raw triangle coordinates; no absent index becomes a default.
pub(crate) fn raw_triangle(
    positions: &[[f64; 3]],
    triangles: &[[u32; 3]],
    id: usize,
) -> Option<[[f64; 3]; 3]> {
    let &[a, b, c] = triangles.get(id)?;
    let read = |i: u32| {
        positions
            .get(usize::try_from(i).ok()?)
            .copied()
            .filter(|p| p.iter().all(|v| v.is_finite()))
    };
    Some([read(a)?, read(b)?, read(c)?])
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn exact_nonzero_rounding_components_survive_one_hundred_chained_products() {
        // The true product has a nonzero 2^-104 residual. Losing that small
        // component would turn a nonzero exact predicate into a false zero.
        let a = 1. + f64::EPSILON;
        let native = crate::geom::expansion::product(a, a).unwrap();
        let expected: Vec<_> = native.iter().copied().filter(|&v| v != 0.).collect();
        assert_eq!(expected.len(), 2);
        let one = scalar(1.).unwrap();
        let mut value = mul(&scalar(a).unwrap(), &scalar(a).unwrap()).unwrap();
        for _ in 0..100 {
            // Assert on EVERY iteration: the old zero-filled implementation
            // fails immediately instead of allocating an exponential test.
            assert_eq!(value.len(), 2);
            assert_eq!(
                value.iter().map(|v| v.to_bits()).collect::<Vec<_>>(),
                expected.iter().map(|v| v.to_bits()).collect::<Vec<_>>()
            );
            value = mul(&value, &one).unwrap();
        }
        assert_eq!(sign(&value), Some(1));
        assert!(!zero(&sub(&value, &scalar(a * a).unwrap()).unwrap()));
    }
    #[test]
    fn exact_zero_removal_preserves_zero_invalid_and_underflow_contracts() {
        assert_eq!(finite(vec![0., -0., 0.]).unwrap(), vec![0.]);
        assert!(finite(vec![0., f64::INFINITY, 0.]).is_none());
        assert!(finite(vec![f64::NAN, 0.]).is_none());
        assert!(scale(&scalar(f64::MIN_POSITIVE * 0.5).unwrap(), 1.).is_none());
        let zero_product = mul(
            &point([0., 0., 0.]).unwrap().into_iter().next().unwrap(),
            &scalar(100.).unwrap(),
        )
        .unwrap();
        assert_eq!(zero_product, vec![0.]);
    }
    #[test]
    fn exact_collinearity_is_not_small_area() {
        assert!(collinear([[0., 0., 0.], [10., 0., 0.], [20., 0., 0.]]));
        assert!(!collinear([[0., 0., 0.], [10., 0., 0.], [20., 1e-12, 0.]]));
    }
    #[test]
    fn complete_degenerate_facet_in_one_retained_triangle() {
        let t = [[0., 0., 0.], [20., 0., 0.], [20., 10., 0.]];
        assert!(
            in_triangle([0., 0., 0.], t)
                && in_triangle([10., 0., 0.], t)
                && in_triangle([20., 0., 0.], t)
        );
        assert!(!in_triangle([21., 0., 0.], t));
    }
}
