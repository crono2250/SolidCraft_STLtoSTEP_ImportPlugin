//! Whole-domain bounds used by source-mesh reconstruction (not upstream).
//!
//! A source triangle is the image of the unit square under the collapsed bilinear map
//! `[a, c; b, b]`. A chosen bilinear UV map into one rational Bezier piece is composed
//! by de Casteljau in polynomial algebra. The coefficients of the homogeneous residual
//! bound every point of that correspondence, not just the corners used to choose it.
//! The caller must prove that the entire UV image is inside the actual trimmed face.
//!
//! Conversely, positive rational weights put a surface piece inside its Euclidean
//! control hull. Distance to ONE fixed closed triangle is convex. A certified distance
//! upper bound from every control enclosure to that same triangle covers the whole
//! piece. Choosing a different source triangle for each control is not this proof.
//!
//! Coefficient errors follow `nurbs::certificate`: the native Bernstein algebra is reused,
//! and each product/elevation/addition carries its floating-point error. Degrees here
//! stay at most eight, so the binomial coefficients used by the native products are
//! exact integers in f64. Every arithmetic upper bound is rounded outward with Ivl.
//!
//! References: Piegl and Tiller, The NURBS Book, 2nd ed., section 4.4 (positive rational
//! hull); Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., section 3.1
//! (gamma); Straub, Exact Computation of the Hausdorff Distance between Triangular
//! Meshes, 2007 (complete-triangle directed distance, rather than point samples).
//!
//! Deviations: none. No recursion. Polynomial degrees are bounded by `MAX_DEGREE`.

use crate::blend::fillet_section::interval::{round_up, Ivl};
use crate::geom::geom_utility::p2::triangle_point_distance;
use crate::math::Point3;
use crate::nurbs::math::gamma;
use crate::offset::construction::bernstein::{Bernstein2, Binomials};
use crate::query::distance_bound::Piece;
use crate::{Result, SolidError};

const OP: &str = "mesh_reconstruction::certificate::hulls";
const MAX_DEGREE: usize = 8;

/// A point whose exact three coordinates are enclosed, in the common translated frame.
pub(crate) type PointBox = [Ivl; 3];
/// The three enclosed corners of one exact triangle, in the common translated frame.
pub(crate) type Triangle = [PointBox; 3];

fn refused(reason: &'static str) -> SolidError {
    SolidError::Unsupported {
        operation: OP,
        reason,
    }
}

fn finite(upper: f64) -> Result<f64> {
    if upper.is_finite() && upper >= 0.0 {
        Ok(upper)
    } else {
        Err(refused("a whole-domain upper bound is not finite"))
    }
}

/// The interval norm of every vector in `v`.
fn norm_upper(v: PointBox) -> Result<f64> {
    let [x, y, z] = v;
    finite((x * x + y * y + z * z).sqrt().hi)
}

/// An upper bound of the distance of any point in one box from any point in the other.
pub(crate) fn point_distance_upper(a: PointBox, b: PointBox) -> Result<f64> {
    let [ax, ay, az] = a;
    let [bx, by, bz] = b;
    norm_upper([ax - bx, ay - by, az - bz])
}

/// A triangle's whole image is within this distance of the exact point enclosed by
/// `witness`. Distance to a fixed point is convex, so the maximum is at a corner.
pub(crate) fn triangle_point_upper(triangle: &Triangle, witness: PointBox) -> Result<f64> {
    let mut worst = 0.0_f64;
    for &corner in triangle {
        worst = worst.max(point_distance_upper(corner, witness)?);
    }
    Ok(worst)
}

/// Four triangles covering the parent's exact convex hull. Outward interval arithmetic
/// carries the rounding of every midpoint; there is no new geometric approximation.
pub(crate) fn quarters(triangle: &Triangle) -> [Triangle; 4] {
    let [a, b, c] = *triangle;
    let middle = |a: PointBox, b: PointBox| {
        let [ax, ay, az] = a;
        let [bx, by, bz] = b;
        let half = Ivl::from(0.5);
        [(ax + bx) * half, (ay + by) * half, (az + bz) * half]
    };
    let (ab, ac, bc) = (middle(a, b), middle(a, c), middle(b, c));
    [[a, ab, ac], [ab, b, bc], [ac, bc, c], [ab, bc, ac]]
}

fn centre(boxed: PointBox) -> Point3 {
    let [x, y, z] = boxed;
    let mid = |v: Ivl| 0.5 * v.lo + 0.5 * v.hi;
    Point3::new(mid(x), mid(y), mid(z))
}

/// A valid point of the exact source triangle near `at`. The numerical solve only
/// chooses barycentric weights: the returned interval encloses their affine evaluation.
/// The weights themselves must prove membership; an unconstrained closest-point value
/// is never accepted as a point of the triangle.
fn triangle_witness(triangle: &Triangle, at: PointBox) -> Result<PointBox> {
    if triangle.iter().flatten().chain(&at).any(|v| !v.is_finite()) {
        return Err(refused("a source witness has a non-finite enclosure"));
    }
    let [a, b, c] = *triangle;
    let [pa, pb, pc] = [a, b, c].map(centre);
    let guess = match triangle_point_distance(pa, pb, pc, centre(at)) {
        Ok(x) => Some((x.u, x.v)),
        Err(e) if super::errors::expected(&e) => None,
        Err(e) => return Err(e),
    };
    let add = |a: PointBox, b: PointBox| {
        let [ax, ay, az] = a;
        let [bx, by, bz] = b;
        [ax + bx, ay + by, az + bz]
    };
    let difference = |a: PointBox, b: PointBox| {
        let [ax, ay, az] = a;
        let [bx, by, bz] = b;
        [ax - bx, ay - by, az - bz]
    };
    let scale = |a: PointBox, t: Ivl| a.map(|v| v * t);
    let edge = |a: PointBox, b: PointBox, t: f64| {
        let t = if t.is_finite() {
            t.clamp(0.0, 1.0)
        } else {
            0.0
        };
        add(a, scale(difference(b, a), Ivl::from(t)))
    };
    let witness = match guess {
        Some((u, v)) if u.is_finite() && v.is_finite() => {
            let sum = Ivl::from(u) + Ivl::from(v);
            if u >= 0.0 && v >= 0.0 && sum.hi <= 1.0 {
                add(
                    add(a, scale(difference(b, a), Ivl::from(u))),
                    scale(difference(c, a), Ivl::from(v)),
                )
            } else if u <= 0.0 {
                edge(a, c, v)
            } else if v <= 0.0 {
                edge(a, b, u)
            } else {
                // Any finite parameter in [0,1] is a proved point of edge b--c.
                edge(b, c, v / (u + v))
            }
        }
        _ => {
            // These two stored doubles are nonnegative and sum to less than one.
            let third = Ivl::from(1.0 / 3.0);
            add(
                add(a, scale(difference(b, a), third)),
                scale(difference(c, a), third),
            )
        }
    };
    if witness.iter().all(|v| v.is_finite()) {
        Ok(witness)
    } else {
        Err(refused("a barycentric source witness is not finite"))
    }
}

/// A rational patch's entire control hull is within this distance of ONE source
/// triangle. Each control enclosure may use its own valid barycentric witness, but
/// every witness belongs to the same convex triangle.
pub(crate) fn piece_triangle_upper(piece: &Piece, source: &Triangle, slack: f64) -> Result<f64> {
    if !(piece.err.is_finite() && piece.err >= 0.0 && slack.is_finite() && slack >= 0.0) {
        return Err(refused(
            "a patch's coefficient or definition error is invalid",
        ));
    }
    if piece
        .h
        .iter()
        .flat_map(Bernstein2::coefficients)
        .any(|v| !v.is_finite())
    {
        return Err(refused("a rational patch has a non-finite control"));
    }
    let [x, y, z, w] = &piece.h;
    let sizes = [x, y, z, w].map(|p| p.coefficients().len());
    if sizes.iter().any(|n| *n != sizes[0]) || sizes[0] == 0 {
        return Err(refused("a rational patch has inconsistent controls"));
    }
    let err = Ivl::from(piece.err);
    let mut worst = 0.0_f64;
    for (((&x, &y), &z), &w) in x
        .coefficients()
        .iter()
        .zip(y.coefficients())
        .zip(z.coefficients())
        .zip(w.coefficients())
    {
        let weight = Ivl::from(w) + Ivl::new(-piece.err, piece.err);
        if !weight.is_positive() {
            return Err(refused(
                "a rational patch's weights are not proved positive",
            ));
        }
        let interval = |v: f64| (Ivl::from(v) + Ivl::new(-err.hi, err.hi)) / weight;
        let point = [interval(x), interval(y), interval(z)];
        let witness = triangle_witness(source, point)?;
        worst = worst.max(point_distance_upper(point, witness)?);
    }
    finite((Ivl::from(worst) + Ivl::from(slack)).hi)
}

/// A Bernstein polynomial and a uniform absolute bound on every coefficient's error.
/// Algebra is the kernel's one Bernstein implementation; this wrapper only carries its
/// rounding and input error, as `nurbs::certificate` does in one parameter.
#[derive(Clone)]
struct BoundedPolynomial {
    polynomial: Bernstein2,
    error: f64,
}

impl BoundedPolynomial {
    fn constant(value: f64, error: f64) -> Self {
        Self {
            polynomial: Bernstein2::constant(value),
            error,
        }
    }

    fn checked(polynomial: Bernstein2, error: f64) -> Result<Self> {
        if error.is_finite()
            && error >= 0.0
            && polynomial.coefficients().iter().all(|v| v.is_finite())
        {
            Ok(Self { polynomial, error })
        } else {
            Err(refused("a bounded polynomial is not finite"))
        }
    }

    fn size(&self) -> f64 {
        self.polynomial.max_abs_coefficient()
    }

    fn product_error(&self, other: &Self) -> Result<f64> {
        let (au, av) = self.polynomial.degrees();
        let (bu, bv) = other.polynomial.degrees();
        let du = au
            .checked_add(bu)
            .ok_or_else(|| refused("a product degree overflowed"))?;
        let dv = av
            .checked_add(bv)
            .ok_or_else(|| refused("a product degree overflowed"))?;
        if du > MAX_DEGREE || dv > MAX_DEGREE {
            return Err(refused(
                "the whole-domain correspondence exceeds degree eight",
            ));
        }
        // At most the product of both input coefficient counts contributes to one
        // coefficient. Each term needs at most eight rounded products/sums/divisions
        // in Bernstein2::mul. All binomials through degree eight are exact integers.
        let terms = self
            .polynomial
            .coefficients()
            .len()
            .checked_mul(other.polynomial.coefficients().len())
            .ok_or_else(|| refused("a product term count overflowed"))?;
        let operations = terms
            .checked_mul(8)
            .and_then(|n| n.checked_add(8))
            .ok_or_else(|| refused("a product operation count overflowed"))?;
        let (a, b) = (Ivl::from(self.size()), Ivl::from(other.size()));
        let (ea, eb) = (Ivl::from(self.error), Ivl::from(other.error));
        let rounding = Ivl::from(round_up(gamma(operations)));
        // The absolute term covers every possible subnormal rounded operation.
        let tiny = Ivl::from(f64::MIN_POSITIVE) * Ivl::from(operations as f64);
        finite((rounding * a * b + ea * b + a * eb + ea * eb + tiny).hi)
    }

    fn mul(&self, other: &Self, binomials: &Binomials) -> Result<Self> {
        Self::checked(
            self.polynomial.mul(&other.polynomial, binomials)?,
            self.product_error(other)?,
        )
    }

    fn derivative(&self, first: bool) -> Result<Self> {
        let (du, dv) = self.polynomial.degrees();
        let degree = if first { du } else { dv };
        let differentiated = if first {
            self.polynomial.deriv_u()
        } else {
            self.polynomial.deriv_v()
        };
        if degree > MAX_DEGREE {
            return Err(refused("a derivative degree exceeds the proof limit"));
        }
        if degree == 0 {
            return Self::checked(differentiated, 0.0);
        }
        #[allow(clippy::cast_precision_loss)] // a checked degree, at most eight
        let degree = Ivl::from(degree as f64);
        // Each coefficient is degree*(next-current): two input errors, one
        // subtraction and one multiplication. A derivative of an exactly constant
        // polynomial is handled separately, not charged as uncertain zero.
        let error = degree
            * (Ivl::from(2.0) * Ivl::from(self.error)
                + Ivl::from(round_up(gamma(2))) * Ivl::from(2.0) * Ivl::from(self.size()))
            + Ivl::from(4.0 * f64::MIN_POSITIVE);
        Self::checked(differentiated, finite(error.hi)?)
    }

    fn elevated(&self, du: usize, dv: usize, binomials: &Binomials) -> Result<Self> {
        let (au, av) = self.polynomial.degrees();
        if (au, av) == (du, dv) {
            return Ok(self.clone());
        }
        if du > MAX_DEGREE || dv > MAX_DEGREE || du < au || dv < av {
            return Err(refused("a correspondence elevation has an invalid degree"));
        }
        let (u, v) = (du - au, dv - av);
        let count = (u + 1)
            .checked_mul(v + 1)
            .ok_or_else(|| refused("an elevation count overflowed"))?;
        let ones = BoundedPolynomial {
            polynomial: Bernstein2::new(u, v, (0..count).map(|_| 1.0).collect())?,
            error: 0.0,
        };
        Self::checked(
            self.polynomial.elevate(du, dv, binomials)?,
            self.product_error(&ones)?,
        )
    }

    fn add(&self, other: &Self, sign: f64, binomials: &Binomials) -> Result<Self> {
        let (au, av) = self.polynomial.degrees();
        let (bu, bv) = other.polynomial.degrees();
        let (a, b) = (
            self.elevated(au.max(bu), av.max(bv), binomials)?,
            other.elevated(au.max(bu), av.max(bv), binomials)?,
        );
        let size = Ivl::from(a.size()) + Ivl::from(b.size());
        let error = Ivl::from(a.error)
            + Ivl::from(b.error)
            + Ivl::from(round_up(gamma(2))) * size
            + Ivl::from(2.0 * f64::MIN_POSITIVE);
        Self::checked(
            a.polynomial.add_scaled(&b.polynomial, sign, binomials)?,
            finite(error.hi)?,
        )
    }
}

/// De Casteljau composition in each parameter. The UV polynomials' values lie in
/// [0,1] because their four coefficients do; they are chosen maps, not trusted solves.
fn compose(
    polynomial: &Bernstein2,
    error: f64,
    u: &BoundedPolynomial,
    v: &BoundedPolynomial,
    binomials: &Binomials,
) -> Result<BoundedPolynomial> {
    let (du, dv) = polynomial.degrees();
    if du.checked_add(dv).is_none_or(|d| d + 1 > MAX_DEGREE) {
        return Err(refused(
            "the whole-domain composition exceeds its degree bound",
        ));
    }
    let one = BoundedPolynomial::constant(1.0, 0.0);
    let omu = one.add(u, -1.0, binomials)?;
    let omv = one.add(v, -1.0, binomials)?;
    let blend = |a: &BoundedPolynomial,
                 b: &BoundedPolynomial,
                 t: &BoundedPolynomial,
                 omt: &BoundedPolynomial| {
        a.mul(omt, binomials)?
            .add(&b.mul(t, binomials)?, 1.0, binomials)
    };
    let mut rows = Vec::new();
    // The bounded row width is nonzero; malformed coefficient counts refuse.
    let width = dv + 1;
    let coefficients = polynomial.coefficients();
    let mut offset = 0_usize;
    while offset < coefficients.len() {
        let end = offset
            .checked_add(width)
            .ok_or_else(|| refused("a composition row offset overflowed"))?;
        let row = coefficients
            .get(offset..end)
            .ok_or_else(|| refused("a composition row is incomplete"))?;
        offset = end;
        let mut level: Vec<_> = row
            .iter()
            .map(|&c| BoundedPolynomial::constant(c, error))
            .collect();
        while level.len() > 1 {
            let mut next = Vec::new();
            for pair in level.windows(2) {
                let [a, b] = pair else {
                    return Err(refused("a composition pair is missing"));
                };
                next.push(blend(a, b, v, &omv)?);
            }
            level = next;
        }
        rows.push(
            level
                .pop()
                .ok_or_else(|| refused("a composition row is empty"))?,
        );
    }
    if rows.len() != du + 1 {
        return Err(refused("a composition has the wrong number of rows"));
    }
    while rows.len() > 1 {
        let mut next = Vec::new();
        for pair in rows.windows(2) {
            let [a, b] = pair else {
                return Err(refused("a composition pair is missing"));
            };
            next.push(blend(a, b, u, &omu)?);
        }
        rows = next;
    }
    rows.pop()
        .ok_or_else(|| refused("a composition has no value"))
}

/// Proves the maximum distance between the COMPLETE source triangle and a chosen
/// rational surface correspondence. `uv` stores three chosen unit-patch parameter
/// corners. Before using this bound, the caller MUST prove the entire resulting
/// native-parameter triangle is on the actual face, including trim/parameter rounding.
/// No point projection or source corner check alone satisfies that requirement.
pub(crate) fn correspondence_upper(
    piece: &Piece,
    source: &Triangle,
    uv: [[f64; 2]; 3],
    slack: f64,
) -> Result<f64> {
    if !(piece.err.is_finite() && piece.err >= 0.0 && slack.is_finite() && slack >= 0.0)
        || uv
            .iter()
            .flatten()
            .any(|v| !v.is_finite() || *v < 0.0 || *v > 1.0)
    {
        return Err(refused("a correspondence map or error is invalid"));
    }
    if piece
        .h
        .iter()
        .flat_map(Bernstein2::coefficients)
        .any(|v| !v.is_finite())
    {
        return Err(refused("a rational patch has a non-finite control"));
    }
    let [[ua, va], [ub, vb], [uc, vc]] = uv;
    let u = BoundedPolynomial {
        polynomial: Bernstein2::new(1, 1, vec![ua, uc, ub, ub])?,
        error: 0.0,
    };
    let v = BoundedPolynomial {
        polynomial: Bernstein2::new(1, 1, vec![va, vc, vb, vb])?,
        error: 0.0,
    };
    let binomials = Binomials::for_degree(MAX_DEGREE)?;
    let mut composed = Vec::new();
    for p in &piece.h {
        composed.push(compose(p, piece.err, &u, &v, &binomials)?);
    }
    let [Some(x), Some(y), Some(z), Some(w)] = [
        composed.first(),
        composed.get(1),
        composed.get(2),
        composed.get(3),
    ] else {
        return Err(refused(
            "a homogeneous correspondence lacks its coordinates",
        ));
    };
    let denominator = (Ivl::from(w.polynomial.min_coefficient()) - Ivl::from(w.error)).lo;
    if !(denominator > 0.0 && denominator.is_finite()) {
        return Err(refused("a correspondence weight is not proved positive"));
    }
    let [a, b, c] = *source;
    let mut residual = Vec::new();
    for (axis, target) in [x, y, z].into_iter().enumerate() {
        let (Some(&a), Some(&b), Some(&c)) = (a.get(axis), b.get(axis), c.get(axis)) else {
            return Err(refused("a source triangle lacks a coordinate"));
        };
        if ![a, b, c].iter().all(|c| c.is_finite()) {
            return Err(refused("a source enclosure is not finite"));
        }
        let midpoint = |c: Ivl| 0.5 * c.lo + 0.5 * c.hi;
        let (ma, mb, mc) = (midpoint(a), midpoint(b), midpoint(c));
        let error = [a - Ivl::from(ma), b - Ivl::from(mb), c - Ivl::from(mc)]
            .iter()
            .map(|e| e.mag())
            .fold(0.0_f64, f64::max);
        let source = BoundedPolynomial {
            polynomial: Bernstein2::new(1, 1, vec![ma, mc, mb, mb])?,
            error,
        };
        let difference = target.add(&source.mul(w, &binomials)?, -1.0, &binomials)?;
        residual.push(
            (Ivl::from(difference.polynomial.max_abs_coefficient()) + Ivl::from(difference.error))
                .hi,
        );
    }
    let [Some(&x), Some(&y), Some(&z)] = [residual.first(), residual.get(1), residual.get(2)]
    else {
        return Err(refused("a residual lacks a coordinate"));
    };
    let upper = norm_upper([Ivl::from(x), Ivl::from(y), Ivl::from(z)])?;
    finite((Ivl::from(upper) / Ivl::from(denominator) + Ivl::from(slack)).hi)
}

/// A whole-parameter curve/segment correspondence and its strict projection
/// monotonicity. These are building blocks for coherent edge deformation; they do
/// not themselves prove a collection of edge tubes disjoint or a trim loop's nesting.
pub(crate) struct CurveGraphBound {
    pub(crate) distance_upper: f64,
    /// Lower bound of d/dt(C(t) dot (segment_end-segment_start)) times W(t)^2.
    pub(crate) projection_numerator_lower: f64,
    pub(crate) endpoints: [PointBox; 2],
}

/// Certify a positive rational curve piece against one oriented source segment using
/// the SAME parameter for every point. `piece.h` must have degree zero in v and
/// represent the whole chosen actual edge interval, with extraction/definition error
/// certified by the kernel's curve-form preparation. No closest point is a proof.
///
/// The derivative numerator's coefficient hull must be strictly positive along the
/// source segment. Thus the curve is a graph in that projection direction, excluding
/// backtracking/loops that a Hausdorff bound alone would allow. Join/adjacent-wedge and
/// nonincident-tube separation remain the topology verifier's obligations.
pub(crate) fn curve_graph_bound(
    piece: &Piece,
    segment: [PointBox; 2],
    slack: f64,
) -> Result<CurveGraphBound> {
    let [a, b] = segment;
    // A value-only certificate does not enclose the definition's derivative. A
    // procedural edge needs derivative enclosures before its monotonicity is proved.
    if slack != 0.0 {
        return Err(refused(
            "a value-only curve definition bound cannot certify edge orientation",
        ));
    }
    if piece.h.iter().any(|p| p.degrees().1 != 0) {
        return Err(refused("an edge proof requires a one-parameter piece"));
    }
    let distance_upper = correspondence_upper(
        piece,
        &[a, b, a],
        [[0.0, 0.0], [1.0, 0.0], [0.0, 0.0]],
        slack,
    )?;
    let binomials = Binomials::for_degree(MAX_DEGREE)?;
    let [hx, hy, hz, hw] = &piece.h;
    let bounded = |p: &Bernstein2| BoundedPolynomial::checked(p.clone(), piece.err);
    let w = bounded(hw)?;
    let dw = w.derivative(true)?;
    let denominator = (Ivl::from(hw.min_coefficient()) - Ivl::from(piece.err)).lo;
    if !(denominator > 0.0 && denominator.is_finite()) {
        return Err(refused("an edge weight is not proved positive"));
    }
    let direction = {
        let [ax, ay, az] = a;
        let [bx, by, bz] = b;
        [bx - ax, by - ay, bz - az]
    };
    let mut projection = BoundedPolynomial::constant(0.0, 0.0);
    for (p, d) in [hx, hy, hz].into_iter().zip(direction) {
        if !d.is_finite() {
            return Err(refused("an edge projection direction is not finite"));
        }
        let h = bounded(p)?;
        let numerator = h.derivative(true)?.mul(&w, &binomials)?.add(
            &h.mul(&dw, &binomials)?,
            -1.0,
            &binomials,
        )?;
        let middle = 0.5 * d.lo + 0.5 * d.hi;
        let coefficient = BoundedPolynomial::constant(middle, (d - Ivl::from(middle)).mag());
        projection = projection.add(&numerator.mul(&coefficient, &binomials)?, 1.0, &binomials)?;
    }
    let lower =
        (Ivl::from(projection.polynomial.min_coefficient()) - Ivl::from(projection.error)).lo;
    if !(lower > 0.0 && lower.is_finite()) {
        return Err(refused(
            "the edge correspondence is not proved strictly monotone",
        ));
    }
    let endpoint = |last: bool| -> Result<PointBox> {
        let choose = |p: &Bernstein2| {
            if last {
                p.coefficients().last().copied()
            } else {
                p.coefficients().first().copied()
            }
        };
        let [Some(x), Some(y), Some(z), Some(w)] = [choose(hx), choose(hy), choose(hz), choose(hw)]
        else {
            return Err(refused("an edge lacks endpoint controls"));
        };
        let weight = Ivl::from(w) + Ivl::new(-piece.err, piece.err);
        if !weight.is_positive() {
            return Err(refused("an edge endpoint weight is not proved positive"));
        }
        let result = [x, y, z].map(|v| (Ivl::from(v) + Ivl::new(-piece.err, piece.err)) / weight);
        if result.iter().all(|v| v.is_finite()) {
            Ok(result)
        } else {
            Err(refused("an edge endpoint enclosure is not finite"))
        }
    };
    Ok(CurveGraphBound {
        distance_upper,
        projection_numerator_lower: lower,
        endpoints: [endpoint(false)?, endpoint(true)?],
    })
}

/// Complete homogeneous sphere-cap predicate on one actual rational curve piece.
/// Values are numerator enclosures, not Euclidean distances. Positive W makes their
/// signs exactly those of ||C(t)-vertex||^2-radius^2. A strictly signed derivative
/// of THIS numerator and opposite signed endpoint values isolate one crossing;
/// interval overlap or sampled branch directions never establish a collar.
/// This helper does not decide ownership, sectors, edge/native-vertex identity or
/// the source/target material collar. Those remain the consuming rim verifier's job.
pub(crate) struct CurveCapBound {
    pub(crate) numerator: Ivl,
    pub(crate) derivative: Ivl,
    pub(crate) endpoints: [Ivl; 2],
}

pub(crate) fn curve_cap_bound(
    piece: &Piece,
    vertex: PointBox,
    radius: f64,
    slack: f64,
) -> Result<CurveCapBound> {
    curve_cap_bound_with_binomials(
        piece,
        vertex,
        radius,
        slack,
        &Binomials::for_degree(MAX_DEGREE)?,
    )
}
fn curve_cap_bound_with_binomials(
    piece: &Piece,
    vertex: PointBox,
    radius: f64,
    slack: f64,
    binomials: &Binomials,
) -> Result<CurveCapBound> {
    if slack != 0.0 {
        return Err(refused(
            "a value-only curve definition bound cannot certify a cap crossing",
        ));
    }
    if !(radius > 0.0 && radius.is_finite())
        || vertex.iter().any(|p| !p.is_finite())
        || piece.h.iter().any(|p| p.degrees().1 != 0)
    {
        return Err(refused(
            "a cap predicate requires a finite ball and a one-parameter curve",
        ));
    }
    let bounded = |p: &Bernstein2| BoundedPolynomial::checked(p.clone(), piece.err);
    let [hx, hy, hz, hw] = &piece.h;
    let w = bounded(hw)?;
    if !(Ivl::from(hw.min_coefficient()) - Ivl::from(piece.err)).is_positive() {
        return Err(refused(
            "a cap predicate's curve weights are not proved positive",
        ));
    }
    let constant = |v: Ivl| {
        let middle = 0.5 * v.lo + 0.5 * v.hi;
        BoundedPolynomial::checked(Bernstein2::constant(middle), (v - Ivl::from(middle)).mag())
    };
    let mut squared = BoundedPolynomial::constant(0.0, 0.0);
    for (h, v) in [hx, hy, hz].into_iter().zip(vertex) {
        let n = bounded(h)?.add(&w.mul(&constant(v)?, binomials)?, -1.0, binomials)?;
        squared = squared.add(&n.mul(&n, binomials)?, 1.0, binomials)?;
    }
    let r = BoundedPolynomial::checked(Bernstein2::constant(radius), 0.0)?;
    let r_squared = r.mul(&r, binomials)?;
    let phi = squared.add(
        &w.mul(&w, binomials)?.mul(&r_squared, binomials)?,
        -1.0,
        binomials,
    )?;
    let differentiated = phi.derivative(true)?;
    let range = |p: &BoundedPolynomial| -> Result<Ivl> {
        let lo = (Ivl::from(p.polynomial.min_coefficient()) - Ivl::from(p.error)).lo;
        let hi = (Ivl::from(p.polynomial.max_coefficient()) + Ivl::from(p.error)).hi;
        let value = Ivl::new(lo, hi);
        if value.is_finite() {
            Ok(value)
        } else {
            Err(refused("a cap polynomial enclosure is not finite"))
        }
    };
    let endpoint = |last: bool| -> Result<Ivl> {
        let c = if last {
            phi.polynomial.coefficients().last()
        } else {
            phi.polynomial.coefficients().first()
        };
        let &c = c.ok_or_else(|| refused("a cap polynomial lacks an endpoint coefficient"))?;
        let value = Ivl::from(c) + Ivl::new(-phi.error, phi.error);
        if value.is_finite() {
            Ok(value)
        } else {
            Err(refused("a cap endpoint enclosure is not finite"))
        }
    };
    Ok(CurveCapBound {
        numerator: range(&phi)?,
        derivative: range(&differentiated)?,
        endpoints: [endpoint(false)?, endpoint(true)?],
    })
}

/// One local native Pascal table for all complete curve bounds in a command
/// stage. It borrows the SAME workflow counters, never starts a nested budget or
/// stores global/TLS state. This is numerical scratch, not a geometry token.
pub(crate) struct CurveBounds<'a> {
    k: &'a crate::Kernel,
    work: &'a super::super::work::MeshWork,
    binomials: Binomials,
}
impl<'a> CurveBounds<'a> {
    pub(crate) fn new(
        k: &'a crate::Kernel,
        work: &'a super::super::work::MeshWork,
    ) -> Result<Self> {
        let rows = MAX_DEGREE
            .checked_mul(2)
            .and_then(|n| n.checked_add(2))
            .ok_or_else(|| refused("binomial storage overflow"))?;
        let count = rows
            .checked_mul(rows)
            .ok_or_else(|| refused("binomial storage overflow"))?;
        work.spend_core(k, count)?;
        work.reserve_cells_core(k, count)?;
        Ok(Self {
            k,
            work,
            binomials: Binomials::for_degree(MAX_DEGREE)?,
        })
    }
    fn scratch(&self, cells: usize) -> Result<()> {
        // Preserve the existing operation allowance. Logical storage follows
        // the actual bounded polynomial producers, including copies/elevations.
        self.work.spend_core(self.k, 4096)?;
        self.work.reserve_cells_core(self.k, cells)
    }
    pub(crate) fn radial(
        &self,
        piece: &Piece,
        centre: PointBox,
        radius: f64,
    ) -> Result<CurveRadialBound> {
        let degree = piece.h.iter().map(|h| h.degrees().0).max().unwrap_or(0);
        let n = degree + 1;
        let squared = 2 * degree + 1;
        // The cap numerator producer:22N input/coordinate/copy coefficients,
        // 27M product/add/elevation coefficients, then4M-3 derivative/row
        // coefficients. Constants and container headroom contribute70 slots.
        // radial() itself adds scalar interval arithmetic, no coefficient Vec.
        self.scratch(22 * n + 31 * squared + 67)?;
        curve_radial_bound_with_binomials(piece, centre, radius, &self.binomials)
    }
    pub(crate) fn paired(&self, a: &Piece, b: &Piece) -> Result<f64> {
        let na = a.h.iter().map(|h| h.degrees().0 + 1).max().unwrap_or(1);
        let nb = b.h.iter().map(|h| h.degrees().0 + 1).max().unwrap_or(1);
        let product = na + nb - 1;
        // Two weights and three coordinate pairs:4(Na+Nb) copies.
        // Six products and three five-copy/result bounded adds:21M.
        // Residual Vec and container headroom:36 logical slots.
        self.scratch(4 * (na + nb) + 21 * product + 36)?;
        paired_curve_upper_with_binomials(a, b, 0., 0., &self.binomials)
    }
    pub(crate) fn context(&self) -> (&crate::Kernel, &super::super::work::MeshWork) {
        (self.k, self.work)
    }
    /// The existing orientation algebra, with its one table shared across every
    /// source/model cell. This is not an authority token or a native API normal.
    pub(crate) fn orientation(&self, piece: &Piece, normal: PointBox) -> Result<f64> {
        let [_, _, _, weights] = &piece.h;
        let (p, q) = weights.degrees();
        let top = p
            .checked_mul(4)
            .and_then(|n| n.checked_sub(1))
            .ok_or_else(|| refused("orientation profile degree overflow"))?;
        if q != 1 || top > MAX_DEGREE || piece.h.iter().any(|h| h.degrees() != (p, q)) {
            return Err(refused(
                "ruling orientation exceeds existing degree-eight algebra",
            ));
        }
        let count = top
            .checked_add(1)
            .and_then(|n| n.checked_mul(4))
            .ok_or_else(|| refused("orientation coefficient count overflow"))?;
        // Keep the same conservative convolution/error-scan work bound.
        // Storage instead follows the actual 21 products and12 bounded adds.
        // q=1 and top<=8 imply p=1 or2. Let N=2(p+1), U=6p,
        // V=2(2p+1), C=16p be the input/derivative/cross array lengths.
        // Four input copies cost4N. Each of four du/dv derivative pairs costs
        // (7p+1)+3(p+1), including temporary rows, inner vectors and up to
        // twice the flattened output length for Vec growth. The six derivative
        // products/adds cost21(U+V): two products and five copies/results per
        // bounded add. Cross products/adds cost21C. Projection costs18C plus
        // 2C for the initial constant's two elevation-one arrays. Its four
        // constants and64 container/header slots are also charged.
        // This counts cumulative logical cells, not a measured byte peak.
        // No numeric operation, rounding enclosure or workflow limit changes.
        let operations = count
            .checked_mul(count)
            .and_then(|n| n.checked_mul(128))
            .ok_or_else(|| refused("orientation work count overflow"))?;
        let input = 2 * (p + 1);
        let u = 6 * p;
        let v = 2 * (2 * p + 1);
        let cross = 16 * p;
        let cells = 4 * input + 4 * (7 * p + 1 + 3 * (p + 1)) + 21 * (u + v) + 41 * cross + 4 + 64;
        self.work.spend_core(self.k, operations)?;
        self.work.reserve_cells_core(self.k, cells)?;
        surface_orientation_lower_with_binomials(piece, normal, 0., &self.binomials)
    }
}

/// A WHOLE positive rational curve's radial projection onto the sphere about
/// `centre` of radius r. This is ONLY a polynomial lemma, not a native analytic
/// surface authority token, circle label, angular coverage or body acceptance.
pub(crate) struct CurveRadialBound {
    pub(crate) radius_lower: f64,
    pub(crate) radius_upper: f64,
    pub(crate) squared_residual_upper: f64,
    pub(crate) distance_upper: f64,
}
/// With phi=||H-CW||^2-r^2 W^2, `q=max|phi|/w_min^2` bounds
/// |rho^2-r^2| over EVERY parameter. If r^2-q>0, rho stays positive and
/// |rho-r|<=q/(sqrt(r^2-q)+r). This is exactly the distance to radial projection;
/// no point samples or the polar converter's `exact` flag establish it.
pub(crate) fn curve_radial_bound_with_work(
    k: &crate::Kernel,
    work: &super::super::work::MeshWork,
    piece: &Piece,
    centre: PointBox,
    radius: f64,
) -> Result<CurveRadialBound> {
    CurveBounds::new(k, work)?.radial(piece, centre, radius)
}
fn curve_radial_bound_with_binomials(
    piece: &Piece,
    centre: PointBox,
    radius: f64,
    binomials: &Binomials,
) -> Result<CurveRadialBound> {
    if piece
        .h
        .iter()
        .any(|h| h.degrees().1 != 0 || h.degrees().0 > 4)
    {
        return Err(refused(
            "radial normalization requires curve degree at most four",
        ));
    }
    let phi = curve_cap_bound_with_binomials(piece, centre, radius, 0., binomials)?;
    let [_, _, _, hw] = &piece.h;
    let weight = Ivl::from(hw.min_coefficient()) - Ivl::from(piece.err);
    if !weight.is_finite() || !weight.is_positive() {
        return Err(refused("radial normalization weights are not positive"));
    }
    let q = Ivl::from(phi.numerator.mag()) / (Ivl::from(weight.lo) * Ivl::from(weight.lo));
    let r = Ivl::from(radius);
    let squared = r * r - q;
    if !q.is_finite() || !squared.is_finite() || !squared.is_positive() {
        return Err(refused(
            "whole radial normalization is not proved away from its centre",
        ));
    }
    let rho = squared.sqrt();
    if !rho.is_finite() || !rho.is_positive() {
        return Err(refused("radial lower bound is not finite positive"));
    }
    let upper = q / (Ivl::from(rho.lo) + r);
    let radius_upper = finite((r * r + q).sqrt().hi)?;
    Ok(CurveRadialBound {
        radius_lower: rho.lo,
        radius_upper,
        squared_residual_upper: finite(q.hi)?,
        distance_upper: finite(upper.hi)?,
    })
}

/// Whole normalized-parameter distance between TWO positive rational curve pieces.
/// Homogeneous numerator `H_a` W_b-H_b `W_a` is bounded in native Bernstein algebra;
/// a positive `W_a` `W_b` lower bound encloses the complete difference. Equal Euclidean
/// control POINTS with different weights do not imply equal curves. Callers must
/// separately bind both actual/model objects and their complete parameter partition.
pub(crate) fn paired_curve_upper(a: &Piece, b: &Piece, slack_a: f64, slack_b: f64) -> Result<f64> {
    paired_curve_upper_with_binomials(a, b, slack_a, slack_b, &Binomials::for_degree(MAX_DEGREE)?)
}
fn paired_curve_upper_with_binomials(
    a: &Piece,
    b: &Piece,
    slack_a: f64,
    slack_b: f64,
    binomials: &Binomials,
) -> Result<f64> {
    if a.h.iter().chain(&b.h).any(|p| p.degrees().1 != 0)
        || !slack_a.is_finite()
        || slack_a < 0.
        || !slack_b.is_finite()
        || slack_b < 0.
    {
        return Err(refused(
            "paired curve pieces require finite complete curve bounds",
        ));
    }
    let ba = |p: &Bernstein2| BoundedPolynomial::checked(p.clone(), a.err);
    let bb = |p: &Bernstein2| BoundedPolynomial::checked(p.clone(), b.err);
    let [_, _, _, weight_a] = &a.h;
    let [_, _, _, weight_b] = &b.h;
    let wa = ba(weight_a)?;
    let wb = bb(weight_b)?;
    let lower_a = (Ivl::from(weight_a.min_coefficient()) - Ivl::from(a.err)).lo;
    let lower_b = (Ivl::from(weight_b.min_coefficient()) - Ivl::from(b.err)).lo;
    if !(lower_a > 0. && lower_b > 0. && lower_a.is_finite() && lower_b.is_finite()) {
        return Err(refused("paired curve weights are not proved positive"));
    }
    let denominator = Ivl::from(lower_a) * Ivl::from(lower_b);
    if !denominator.is_positive() || !denominator.is_finite() {
        return Err(refused("paired curve denominator is not finite positive"));
    }
    let mut residual = Vec::new();
    for (a_coordinate, b_coordinate) in a.h.iter().zip(&b.h).take(3) {
        let numerator = ba(a_coordinate)?.mul(&wb, binomials)?.add(
            &bb(b_coordinate)?.mul(&wa, binomials)?,
            -1.,
            binomials,
        )?;
        residual.push(
            (Ivl::from(numerator.polynomial.max_abs_coefficient()) + Ivl::from(numerator.error)).hi,
        );
    }
    let [Some(&x), Some(&y), Some(&z)] = [residual.first(), residual.get(1), residual.get(2)]
    else {
        return Err(refused("a paired curve residual lacks a coordinate"));
    };
    let norm = norm_upper([Ivl::from(x), Ivl::from(y), Ivl::from(z)])?;
    finite(
        (Ivl::from(norm) / Ivl::from(denominator.lo) + Ivl::from(slack_a) + Ivl::from(slack_b)).hi,
    )
}

/// A complete positive rational surface piece has this strictly positive
/// numerator for (`S_u` cross `S_v`) dot `normal`. Coefficient hulls cover the full
/// parameter rectangle. `normal` may be the exact raw source triangle's enclosed
/// oriented normal; it need not be normalized to establish the sign.
///
/// This excludes local folds/reversal only. A coherent global chart, oriented map
/// determinant, boundary degree/nesting, seams/poles and movement-tube separation
/// are still mandatory for final topology acceptance. A value-only definition slack
/// proves no derivative sign and therefore refuses here.
#[cfg(test)]
pub(crate) fn surface_orientation_lower(
    piece: &Piece,
    normal: PointBox,
    slack: f64,
) -> Result<f64> {
    orientation_input(normal, slack)?;
    let binomials = Binomials::new();
    surface_orientation_lower_with_binomials(piece, normal, slack, &binomials)
}
fn surface_orientation_lower_with_binomials(
    piece: &Piece,
    normal: PointBox,
    slack: f64,
    binomials: &Binomials,
) -> Result<f64> {
    orientation_input(normal, slack)?;

    let [hx, hy, hz, hw] = &piece.h;
    let bounded = |p: &Bernstein2| BoundedPolynomial::checked(p.clone(), piece.err);
    let w = bounded(hw)?;
    if !(Ivl::from(hw.min_coefficient()) - Ivl::from(piece.err)).is_positive() {
        return Err(refused(
            "surface orientation weights are not proved positive",
        ));
    }
    let wu = w.derivative(true)?;
    let wv = w.derivative(false)?;
    let mut us = Vec::new();
    let mut vs = Vec::new();
    for h in [hx, hy, hz] {
        let h = bounded(h)?;
        us.push(h.derivative(true)?.mul(&w, binomials)?.add(
            &h.mul(&wu, binomials)?,
            -1.0,
            binomials,
        )?);
        vs.push(h.derivative(false)?.mul(&w, binomials)?.add(
            &h.mul(&wv, binomials)?,
            -1.0,
            binomials,
        )?);
    }
    let [Some(ux), Some(uy), Some(uz), Some(vx), Some(vy), Some(vz)] = [
        us.first(),
        us.get(1),
        us.get(2),
        vs.first(),
        vs.get(1),
        vs.get(2),
    ] else {
        return Err(refused("a surface derivative numerator lacks a coordinate"));
    };
    let cross = [
        uy.mul(vz, binomials)?
            .add(&uz.mul(vy, binomials)?, -1.0, binomials)?,
        uz.mul(vx, binomials)?
            .add(&ux.mul(vz, binomials)?, -1.0, binomials)?,
        ux.mul(vy, binomials)?
            .add(&uy.mul(vx, binomials)?, -1.0, binomials)?,
    ];
    let mut projected = BoundedPolynomial::constant(0.0, 0.0);
    for (c, n) in cross.into_iter().zip(normal) {
        let middle = 0.5 * n.lo + 0.5 * n.hi;
        let n = BoundedPolynomial::constant(middle, (n - Ivl::from(middle)).mag());
        projected = projected.add(&c.mul(&n, binomials)?, 1.0, binomials)?;
    }
    let lower = (Ivl::from(projected.polynomial.min_coefficient()) - Ivl::from(projected.error)).lo;
    if lower > 0.0 && lower.is_finite() {
        Ok(lower)
    } else {
        Err(refused(
            "the complete surface orientation is not proved positive",
        ))
    }
}

fn orientation_input(normal: PointBox, slack: f64) -> Result<()> {
    if slack != 0.0 {
        return Err(refused(
            "a value-only surface definition bound cannot certify orientation",
        ));
    }
    if normal.iter().any(|v| !v.is_finite()) {
        return Err(refused("the source orientation is not finite"));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn exact(x: f64, y: f64, z: f64) -> PointBox {
        [Ivl::from(x), Ivl::from(y), Ivl::from(z)]
    }
    fn piece(x: Vec<f64>, y: Vec<f64>, z: Vec<f64>, w: Vec<f64>, degree: (usize, usize)) -> Piece {
        Piece {
            h: [x, y, z, w].map(|p| Bernstein2::new(degree.0, degree.1, p).unwrap()),
            err: 0.0,
            lower: 0.0,
            depth: 0,
            uv: [0.0, 1.0, 0.0, 1.0],
            parameter_ends: [0.0, 1.0, 0.0, 1.0].map(Ivl::from),
        }
    }

    #[test]
    fn repeated_complete_curve_bounds_keep_same_arithmetic_and_shared_budget() {
        let k = crate::Kernel::default();
        let work = super::super::super::work::MeshWork::new();
        let curve = piece(vec![1.25; 3], vec![0.; 3], vec![0.; 3], vec![1.; 3], (2, 0));
        let centre = exact(0., 0., 0.);
        let full = Binomials::new();
        let expected_pair =
            paired_curve_upper_with_binomials(&curve, &curve, 0., 0., &full).unwrap();
        let expected_radial = curve_radial_bound_with_binomials(&curve, centre, 1., &full).unwrap();
        let bounds = CurveBounds::new(&k, &work).unwrap();
        for _ in 0..512 {
            assert_eq!(
                bounds.paired(&curve, &curve).unwrap().to_bits(),
                expected_pair.to_bits()
            );
            let actual = bounds.radial(&curve, centre, 1.).unwrap();
            assert_eq!(
                actual.distance_upper.to_bits(),
                expected_radial.distance_upper.to_bits()
            );
            assert_eq!(
                actual.radius_lower.to_bits(),
                expected_radial.radius_lower.to_bits()
            );
            assert_eq!(
                actual.radius_upper.to_bits(),
                expected_radial.radius_upper.to_bits()
            );
            assert_eq!(
                actual.squared_residual_upper.to_bits(),
                expected_radial.squared_residual_upper.to_bits()
            );
        }
        assert!(work.check(&k).is_ok());
    }

    #[test]
    fn bounded_native_pascal_table_retains_every_used_coefficient() {
        let full = Binomials::new();
        let bounded = Binomials::for_degree(MAX_DEGREE).unwrap();
        for n in 0..=2 * MAX_DEGREE {
            for k in 0..=n {
                assert_eq!(bounded.get(n, k).to_bits(), full.get(n, k).to_bits());
            }
        }
        assert!(
            Binomials::for_degree(crate::offset::construction::bernstein::MAX_DEGREE + 1).is_err()
        );
    }

    #[test]
    fn repeated_whole_ruling_orientation_keeps_same_numeric_proof_and_budget() {
        let k = crate::Kernel::default();
        let work = super::super::super::work::MeshWork::new();
        // A degree-two representation of the whole plane S(u,v)=(u,v,0).
        let surface = piece(
            vec![0., 0., 0.5, 0.5, 1., 1.],
            vec![0., 1., 0., 1., 0., 1.],
            vec![0.; 6],
            vec![1.; 6],
            (2, 1),
        );
        let normal = exact(0., 0., 1.);
        let expected = surface_orientation_lower(&surface, normal, 0.).unwrap();
        let bounds = CurveBounds::new(&k, &work).unwrap();
        for _ in 0..512 {
            assert_eq!(
                bounds.orientation(&surface, normal).unwrap().to_bits(),
                expected.to_bits()
            );
        }
        let depleted = super::super::super::work::MeshWork::new();
        depleted.reserve_cells_core(&k, 1_999_999).unwrap();
        assert!(CurveBounds::new(&k, &depleted).is_err());
        assert!(work.check(&k).is_ok());
    }

    #[test]
    fn a_centre_witness_does_not_certify_a_large_triangle() {
        let triangle = [
            exact(0.0, 0.0, 0.0),
            exact(12.0, 0.0, 0.0),
            exact(0.0, 12.0, 0.0),
        ];
        assert!(triangle_point_upper(&triangle, exact(4.0, 4.0, 0.0)).unwrap() > 8.0);
    }

    #[test]
    fn a_complete_plane_correspondence_has_only_rounding_error() {
        let plane = piece(
            vec![0.0, 0.0, 12.0, 12.0],
            vec![0.0, 12.0, 0.0, 12.0],
            vec![0.0; 4],
            vec![1.0; 4],
            (1, 1),
        );
        let triangle = [
            exact(0.0, 0.0, 0.0),
            exact(12.0, 0.0, 0.0),
            exact(0.0, 12.0, 0.0),
        ];
        assert!(
            correspondence_upper(&plane, &triangle, [[0.0, 0.0], [1.0, 0.0], [0.0, 1.0]], 0.0)
                .unwrap()
                < 1e-9
        );
    }

    #[test]
    fn matching_vertices_do_not_hide_a_patch_interior_bulge() {
        let bulge = piece(
            vec![0.0, 0.0, 0.0, 0.5, 0.5, 0.5, 1.0, 1.0, 1.0],
            vec![0.0, 0.5, 1.0, 0.0, 0.5, 1.0, 0.0, 0.5, 1.0],
            vec![0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0],
            vec![1.0; 9],
            (2, 2),
        );
        let triangle = [
            exact(0.0, 0.0, 0.0),
            exact(1.0, 0.0, 0.0),
            exact(0.0, 1.0, 0.0),
        ];
        assert!(
            correspondence_upper(&bulge, &triangle, [[0.0, 0.0], [1.0, 0.0], [0.0, 1.0]], 0.0)
                .unwrap()
                > 0.05
        );
    }

    #[test]
    fn different_source_triangles_per_control_would_be_unsound() {
        let bridge = piece(
            vec![0.0, 0.0, 10.0, 10.0],
            vec![0.0, 1.0, 0.0, 1.0],
            vec![0.0; 4],
            vec![1.0; 4],
            (1, 1),
        );
        let left = [
            exact(0.0, -2.0, 0.0),
            exact(0.0, 2.0, 0.0),
            exact(0.0, 0.0, 2.0),
        ];
        let right = [
            exact(10.0, -2.0, 0.0),
            exact(10.0, 2.0, 0.0),
            exact(10.0, 0.0, 2.0),
        ];
        assert!(piece_triangle_upper(&bridge, &left, 0.0).unwrap() > 9.0);
        assert!(piece_triangle_upper(&bridge, &right, 0.0).unwrap() > 9.0);
    }

    #[test]
    fn unproved_weights_are_not_a_certificate() {
        let invalid = piece(
            vec![0.0; 4],
            vec![0.0; 4],
            vec![0.0; 4],
            vec![0.0; 4],
            (1, 1),
        );
        let source = [
            exact(0.0, 0.0, 0.0),
            exact(1.0, 0.0, 0.0),
            exact(0.0, 1.0, 0.0),
        ];
        assert!(piece_triangle_upper(&invalid, &source, 0.0).is_err());
        assert!(
            correspondence_upper(&invalid, &source, [[0.0, 0.0], [1.0, 0.0], [0.0, 1.0]], 0.0)
                .is_err()
        );
    }
    #[test]
    fn a_whole_edge_graph_has_a_positive_orientation_bound() {
        let line = piece(
            vec![0.0, 4.0],
            vec![0.0; 2],
            vec![0.0; 2],
            vec![1.0; 2],
            (1, 0),
        );
        let bound =
            curve_graph_bound(&line, [exact(0.0, 0.0, 0.0), exact(4.0, 0.0, 0.0)], 0.0).unwrap();
        assert!(bound.distance_upper < 1e-9);
        assert!(bound.projection_numerator_lower > 15.0);
    }
    #[test]
    fn reversed_edge_parameterization_cannot_pass_an_oriented_graph_proof() {
        let line = piece(
            vec![4.0, 0.0],
            vec![0.0; 2],
            vec![0.0; 2],
            vec![1.0; 2],
            (1, 0),
        );
        assert!(
            curve_graph_bound(&line, [exact(0.0, 0.0, 0.0), exact(4.0, 0.0, 0.0)], 0.0).is_err()
        );
    }
    #[test]
    fn a_complete_plane_has_a_strict_oriented_normal_bound() {
        let plane = piece(
            vec![0.0, 0.0, 4.0, 4.0],
            vec![0.0, 3.0, 0.0, 3.0],
            vec![0.0; 4],
            vec![1.0; 4],
            (1, 1),
        );
        assert!(surface_orientation_lower(&plane, exact(0.0, 0.0, 1.0), 0.0).unwrap() > 11.0);
        assert!(surface_orientation_lower(&plane, exact(0.0, 0.0, -1.0), 0.0).is_err());
        assert!(surface_orientation_lower(&plane, exact(0.0, 0.0, 1.0), 1e-6).is_err());
    }
    #[test]
    fn arbitrary_nondyadic_curve_restriction_carries_rounding_and_parameter_error() {
        let line = piece(
            vec![0.0, 7.0],
            vec![0.0; 2],
            vec![0.0; 2],
            vec![1.0; 2],
            (1, 0),
        );
        let cut = line.restricted_u(1.0 / 3.0, 2.0 / 3.0).unwrap();
        assert!(cut.err > 0.0);
        let bound = curve_graph_bound(
            &cut,
            [exact(7.0 / 3.0, 0.0, 0.0), exact(14.0 / 3.0, 0.0, 0.0)],
            0.0,
        )
        .unwrap();
        assert!(bound.distance_upper < 1e-9);
        assert!(bound.projection_numerator_lower > 0.0);
        assert!(line.restricted_u(0.8, 0.2).is_err());
    }
    #[test]
    fn cap_predicate_isolates_a_whole_monotone_exit() {
        let p = piece(
            vec![0.25, 1.0],
            vec![0.0; 2],
            vec![0.0; 2],
            vec![1.0; 2],
            (1, 0),
        );
        let b = curve_cap_bound(&p, exact(0.0, 0.0, 0.0), 0.5, 0.0).unwrap();
        assert!(b.endpoints[0].hi < 0.0);
        assert!(b.endpoints[1].lo > 0.0);
        assert!(b.derivative.lo > 0.0);
    }

    #[test]
    fn cap_endpoints_cannot_hide_an_interior_return() {
        let p = piece(
            vec![0.25, 2.0, -2.0, 1.0],
            vec![0.0; 4],
            vec![0.0; 4],
            vec![1.0; 4],
            (3, 0),
        );
        let b = curve_cap_bound(&p, exact(0.0, 0.0, 0.0), 0.5, 0.0).unwrap();
        assert!(b.endpoints[0].hi < 0.0 && b.endpoints[1].lo > 0.0);
        assert!(b.derivative.lo <= 0.0);
    }
    #[test]
    fn paired_rational_curve_bound_covers_complete_equal_parameter_images() {
        let a = piece(
            vec![0., 1., 2.],
            vec![0., 2., 0.],
            vec![0.; 3],
            vec![1.; 3],
            (2, 0),
        );
        let b = piece(
            vec![0., 1., 2.],
            vec![0., 2., 0.],
            vec![0.; 3],
            vec![1.; 3],
            (2, 0),
        );
        assert!(paired_curve_upper(&a, &b, 0., 0.).unwrap() < 1e-10);
    }
    #[test]
    fn equal_euclidean_controls_with_different_weights_are_not_equal_curves() {
        let a = piece(
            vec![0., 1., 2.],
            vec![0., 2., 0.],
            vec![0.; 3],
            vec![1.; 3],
            (2, 0),
        );
        let b = piece(
            vec![0., 4., 2.],
            vec![0., 8., 0.],
            vec![0.; 3],
            vec![1., 4., 1.],
            (2, 0),
        );
        // Both nets have Euclidean controls(0,0),(1,2),(2,0), but their
        // actual midpoint heights are1 and1.6. Pointwise control equality
        // would falsely accept; the complete rational bound cannot be zero.
        assert!(paired_curve_upper(&a, &b, 0., 0.).unwrap() >= 0.6);
    }
    #[test]
    fn full_native_cylinder_and_frustum_polar_roots_have_whole_radial_bounds() {
        use crate::math::Vec3;
        use crate::mesh_reconstruction::{actual_roots::actual_roots, MeshWork};
        use crate::surface::cone::Cone;
        let k = crate::Kernel::default();
        for cone in [false, true] {
            for swap in [false, true] {
                for reverse in [false, true] {
                    let w = MeshWork::new();
                    let mut surface = if cone {
                        Cone::new_bounded(
                            Vec3::ZERO,
                            Vec3::X,
                            Vec3::Y,
                            3.,
                            2.,
                            0.,
                            360.,
                            5.,
                            swap,
                            reverse,
                            false,
                        )
                    } else {
                        Cone::new_cylinder_bounded(
                            Vec3::ZERO,
                            Vec3::X,
                            Vec3::Y,
                            3.,
                            0.,
                            360.,
                            5.,
                            swap,
                            reverse,
                            false,
                        )
                    };
                    surface.make_nurb(&k).unwrap();
                    let owner = surface.rev().polar_curve.as_ref().unwrap();
                    let polar = surface.rev().polar_curve().unwrap();
                    let o = polar.position().origin();
                    let roots = actual_roots(&k, &w, owner, true).unwrap();
                    assert_eq!(roots.len(), 4, "every natural polar root is required");
                    assert_eq!(
                        roots.first().unwrap().native_interval[0],
                        polar.base().natural_interval().min()
                    );
                    assert_eq!(
                        roots.last().unwrap().native_interval[1],
                        polar.base().natural_interval().max()
                    );
                    for pair in roots.windows(2) {
                        assert_eq!(pair[0].native_interval[1], pair[1].native_interval[0]);
                    }
                    for root in roots {
                        let bound = curve_radial_bound_with_work(
                            &k,
                            &w,
                            &root.piece,
                            exact(o.x, o.y, o.z),
                            polar.x_radius(),
                        )
                        .unwrap();
                        assert!(bound.radius_lower > 0.);
                        assert!(
                            bound.distance_upper < 1e-9,
                            "{cone}/{swap}/{reverse}: {}",
                            bound.distance_upper
                        );
                    }
                }
            }
        }
    }
    #[test]
    fn whole_radial_bound_refuses_centre_crossing_and_bounds_a_known_offset() {
        let k = crate::Kernel::default();
        let w = super::super::super::work::MeshWork::new();
        let crossing = piece(
            vec![-1., 1.],
            vec![0., 0.],
            vec![0., 0.],
            vec![1., 1.],
            (1, 0),
        );
        assert!(curve_radial_bound_with_work(&k, &w, &crossing, exact(0., 0., 0.), 1.).is_err());
        let outside = piece(
            vec![1.25, 1.25],
            vec![0., 0.],
            vec![0., 0.],
            vec![1., 1.],
            (1, 0),
        );
        let bound = curve_radial_bound_with_work(&k, &w, &outside, exact(0., 0., 0.), 1.).unwrap();
        assert!(bound.distance_upper >= 0.25);
        assert!(curve_radial_bound_with_work(&k, &w, &outside, exact(0., 0., 0.), 0.).is_err());
    }
}
