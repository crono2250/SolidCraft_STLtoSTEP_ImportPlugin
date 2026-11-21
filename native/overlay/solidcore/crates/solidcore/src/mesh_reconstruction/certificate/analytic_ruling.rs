//! Full natural-domain value authority for a bounded native circular Cone/Cylinder.
//!
//! S is the ACTUAL polar-inverting STEP evaluator, not its label or cached net.
//! All positive rational roots are covered; two same-weight ruling rows bind the
//! SAME stored net to a projected-polar reference. Whole radial normalization,
//! native endpoint/context/late-period seam branches and all affine heights are
//! bounded under the existing certified.rs one-ulp libm arithmetic model.
//! This is a value band only. Model embedding, cap/edge/vertex zones, trims, CW,
//! orientation and material remain independent mandatory consumers. No token is
//! returned for an incomplete branch, partial angular domain or unbounded height.
//! Deviations: none. At most64 roots, shared `MeshWork`, no recursion or samples.
use super::super::actual_roots::{actual_roots, ActualRoot};
use super::super::{MeshError, MeshWork};
use super::hulls::{CurveBounds, PointBox};
use crate::blend::fillet_section::interval::{round_up, Ivl};
use crate::geom::certified::{gamma, UNDERFLOW_ROOT};
use crate::geom::tol::{context_zone_tol_3d, SmallTopoType};
use crate::math::{Vec3, EFF_ZERO, EFF_ZERO_DEG, PI};
use crate::nurbs::{
    b_spline_curve::BSplineCurve,
    crv_basic,
    math::{CPoint, NOW, NOZ},
};
use crate::offset::construction::bernstein::Bernstein2;
use crate::query::distance_bound::Piece;
use crate::surface::{
    cone::Cone,
    surface::{Surface, SurfaceKind},
};
use crate::{Kernel, Result, SolidError};
const OP: &str = "mesh_reconstruction::certificate::analytic_ruling";
const ROOT_LIMIT: usize = 64;
fn no(s: &'static str) -> SolidError {
    SolidError::Unsupported {
        operation: OP,
        reason: s,
    }
}
fn inv(s: &'static str) -> SolidError {
    SolidError::PortInvariant {
        operation: OP,
        reason: s,
    }
}
fn finite(v: Ivl) -> Result<Ivl> {
    if v.is_finite() {
        Ok(v)
    } else {
        Err(no("analytic arithmetic interval is not finite"))
    }
}
fn upper(v: Ivl) -> Result<f64> {
    let v = finite(v)?;
    if v.hi >= 0. {
        Ok(v.hi)
    } else {
        Err(no("analytic error is negative"))
    }
}
fn norm(v: PointBox) -> Result<f64> {
    let [x, y, z] = v.map(|a| Ivl::from(a.mag()));
    upper((x * x + y * y + z * z).sqrt())
}
fn xy_norm(v: [Ivl; 2]) -> Result<f64> {
    let [x, y] = v.map(|a| Ivl::from(a.mag()));
    upper((x * x + y * y).sqrt())
}
fn vec(v: Vec3) -> PointBox {
    [v.x, v.y, v.z].map(Ivl::from)
}
fn dot(a: PointBox, b: PointBox) -> Ivl {
    a.into_iter()
        .zip(b)
        .fold(Ivl::from(0.), |v, (a, b)| v + a * b)
}
fn cross(lhs: PointBox, rhs: PointBox) -> PointBox {
    let [a, b, c] = lhs;
    let [d, e, f] = rhs;
    [b * f - c * e, c * d - a * f, a * e - b * d]
}
fn add(lhs: PointBox, rhs: PointBox) -> PointBox {
    let [a, b, c] = lhs;
    let [d, e, f] = rhs;
    [a + d, b + e, c + f]
}
fn mul(a: PointBox, b: Ivl) -> PointBox {
    a.map(|a| a * b)
}
fn native<T>(k: &Kernel, w: &MeshWork, r: super::super::Result<T>) -> Result<T> {
    w.spend_core(k, 0)?;
    match r {
        Ok(v) => Ok(v),
        Err(MeshError::Kernel(e)) => Err(e),
        Err(MeshError::Refused { .. } | MeshError::Undecided { .. }) => {
            Err(no("complete actual polar/model root extraction unresolved"))
        }
        Err(_) => Err(inv("unexpected native root result")),
    }
}
/// An immutable all-branch value certificate, deliberately not Clone or a body token.
pub(crate) struct AnalyticNetAuthority<'a> {
    kernel: &'a Kernel,
    definition: &'a Surface,
    domain: [f64; 4],
    upper: f64,
    roots: usize,
}
impl<'a> AnalyticNetAuthority<'a> {
    pub(crate) fn kernel(&self) -> &'a Kernel {
        self.kernel
    }
    pub(crate) fn definition(&self) -> &'a Surface {
        self.definition
    }
    pub(crate) fn domain(&self) -> [f64; 4] {
        self.domain
    }
    pub(crate) fn distance_upper(&self) -> f64 {
        self.upper
    }
    pub(crate) fn covered_roots(&self) -> usize {
        self.roots
    }
}
fn piece(
    k: &Kernel,
    w: &MeshWork,
    coordinates: impl IntoIterator<Item = [Ivl; 4]>,
    degree: usize,
) -> Result<Piece> {
    let mut h: [Vec<f64>; 4] = core::array::from_fn(|_| Vec::new());
    let mut err = 0_f64;
    for row in coordinates {
        w.spend_core(k, 4)?;
        w.reserve_cells_core(k, 4)?;
        for (out, v) in h.iter_mut().zip(row) {
            let v = finite(v)?;
            let m = 0.5 * v.lo + 0.5 * v.hi;
            err = err.max((v - Ivl::from(m)).mag());
            out.push(m);
        }
    }
    let [x, y, z, a] = h;
    Ok(Piece {
        h: [
            Bernstein2::new(degree, 0, x)?,
            Bernstein2::new(degree, 0, y)?,
            Bernstein2::new(degree, 0, z)?,
            Bernstein2::new(degree, 0, a)?,
        ],
        err,
        lower: 0.,
        depth: 0,
        uv: [0., 1., 0., 0.],
        parameter_ends: [Ivl::from(0.), Ivl::from(1.), Ivl::from(0.), Ivl::from(0.)],
    })
}
fn controls(p: &Piece) -> Result<impl Iterator<Item = [Ivl; 4]> + '_> {
    let [a, b, c, d] = &p.h;
    let n = a.coefficients().len();
    if [b, c, d].iter().any(|v| v.coefficients().len() != n) {
        return Err(inv("homogeneous control counts disagree"));
    }
    let e = Ivl::new(-p.err, p.err);
    Ok(a.coefficients()
        .iter()
        .zip(b.coefficients())
        .zip(c.coefficients())
        .zip(d.coefficients())
        .map(move |(((&a, &b), &c), &d)| {
            [
                Ivl::from(a) + e,
                Ivl::from(b) + e,
                Ivl::from(c) + e,
                Ivl::from(d) + e,
            ]
        }))
}
fn box_of(p: &Piece) -> Result<PointBox> {
    let [hx, hy, hz, hw] = &p.h;
    let e = Ivl::new(-p.err, p.err);
    let weight = finite(Ivl::new(hw.min_coefficient(), hw.max_coefficient()) + e)?;
    if !weight.is_positive() {
        return Err(no("complete curve weights are not positive"));
    }
    let coordinate =
        |h: &Bernstein2| finite((Ivl::new(h.min_coefficient(), h.max_coefficient()) + e) / weight);
    Ok([coordinate(hx)?, coordinate(hy)?, coordinate(hz)?])
}
fn containing<'a>(
    k: &Kernel,
    w: &MeshWork,
    roots: &'a [ActualRoot],
    a: f64,
    b: f64,
) -> Result<&'a ActualRoot> {
    w.spend_core(k, roots.len())?;
    roots
        .iter()
        .find(|r| {
            let [l, h] = r.native_interval;
            l <= a && b <= h
        })
        .ok_or_else(|| no("union partition has an uncovered native cell"))
}

fn project(
    k: &Kernel,
    w: &MeshWork,
    p: &Piece,
    o: PointBox,
    x: PointBox,
    y: PointBox,
) -> Result<Piece> {
    w.spend_core(
        k,
        p.h.first()
            .ok_or_else(|| inv("curve controls absent"))?
            .coefficients()
            .len()
            .checked_mul(128)
            .ok_or_else(|| no("projection count overflow"))?,
    )?;
    let rows = controls(p)?.map(|[a, b, c, weight]| {
        let d = add([a, b, c], mul(o, Ivl::from(-1.) * weight));
        [dot(d, x), dot(d, y), Ivl::from(0.), weight]
    });
    piece(
        k,
        w,
        rows,
        p.h.first()
            .ok_or_else(|| inv("curve controls absent"))?
            .degrees()
            .0,
    )
}
fn reference(
    k: &Kernel,
    w: &MeshWork,
    q: &Piece,
    rp: f64,
    r: Ivl,
    h: f64,
    o: PointBox,
    x: PointBox,
    y: PointBox,
    z: PointBox,
) -> Result<Piece> {
    // W_ref=rp*W: no rounded R/rp defines the reference. The interval row encloses
    // every common allowed radius slope; convex same-weight ruling interpolation
    // below bounds ALL heights, not merely the two inspected meridians.
    w.spend_core(
        k,
        q.h.first()
            .ok_or_else(|| inv("curve controls absent"))?
            .coefficients()
            .len()
            .checked_mul(128)
            .ok_or_else(|| no("reference count overflow"))?,
    )?;
    let centre = add(o, mul(z, Ivl::from(h)));
    let rows = controls(q)?.map(|[qx, qy, _, weight]| {
        let denominator = Ivl::from(rp) * weight;
        let v = add(
            mul(centre, denominator),
            mul(add(mul(x, qx), mul(y, qy)), r),
        );
        let [a, b, c] = v;
        [a, b, c, denominator]
    });
    piece(
        k,
        w,
        rows,
        q.h.first()
            .ok_or_else(|| inv("polar controls absent"))?
            .degrees()
            .0,
    )
}
fn partition(k: &Kernel, w: &MeshWork, roots: &[ActualRoot], ends: [f64; 2]) -> Result<()> {
    if roots.is_empty() || roots.len() > ROOT_LIMIT {
        return Err(no("full natural root count unsupported"));
    }
    let mut at = ends
        .first()
        .copied()
        .ok_or_else(|| inv("interval missing"))?;
    for r in roots {
        w.spend_core(k, 1)?;
        let [a, b] = r.native_interval;
        if a != at || !a.is_finite() || !b.is_finite() || a >= b {
            return Err(no(
                "native roots do not cover one complete ordered natural interval",
            ));
        }
        at = b;
    }
    if Some(&at) != ends.last() {
        return Err(no("native full natural interval has an uncovered end"));
    }
    Ok(())
}
/// Restrict at EXACT native break values. Numerical fractions only choose
/// Bernstein operations; interval fractions enclose the intended exact values.
/// The existing blossom Lipschitz bound carries the EXTRA fraction discrepancy.
fn restrict(k: &Kernel, w: &MeshWork, root: &ActualRoot, a: f64, b: f64) -> Result<Piece> {
    let [l, r] = root.native_interval;
    if !(l <= a && a < b && b <= r) {
        return Err(no("native restriction outside root"));
    }
    let unit = |v: f64| -> Result<(f64, Ivl)> {
        if v == l {
            return Ok((0., Ivl::from(0.)));
        }
        if v == r {
            return Ok((1., Ivl::from(1.)));
        }
        let exact = finite((Ivl::from(v) - Ivl::from(l)) / (Ivl::from(r) - Ivl::from(l)))?;
        let hint = (v - l) / (r - l);
        if !(0. < hint && hint < 1.) {
            return Err(no("native restriction fraction unresolved"));
        }
        Ok((hint, exact))
    };
    let (fa, ea) = unit(a)?;
    let (fb, eb) = unit(b)?;
    w.spend_core(k, 64)?;
    w.reserve_cells_core(k, 64)?;
    let mut p = root.piece.restricted_u(fa, fb)?;
    let delta = (Ivl::from(fa) - ea).mag().max((Ivl::from(fb) - eb).mag());
    let (degree, _) = root
        .piece
        .h
        .first()
        .ok_or_else(|| inv("root polynomial absent"))?
        .degrees();
    let d = u32::try_from(degree).map_err(|_| no("root degree overflow"))?;
    let m = root
        .piece
        .h
        .iter()
        .map(Bernstein2::max_abs_coefficient)
        .fold(0_f64, f64::max);
    p.err = upper(
        Ivl::from(p.err)
            + Ivl::from(2.)
                * Ivl::from(f64::from(d))
                * (Ivl::from(m) + Ivl::from(root.piece.err))
                * Ivl::from(delta),
    )?;
    p.uv = [a, b, 0., 0.];
    p.parameter_ends = [Ivl::from(a), Ivl::from(b), Ivl::from(0.), Ivl::from(0.)];
    Ok(p)
}
fn slope(c: &Cone) -> Result<Ivl> {
    let a = c.semi_angle_deg();
    if !a.is_finite() {
        return Err(no("semi-angle is not finite"));
    }
    if c.is_cylinder_class() && a != 0. {
        return Err(no("cylinder flag contradicts stored radius law"));
    }
    // Native deg2rad is a*(PI/180), not a*PI/180. The mathematical PI is
    // enclosed by its adjacent doubles; include BOTH native and mathematical angles.
    let true_pi = Ivl::new(
        -crate::geom::certified::next_up(-PI),
        crate::geom::certified::next_up(PI),
    );
    let exact = finite(Ivl::from(a) * true_pi / Ivl::from(180.))?;
    let input = a * (PI / 180.);
    let angle = Ivl::new(exact.lo.min(input), exact.hi.max(input));
    let reach = angle.mag();
    if reach.partial_cmp(&(true_pi.lo * 0.5)) != Some(core::cmp::Ordering::Less) {
        return Err(no("radius slope crosses a tangent pole"));
    }
    // cos decreases on [0,pi/2]. Existing one-ulp model, not a new libm guarantee.
    let cosine = reach.cos();
    let cosine_lower = (Ivl::from(cosine)
        - Ivl::from(f64::EPSILON) * Ivl::from(cosine.abs())
            / (Ivl::from(1.) - Ivl::from(f64::EPSILON))
        - Ivl::from(f64::MIN_POSITIVE))
    .lo;
    if cosine_lower.partial_cmp(&0.) != Some(core::cmp::Ordering::Greater) {
        return Err(no("radius slope lacks a positive cosine lower bound"));
    }
    let tangent = c.tan_semi_angle();
    if !tangent.is_finite() {
        return Err(no("stored tangent is not finite"));
    }
    let delta = (angle - Ivl::from(input)).mag();
    let e = finite(
        Ivl::from(delta) / (Ivl::from(cosine_lower) * Ivl::from(cosine_lower))
            + Ivl::from(f64::EPSILON) * Ivl::from(tangent.abs())
                / (Ivl::from(1.) - Ivl::from(f64::EPSILON))
            + Ivl::from(f64::MIN_POSITIVE),
    )?;
    // Each actual call may round within the EXISTING one-ulp model. Two such
    // results are separated by at most twice that allowance.
    finite(Ivl::from(tangent) + Ivl::new(-2. * e.hi, 2. * e.hi))
}
/// Forward error of the ACTUAL native basis/MAC evaluation, not a sampled
/// evaluation or a second curve implementation. The caller supplies an original
/// full-multiplicity root from `actual_roots` and the ORIGINAL representation bit.
fn eval_error(k: &Kernel, w: &MeshWork, root: &ActualRoot, rational: bool) -> Result<f64> {
    let p = &root.piece;
    let (degree, vdegree) =
        p.h.first()
            .ok_or_else(|| inv("polar polynomial absent"))?
            .degrees();
    if degree == 0 || degree > 4 || vdegree != 0 || p.err != 0. {
        return Err(no(
            "native evaluation needs exact original degree-one-through-four controls",
        ));
    }
    let q = degree
        .checked_add(1)
        .ok_or_else(|| no("evaluation count overflow"))?;
    if p.h
        .iter()
        .any(|h| h.degrees() != (degree, 0) || h.coefficients().len() != q)
    {
        return Err(inv(
            "original native polar root shape differs from basis input",
        ));
    }
    w.spend_core(
        k,
        q.checked_mul(128)
            .ok_or_else(|| no("evaluation work overflow"))?,
    )?;
    // Full multiplicity p at every interior break is established by actual_roots.
    // In the native basis loop, every left[k]=fl(t-l), right[k]=fl(r-t).
    // Both are nonnegative throughout this span, so each delta lies inside
    // (1 +/- gamma3)*(r-l). This ALSO proves its existing Degenerate branch
    // cannot be ignored into UNDEF by the polar inverter. All spans are checked;
    // outer natural endpoints return their controls without entering this loop.
    let [l, r] = root.native_interval;
    let span = finite(Ivl::from(r) - Ivl::from(l))?;
    let g3 = Ivl::from(round_up(gamma(3)));
    let delta_lower = finite((Ivl::from(1.) - g3) * span)?;
    let delta_upper = finite((Ivl::from(1.) + g3) * span)?;
    if !(l.is_finite()
        && r.is_finite()
        && l < r
        && delta_lower.lo > crate::math::EFF_ZERO_SQ
        && delta_upper.hi < f64::MAX)
    {
        return Err(no("whole native basis denominator/status is not proved"));
    }
    let one = Ivl::from(1.);
    let two = Ivl::from(2.);
    let unit = Ivl::from(f64::EPSILON * 0.5);
    // Absolute floating underflow allowance, NOT a geometric tolerance.
    // MIN_POSITIVE conservatively exceeds half the smallest subnormal.
    let tiny = Ivl::from(f64::MIN_POSITIVE);
    let g4 = Ivl::from(round_up(gamma(4)));
    let a = (one + unit) * (one + unit) * (one + g4 + two * tiny);
    let mut additive = Ivl::from(0.);
    for level in 1..=degree {
        let n = u32::try_from(level).map_err(|_| no("basis degree overflow"))?;
        let prior = Ivl::from(round_up(gamma(6 * (level - 1))));
        // At level k: two ratios,2k products,k additions. Propagation is
        // nonnegative; their absolute errors have this complete L1 recurrence.
        let b = (two * (one + unit) * (one + unit) * (one + prior)
            + Ivl::from(f64::from(n)) * (Ivl::from(3.) + two * unit))
            * tiny;
        additive = finite(a * additive + b)?;
    }
    let gb = Ivl::from(round_up(gamma(6 * degree)));
    let gm = Ivl::from(round_up(gamma(2 * q)));
    let g = finite((one + gb) * (one + gm) - one)?;
    let qf = Ivl::from(f64::from(
        u32::try_from(q).map_err(|_| no("MAC count overflow"))?,
    ));
    let mac_absolute = finite(two * qf * (one + gm) * tiny)?;
    let mut hsum = Ivl::from(0.);
    let mut wsum = Ivl::from(0.);
    let mut hmax = 0_f64;
    let mut wmax = 0_f64;
    let mut wmin = f64::INFINITY;
    let mut size = 0_f64;
    for [hx, hy, hz, weight] in controls(p)? {
        if !weight.is_finite() || !weight.is_positive() {
            return Err(no("native polar weights not positive"));
        }
        let h = norm([hx, hy, hz])?;
        hsum = finite(hsum + Ivl::from(h))?;
        wsum = finite(wsum + weight)?;
        hmax = hmax.max(h);
        wmax = wmax.max(weight.hi);
        wmin = wmin.min(weight.lo);
        size = size.max(norm([hx / weight, hy / weight, hz / weight])?);
    }
    let h_abs = finite((one + gm) * additive * hsum + two * mac_absolute)?;
    let w_abs = finite((one + gm) * additive * wsum + mac_absolute)?;
    let basis_sum = finite(one + gb + qf * additive)?;
    // Absolute partial-MAC bounds prevent overflow BEFORE cancellation. Strict
    // <MAX also excludes a computed homogeneous z==NOZ (a native special value).
    let numerator = finite((one + gm) * basis_sum * Ivl::from(hmax) + two * mac_absolute)?;
    let denominator = finite((one + gm) * basis_sum * Ivl::from(wmax) + mac_absolute)?;
    if numerator.hi >= f64::MAX || denominator.hi >= f64::MAX {
        return Err(no("native homogeneous arithmetic may overflow or hit NOZ"));
    }
    let size = Ivl::from(size);
    if !rational {
        // NOW markers propagate through native MAC, and to_euclid returns xyz
        // WITHOUT dividing by a hypothetical rounded sum of basis values.
        // The strict numerator bound above already encloses this direct final
        // point as well as every partial MAC, excluding both overflow and NOZ.
        return upper(g * size + h_abs);
    }
    let minimum = Ivl::from(wmin);
    let denominator_margin = finite(one - g - w_abs / minimum)?;
    if !denominator_margin.is_positive() {
        return Err(no(
            "rounded native rational denominator is not proved positive",
        ));
    }
    let pre = finite((two * g * size + (h_abs + size * w_abs) / minimum) / denominator_margin)?;
    let result = finite((one + unit) * pre + unit * size + two * tiny)?;
    let point = finite((one + unit) * (size + pre) + two * tiny)?;
    if point.hi >= f64::MAX {
        return Err(no("native division may overflow or hit NOZ"));
    }
    upper(result)
}

type RulingRows = ([Vec<ActualRoot>; 2], [f64; 2], [f64; 2]);
fn rows(k: &Kernel, w: &MeshWork, c: &Cone) -> Result<RulingRows> {
    let rev = c.rev();
    let n = rev
        .base()
        .gw_nurb()
        .ok_or_else(|| no("actual analytic net not materialized"))?;
    super::super::budgeted::admit_surface_control_storage_with_work(k, w, n)?;
    let swap = rev.swap_uv();
    let ruling = if swap { n.u_knots() } else { n.v_knots() };
    let [a, b, d, e] = ruling else {
        return Err(no("analytic net is not a single bounded linear ruling"));
    };
    if a != b
        || d != e
        || !a.is_finite()
        || !d.is_finite()
        || a >= d
        || (if swap { n.p() } else { n.q() }) != 1
    {
        return Err(no("analytic ruling degree/domain unsupported"));
    }
    let knots = if swap { n.v_knots() } else { n.u_knots() };
    let degree = if swap { n.q() } else { n.p() };
    if degree == 0 || degree > 4 || knots.len() > 512 {
        return Err(no("analytic profile degree/partition unsupported"));
    }
    if (if swap { n.n() } else { n.m() }) != 1 {
        return Err(no("linear ruling has extra controls"));
    }
    let count = (if swap { n.m() } else { n.n() })
        .checked_add(1)
        .ok_or_else(|| no("profile control count overflow"))?;
    if count > 256 {
        return Err(no("analytic profile control count unsupported"));
    }
    let mut controls = [Vec::new(), Vec::new()];
    for i in 0..count {
        w.spend_core(k, 1)?;
        w.reserve_cells_core(k, 2)?;
        let (lo, hi) = if swap {
            (n.cpt(0, i)?, n.cpt(1, i)?)
        } else {
            (n.cpt(i, 0)?, n.cpt(i, 1)?)
        };
        let weight = |p: CPoint| if p.w == NOW { 1. } else { p.w };
        if weight(lo) != weight(hi)
            || !weight(lo).is_finite()
            || weight(lo) <= 0.
            || [lo.z, hi.z].contains(&NOZ)
        {
            return Err(no(
                "ruling rows lack identical positive weights and 3D controls",
            ));
        }
        for (out, p) in controls.iter_mut().zip([lo, hi]) {
            out.push(p);
        }
    }
    let [lo, hi] = controls;
    let mut output = Vec::new();
    for row in [lo, hi] {
        w.reserve_cells_core(k, knots.len())?;
        let net = crv_basic::Curve::new(row, degree, knots.to_vec())?;
        let owner = crate::curve::curve::Curve::from(BSplineCurve::from_nurb(net, 3, true));
        output.push(native(k, w, actual_roots(k, w, &owner, true))?);
    }
    let mut output = output.into_iter();
    let (Some(lo), Some(hi), None) = (output.next(), output.next(), output.next()) else {
        return Err(inv("ruling row extraction missing"));
    };
    let native = rev.base().natural_uv_domain();
    let profile = if swap {
        native.v_interval()
    } else {
        native.u_interval()
    };
    Ok(([lo, hi], [profile.min(), profile.max()], [*a, *d]))
}
fn seam_distance(q: &Piece, rp: f64) -> Result<f64> {
    let b = box_of(q)?;
    let [x, y, _] = b;
    xy_norm([x - Ivl::from(rp), y])
}
/// Conditional opposite-branch lemma. Whole strip gives sigma*y>=-eta.
/// The actual atan2 seam predicate implies sigma*`y_float`<=`angle_error`*`rho_float`
/// and `x_float>=0` (its angle lies strictly within90deg of the positive x ray).
/// Projection/evaluation error then yields |y|<=Y and x>=-E. If `rho_min^2 > E^2 + Y^2`,
/// x MUST be positive. The full radial polynomial bounds |x-r| without samples.
fn opposite_seam(
    q: &Piece,
    rp: f64,
    sigma: f64,
    projection_error: f64,
    angular_error: f64,
    curves: &CurveBounds<'_>,
) -> Result<f64> {
    let radial = curves.radial(q, [Ivl::from(0.); 3], rp)?;
    let [_, y, _] = box_of(q)?;
    let eta = if sigma > 0. {
        (-y.lo).max(0.)
    } else {
        y.hi.max(0.)
    };
    let yy = upper(
        Ivl::from(projection_error)
            + (Ivl::from(radial.radius_upper) + Ivl::from(projection_error))
                * Ivl::from(angular_error),
    )?
    .max(eta);
    let low = finite(
        Ivl::from(radial.radius_lower) * Ivl::from(radial.radius_lower)
            - Ivl::from(yy) * Ivl::from(yy),
    )?;
    if low.lo.partial_cmp(&upper(
        Ivl::from(projection_error) * Ivl::from(projection_error),
    )?) != Some(core::cmp::Ordering::Greater)
    {
        return Err(no(
            "opposite seam branch is not proved on the positive radial half-plane",
        ));
    }
    let xlo = finite(low.sqrt())?.lo;
    let dx = (Ivl::from(radial.squared_residual_upper) + Ivl::from(yy) * Ivl::from(yy))
        / (Ivl::from(xlo) + Ivl::from(rp));
    xy_norm([dx, Ivl::from(yy)])
}
/// Every native branch is enclosed BEFORE returning the one immutable token.
pub(crate) fn prove_analytic_net_with_work<'a>(
    k: &'a Kernel,
    w: &MeshWork,
    s: &'a Surface,
    maximum: f64,
) -> Result<AnalyticNetAuthority<'a>> {
    w.spend_core(k, 4096)?;
    w.reserve_cells_core(k, 4096)?;
    if !(maximum >= 0. && maximum.is_finite()) {
        return Err(no("analytic value budget is not finite nonnegative"));
    }
    if s.has_kept_definition() {
        return Err(no("carried definition has no analytic native authority"));
    }
    let SurfaceKind::Cone(c) = s.kind() else {
        return Err(no("only actual native circular Cone/Cylinder is supported"));
    };
    let rev = c.rev();
    let step = rev.step_uv_domain();
    if step.u_min() != 0.
        || step.u_max() != 360.
        || !step.v_interval().is_bounded()
        || !rev.is_bounded()?
    {
        return Err(no(
            "partial sweep or unbounded analytic height is not proved",
        ));
    }
    let heights = [step.v_min(), step.v_max()];
    let [hmin, hmax] = heights;
    if !hmin.is_finite() || !hmax.is_finite() || hmin >= hmax {
        return Err(no("analytic height domain is not finite positive"));
    }
    let slope = slope(c)?;
    let radii = heights.map(|h| Ivl::from(c.base_radius()) + slope * Ivl::from(h));
    let whole_radius = finite(Ivl::from(c.base_radius()) + slope * Ivl::new(hmin, hmax))?;
    if !whole_radius.is_positive() {
        return Err(no("analytic radius crosses zero or is not finite"));
    }
    let rmax = whole_radius.hi;
    let height_size = hmin.abs().max(hmax.abs());
    let position = rev.position();
    let o = vec(position.origin());
    let x = vec(position.x_axis());
    let y = vec(position.y_axis());
    let z = vec(position.z_axis());
    if !dot(cross(x, y), z).is_positive() {
        return Err(no(
            "native analytic frame is singular or oppositely oriented",
        ));
    }
    let operator = upper(
        (Ivl::from(norm(x)?) * Ivl::from(norm(x)?) + Ivl::from(norm(y)?) * Ivl::from(norm(y)?))
            .sqrt(),
    )?;
    let polar = rev
        .polar_curve()
        .ok_or_else(|| no("actual polar ellipse absent"))?;
    let rp = polar.x_radius();
    if !(rp > 0.
        && rp.is_finite()
        && polar.y_radius() == rp
        && polar.step_interval().min() == 0.
        && polar.step_interval().max() == 360.)
    {
        return Err(no(
            "actual polar curve is not a full positive circular domain",
        ));
    }
    let owner = rev
        .polar_curve
        .as_ref()
        .ok_or_else(|| inv("actual polar owner absent"))?;
    let polar_rational = polar
        .base()
        .gw_nurb()
        .ok_or_else(|| no("actual polar net absent"))?
        .is_rational();
    let polar_roots = native(k, w, actual_roots(k, w, owner, true))?;
    let pd = polar.base().natural_interval();
    let ends = [pd.min(), pd.max()];
    let [polar_low, polar_high] = ends;
    partition(k, w, &polar_roots, ends)?;
    if !(pd.length() > 4. * EFF_ZERO && pd.length().is_finite()) {
        return Err(no("natural polar endpoints overlap their snap strips"));
    }
    let converter = rev.polar_converter();
    let knots = converter.natural_knots();
    let angles = converter.angles();
    let expected = if polar.inside_out() {
        [360., 0.]
    } else {
        [0., 360.]
    };
    if !converter.has_curve
        || knots.first() != Some(&polar_low)
        || knots.last() != Some(&polar_high)
        || angles.first() != expected.first()
        || angles.last() != expected.last()
        || knots.iter().chain(angles).any(|v| !v.is_finite())
    {
        return Err(no(
            "actual polar converter endpoint tables do not bind the full native circle",
        ));
    }
    let ([model_low, model_high], profile, height_native) = rows(k, w, c)?;
    if profile != ends {
        return Err(no("polar and stored net natural domains differ"));
    }
    partition(k, w, &model_low, profile)?;
    partition(k, w, &model_high, profile)?;
    if model_low.len() != model_high.len()
        || model_low
            .iter()
            .zip(&model_high)
            .any(|(a, b)| a.native_interval != b.native_interval)
    {
        return Err(inv("same-weight ruling row partitions disagree"));
    }
    let [native_height_low, native_height_high] = height_native;
    let native_height = Ivl::from(native_height_high) - Ivl::from(native_height_low);
    if !native_height.is_finite()
        || !native_height.is_positive()
        || native_height.lo < f64::MIN_POSITIVE
    {
        return Err(no("native height conversion denominator unsupported"));
    }
    let normal_heights = if c.inside_out() {
        [hmax, hmin]
    } else {
        [hmin, hmax]
    };
    let [radius_low, radius_high] = radii;
    let normal_radii = if c.inside_out() {
        [radius_high, radius_low]
    } else {
        radii
    };
    let pc_o = vec(polar.position().origin());
    let pc_x = vec(polar.position().x_axis());
    let pc_y = vec(polar.position().y_axis());
    let projection_operator = upper(
        (Ivl::from(norm(pc_x)?) * Ivl::from(norm(pc_x)?)
            + Ivl::from(norm(pc_y)?) * Ivl::from(norm(pc_y)?))
        .sqrt(),
    )?;
    let angular_error = upper(
        Ivl::from(round_up(gamma(128)))
            * Ivl::from(8.)
            * Ivl::from(crate::geom::certified::next_up(PI))
            + Ivl::from(f64::MIN_POSITIVE),
    )?;
    // Raw degree inversion is already in [-round,360+round], within native
    // contains_periodic_value's tolerance, so its first return branch is proved.
    if angular_error * 360. >= EFF_ZERO_DEG || EFF_ZERO_DEG + angular_error * 360. >= 90. {
        return Err(no(
            "native period/sign branches are not bounded by arithmetic",
        ));
    }
    let mut breaks = Vec::new();
    for r in polar_roots.iter().chain(&model_low) {
        for v in r.native_interval {
            w.spend_core(k, 1)?;
            w.reserve_cells_core(k, 1)?;
            breaks.push(v);
        }
    }
    breaks.sort_by(f64::total_cmp);
    breaks.dedup();
    let curves = CurveBounds::new(k, w)?;
    let mut paired = 0_f64;
    let mut ordinary = 0_f64;
    let mut epolar = 0_f64;
    let mut polar_size = 0_f64;
    let mut q_min = f64::INFINITY;
    for pair in breaks.windows(2) {
        let [a, b] = pair else {
            return Err(inv("partition pair missing"));
        };
        w.spend_core(
            k,
            polar_roots
                .len()
                .checked_add(model_low.len())
                .and_then(|v| v.checked_add(model_high.len()))
                .ok_or_else(|| no("root lookup count overflow"))?,
        )?;
        let actual = containing(k, w, &polar_roots, *a, *b)?;
        let p = restrict(k, w, actual, *a, *b)?;
        epolar = epolar.max(eval_error(k, w, actual, polar_rational)?);
        polar_size = polar_size.max(norm(box_of(&actual.piece)?)?);
        let q = project(k, w, &p, pc_o, pc_x, pc_y)?;
        let radial = curves.radial(&q, [Ivl::from(0.); 3], rp)?;
        ordinary = ordinary.max(radial.distance_upper);
        q_min = q_min.min(radial.radius_lower);
        for ((row, h), r) in [&model_low, &model_high]
            .into_iter()
            .zip(normal_heights)
            .zip(normal_radii)
        {
            let row = restrict(k, w, containing(k, w, row, *a, *b)?, *a, *b)?;
            let reference = reference(k, w, &q, rp, r, h, o, x, y, z)?;
            paired = paired.max(curves.paired(&row, &reference)?);
        }
    }
    let projection_error = upper(
        Ivl::from(projection_operator) * Ivl::from(epolar)
            + Ivl::from(round_up(gamma(8)))
                * (Ivl::from(polar_size) + Ivl::from(norm(pc_o)?))
                * Ivl::from(projection_operator)
            + Ivl::from(16.)
                * Ivl::from(f64::MIN_POSITIVE)
                * (Ivl::from(1.) + Ivl::from(projection_operator)),
    )?;
    if q_min.partial_cmp(&projection_error) != Some(core::cmp::Ordering::Greater) {
        return Err(no("actual inversion can reach its polar axis"));
    }
    let normalizing = upper(
        Ivl::from(ordinary) / Ivl::from(rp)
            + Ivl::from(2.) * Ivl::from(projection_error) / Ivl::from(q_min)
            + Ivl::from(angular_error),
    )?;
    let gain = upper(Ivl::from(rmax) / Ivl::from(rp) * Ivl::from(operator))?;
    let mut special = 0_f64;
    // Rounded subtraction in Start/End comparisons can admit a slightly wider
    // parameter strip. Derive it from the native constant and one rounding only.
    let endpoint_strip = upper(
        Ivl::from(EFF_ZERO) / (Ivl::from(1.) - Ivl::from(f64::EPSILON))
            + Ivl::from(f64::MIN_POSITIVE),
    )?;
    let late_strip = upper(
        ((Ivl::from(polar_high) - Ivl::from(polar_low)) / Ivl::from(360.)
            * Ivl::from(EFF_ZERO_DEG))
            / (Ivl::from(1.) - Ivl::from(round_up(gamma(4))))
            + Ivl::from(f64::MIN_POSITIVE),
    )?;
    for (end, first) in [(polar_low, true), (polar_high, false)] {
        for (width, late) in [(endpoint_strip, false), (late_strip, true)] {
            if late && rev.is_out_of_bounds_enabled() {
                continue;
            }
            let clipped = if first {
                [
                    end,
                    finite(Ivl::from(end) + Ivl::from(width))?
                        .hi
                        .min(polar_high),
                ]
            } else {
                [
                    finite(Ivl::from(end) - Ivl::from(width))?.lo.max(polar_low),
                    end,
                ]
            };
            let [clipped_low, clipped_high] = clipped;
            for root in &polar_roots {
                w.spend_core(k, 1)?;
                let [root_low, root_high] = root.native_interval;
                let a = clipped_low.max(root_low);
                let b = clipped_high.min(root_high);
                if a >= b {
                    continue;
                }
                let p = restrict(k, w, root, a, b)?;
                let q = project(k, w, &p, pc_o, pc_x, pc_y)?;
                let distance = if late {
                    let [first_angle, last_angle] = expected;
                    let angle = if first { first_angle } else { last_angle };
                    let sigma = if angle == 0. { 1. } else { -1. };
                    opposite_seam(&q, rp, sigma, projection_error, angular_error, &curves)?
                } else {
                    seam_distance(&q, rp)?
                };
                special = special.max(distance);
            }
        }
    }
    // Context seam: native computed distance<=zone/100. Bound that distance's
    // rounding and BOTH point evaluations; project with the actual frame operator.
    // A non-orthonormal circle frame contributes its exact Gram discrepancy too.
    let zone = context_zone_tol_3d(k, None, SmallTopoType::NormalSize);
    if !(zone >= 0. && zone.is_finite()) {
        return Err(no("actual seam context tolerance is invalid"));
    }
    let threshold = Ivl::from(zone / 100.);
    let distance = finite(
        (threshold + Ivl::from(UNDERFLOW_ROOT)) / (Ivl::from(1.) - Ivl::from(round_up(gamma(5)))),
    )?;
    let end_error = upper(
        Ivl::from(round_up(gamma(16)))
            * (Ivl::from(norm(pc_o)?)
                + Ivl::from(rp) * (Ivl::from(norm(pc_x)?) + Ivl::from(norm(pc_y)?)))
            + Ivl::from(rp) * Ivl::from(projection_operator) * Ivl::from(angular_error)
            + Ivl::from(16.)
                * Ivl::from(f64::MIN_POSITIVE)
                * (Ivl::from(1.) + Ivl::from(projection_operator)),
    )?;
    let gram = xy_norm([
        Ivl::from(rp) * (dot(pc_x, pc_x) - Ivl::from(1.)),
        Ivl::from(rp) * dot(pc_x, pc_y),
    ])?;
    let context = upper(
        Ivl::from(projection_operator) * (distance + Ivl::from(epolar) + Ivl::from(end_error))
            + Ivl::from(gram),
    )?;
    special = special.max(context);
    let height_error = upper(
        Ivl::from(round_up(gamma(16)))
            * Ivl::from(2.)
            * (Ivl::from(hmin.abs()) + Ivl::from(hmax.abs()))
            + Ivl::from(32.) * Ivl::from(f64::MIN_POSITIVE) / native_height,
    )?;
    let radius_error = upper(
        Ivl::from(round_up(gamma(4)))
            * (Ivl::from(c.base_radius().abs())
                + Ivl::from(slope.mag()) * (Ivl::from(height_size) + Ivl::from(height_error)))
            + Ivl::from(4.) * Ivl::from(f64::MIN_POSITIVE),
    )?;
    if whole_radius.lo
        <= upper(Ivl::from(radius_error) + Ivl::from(height_error) * Ivl::from(slope.mag()))?
    {
        return Err(no("rounded actual radius may reach zero"));
    }
    let assembly = upper(
        Ivl::from(round_up(gamma(16)))
            * (Ivl::from(norm(o)?)
                + (Ivl::from(rmax)
                    + Ivl::from(radius_error)
                    + Ivl::from(slope.mag()) * Ivl::from(height_error))
                    * (Ivl::from(norm(x)?) + Ivl::from(norm(y)?))
                + (Ivl::from(height_size) + Ivl::from(height_error)) * Ivl::from(norm(z)?))
            * Ivl::from(2.)
            + Ivl::from(32.)
                * Ivl::from(f64::MIN_POSITIVE)
                * (Ivl::from(1.)
                    + Ivl::from(rmax)
                    + Ivl::from(radius_error)
                    + Ivl::from(slope.mag()) * Ivl::from(height_error)
                    + Ivl::from(height_size)
                    + Ivl::from(height_error)
                    + Ivl::from(norm(x)?)
                    + Ivl::from(norm(y)?)
                    + Ivl::from(norm(z)?)),
    )?;
    let angular =
        upper(Ivl::from(rmax) * Ivl::from(operator) * Ivl::from(normalizing))?.max(upper(
            Ivl::from(gain) * Ivl::from(special)
                + Ivl::from(rmax) * Ivl::from(operator) * Ivl::from(angular_error),
        )?);
    let bound = upper(
        Ivl::from(paired)
            + Ivl::from(angular)
            + Ivl::from(height_error)
                * (Ivl::from(norm(z)?)
                    + Ivl::from(slope.mag())
                        * Ivl::from(operator)
                        * (Ivl::from(1.) + Ivl::from(angular_error)))
            + Ivl::from(radius_error)
                * Ivl::from(operator)
                * (Ivl::from(1.) + Ivl::from(angular_error))
            + Ivl::from(assembly),
    )?;
    if bound > maximum {
        return Err(no(
            "full actual analytic-to-same-net value band exceeds its supplied budget",
        ));
    }
    w.spend_core(k, 0)?;
    let natural = rev.base().natural_uv_domain();
    Ok(AnalyticNetAuthority {
        kernel: k,
        definition: s,
        domain: [
            natural.u_min(),
            natural.u_max(),
            natural.v_min(),
            natural.v_max(),
        ],
        upper: bound,
        roots: breaks.len().saturating_sub(1),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::geom::axis2_placement::Axis2Placement;
    use crate::math::{Point2, INFINITE_PARAMETER};
    fn cone(k: &Kernel, frustum: bool, swap: bool, reverse: bool) -> Cone {
        let mut c = if frustum {
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
        c.make_nurb(k).unwrap();
        c
    }
    #[test]
    fn complete_native_cylinder_and_frustum_authority_covers_all_swaps_reversals_and_clamp_modes() {
        let k = Kernel::default();
        for frustum in [false, true] {
            for swap in [false, true] {
                for reverse in [false, true] {
                    for unclamped in [false, true] {
                        let mut c = cone(&k, frustum, swap, reverse);
                        c.set_out_of_bounds_enabled(unclamped);
                        let s = Surface::from(c);
                        let w = MeshWork::new();
                        let proof = prove_analytic_net_with_work(&k, &w, &s, 1e-6).unwrap();
                        assert!(core::ptr::eq(proof.definition(), &raw const s));
                        assert!(core::ptr::eq(proof.kernel(), &raw const k));
                        assert_eq!(proof.covered_roots(), 4);
                        assert!(proof.distance_upper() > 0. && proof.distance_upper() < 1e-6);
                        // Validation probes deliberately INCLUDE both EFF_ZERO endpoint strips,
                        // late-period strips, root seams and interior heights. They are NOT any
                        // premise of the all-branch certificate above.
                        let [u0, u1, v0, v1] = proof.domain();
                        for t in [
                            0.,
                            0.5 * EFF_ZERO,
                            2. * EFF_ZERO,
                            1e-8,
                            0.125,
                            0.25,
                            0.5,
                            0.75,
                            1. - 1e-8,
                            1. - 2. * EFF_ZERO,
                            1. - 0.5 * EFF_ZERO,
                            1.,
                        ] {
                            for h in [0., 0.3, 1.] {
                                let uv = if swap {
                                    Point2::new(u0 + h * (u1 - u0), v0 + t * (v1 - v0))
                                } else {
                                    Point2::new(u0 + t * (u1 - u0), v0 + h * (v1 - v0))
                                };
                                let SurfaceKind::Cone(c) = s.kind_with_nurb(&k).unwrap() else {
                                    panic!()
                                };
                                let actual = s.evaluate_point(&k, uv).unwrap();
                                let net = c.rev().base().evaluate_point(uv).unwrap();
                                assert!(
                                    actual.distance(net) <= proof.distance_upper(),
                                    "{frustum}/{swap}/{reverse}/{unclamped} t={t}: {} > {}",
                                    actual.distance(net),
                                    proof.distance_upper()
                                );
                            }
                        }
                    }
                }
            }
        }
    }
    fn refused_small(k: &Kernel, c: Cone, case: &str) {
        let work = MeshWork::new();
        let surface = Surface::from(c);
        let result = prove_analytic_net_with_work(k, &work, &surface, 1e-6);
        assert!(
            matches!(result, Err(SolidError::Unsupported { .. })),
            "{case}: {}",
            match &result {
                Ok(proof) => format!("unexpected authority bound {}", proof.distance_upper()),
                Err(e) => format!("unexpected error {e:?}"),
            }
        );
        assert!(
            work.check(k).is_ok(),
            "a budget error must not masquerade as geometric refusal"
        );
    }
    #[test]
    fn independent_cached_net_polar_and_frame_mutations_cannot_receive_small_authority() {
        let k = Kernel::default();
        let mut net = cone(&k, false, false, false);
        net.rev
            .base
            .get_or_create_gw_nurb()
            .unwrap()
            .cpt_mut(1, 0)
            .unwrap()
            .x += 0.01;
        refused_small(&k, net, "independent cached row");
        let mut nonlinear = cone(&k, false, false, false);
        let net = nonlinear.rev.base.get_or_create_gw_nurb().unwrap();
        for i in 0..=net.n() {
            let p = net.cpt_mut(i, 1).unwrap();
            assert_ne!(p.w, NOW);
            p.x *= 2.;
            p.y *= 2.;
            p.z *= 2.;
            p.w *= 2.;
        }
        // All upper/lower Euclidean row controls stay unchanged, but unequal
        // row weights make the INTERIOR height law nonlinear. Endpoint fitting
        // cannot pass the complete single-ruling prerequisite.
        refused_small(&k, nonlinear, "unequal ruling weights");
        let mut polar = cone(&k, false, false, false);
        let crate::curve::curve::CurveKind::Ellipse(p) =
            polar.rev.polar_curve.as_mut().unwrap().kind_mut()
        else {
            panic!()
        };
        p.position = Axis2Placement::new(Vec3::ZERO, Vec3::Y, -Vec3::X);
        refused_small(&k, polar, "independent polar frame");
        let mut frame = cone(&k, false, false, false);
        let repaired = Axis2Placement::new(Vec3::ZERO, Vec3::X, Vec3::X);
        assert_eq!(repaired.x_axis(), Vec3::X);
        assert_eq!(repaired.y_axis(), Vec3::Y);
        // The canonical constructor repairs parallel axes; hostile stored data
        // must instead keep both actual axes equal, as the test promises.
        frame.rev.position = Axis2Placement::from_stored(Vec3::ZERO, Vec3::X, Vec3::X);
        assert_eq!(frame.rev.position.x_axis(), Vec3::X);
        assert_eq!(frame.rev.position.y_axis(), Vec3::X);
        refused_small(&k, frame, "singular stored frame");
        let mut reflected = cone(&k, false, false, false);
        reflected.rev.position = Axis2Placement::new(Vec3::ZERO, Vec3::X, -Vec3::Y);
        refused_small(&k, reflected, "independent reflected frame");
    }
    #[test]
    fn unsupported_partial_unbounded_apex_and_cylinder_angle_mismatch_are_explicit_refusals() {
        let k = Kernel::default();
        let mut partial = cone(&k, false, false, false);
        partial.rev.anal_uv_domain = crate::geom::extent2d::Extent2d::from_bounds(0., 0., 180., 5.);
        let mut unbounded = cone(&k, false, false, false);
        unbounded.rev.anal_uv_domain =
            crate::geom::extent2d::Extent2d::from_bounds(0., 0., 360., INFINITE_PARAMETER);
        let mut mismatch = cone(&k, false, false, false);
        mismatch.semi_angle_deg = 10.;
        let mut apex = cone(&k, true, false, false);
        apex.semi_angle_deg = -45.;
        for c in [partial, unbounded, mismatch, apex] {
            refused_small(&k, c, "unsupported construction class");
        }
    }
    #[test]
    fn exact_native_break_restriction_accounts_for_non_dyadic_fraction_rounding() {
        let k = Kernel::default();
        let w = MeshWork::new();
        let root = ActualRoot {
            piece: piece(
                &k,
                &w,
                [[0., 0., 0., 1.], [3., 0., 0., 1.]].map(|p| p.map(Ivl::from)),
                1,
            )
            .unwrap(),
            native_interval: [0., 3.],
        };
        let bounded = restrict(&k, &w, &root, 1., 2.).unwrap();
        let [x, _, _, weights] = &bounded.h;
        for ((&x, &weight), expected) in x
            .coefficients()
            .iter()
            .zip(weights.coefficients())
            .zip([1., 2.])
        {
            let point = (Ivl::from(x) + Ivl::new(-bounded.err, bounded.err))
                / (Ivl::from(weight) + Ivl::new(-bounded.err, bounded.err));
            assert!(point.lo <= expected && expected <= point.hi);
        }
        assert!(bounded.err > 0.);
    }
    #[test]
    fn native_basis_underflow_cannot_produce_a_small_rational_evaluation_certificate() {
        let k = Kernel::default();
        let work = MeshWork::new();
        let small = 1e-250;
        let large = 1e250;
        let mut controls = vec![CPoint::new(small, 0., 0., small); 4];
        controls.push(CPoint::new(0., 0., 0., large));
        let net = crv_basic::Curve::new(controls, 4, vec![0., 0., 0., 0., 0., 1., 1., 1., 1., 1.])
            .unwrap();
        let curve = crate::curve::curve::Curve::from(BSplineCurve::from_nurb(net, 3, true));
        let actual = curve.evaluate_point(&k, 1e-100).unwrap();
        assert!(
            actual.x > 0.9,
            "native basis t^4 underflows and loses the large weight: {actual:?}"
        );
        // Closed form: x=small*(1-t^4)/(small*(1-t^4)+large*t^4).
        // The stored binary64 inputs lie inside [0.5,2] times their stated
        // powers of ten, so x<1e-96 independently of the native evaluator.
        let root = actual_roots(&k, &work, &curve, true).unwrap();
        let lower = (Ivl::from(actual.x) - Ivl::from(1e-96)).lo;
        match eval_error(&k, &work, &root[0], true) {
            Ok(bound) => assert!(
                bound >= lower,
                "false small native error {bound} vs proven gap {lower}"
            ),
            Err(SolidError::Unsupported { .. }) => {}
            Err(e) => panic!("unexpected error: {e:?}"),
        }
        work.check(&k).unwrap();
    }
    #[test]
    fn tiny_internal_span_cannot_hide_native_basis_failure_inside_analytic_authority() {
        let mut k = Kernel::default();
        k.tolerances.zone_tol_3d = 1e-12;
        let mut c = cone(&k, false, false, false);
        let a = 2e-12;
        let mid = crate::geom::certified::next_up(a);
        let b = crate::geom::certified::next_up(mid);
        assert!(a < mid && mid < b && b - a < crate::math::EFF_ZERO_SQ);
        let knots = vec![-1., -1., -1., a, a, b, b, 1., 1., 2., 2., 2.];
        {
            let crate::curve::curve::CurveKind::Ellipse(polar) =
                c.rev.polar_curve.as_mut().unwrap().kind_mut()
            else {
                panic!()
            };
            let original = polar.base().gw_nurb().unwrap();
            assert_eq!(original.degree(), 2);
            assert_eq!(original.cpts().len(), 9);
            let modified =
                crv_basic::Curve::new(original.cpts().to_vec(), 2, knots.clone()).unwrap();
            polar.base_mut().set_from_gw_nurb(Some(&modified)).unwrap();
        }
        c.rev
            .base
            .get_or_create_gw_nurb()
            .unwrap()
            .u_knots_mut()
            .copy_from_slice(&knots);
        c.rev.polar.natural_knots = vec![-1., a, b, 1., 2.];
        c.rev.polar.angles = vec![0., 90., 180., 270., 360.];
        let owner = c.rev.polar_curve.as_ref().unwrap();
        assert!(
            owner.evaluate_point(&k, mid).is_err(),
            "the ACTUAL basis evaluator must exercise its Degenerate status"
        );
        let work = MeshWork::new();
        let roots = actual_roots(&k, &work, owner, true).unwrap();
        // Exact rational quadratic midpoint, independent of the failing global
        // basis routine. The second quarter lies at x< -2 on the radius3 circle.
        let [hx, _, _, hw] = &roots[1].piece.h;
        let midpoint = |p: &Bernstein2| {
            p.coefficients()
                .iter()
                .zip([0.25, 0.5, 0.25])
                .fold(Ivl::from(0.), |sum, (&c, n)| {
                    sum + Ivl::from(c) * Ivl::from(n)
                })
        };
        let exact_x = midpoint(hx) / midpoint(hw);
        assert!(exact_x.hi < -2.);
        let surface = Surface::from(c);
        let actual = surface.evaluate_point(&k, Point2::new(mid, 2.5)).unwrap();
        assert!(
            (Ivl::from(actual.x) - exact_x).lo > 4.,
            "ignored status inverts UNDEF near45deg, not the exact135deg curve: {actual:?}"
        );
        let result = prove_analytic_net_with_work(&k, &work, &surface, 1e-6);
        work.check(&k).unwrap();
        assert!(
            matches!(result, Err(SolidError::Unsupported { .. })),
            "a whole-domain token cannot ignore this basis failure: {}",
            match &result {
                Ok(proof) => format!("unexpected authority bound {}", proof.distance_upper()),
                Err(e) => format!("unexpected error {e:?}"),
            }
        );
        work.check(&k).unwrap();
    }
}
