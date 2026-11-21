//! Exact control extraction and analytic-line enclosures of immutable actual curves.
use super::{MeshError, MeshWork};
use crate::blend::fillet_section::interval::Ivl;
use crate::curve::curve::{Curve, CurveKind};
use crate::nurbs::b_spline_curve::BSplineCurve;
use crate::nurbs::math::{NOW, NOZ};
use crate::offset::construction::bernstein::Bernstein2;
use crate::query::distance_bound::Piece;
use crate::Kernel;
const OP: &str = "mesh_reconstruction::actual_curve_roots";
type Result<T> = core::result::Result<T, MeshError>;
fn unsure(n: usize) -> MeshError {
    MeshError::Undecided { stage: OP, work: n }
}
fn piece(h: [Bernstein2; 4], err: f64) -> Piece {
    Piece {
        h,
        err,
        lower: 0.,
        depth: 0,
        uv: [0., 1., 0., 0.],
        parameter_ends: [Ivl::from(0.), Ivl::from(1.), Ivl::from(0.), Ivl::from(0.)],
    }
}
pub(crate) struct ActualRoot {
    pub(crate) piece: Piece,
    pub(crate) native_interval: [f64; 2],
}
fn spline(k: &Kernel, work: &MeshWork, base: &BSplineCurve, uv: bool) -> Result<Vec<ActualRoot>> {
    if base.dim() != if uv { 2 } else { 3 } {
        return Err(unsure(0));
    }
    let Some(n) = base.gw_nurb() else {
        return Err(unsure(0));
    };
    // Retained backing may be larger than its active prefixes. Admit it before
    // reading those prefixes or materializing a new root representation.
    let admitted = n.visit_stored_payload(&mut |count| {
        work.spend_core(k, count)?;
        work.reserve_cells_core(k, count)
    });
    work.check(k)?;
    admitted?;
    let p = n.degree();
    if p == 0 || p > 8 {
        return Err(unsure(0));
    }
    let controls = n.n().checked_add(1).ok_or_else(|| unsure(n.n()))?;
    let knots_count = n.m().checked_add(1).ok_or_else(|| unsure(n.m()))?;
    let (stored_controls, stored_knots) = n.storage();
    if n.n() < p
        || n.n().checked_add(p).and_then(|v| v.checked_add(1)) != Some(n.m())
        || controls > stored_controls
        || knots_count > stored_knots
    {
        return Err(unsure(controls));
    }
    let knots = n.knots();
    let controls = n.cpts();
    work.spend(k, knots.len())?;
    work.spend(k, controls.len())?;
    if knots.iter().any(|u| !u.is_finite()) || knots.windows(2).any(|w| matches!(w,[a,b] if a>b)) {
        return Err(unsure(knots.len()));
    }
    let mut groups = Vec::<(f64, usize)>::new();
    for &u in knots {
        work.spend(k, 1)?;
        if let Some((last, count)) = groups.last_mut() {
            if *last == u {
                *count += 1;
                continue;
            }
        }
        work.reserve_output(k, 1)?;
        groups.push((u, 1));
    }
    let (Some(&(lo, lc)), Some(&(hi, hc))) = (groups.first(), groups.last()) else {
        return Err(unsure(0));
    };
    if n.param_bounds() != (lo, hi)
        || !crate::geom::certified::above(hi, lo)
        || lc != p + 1
        || hc != p + 1
    {
        return Err(unsure(0));
    }
    if groups
        .iter()
        .skip(1)
        .take(groups.len().saturating_sub(2))
        .any(|(_, m)| *m != p)
    {
        return Err(unsure(groups.len()));
    }
    let count = groups.len().checked_sub(1).ok_or_else(|| unsure(0))?;
    let want = count
        .checked_mul(p)
        .and_then(|n| n.checked_add(1))
        .ok_or_else(|| unsure(count))?;
    if controls.len() != want {
        return Err(unsure(controls.len()));
    }
    work.reserve_output(k, count)?;
    let rational = n.is_rational();
    let mut roots = Vec::new();
    for i in 0..count {
        work.reserve_cells(k, 1)?;
        let start = i.checked_mul(p).ok_or_else(|| unsure(i))?;
        let end = start.checked_add(p + 1).ok_or_else(|| unsure(i))?;
        let Some(net) = controls.get(start..end) else {
            return Err(unsure(i));
        };
        let mut x = Vec::new();
        let mut y = Vec::new();
        let mut z = Vec::new();
        let mut w = Vec::new();
        for q in net {
            work.spend(k, 1)?;
            if (q.w == NOW) == rational {
                return Err(unsure(i));
            }
            let weight = if q.w == NOW { 1. } else { q.w };
            let coordinate_z = if uv {
                // Native nurbs_crv::{to_euclid,crv_eval} explicitly interpret
                // NOZ as zero. The UV chart consumes x/y, not a fabricated3D
                // elevation. Refuse inconsistent nonzero stored z metadata.
                if q.z != NOZ && q.z != 0. {
                    return Err(unsure(i));
                }
                0.
            } else {
                q.z
            };
            if ![q.x, q.y, coordinate_z, weight]
                .into_iter()
                .all(f64::is_finite)
                || (!uv && q.z == NOZ)
                || weight <= 0.
            {
                return Err(unsure(i));
            }
            x.push(q.x);
            y.push(q.y);
            z.push(coordinate_z);
            w.push(weight);
        }
        let (Some(&(u0, _)), Some(&(u1, _))) = (groups.get(i), groups.get(i + 1)) else {
            return Err(unsure(i));
        };
        roots.push(ActualRoot {
            piece: piece(
                [
                    Bernstein2::new(p, 0, x)?,
                    Bernstein2::new(p, 0, y)?,
                    Bernstein2::new(p, 0, z)?,
                    Bernstein2::new(p, 0, w)?,
                ],
                0.,
            ),
            native_interval: [u0, u1],
        });
    }
    Ok(roots)
}
/// Reads the actual evaluated curve definition; procedural curves without a
/// bounded representation are refused. No endpoint-only replacement of an arc.
fn roots_mode(
    k: &Kernel,
    work: &MeshWork,
    curve: &Curve,
    forward: bool,
    uv: bool,
) -> Result<Vec<ActualRoot>> {
    work.check(k)?;
    if uv && curve.dim() != 2 {
        return Err(unsure(0));
    }
    let roots = match curve.kind() {
        CurveKind::BSpline(b) => spline(k, work, b, uv)?,
        CurveKind::Ellipse(e) => spline(k, work, e.base(), uv)?,
        CurveKind::Line(line) => {
            work.reserve_output(k, 1)?;
            work.reserve_cells(k, 1)?;
            work.spend(k, 16)?;
            let natural = line.natural_interval();
            let step = line.step_interval();
            if !(line.is_bounded()
                && natural.min().is_finite()
                && natural.max().is_finite()
                && natural.min() < natural.max())
            {
                return Err(unsure(0));
            }
            let mut ends = [step.min(), step.max()];
            if crate::geom::tol::is_zero(natural.length()) {
                ends = [natural.min(), natural.max()];
            } else if line.inside_out() {
                ends.reverse();
            }
            let origin = line.line_point();
            let vector = line.line_vector();
            let scale = Ivl::from(line.line_scale());
            // Actual surface parameter evaluation consumes only x/y. Retain
            // the exact native Line parameter conversion; NOZ is not arithmetic.
            let coordinates = [origin.x, origin.y, if uv { 0. } else { origin.z }];
            let direction = [vector.x, vector.y, if uv { 0. } else { vector.z }];
            let mut controls = [Vec::new(), Vec::new(), Vec::new()];
            let mut error = 0.0_f64;
            for parameter in ends {
                for ((out, p), v) in controls.iter_mut().zip(coordinates).zip(direction) {
                    let value = Ivl::from(p) + Ivl::from(parameter) * scale * Ivl::from(v);
                    if !value.is_finite() {
                        return Err(unsure(0));
                    }
                    let middle = 0.5 * value.lo + 0.5 * value.hi;
                    error = error.max((value - Ivl::from(middle)).mag());
                    out.push(middle);
                }
            }
            let [x, y, z] = controls;
            vec![ActualRoot {
                piece: piece(
                    [
                        Bernstein2::new(1, 0, x)?,
                        Bernstein2::new(1, 0, y)?,
                        Bernstein2::new(1, 0, z)?,
                        Bernstein2::new(1, 0, vec![1., 1.])?,
                    ],
                    error,
                ),
                native_interval: [natural.min(), natural.max()],
            }]
        }
        _ => return Err(unsure(0)),
    };
    orient_roots(k, work, roots, forward)
}
pub(crate) fn orient_roots(
    k: &Kernel,
    work: &MeshWork,
    mut roots: Vec<ActualRoot>,
    forward: bool,
) -> Result<Vec<ActualRoot>> {
    if !forward {
        roots.reverse();
        for root in &mut roots {
            root.native_interval.reverse();
            for polynomial in &mut root.piece.h {
                let (degree, v) = polynomial.degrees();
                let reversed = polynomial.coefficients().iter().rev().copied().collect();
                *polynomial = Bernstein2::new(degree, v, reversed)?;
            }
        }
    }
    work.check(k)?;
    Ok(roots)
}

/// Whole authoritative 3D roots; existing behavior is unchanged.
pub(crate) fn actual_roots(
    k: &Kernel,
    work: &MeshWork,
    curve: &Curve,
    forward: bool,
) -> Result<Vec<ActualRoot>> {
    roots_mode(k, work, curve, forward, false)
}
/// Full ACTUAL edge-use roots. An unbounded native Line is affine over
/// its finite used interval, even though its natural support is infinite.
/// B-splines also admit complete existing knot-aligned root ranges. Other kinds
/// retain their existing complete-natural-domain proof obligation;
/// no failed extraction is retried with a different representation.
pub(crate) fn actual_used_roots(
    k: &Kernel,
    work: &MeshWork,
    curve: &Curve,
    used: crate::geom::extent1d::Extent1d,
    forward: bool,
) -> Result<Vec<ActualRoot>> {
    work.check(k)?;
    // Native infinity markers are finite binary64 values. An edge-use proof
    // covers a bounded interval, never either semantic infinite tail.
    if !used.is_bounded()
        || !used.min().is_finite()
        || !used.max().is_finite()
        || used.min() >= used.max()
    {
        return Err(unsure(0));
    }
    if let CurveKind::Line(line) = curve.kind() {
        if !line.is_bounded() {
            // The shared affine proof reads the ACTUAL +/-t evaluator, not the
            // cached net or endpoints inferred from a label. Reserve BEFORE its
            // fixed-degree expansion arithmetic and endpoint enclosure copies.
            work.spend(k, 128)?;
            work.reserve_cells(k, 128)?;
            work.reserve_output(k, 1)?;
            if curve.dim() != 3 {
                return Err(unsure(0));
            }
            let ends =
                super::certificate::affine_ends(curve, used, false).ok_or_else(|| unsure(0))?;
            let mut h: [Vec<f64>; 3] = core::array::from_fn(|_| Vec::new());
            let mut error = 0_f64;
            for point in ends {
                for (out, coordinate) in h.iter_mut().zip(point) {
                    let value = super::certificate::exact_geometry::interval(&coordinate)
                        .ok_or_else(|| unsure(0))?;
                    if !value.is_finite() {
                        return Err(unsure(0));
                    }
                    let middle = 0.5 * value.lo + 0.5 * value.hi;
                    error = error.max((value - Ivl::from(middle)).mag());
                    out.push(middle);
                }
            }
            let [x, y, z] = h;
            let root = ActualRoot {
                piece: piece(
                    [
                        Bernstein2::new(1, 0, x)?,
                        Bernstein2::new(1, 0, y)?,
                        Bernstein2::new(1, 0, z)?,
                        Bernstein2::new(1, 0, vec![1., 1.])?,
                    ],
                    error,
                ),
                native_interval: [used.min(), used.max()],
            };
            return orient_roots(k, work, vec![root], forward);
        }
    }
    let natural = curve.natural_interval();
    if used.min() == natural.min() && used.max() == natural.max() {
        return actual_roots(k, work, curve, forward);
    }
    // An unchanged B-spline restricted at its EXISTING native knot boundaries
    // retains complete authoritative roots. No rounded sub-root ratio, new
    // parameter law or endpoint-only geometry is introduced here.
    if !matches!(curve.kind(), CurveKind::BSpline(_)) {
        return Err(unsure(0));
    }
    let roots = actual_roots(k, work, curve, true)?;
    work.reserve_output(k, roots.len())?;
    let mut selected = Vec::new();
    selected
        .try_reserve_exact(roots.len())
        .map_err(|_| MeshError::Refused {
            stage: "actual curve root workspace",
            detail: "allocation refused".into(),
        })?;
    for root in roots {
        work.spend(k, 8)?;
        let [a, b] = root.native_interval;
        if b <= used.min() || a >= used.max() {
            continue;
        }
        if a < used.min() || b > used.max() {
            return Err(unsure(0));
        }
        if selected
            .last()
            .is_some_and(|old: &ActualRoot| old.native_interval[1] != a)
        {
            return Err(unsure(0));
        }
        selected.push(root);
    }
    if selected
        .first()
        .is_none_or(|r| r.native_interval[0] != used.min())
        || selected
            .last()
            .is_none_or(|r| r.native_interval[1] != used.max())
    {
        return Err(unsure(0));
    }
    orient_roots(k, work, selected, forward)
}
/// Whole authoritative native UV trim roots (z=0). This is a distinct dimension
/// contract, not a 3D approximation of an unrelated analytic ellipse. Each full
/// natural root is retained; the consuming face must prove used parameter ranges,
/// orientation, complete boundary partition, S/clamp image and native zones.
pub(crate) fn actual_uv_roots(
    k: &Kernel,
    work: &MeshWork,
    curve: &Curve,
    forward: bool,
) -> Result<Vec<ActualRoot>> {
    roots_mode(k, work, curve, forward, true)
}
#[cfg(test)]
mod tests {
    use super::super::certificate::curve_graph_bound;
    use super::*;
    use crate::math::Vec3;
    #[test]
    fn native_analytic_line_without_a_nurb_uses_its_actual_affine_definition() {
        let k = Kernel::default();
        let work = MeshWork::new();
        let line = crate::curve::line::Line::from_points(
            Vec3::new(10., 20., 0.),
            Vec3::new(11., 21., 0.),
            3,
        );
        let curve = Curve::new(CurveKind::Line(line));
        let roots = actual_roots(&k, &work, &curve, false).unwrap();
        let root = roots.first().unwrap();
        assert_eq!(root.native_interval, [1., 0.]);
        let source = [[11., 21., 0.], [10., 20., 0.]].map(|p| p.map(Ivl::from));
        let proof = curve_graph_bound(&root.piece, source, 0.).unwrap();
        assert!(proof.distance_upper < 1e-10 && proof.projection_numerator_lower > 0.);
    }
    #[test]
    fn actual_two_dimensional_rational_trim_roots_use_native_noz_semantics() {
        let k = Kernel::default();
        let work = MeshWork::new();
        let net = crate::nurbs::crv_basic::Curve::new(
            vec![
                crate::nurbs::math::CPoint::new(1., 0., NOZ, 1.),
                crate::nurbs::math::CPoint::new(0.5, 0.5, NOZ, 0.5),
                crate::nurbs::math::CPoint::new(0., 1., NOZ, 1.),
            ],
            2,
            vec![0., 0., 0., 1., 1., 1.],
        )
        .unwrap();
        let curve = Curve::from(BSplineCurve::from_nurb(net, 2, true));
        let roots = actual_uv_roots(&k, &work, &curve, true).unwrap();
        assert_eq!(roots.len(), 1);
        let root = &roots[0];
        assert!(root.piece.h[2].coefficients().iter().all(|&v| v == 0.));
        assert_eq!(root.native_interval, [0., 1.]);
        assert!(actual_roots(&k, &work, &curve, true).is_err());
    }
    #[test]
    fn canonical_unbounded_line_roots_cover_the_same_complete_used_interval() {
        use crate::curve::line::Line;
        use crate::geom::extent1d::Extent1d;
        let k = Kernel::default();
        let work = MeshWork::new();
        let curve = Curve::from(Line::create_canonical(Vec3::new(-2., 0., 0.), Vec3::X));
        let used = Extent1d::from_raw(2., 5.);
        for unbounded in [
            curve.natural_interval(),
            Extent1d::from_raw(0., crate::math::INFINITE_PARAMETER),
            Extent1d::from_raw(-crate::math::INFINITE_PARAMETER_SQRT, 5.),
        ] {
            assert!(!unbounded.is_bounded());
            assert!(actual_used_roots(&k, &work, &curve, unbounded, true).is_err());
        }
        assert!(
            actual_roots(&k, &work, &curve, true).is_err(),
            "whole infinite support is not a finite edge"
        );
        for forward in [true, false] {
            let roots = actual_used_roots(&k, &work, &curve, used, forward).unwrap();
            assert_eq!(roots.len(), 1);
            let root = &roots[0];
            let mut params = [2., 5.];
            let mut source = [[0., 0., 0.], [3., 0., 0.]];
            if !forward {
                params.reverse();
                source.reverse();
            }
            assert_eq!(root.native_interval, params);
            let graph =
                curve_graph_bound(&root.piece, source.map(|p| p.map(Ivl::from)), 0.).unwrap();
            assert!(graph.distance_upper < 1e-10 && graph.projection_numerator_lower > 0.);
        }
        assert!(actual_used_roots(&k, &work, &curve, Extent1d::from_raw(5., 2.), true).is_err());
        let bounded = Curve::from(Line::from_points(Vec3::ZERO, Vec3::X, 3));
        assert!(
            actual_used_roots(&k, &work, &bounded, Extent1d::from_raw(0.2, 0.8), true).is_err()
        );
        assert!(actual_used_roots(&k, &work, &bounded, bounded.natural_interval(), true).is_ok());
    }
    #[test]
    fn native_curve_budget_counts_inactive_backing_before_root_materialization() {
        use crate::nurbs::math::CPoint;
        let k = Kernel::default();
        let mut points = vec![CPoint::new(0., 0., 0., 1.), CPoint::new(1., 0., 0., 1.)];
        points.extend([CPoint::ZERO; 32]);
        let mut knots = vec![0., 0., 1., 1.];
        knots.extend([0.; 32]);
        let net = crate::nurbs::crv_basic::Curve::with_indices(points, 1, 1, knots, 3).unwrap();
        assert_eq!(net.cpts().len(), 2);
        assert_eq!(net.knots().len(), 4);
        assert_eq!(net.storage(), (34, 36));
        let curve = Curve::from(BSplineCurve::from_nurb(net, 3, true));
        assert_eq!(
            actual_roots(&k, &MeshWork::new(), &curve, true)
                .unwrap()
                .len(),
            1
        );
        let work = MeshWork::new();
        work.reserve_cells(&k, 2_000_000 - 16).unwrap();
        assert!(matches!(actual_roots(&k,&work,&curve,true),Err(MeshError::BudgetExceeded {..})),
            "inactive full backing exceeds the retained-storage allowance even though active geometry is tiny");
        assert!(matches!(
            work.check(&k),
            Err(MeshError::BudgetExceeded { .. })
        ));
    }
}
