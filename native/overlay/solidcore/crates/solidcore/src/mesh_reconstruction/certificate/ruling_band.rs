//! Whole positive-rational-net band about an exact capped extrusion (not upstream).
//!
//! Native side controls need not have bit-exact H1-H0=D*W: extrusion products round.
//! This constructs an EXACT product witness, projects its base onto NﾂｷP=low along D,
//! and encloses every control residual against the actual stored net. Positive B-spline
//! basis/weights bound the complete surface, not samples or just the end controls.
//! The caller must still prove the actual face trim is the full ruled rectangle, match
//! both actual caps/profile curves, and fit this witness inside actual face/edge/vertex
//! allowances before using a target-product theorem. This band alone never adopts.
//!
//! Deviations: none. No recursion; at most 65,536 ruling control pairs. All scans and
//! internal reference allocations charge the single caller-owned `MeshWork`.
use super::super::work::MeshWork;
use super::exact_geometry as x;
use crate::blend::fillet_section::interval::Ivl;
use crate::kernel::Kernel;
use crate::nurbs::math::{CPoint, NOW, NOZ};
use crate::nurbs::srf_basic::Surface;
use crate::Result;

pub(crate) struct RulingBand {
    /// Exact homogeneous base controls (X,Y,Z,W) after projection. `Q_W=delta`*W,
    /// delta=NﾂｷD>0. The upper controls are `Q_H+D`*`Q_W`, so this is an exact product.
    pub(crate) base_controls: Vec<[x::E; 4]>,
    pub(crate) profile_degree: usize,
    pub(crate) profile_knots: Vec<f64>,
    pub(crate) ruling_parameters: [f64; 2],
    pub(crate) ruling_is_u: bool,
    pub(crate) definition_error_upper: f64,
}
fn enclosure(e: &x::E) -> Option<Ivl> {
    let mut value = Ivl::from(0.0);
    for &a in e {
        value = value.add_ulp(Ivl::from(a));
    }
    value.is_finite().then_some(value)
}
fn norm(v: [Ivl; 3]) -> Option<f64> {
    let [a, b, c] = v;
    let upper = (a * a + b * b + c * c).sqrt().hi;
    (upper.is_finite() && upper >= 0.).then_some(upper)
}
fn point(p: &CPoint) -> Option<x::P> {
    (p.z != NOZ).then(|| x::point([p.x, p.y, p.z])).flatten()
}
fn weight(p: &CPoint) -> Option<f64> {
    let w = if p.w == NOW { 1. } else { p.w };
    (w.is_finite() && w > 0.).then_some(w)
}
fn shifted(h: &x::P, d: &x::P, amount: &x::E) -> Option<x::P> {
    let mut q = Vec::new();
    for (a, b) in h.iter().zip(d) {
        q.push(x::sub(a, &x::mul(b, amount)?)?);
    }
    let [Some(a), Some(b), Some(c)] = [q.first(), q.get(1), q.get(2)] else {
        return None;
    };
    Some([a.clone(), b.clone(), c.clone()])
}
/// Inspect the actual net; `ruling_is_u` and `reverse` are candidate correspondences,
/// never trusted flags. Full knot/control/weight algebra is checked before returning.
pub(crate) fn prove_ruling_band_with_work(
    k: &Kernel,
    work: &MeshWork,
    net: &Surface,
    normal: &x::P,
    low: &x::E,
    d: &x::P,
    ruling_is_u: bool,
    reverse: bool,
) -> Result<Option<RulingBand>> {
    work.spend_core(k, 0)?;
    super::super::budgeted::admit_surface_control_storage_with_work(k, work, net)?;
    let Some(delta) = x::dot(normal, d) else {
        return Ok(None);
    };
    if x::sign(&delta) != Some(1) {
        return Ok(None);
    }
    let ruling_knots = if ruling_is_u {
        net.u_knots()
    } else {
        net.v_knots()
    };
    let [a, b, c, e] = ruling_knots else {
        return Ok(None);
    };
    if !a.is_finite() || !c.is_finite() || a != b || c != e || a >= c {
        return Ok(None);
    }
    if (if ruling_is_u { net.p() } else { net.q() }) != 1 {
        return Ok(None);
    }
    let mut pairs = Vec::new();
    if ruling_is_u {
        let mut rows = net.rows();
        let (Some(a), Some(b), None) = (rows.next(), rows.next(), rows.next()) else {
            return Ok(None);
        };
        if a.len() != b.len() {
            return Ok(None);
        }
        for (a, b) in a.iter().zip(b) {
            work.spend_core(k, 1)?;
            if pairs.len() >= 65_536 {
                return Ok(None);
            }
            work.reserve_cells_core(k, 1)?;
            pairs.push((a, b));
        }
    } else {
        for row in net.rows() {
            work.spend_core(k, 1)?;
            let [a, b] = row else {
                return Ok(None);
            };
            if pairs.len() >= 65_536 {
                return Ok(None);
            }
            work.reserve_cells_core(k, 1)?;
            pairs.push((a, b));
        }
    }
    if pairs.len() < 2 {
        return Ok(None);
    }
    let (profile_degree, profile_knots) = if ruling_is_u {
        (net.q(), net.v_knots())
    } else {
        (net.p(), net.u_knots())
    };
    let profile_count = pairs.len();
    if profile_degree == 0
        || profile_degree > 8
        || profile_count <= profile_degree
        || profile_knots.len() != profile_count + profile_degree + 1
        || profile_knots.len() > 65_536
        || !profile_knots.iter().all(|v| v.is_finite())
        || profile_knots
            .windows(2)
            .any(|p| matches!(p, [a, b] if a > b))
        || !profile_knots
            .get(profile_degree)
            .zip(profile_knots.get(profile_count))
            .is_some_and(|(a, b)| a < b)
    {
        return Ok(None);
    }

    let mut base_controls = Vec::new();
    let mut residual_max = 0.0_f64;
    let mut denominator_min = f64::INFINITY;
    for (a, b) in pairs {
        work.spend_core(k, 1)?;
        let (a, b) = if reverse { (b, a) } else { (a, b) };
        let (Some(wa), Some(wb)) = (weight(a), weight(b)) else {
            return Ok(None);
        };
        if wa != wb {
            return Ok(None);
        }
        let (Some(ha), Some(hb), Some(w)) = (point(a), point(b), x::scalar(wa)) else {
            return Ok(None);
        };
        // A=NﾂｷH0-low*W. Projected exact base controls are
        // (delta*H0-D*A, delta*W); no rounded division defines the witness.
        let Some(excess) = x::dot(normal, &ha).and_then(|v| x::sub(&v, &x::mul(low, &w)?)) else {
            return Ok(None);
        };
        let mut scaled = Vec::new();
        for coord in &ha {
            let Some(v) = x::mul(coord, &delta) else {
                return Ok(None);
            };
            scaled.push(v);
        }
        let [Some(xh), Some(yh), Some(zh)] = [scaled.first(), scaled.get(1), scaled.get(2)] else {
            return Ok(None);
        };
        let Some(q) = shifted(&[xh.clone(), yh.clone(), zh.clone()], d, &excess) else {
            return Ok(None);
        };
        let Some(qw) = x::mul(&delta, &w) else {
            return Ok(None);
        };
        let Some(denominator) = enclosure(&qw) else {
            return Ok(None);
        };
        if !denominator.is_positive() {
            return Ok(None);
        }
        denominator_min = denominator_min.min(denominator.lo);
        // The actual lower/upper residuals are delta*H_actual-Q_H.
        // At the upper end Q_H=Q_base+D*Q_W. The same weights make a complete
        // positive-basis control-hull bound valid throughout both parameters.
        for (h, top) in [(&ha, false), (&hb, true)] {
            let mut residual = Vec::new();
            for ((actual, base), direction) in h.iter().zip(&q).zip(d) {
                let Some(value) = x::mul(actual, &delta)
                    .and_then(|h| x::sub(&h, base))
                    .and_then(|v| {
                        if top {
                            x::sub(&v, &x::mul(direction, &qw)?)
                        } else {
                            Some(v)
                        }
                    })
                else {
                    return Ok(None);
                };
                let Some(value) = enclosure(&value) else {
                    return Ok(None);
                };
                residual.push(value);
            }
            let [Some(&x), Some(&y), Some(&z)] =
                [residual.first(), residual.get(1), residual.get(2)]
            else {
                return Ok(None);
            };
            let Some(bound) = norm([x, y, z]) else {
                return Ok(None);
            };
            residual_max = residual_max.max(bound);
        }
        let [qx, qy, qz] = q;
        work.reserve_cells_core(k, 1)?;
        base_controls.push([qx, qy, qz, qw]);
    }
    if !(denominator_min > 0. && denominator_min.is_finite()) {
        return Ok(None);
    }
    let error = (Ivl::from(residual_max) / Ivl::from(denominator_min)).hi;
    if !(error >= 0. && error.is_finite()) {
        return Ok(None);
    }
    work.reserve_cells_core(k, profile_knots.len())?;
    work.spend_core(k, 0)?;
    Ok(Some(RulingBand {
        base_controls,
        profile_degree,
        profile_knots: profile_knots.to_vec(),
        ruling_parameters: [*a, *c],
        ruling_is_u,
        definition_error_upper: error,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::KernelOptions;
    fn net(perturb: f64) -> Surface {
        Surface::new(
            vec![
                vec![CPoint::new(0., 0., 0., 1.), CPoint::new(2., 0., 0., 1.)],
                vec![
                    CPoint::new(0., 0., 5., 1.),
                    CPoint::new(2., 0., 5. + perturb, 1.),
                ],
            ],
            1,
            1,
            vec![0., 0., 1., 1.],
            vec![0., 0., 1., 1.],
        )
        .unwrap()
    }
    #[test]
    fn ruling_residual_covers_full_net_not_only_one_generator() {
        let k = Kernel::new(&KernelOptions::default());
        let work = MeshWork::new();
        let b = prove_ruling_band_with_work(
            &k,
            &work,
            &net(0.125),
            &x::point([0., 0., 1.]).unwrap(),
            &x::scalar(0.).unwrap(),
            &x::point([0., 0., 5.]).unwrap(),
            true,
            false,
        )
        .unwrap()
        .unwrap();
        assert!(b.definition_error_upper >= 0.125);
        assert!(b.definition_error_upper < 0.126);
    }
    #[test]
    fn invalid_profile_basis_cannot_use_positive_hull_theorem() {
        let k = Kernel::new(&KernelOptions::default());
        let work = MeshWork::new();
        let mut n = net(0.);
        n.v_knots_mut().copy_from_slice(&[0., 1., 0., 1.]);
        assert!(prove_ruling_band_with_work(
            &k,
            &work,
            &n,
            &x::point([0., 0., 1.]).unwrap(),
            &x::scalar(0.).unwrap(),
            &x::point([0., 0., 5.]).unwrap(),
            true,
            false
        )
        .unwrap()
        .is_none());
    }
}
