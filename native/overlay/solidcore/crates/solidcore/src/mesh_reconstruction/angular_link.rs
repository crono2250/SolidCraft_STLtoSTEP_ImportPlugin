//! Shared complete angular-link proof for canonical analytic cone apex stars.
//! No point-sampled winding sum; every edge turn and crossing is interval certified.
use super::primitive_certificate::{cross, dot, norm, normalized, scale, sub, PointBox};
use super::types::{MeshError, Result};
use super::MeshWork;
use crate::blend::fillet_section::interval::Ivl;
use crate::Kernel;
const OP: &str = "mesh_reconstruction::angular_link";

pub(crate) fn certify_angular_link(
    k: &Kernel,
    work: &MeshWork,
    link: &[PointBox],
    axis: PointBox,
) -> Result<()> {
    if link.len() < 3 || link.len() > 200_000 {
        return Err(MeshError::Undecided {
            stage: OP,
            work: link.len(),
        });
    }
    work.spend(k, link.len())?;
    work.reserve_output(k, link.len())?;
    let radial: Vec<_> = link
        .iter()
        .map(|p| sub(*p, scale(axis, dot(*p, axis))))
        .collect();
    for p in &radial {
        if !norm(*p).is_finite() || norm(*p).lo <= 0. {
            return Err(MeshError::Undecided {
                stage: OP,
                work: link.len(),
            });
        }
    }
    let mut sense = None;
    for (a, b) in radial
        .iter()
        .zip(radial.iter().cycle().skip(1))
        .take(radial.len())
    {
        let d = dot(axis, cross(*a, *b));
        let sign = if d.lo > 0. {
            1i32
        } else if d.hi < 0. {
            -1i32
        } else {
            return Err(MeshError::Undecided {
                stage: OP,
                work: link.len(),
            });
        };
        if sense.is_some_and(|old| old != sign) {
            return Err(MeshError::Refused {
                stage: OP,
                detail: "the apex link reverses angular direction".into(),
            });
        }
        sense = Some(sign);
    }
    // Fixed exact integer rays choose a crossing basis only; all crossing signs are
    // full interval statements about the original link, never samples of its angular sum.
    for (rx, ry, rz) in [
        (1., 0., 0.),
        (0., 1., 0.),
        (0., 0., 1.),
        (1., 2., 3.),
        (2., 3., 5.),
        (3., 5., 7.),
        (5., 7., 11.),
        (7., 11., 13.),
        (11., 13., 17.),
        (13., 17., 19.),
        (17., 19., 23.),
        (19., 23., 29.),
        (23., 29., 31.),
        (29., 31., 37.),
        (31., 37., 41.),
        (37., 41., 43.),
    ] {
        work.spend(k, radial.len())?;
        let ray = [Ivl::from(rx), Ivl::from(ry), Ivl::from(rz)];
        let Some(u) = normalized(sub(ray, scale(axis, dot(ray, axis)))) else {
            continue;
        };
        let v = cross(axis, u);
        work.reserve_output(k, radial.len())?;
        let points: Vec<_> = radial.iter().map(|p| (dot(*p, u), dot(*p, v))).collect();
        if points
            .iter()
            .any(|(x, y)| !x.is_finite() || !y.is_finite() || !(y.lo > 0. || y.hi < 0.))
        {
            continue;
        }
        let (mut winding, mut decided) = (0i32, true);
        for ((x0, y0), (x1, y1)) in points
            .iter()
            .zip(points.iter().cycle().skip(1))
            .take(points.len())
        {
            if (y0.lo > 0.) == (y1.lo > 0.) {
                continue;
            }
            let determinant = x0.mul_ulp(*y1).sub_ulp(x1.mul_ulp(*y0));
            if !(determinant.lo > 0. || determinant.hi < 0.) {
                decided = false;
                break;
            }
            if y0.hi < 0. && y1.lo > 0. && determinant.lo > 0. {
                winding += 1;
            }
            if y0.lo > 0. && y1.hi < 0. && determinant.hi < 0. {
                winding -= 1;
            }
        }
        if decided {
            if winding.abs() == 1 && sense == Some(winding) {
                return Ok(());
            }
            return Err(MeshError::Refused {
                stage: OP,
                detail: "the apex link does not have angular degree one".into(),
            });
        }
    }
    Err(MeshError::Undecided {
        stage: OP,
        work: link.len().saturating_mul(16),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn angular_degree_two_is_not_mistaken_for_a_complete_simple_apex() {
        let make = |turns: f64| -> Vec<PointBox> {
            (0..128)
                .map(|i| {
                    let angle = std::f64::consts::TAU * turns * f64::from(i) / 128.;
                    [
                        Ivl::from(angle.cos()),
                        Ivl::from(angle.sin()),
                        Ivl::from(1.),
                    ]
                })
                .collect()
        };
        let k = Kernel::default();
        assert!(certify_angular_link(
            &k,
            &MeshWork::new(),
            &make(1.),
            [Ivl::from(0.), Ivl::from(0.), Ivl::from(1.)]
        )
        .is_ok());
        assert!(certify_angular_link(
            &k,
            &MeshWork::new(),
            &make(2.),
            [Ivl::from(0.), Ivl::from(0.), Ivl::from(1.)]
        )
        .is_err());
    }
}
