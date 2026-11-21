//! Exact finite partition of an actual Plane's affine UV-trim image (not upstream).
//! Coordinatewise clamping changes formula only at four possible boundary crossings.
//! Those parameters are exact expansion ratios. On EVERY intervening interval the
//! image is affine, so convex endpoint bounds cover its full domain. Breakpoints
//! are constructed from the actual definition S, never chosen as dense samples.
//! This is a distance/representation bound helper, not independent trim acceptance.
//! Deviations: none; <=6 knots, no recursion, one shared `MeshWork`.
use super::super::work::MeshWork;
use super::exact_geometry as x;
use super::hulls::PointBox;
use crate::blend::fillet_section::interval::Ivl;
use crate::surface::plane::Plane;
use crate::{Kernel, Result, SolidError};
const OP: &str = "mesh_reconstruction::certificate::plane_trim_image";
fn refusal() -> SolidError {
    SolidError::Unsupported {
        operation: OP,
        reason: "actual affine-UV Plane image could not be bounded exactly",
    }
}
struct Ratio {
    n: x::E,
    d: x::E,
}
fn ratio(n: x::E, d: x::E) -> Option<Ratio> {
    match x::sign(&d)? {
        1 => Some(Ratio { n, d }),
        -1 => Some(Ratio {
            n: x::scale(&n, -1.)?,
            d: x::scale(&d, -1.)?,
        }),
        _ => None,
    }
}
fn compare(a: &Ratio, b: &Ratio) -> Option<i32> {
    x::sign(&x::sub(&x::mul(&a.n, &b.d)?, &x::mul(&b.n, &a.d)?)?)
}
fn enclosure(e: &x::E) -> Option<Ivl> {
    let mut a = Ivl::from(0.);
    for &v in e {
        a = a.add_ulp(Ivl::from(v));
    }
    a.is_finite().then_some(a)
}
pub(crate) struct PlaneTrimKnot {
    pub(crate) parameter: Ivl,
    pub(crate) point: PointBox,
}
pub(crate) struct PlaneTrimImage<'a> {
    _plane: &'a Plane,
    /// ALL formula-change parameters, in exact order. Each closed parameter cell's
    /// full actual image is the affine segment between its two enclosed endpoints.
    pub(crate) knots: Vec<PlaneTrimKnot>,
}
pub(crate) fn plane_trim_image_with_work<'a>(
    k: &Kernel,
    work: &MeshWork,
    plane: &'a Plane,
    uv: &[x::P; 2],
) -> Result<PlaneTrimImage<'a>> {
    work.spend_core(k, 64)?;
    if !uv.iter().all(|p| x::zero(&p[2])) {
        return Err(refusal());
    }
    let delta = x::difference(&uv[1], &uv[0]).ok_or_else(refusal)?;
    let zero = ratio(
        x::scalar(0.).ok_or_else(refusal)?,
        x::scalar(1.).ok_or_else(refusal)?,
    )
    .ok_or_else(refusal)?;
    let one = ratio(
        x::scalar(1.).ok_or_else(refusal)?,
        x::scalar(1.).ok_or_else(refusal)?,
    )
    .ok_or_else(refusal)?;
    let mut parameters = vec![zero, one];
    let domain = plane.step_uv_domain();
    let bounds = [
        (domain.u_min(), domain.u_max()),
        (domain.v_min(), domain.v_max()),
    ];
    let clamp = !plane.is_out_of_bounds_enabled();
    if clamp {
        if !domain.is_bounded()
            || bounds
                .iter()
                .any(|&(a, b)| !a.is_finite() || !b.is_finite() || a >= b)
        {
            return Err(refusal());
        }
        for (coordinate, (lo, hi)) in bounds.into_iter().enumerate() {
            if x::zero(delta.get(coordinate).ok_or_else(refusal)?) {
                continue;
            }
            for boundary in [lo, hi] {
                let n = x::scalar(boundary)
                    .and_then(|b| x::sub(&b, uv[0].get(coordinate)?))
                    .ok_or_else(refusal)?;
                let t = ratio(n, delta.get(coordinate).ok_or_else(refusal)?.clone())
                    .ok_or_else(refusal)?;
                if x::sign(&t.n) != Some(1)
                    || x::sub(&t.d, &t.n).and_then(|d| x::sign(&d)) != Some(1)
                {
                    continue;
                }
                let mut at = 0usize;
                let mut duplicate = false;
                while at < parameters.len() {
                    match compare(&t, parameters.get(at).ok_or_else(refusal)?)
                        .ok_or_else(refusal)?
                    {
                        -1 => break,
                        0 => {
                            duplicate = true;
                            break;
                        }
                        _ => at += 1,
                    }
                }
                if !duplicate {
                    parameters.insert(at, t);
                }
            }
        }
    }
    if parameters.len() > 6 {
        return Err(refusal());
    }
    work.reserve_cells_core(k, parameters.len())?;
    let frame = plane.position();
    let origin = x::vec(frame.origin()).ok_or_else(refusal)?;
    let a = x::vec(frame.x_axis()).ok_or_else(refusal)?;
    let b = x::vec(frame.y_axis()).ok_or_else(refusal)?;
    let scale = plane.uv_scale();
    if !scale.x.is_finite() || !scale.y.is_finite() {
        return Err(refusal());
    }
    let mut knots = Vec::new();
    for t in parameters {
        work.spend_core(k, 1)?;
        let mut parameter = Vec::new();
        for coordinate in 0..2 {
            let mut h = x::mul(uv[0].get(coordinate).ok_or_else(refusal)?, &t.d)
                .and_then(|h| x::add(&h, &x::mul(delta.get(coordinate)?, &t.n)?))
                .ok_or_else(refusal)?;
            if clamp {
                let &(lo, hi) = bounds.get(coordinate).ok_or_else(refusal)?;
                let lo = x::scale(&t.d, lo).ok_or_else(refusal)?;
                let hi = x::scale(&t.d, hi).ok_or_else(refusal)?;
                if x::sub(&h, &lo)
                    .and_then(|v| x::sign(&v))
                    .ok_or_else(refusal)?
                    < 0
                {
                    h = lo;
                } else if x::sub(&h, &hi)
                    .and_then(|v| x::sign(&v))
                    .ok_or_else(refusal)?
                    > 0
                {
                    h = hi;
                }
            }
            parameter.push(h);
        }
        let denominator = enclosure(&t.d).ok_or_else(refusal)?;
        if !denominator.is_positive() {
            return Err(refusal());
        }
        let (u, v) = (
            x::scale(parameter.first().ok_or_else(refusal)?, scale.x).ok_or_else(refusal)?,
            x::scale(parameter.get(1).ok_or_else(refusal)?, scale.y).ok_or_else(refusal)?,
        );
        let mut point = Vec::new();
        for ((origin, a), b) in origin.iter().zip(&a).zip(&b) {
            let h = x::mul(origin, &t.d)
                .and_then(|h| x::add(&h, &x::mul(a, &u)?))
                .and_then(|h| x::add(&h, &x::mul(b, &v)?))
                .ok_or_else(refusal)?;
            let value = enclosure(&h).ok_or_else(refusal)? / denominator;
            if !value.is_finite() {
                return Err(refusal());
            }
            point.push(value);
        }
        let parameter = enclosure(&t.n).ok_or_else(refusal)? / denominator;
        if !parameter.is_finite() {
            return Err(refusal());
        }
        let [Some(&x), Some(&y), Some(&z)] = [point.first(), point.get(1), point.get(2)] else {
            return Err(refusal());
        };
        knots.push(PlaneTrimKnot {
            parameter,
            point: [x, y, z],
        });
    }
    work.spend_core(k, 0)?;
    Ok(PlaneTrimImage {
        _plane: plane,
        knots,
    })
}

/// Whole actual clamped affine trim ↔ ONE full coherent affine witness side.
/// The witness is proved clamp-inactive by its complete endpoint hull; actual
/// clamp formula changes use the SAME exact event partition above. This is a
/// same-parameter bound on EVERY cell, not an endpoint-only matching predicate.
pub(crate) struct AffinePlanePair {
    pub(crate) distance_upper: f64,
    pub(crate) actual_endpoints: [PointBox; 2],
}
pub(crate) fn affine_plane_pair_with_work(
    k: &Kernel,
    work: &MeshWork,
    plane: &Plane,
    actual: &[x::P; 2],
    witness: &[x::P; 2],
) -> Result<AffinePlanePair> {
    work.spend_core(k, 0)?;
    let domain = plane.step_uv_domain();
    for p in witness {
        for (coordinate, (lo, hi)) in [
            (domain.u_min(), domain.u_max()),
            (domain.v_min(), domain.v_max()),
        ]
        .into_iter()
        .enumerate()
        {
            let h = p.get(coordinate).ok_or_else(refusal)?;
            if x::sub(h, &x::scalar(lo).ok_or_else(refusal)?)
                .and_then(|v| x::sign(&v))
                .is_none_or(|s| s < 0)
                || x::sub(&x::scalar(hi).ok_or_else(refusal)?, h)
                    .and_then(|v| x::sign(&v))
                    .is_none_or(|s| s < 0)
            {
                return Err(refusal());
            }
        }
    }
    let actual = plane_trim_image_with_work(k, work, plane, actual)?;
    let model = plane_trim_image_with_work(k, work, plane, witness)?;
    let [a, z] = model.knots.as_slice() else {
        return Err(refusal());
    };
    let [ax, ay, az] = a.point;
    let [zx, zy, zz] = z.point;
    let mut upper = 0.0_f64;
    for knot in &actual.knots {
        work.spend_core(k, 1)?;
        let t = knot.parameter;
        let same_parameter = [ax + (zx - ax) * t, ay + (zy - ay) * t, az + (zz - az) * t];
        upper = upper.max(super::hulls::point_distance_upper(
            knot.point,
            same_parameter,
        )?);
    }
    let (Some(a), Some(z)) = (actual.knots.first(), actual.knots.last()) else {
        return Err(refusal());
    };
    work.spend_core(k, 0)?;
    Ok(AffinePlanePair {
        distance_upper: upper,
        actual_endpoints: [a.point, z.point],
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        geom::extent2d::Extent2d,
        kernel::KernelOptions,
        math::{Point3, Vec2, Vec3},
    };
    #[test]
    fn an_interior_clamp_corner_is_not_hidden_by_matching_endpoints() {
        let k = Kernel::new(&KernelOptions::default());
        let work = MeshWork::new();
        let p = Plane::new(
            Point3::new(0., 0., 0.),
            Vec3::new(1., 0., 0.),
            Vec3::new(0., 1., 0.),
            Vec2::new(1., 1.),
            &Extent2d::from_bounds(0., 0., 5., 20.),
        );
        let uv = [
            x::point([-1., 0., 0.]).unwrap(),
            x::point([1., 2., 0.]).unwrap(),
        ];
        let image = plane_trim_image_with_work(&k, &work, &p, &uv).unwrap();
        assert_eq!(image.knots.len(), 3);
        let mid = &image.knots[1];
        assert!(mid.parameter.lo <= 0.5 && mid.parameter.hi >= 0.5);
        assert!(
            mid.point[0].lo <= 0.
                && mid.point[0].hi >= 0.
                && mid.point[1].lo <= 1.
                && mid.point[1].hi >= 1.
        );
        // Linear interpolation between clamped ENDPOINTS would give(0.5,1),
        // missing the actual whole-image corner by0.5 despite perfect end matches.
        let distance = super::super::hulls::point_distance_upper(
            mid.point,
            [Ivl::from(0.5), Ivl::from(1.), Ivl::from(0.)],
        )
        .unwrap();
        assert!(distance >= 0.5);
    }
    #[test]
    fn same_parameter_plane_pair_covers_an_interior_clamp_kink_with_matching_ends() {
        let k = Kernel::new(&KernelOptions::default());
        let work = MeshWork::new();
        let plane = Plane::new(
            Point3::ZERO,
            Vec3::X,
            Vec3::Y,
            Vec2::new(1., 1.),
            &Extent2d::from_bounds(0., 0., 5., 20.),
        );
        let actual = [
            x::point([-1., 0., 0.]).unwrap(),
            x::point([1., 2., 0.]).unwrap(),
        ];
        let model = [
            x::point([0., 0., 0.]).unwrap(),
            x::point([1., 2., 0.]).unwrap(),
        ];
        let bound = affine_plane_pair_with_work(&k, &work, &plane, &actual, &model).unwrap();
        assert!(bound.distance_upper >= 0.5 && bound.distance_upper < 0.501);
        // Exact endpoint agreement does NOT authorize zero error for the kink.
        assert!(bound.actual_endpoints[0][0].lo <= 0. && bound.actual_endpoints[1][0].hi >= 1.);
    }
}
