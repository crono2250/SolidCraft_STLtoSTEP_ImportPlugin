//! Full original rational trim/edge roots as a degree-one radial graph.
//!
//! Every retained root is projected into one exact axial reference frame.
//! Bernstein hulls bound radius and height, and a signed homogeneous angular
//! derivative plus an open half plane exclude backtracking on each root.
//! Complete exact projective endpoint joins and one angular link degree bind
//! the roots into one simple closed curve. The graph is over a fixed circle:
//! its same-ray/same-height pair directly gives a two-sided value bound.
//!
//! Only ordinary positive rational curve evaluators belong here. The return
//! value does not certify a face, Native material or the full B-rep by itself.
//! Deviations: none. At most 64 roots, degree <=4, shared MeshWork.
use super::super::actual_roots::{actual_used_roots, ActualRoot};
use super::super::angular_link::certify_angular_link;
use super::super::{MeshError, MeshWork};
use super::analytic_ruling::eval_error;
use super::exact_geometry as x;
use super::hulls::{radial_curve_turn_with_work, CurveBounds, PointBox};
use super::radial_frame::AxialEndpointProposal;
use crate::blend::fillet_section::interval::Ivl;
use crate::curve::curve::{Curve, CurveKind};
use crate::geom::extent1d::Extent1d;
use crate::offset::construction::bernstein::Bernstein2;
use crate::query::distance_bound::Piece;
use crate::{Kernel, Result, SolidError};

const OP: &str = "mesh_reconstruction::certificate::radial_curve";
fn refused(reason: &'static str) -> SolidError {
    SolidError::Unsupported {
        operation: OP,
        reason,
    }
}
fn ordinary<T>(k: &Kernel, w: &MeshWork, result: super::super::Result<T>) -> Result<T> {
    w.spend_core(k, 0)?;
    match result {
        Ok(v) => Ok(v),
        Err(MeshError::Kernel(e)) => Err(e),
        Err(_) => Err(refused("cannot prove all actual used curve roots")),
    }
}

fn cross([a, b, c]: PointBox, [d, e, f]: PointBox) -> PointBox {
    [b * f - c * e, c * d - a * f, a * e - b * d]
}
fn dot(a: PointBox, b: PointBox) -> Ivl {
    a.into_iter()
        .zip(b)
        .fold(Ivl::from(0.), |q, (a, b)| q + a * b)
}
fn add([a, b, c]: PointBox, [d, e, f]: PointBox) -> PointBox {
    [a + d, b + e, c + f]
}
fn minus([a, b, c]: PointBox, [d, e, f]: PointBox) -> PointBox {
    [a - d, b - e, c - f]
}
fn scale(p: PointBox, s: Ivl) -> PointBox {
    p.map(|a| a * s)
}
fn norm(p: PointBox) -> Ivl {
    let [a, b, c] = p.map(|v| Ivl::from(v.mag()));
    (a * a + b * b + c * c).sqrt()
}
struct Projection {
    origin: PointBox,
    dual: [PointBox; 3],
    radial_norm: f64,
    axial_norm: f64,
}
fn projection(chart: &AxialEndpointProposal, center: [f64; 2], z: f64) -> Result<Projection> {
    let [a, b, c] = chart.columns.map(|row| row.map(Ivl::from));
    let [x, y] = center.map(Ivl::from);
    let origin = add(
        add(add(chart.origin.map(Ivl::from), scale(a, x)), scale(b, y)),
        scale(c, Ivl::from(z)),
    );
    let rows = [cross(b, c), cross(c, a), cross(a, b)];
    let det = dot(a, cross(b, c));
    if !det.is_finite() || !det.is_positive() || origin.iter().any(|q| !q.is_finite()) {
        return Err(refused("axial curve chart is not proved invertible"));
    }
    let dual = rows.map(|p| p.map(|v| v / det));
    let na = norm(a);
    let nb = norm(b);
    let radial = (na * na + nb * nb).sqrt();
    let axial = norm(c);
    if !radial.is_finite() || !axial.is_finite() || dual.iter().flatten().any(|v| !v.is_finite()) {
        return Err(refused("axial curve chart has an unbounded metric"));
    }
    Ok(Projection {
        origin,
        dual,
        radial_norm: radial.hi,
        axial_norm: axial.hi,
    })
}
fn projected(k: &Kernel, w: &MeshWork, f: &Projection, piece: &Piece) -> Result<(Piece, f64)> {
    let [x, y, z, weight] = &piece.h;
    let (degree, v) = weight.degrees();
    if v != 0 || !(1..=4).contains(&degree) || piece.h.iter().any(|p| p.degrees() != (degree, 0)) {
        return Err(refused("unsupported rational dimension of radial curve"));
    }
    w.spend_core(k, 1_024)?;
    w.reserve_cells_core(k, 256)?;
    let uncertainty = Ivl::new(-piece.err, piece.err);
    let mut error = 0_f64;
    let mut altitude = 0_f64;
    let mut coordinates: [Vec<f64>; 4] = core::array::from_fn(|_| Vec::new());
    for (((&x, &y), &z), &ww) in x
        .coefficients()
        .iter()
        .zip(y.coefficients())
        .zip(z.coefficients())
        .zip(weight.coefficients())
    {
        w.spend_core(k, 32)?;
        let ww = Ivl::from(ww) + uncertainty;
        if !ww.is_finite() || !ww.is_positive() {
            return Err(refused(
                "cannot bound complete radial curve weight positively",
            ));
        }
        let point = minus(
            [x, y, z].map(|v| Ivl::from(v) + uncertainty),
            scale(f.origin, ww),
        );
        let [u, v, h] = f.dual.map(|axis| dot(axis, point));
        let height = h / ww;
        if !height.is_finite() {
            return Err(refused("whole radial curve height is not finite"));
        }
        altitude = altitude.max(height.mag());
        for (out, val) in coordinates.iter_mut().zip([u, v, Ivl::from(0.), ww]) {
            if !val.is_finite() {
                return Err(refused("radial chart root control is not finite"));
            }
            let mid = 0.5 * val.lo + 0.5 * val.hi;
            error = error.max((val - Ivl::from(mid)).mag());
            out.push(mid);
        }
    }
    let [u, v, z, a] = coordinates;
    Ok((
        Piece {
            h: [
                Bernstein2::new(degree, 0, u)?,
                Bernstein2::new(degree, 0, v)?,
                Bernstein2::new(degree, 0, z)?,
                Bernstein2::new(degree, 0, a)?,
            ],
            err: error,
            lower: 0.,
            depth: 0,
            uv: piece.uv,
            parameter_ends: piece.parameter_ends,
        },
        altitude,
    ))
}
fn endpoint(piece: &Piece, last: bool) -> Result<[f64; 4]> {
    let [a, b, c, d] = piece.h.each_ref().map(|p| {
        if last {
            p.coefficients().last().copied()
        } else {
            p.coefficients().first().copied()
        }
    });
    let [Some(a), Some(b), Some(c), Some(d)] = [a, b, c, d] else {
        return Err(refused("closed curve endpoint control is absent"));
    };
    Ok([a, b, c, d])
}
fn same_projective(a: [f64; 4], b: [f64; 4]) -> bool {
    let [ax, ay, az, aw] = a;
    let [bx, by, bz, bw] = b;
    aw > 0.
        && bw > 0.
        && [ax, ay, az].into_iter().zip([bx, by, bz]).all(|(a, b)| {
            (|| {
                x::sub(
                    &x::mul(&x::scalar(a)?, &x::scalar(bw)?)?,
                    &x::mul(&x::scalar(b)?, &x::scalar(aw)?)?,
                )
            })()
            .is_some_and(|q| x::zero(&q))
        })
}
fn radial_point(piece: &Piece) -> Result<PointBox> {
    let [x, y, _, w] = endpoint(piece, false)?;
    let e = Ivl::new(-piece.err, piece.err);
    let weight = Ivl::from(w) + e;
    if !weight.is_positive() {
        return Err(refused("radial degree vertex lacks a positive weight"));
    }
    Ok([
        (Ivl::from(x) + e) / weight,
        (Ivl::from(y) + e) / weight,
        Ivl::from(0.),
    ])
}

pub(crate) struct NativeRadialCurve<'a> {
    _curve: &'a Curve,
    pub(crate) world_error_upper: f64,
    pub(crate) sense: i32,
}
pub(crate) fn prove_native_radial_curve_with_work<'a>(
    k: &Kernel,
    w: &MeshWork,
    curve: &'a Curve,
    used: Extent1d,
    forward: bool,
    chart: &AxialEndpointProposal,
    center: [f64; 2],
    height: f64,
    radius: f64,
    allowance: f64,
) -> Result<NativeRadialCurve<'a>> {
    w.spend_core(k, 128)?;
    if !radius.is_finite() || radius <= 0. || !allowance.is_finite() || allowance < 0. {
        return Err(refused(
            "target radial curve needs a finite positive reference ring",
        ));
    }
    let base = match curve.kind() {
        CurveKind::BSpline(base) => base,
        CurveKind::Ellipse(ellipse) => ellipse.base(),
        _ => {
            return Err(refused(
                "radial edge evaluator is not a stored rational curve",
            ))
        }
    };
    let rational = base
        .gw_nurb()
        .ok_or_else(|| refused("actual rational edge is missing its control net"))?
        .is_rational();
    let roots = ordinary(k, w, actual_used_roots(k, w, curve, used, forward))?;
    if !(3..=64).contains(&roots.len()) {
        return Err(refused(
            "complete radial edge root partition is unsupported",
        ));
    }
    let projection = projection(chart, center, height)?;
    let bounds = CurveBounds::new(k, w)?;
    let mut link = Vec::new();
    let mut sense = None;
    let mut world = 0_f64;
    for (root, next) in roots.iter().zip(roots.iter().cycle().skip(1)) {
        w.spend_core(k, 512)?;
        w.reserve_cells_core(k, 256)?;
        if root.piece.err != 0.
            || next.piece.err != 0.
            || !same_projective(endpoint(&root.piece, true)?, endpoint(&next.piece, false)?)
        {
            return Err(refused(
                "complete radial edge roots do not share exact projective joins",
            ));
        }
        let (radial, z) = projected(k, w, &projection, &root.piece)?;
        let sign = radial_curve_turn_with_work(k, w, &radial)?;
        if sense.is_some_and(|previous| previous != sign) {
            return Err(refused("actual edge reverses radial angular direction"));
        }
        sense = Some(sign);
        let point = radial_point(&radial)?;
        w.reserve_output_core(k, 1)?;
        link.push(point);
        let delta = bounds
            .radial(&radial, [Ivl::from(0.); 3], radius)?
            .distance_upper;
        // eval_error expects increasing native parameter bounds. Reversing
        // the control rows never changes its operation count or range bound.
        let [a, b] = root.native_interval;
        let eval_root = ActualRoot {
            piece: root.piece.clone(),
            native_interval: [a.min(b), a.max(b)],
        };
        let eval = eval_error(k, w, &eval_root, rational)?;
        let distance = Ivl::from(delta) * Ivl::from(projection.radial_norm)
            + Ivl::from(z) * Ivl::from(projection.axial_norm)
            + Ivl::from(eval);
        if !distance.is_finite() || distance.hi > allowance {
            return Err(refused("whole radial edge exceeds its supplied allowance"));
        }
        world = world.max(distance.hi);
    }
    ordinary(
        k,
        w,
        certify_angular_link(k, w, &link, [Ivl::from(0.), Ivl::from(0.), Ivl::from(1.)]),
    )?;
    Ok(NativeRadialCurve {
        _curve: curve,
        world_error_upper: world,
        sense: sense.ok_or_else(|| refused("closed edge has no angular sense"))?,
    })
}

/// The exact affine image of every full UV Bernstein root on an ordinary
/// Plane. Proving the positive-weight convex hull lies inside the evaluator
/// rectangle also keeps the entire filled disk inside that same rectangle.
fn plane_root_image(
    k: &Kernel,
    w: &MeshWork,
    root: &Piece,
    plane: &crate::surface::plane::Plane,
) -> Result<(Piece, f64)> {
    use super::analytic_ruling::{controls, piece};
    let [u, v, _, den] = &root.h;
    let (degree, vertical) = den.degrees();
    if root.err != 0. || vertical != 0 || !(1..=4).contains(&degree) {
        return Err(refused(
            "cap UV curve does not have exact rational controls",
        ));
    }
    let bounds = plane.step_uv_domain();
    let us = plane.uv_scale();
    let pos = plane.position();
    let shift = pos.origin().to_array().map(Ivl::from);
    let lift = |s, a: crate::math::Vec3| a.to_array().map(|v| Ivl::from(v) * Ivl::from(s));
    let a = lift(us.x, pos.x_axis());
    let b = lift(us.y, pos.y_axis());
    w.spend_core(k, 256)?;
    w.reserve_cells_core(k, 64)?;
    let in_bounds = |h: f64, weight: f64, lo: f64, hi: f64| -> Option<bool> {
        let hw = x::scalar(h)?;
        let lw = x::mul(&x::scalar(lo)?, &x::scalar(weight)?)?;
        let uw = x::mul(&x::scalar(hi)?, &x::scalar(weight)?)?;
        Some(x::sign(&x::sub(&hw, &lw)?)? >= 0 && x::sign(&x::sub(&uw, &hw)?)? >= 0)
    };
    let mut magnitude = 0_f64;
    for ((&u, &v), &weight) in u
        .coefficients()
        .iter()
        .zip(v.coefficients())
        .zip(den.coefficients())
    {
        if weight <= 0.
            || (!plane.is_out_of_bounds_enabled()
                && (!bounds.is_bounded()
                    || in_bounds(u, weight, bounds.u_min(), bounds.u_max()) != Some(true)
                    || in_bounds(v, weight, bounds.v_min(), bounds.v_max()) != Some(true)))
        {
            return Err(refused(
                "complete cap UV control hull crosses an evaluator clamp",
            ));
        }
        let u = Ivl::from(u) / Ivl::from(weight);
        let v = Ivl::from(v) / Ivl::from(weight);
        let op = norm(shift) + norm(a) * Ivl::from(u.mag()) + norm(b) * Ivl::from(v.mag());
        if !op.is_finite() || op.hi >= f64::MAX / 128. {
            return Err(refused(
                "complete cap affine evaluator range is not bounded",
            ));
        }
        magnitude = magnitude.max(op.hi);
    }
    let lifted = piece(
        k,
        w,
        controls(root)?.map(|[u, v, _, ww]| {
            let [x, y, z] = add(add(scale(shift, ww), scale(a, u)), scale(b, v));
            [x, y, z, ww]
        }),
        degree,
    )?;
    // Per coordinate: two scaled parameters, two axis products, two sums.
    // 64 epsilons cover the 3D norm of those errors, with margin for gradual
    // underflow; this does not include the rational UV evaluator error.
    let error =
        Ivl::from(magnitude) * Ivl::from(64. * f64::EPSILON) + Ivl::from(64. * f64::MIN_POSITIVE);
    Ok((lifted, error.hi))
}

/// Complete same-parameter trim-to-edge bound plus a radial-disk proof for one
/// planar end cap of a canonical Native frustum. The caller has already proved
/// that this one circular edge is the complete cap and conical side boundary.
pub(crate) fn prove_native_radial_cap_with_work(
    k: &Kernel,
    work: &MeshWork,
    plane: &crate::surface::plane::Plane,
    pcurve: &Curve,
    edge: &Curve,
    used: Extent1d,
    forward: bool,
    chart: &AxialEndpointProposal,
    center: [f64; 2],
    height: f64,
    radius: f64,
    allowance: f64,
) -> Result<(f64, i32)> {
    use super::super::actual_roots::actual_uv_roots;
    if !radius.is_finite() || radius <= 0. || !allowance.is_finite() || allowance <= 0. {
        return Err(refused(
            "radial cap is missing positive radius and allowance",
        ));
    }
    if pcurve.natural_interval() != used {
        return Err(refused(
            "actual cap UV and 3D edge use different whole ranges",
        ));
    }
    let world = ordinary(k, work, actual_used_roots(k, work, edge, used, forward))?;
    let uv = ordinary(k, work, actual_uv_roots(k, work, pcurve, forward))?;
    if world.len() != uv.len()
        || !(3..=64).contains(&world.len())
        || world
            .iter()
            .zip(&uv)
            .any(|(a, b)| a.native_interval != b.native_interval)
    {
        return Err(refused(
            "actual cap UV and 3D edge roots use different partitions",
        ));
    }
    let rational = |curve: &Curve| {
        let base = match curve.kind() {
            CurveKind::BSpline(base) => base,
            CurveKind::Ellipse(ellipse) => ellipse.base(),
            _ => {
                return Err(refused(
                    "radial cap needs actual rational trim and edge curves",
                ))
            }
        };
        Ok(base
            .gw_nurb()
            .ok_or_else(|| refused("radial cap rational control net is missing"))?
            .is_rational())
    };
    let uv_rational = rational(pcurve)?;
    let xyz_rational = rational(edge)?;
    let chart_projection = projection(chart, center, height)?;
    let plane_orientation = plane.position();
    let scales = plane.uv_scale();
    let axis_x = scale(
        plane_orientation.x_axis().to_array().map(Ivl::from),
        Ivl::from(scales.x),
    );
    let axis_y = scale(
        plane_orientation.y_axis().to_array().map(Ivl::from),
        Ivl::from(scales.y),
    );
    let [u, v, _] = chart_projection.dual;
    let det = dot(u, axis_x) * dot(v, axis_y) - dot(u, axis_y) * dot(v, axis_x);
    let gain = (norm(axis_x) * norm(axis_x) + norm(axis_y) * norm(axis_y)).sqrt();
    if !det.is_finite() || (det.lo <= 0. && det.hi >= 0.) || !gain.is_finite() {
        return Err(refused(
            "cap plane projection is not proved injective over the whole disk",
        ));
    }
    let bounds = CurveBounds::new(k, work)?;
    let mut link = Vec::new();
    let mut direction = None;
    let mut upper = 0_f64;
    for ((uv, next), xyz) in uv.iter().zip(uv.iter().cycle().skip(1)).zip(&world) {
        if uv.piece.err != 0.
            || next.piece.err != 0.
            || !same_projective(endpoint(&uv.piece, true)?, endpoint(&next.piece, false)?)
        {
            return Err(refused(
                "actual cap UV roots are not a complete joined loop",
            ));
        }
        let (lifted, plane_error) = plane_root_image(k, work, &uv.piece, plane)?;
        let (radial, vertical) = projected(k, work, &chart_projection, &lifted)?;
        let sign = radial_curve_turn_with_work(k, work, &radial)?;
        if direction.replace(sign).is_some_and(|prev| prev != sign) {
            return Err(refused("actual cap angular orientation reverses"));
        }
        work.reserve_output_core(k, 1)?;
        link.push(radial_point(&radial)?);
        let calc_eval = |root: &ActualRoot, has_weights| -> Result<Ivl> {
            work.reserve_cells_core(k, 64)?;
            let [a, b] = root.native_interval;
            let r = ActualRoot {
                piece: root.piece.clone(),
                native_interval: [a.min(b), a.max(b)],
            };
            Ok(Ivl::from(eval_error(k, work, &r, has_weights)?))
        };
        let cap_eval = calc_eval(uv, uv_rational)? * gain + Ivl::from(plane_error);
        let gap = Ivl::from(bounds.paired(&lifted, &xyz.piece)?)
            + cap_eval
            + calc_eval(xyz, xyz_rational)?;
        if !gap.is_finite() || gap.hi > allowance {
            return Err(refused(
                "whole cap trim does not match its physical edge at the same parameter",
            ));
        }
        let radius_error = bounds
            .radial(&radial, [Ivl::from(0.); 3], radius)?
            .distance_upper;
        // The nonsingular planar chart and complete simple radial loop show
        // the filled cap is a disk. At every ray interpolate from the axis
        // intersection to the rim, so the complete rim bound bounds interior
        // radius and altitude too (the plane height is affine).
        let distance = Ivl::from(radius_error) * Ivl::from(chart_projection.radial_norm)
            + Ivl::from(vertical) * Ivl::from(chart_projection.axial_norm)
            + cap_eval;
        if !distance.is_finite() || distance.hi > allowance {
            return Err(refused(
                "whole filled cap exceeds its radial disk allowance",
            ));
        }
        upper = upper.max(distance.hi).max(gap.hi);
    }
    ordinary(
        k,
        work,
        certify_angular_link(
            k,
            work,
            &link,
            [Ivl::from(0.), Ivl::from(0.), Ivl::from(1.)],
        ),
    )?;
    Ok((
        upper,
        direction.ok_or_else(|| refused("actual filled cap has no radial orientation"))?,
    ))
}
