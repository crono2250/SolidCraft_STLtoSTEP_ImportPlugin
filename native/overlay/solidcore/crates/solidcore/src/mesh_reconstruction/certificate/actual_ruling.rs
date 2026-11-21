//! Binds whole ruled-net product bands to an ACTUAL authoritative surface (not upstream).
//! A raw `RulingBand` is only algebra on a supplied net. This constructor additionally
//! borrows the exact final Surface, rejects every carried/procedural definition, and
//! admits net-evaluator families `BSpline` and `SurfOfExtrusion`. A complete Plane
//! rectangle is enclosed from its actual affine definition, never its cached net.
//! Constant-radius Cone is admitted only with the retained full actual evaluator
//! authority, added once to its net-to-model residual. A label is never authority.
//! Nonconstant-radius frustums remain outside this constant-translation model.
//! The returned band covers the complete natural rectangle, not an arbitrary trim.
//! Native face rectangle/edge/vertex/cap/CW correspondence remains mandatory before
//! a full product-solid certificate. This token alone authorizes no adoption.
//! Deviations: none; fixed family dispatch and shared `MeshWork`, no recursion.
use super::super::work::MeshWork;
use super::analytic_ruling::{prove_analytic_net_with_work, AnalyticNetAuthority};
use super::exact_geometry as x;
use super::hulls::{CurveBounds, PointBox};
use super::ruling_band::{prove_ruling_band_with_work, RulingBand};
use crate::blend::fillet_section::interval::Ivl;
use crate::nurbs::{
    math::{CPoint, NOW, NOZ},
    srf_basic,
};
use crate::offset::construction::bernstein::Bernstein2;
use crate::query::distance_bound::Piece;
use crate::surface::{
    plane::Plane,
    surface::{Surface, SurfaceKind},
};
use crate::{Kernel, Result, SolidError};
const OP: &str = "mesh_reconstruction::certificate::actual_ruling";
fn refused(reason: &'static str) -> SolidError {
    SolidError::Unsupported {
        operation: OP,
        reason,
    }
}
fn invariant(reason: &'static str) -> SolidError {
    SolidError::PortInvariant {
        operation: OP,
        reason,
    }
}
pub(crate) struct ActualRulingBand<'a> {
    definition: &'a Surface,
    band: RulingBand,
    domain: [f64; 4],
    reverse_ruling: bool,
    // Retains the SAME evaluator and Kernel arithmetic context for analytic sides.
    authority: Option<AnalyticNetAuthority<'a>>,
}
impl<'a> ActualRulingBand<'a> {
    /// Whole retained mathematical-net normal projected onto `normal`, with its native
    /// u/v orientation. Only the caller's independently proved full-multiplicity
    /// root partition may select `root`; this scalar proof is not domain coverage.
    /// Restrict each actual ruling row via the existing coefficient-error-carrying
    /// Piece restriction, then reuse the native Bernstein derivative certificate.
    #[cfg(test)]
    pub(crate) fn orientation_lower_with_work(
        &self,
        k: &Kernel,
        work: &MeshWork,
        root: usize,
        unit: [f64; 2],
        normal: PointBox,
    ) -> Result<f64> {
        let bounds = CurveBounds::new(k, work)?;
        self.orientation_lower_in_bounds(&bounds, root, unit, normal)
    }
    /// Retains the existing complete native net/Plane sign check, sharing the
    /// caller's same workflow/table. No generic normal-repair proof is claimed.
    pub(crate) fn orientation_lower_in_bounds(
        &self,
        bounds: &CurveBounds<'_>,
        root: usize,
        unit: [f64; 2],
        normal: PointBox,
    ) -> Result<f64> {
        let (k, work) = bounds.context();
        work.spend_core(k, 0)?;
        if let Some(authority) = &self.authority {
            if !core::ptr::eq(authority.kernel(), k)
                || !core::ptr::eq(authority.definition(), self.definition)
                || authority.domain() != self.domain
            {
                return Err(invariant("analytic ruling authority context changed"));
            }
        }
        if let SurfaceKind::Plane(plane) = self.definition.kind_with_nurb(k)? {
            return plane_orientation(plane, normal);
        }
        let base = match self.definition.kind_with_nurb(k)? {
            SurfaceKind::BSpline(base) => std::borrow::Cow::Borrowed(base),
            SurfaceKind::Cone(cone) if self.authority.is_some() => {
                std::borrow::Cow::Borrowed(cone.rev().base())
            }
            SurfaceKind::SurfOfExtrusion(_) => self.definition.extrusion_base_with_nurb(k)?,
            _ => {
                return Err(invariant(
                    "actual ruling family changed while immutably borrowed",
                ))
            }
        };
        // Keep an owned extrusion-evaluation Cow alive until all controls have
        // been consumed; no reference may escape a temporary generated base.
        let net = base
            .gw_nurb()
            .ok_or_else(|| invariant("certified actual evaluator net missing"))?;
        let piece = actual_root_piece(k, work, net, self.band(), root, unit)?;
        let normal = if self.band.ruling_is_u {
            normal.map(|v| Ivl {
                lo: -v.hi,
                hi: -v.lo,
            })
        } else {
            normal
        };
        bounds.orientation(&piece, normal)
    }
    pub(crate) fn definition(&self) -> &'a Surface {
        self.definition
    }
    pub(crate) fn band(&self) -> &RulingBand {
        &self.band
    }
    /// Native ruling max is the original low end when this is true.
    pub(crate) fn reverse_ruling(&self) -> bool {
        self.reverse_ruling
    }
    pub(crate) fn domain(&self) -> [f64; 4] {
        self.domain
    }
}
/// Uses synthetic parameters (profile, native-increasing ruling), hence its
/// cross normal changes sign when native ruling is u. The caller accounts for
/// that swap explicitly; no surface-normal orientation is guessed from a sample.
fn actual_root_piece(
    k: &Kernel,
    work: &MeshWork,
    net: &srf_basic::Surface,
    band: &RulingBand,
    root: usize,
    unit: [f64; 2],
) -> Result<Piece> {
    super::super::budgeted::admit_surface_control_storage_with_work(k, work, net)?;
    let p = band.profile_degree;
    if !(1..=8).contains(&p) {
        return Err(refused("actual side profile degree unsupported"));
    }
    let knots = if band.ruling_is_u {
        net.v_knots()
    } else {
        net.u_knots()
    };
    if knots != band.profile_knots {
        return Err(invariant("actual side profile knots changed"));
    }
    // Validate root-index semantics against the COMPLETE native knot vector.
    let mut groups: Vec<(f64, usize)> = Vec::new();
    for &u in knots {
        work.spend_core(k, 1)?;
        if let Some((old, n)) = groups.last_mut() {
            if *old == u {
                *n = n
                    .checked_add(1)
                    .ok_or_else(|| refused("knot multiplicity overflow"))?;
                continue;
            }
        }
        work.reserve_cells_core(k, 1)?;
        groups.push((u, 1));
    }
    let (Some(&(_, lc)), Some(&(_, hc))) = (groups.first(), groups.last()) else {
        return Err(refused("actual side knot groups empty"));
    };
    if lc != p + 1
        || hc != p + 1
        || groups
            .iter()
            .skip(1)
            .take(groups.len().saturating_sub(2))
            .any(|&(_, n)| n != p)
        || root >= groups.len().saturating_sub(1)
    {
        return Err(refused(
            "actual side has no full-multiplicity root at selected index",
        ));
    }
    let start = root
        .checked_mul(p)
        .ok_or_else(|| refused("actual root offset overflow"))?;
    let finish = start
        .checked_add(p + 1)
        .ok_or_else(|| refused("actual root extent overflow"))?;
    let mut rows = [Vec::new(), Vec::new()];
    for i in start..finish {
        work.spend_core(k, 1)?;
        let a = if band.ruling_is_u {
            net.cpt(0, i)?
        } else {
            net.cpt(i, 0)?
        };
        let z = if band.ruling_is_u {
            net.cpt(1, i)?
        } else {
            net.cpt(i, 1)?
        };
        for (out, p) in rows.iter_mut().zip([a, z]) {
            work.reserve_cells_core(k, 1)?;
            out.push(p);
        }
    }
    let mut restricted = Vec::new();
    for row in rows {
        let mut h: [Vec<f64>; 4] = core::array::from_fn(|_| Vec::new());
        for point in row {
            work.spend_core(k, 1)?;
            let CPoint { x, y, z, w } = point;
            let w = if w == NOW { 1. } else { w };
            if z == NOZ || ![x, y, z, w].iter().all(|v| v.is_finite()) || w <= 0. {
                return Err(invariant(
                    "actual ruling coefficient is not finite positive3D",
                ));
            }
            work.reserve_cells_core(k, 4)?;
            for (out, v) in h.iter_mut().zip([x, y, z, w]) {
                out.push(v);
            }
        }
        let [x, y, z, w] = h;
        let piece = Piece {
            h: [
                Bernstein2::new(p, 0, x)?,
                Bernstein2::new(p, 0, y)?,
                Bernstein2::new(p, 0, z)?,
                Bernstein2::new(p, 0, w)?,
            ],
            err: 0.,
            lower: 0.,
            depth: 0,
            uv: [0., 1., 0., 0.],
            parameter_ends: [Ivl::from(0.), Ivl::from(1.), Ivl::from(0.), Ivl::from(0.)],
        };
        work.reserve_cells_core(k, 1)?;
        restricted.push({
            let [a, b] = unit;
            piece.restricted_u(a, b)?
        });
    }
    let (Some(lo), Some(hi)) = (restricted.first(), restricted.get(1)) else {
        return Err(invariant("actual ruling rows missing"));
    };
    let mut tensor = Vec::new();
    for (a, z) in lo.h.iter().zip(&hi.h) {
        let mut controls = Vec::new();
        for (&a, &z) in a.coefficients().iter().zip(z.coefficients()) {
            work.spend_core(k, 1)?;
            work.reserve_cells_core(k, 2)?;
            controls.push(a);
            controls.push(z);
        }
        work.reserve_cells_core(k, 1)?;
        tensor.push(Bernstein2::new(p, 1, controls)?);
    }
    let mut it = tensor.into_iter();
    let (Some(a), Some(b), Some(c), Some(w), None) =
        (it.next(), it.next(), it.next(), it.next(), it.next())
    else {
        return Err(invariant("actual ruling tensor coordinates missing"));
    };
    Ok(Piece {
        h: [a, b, c, w],
        err: lo.err.max(hi.err),
        lower: 0.,
        depth: 0,
        uv: [0., 1., 0., 1.],
        parameter_ends: [Ivl::from(0.), Ivl::from(1.), Ivl::from(0.), Ivl::from(1.)],
    })
}
/// Shared actual Plane normal/parameter orientation premise. The native normal
/// is `placement::z_axis()`, which unitizes rounded X×Y and can fall back to +Z on
/// a near-degenerate stored frame. Never assume it has the exact affine S sense.
pub(crate) fn plane_parameter_normal_is_consistent(plane: &Plane) -> bool {
    let frame = plane.position();
    let scale = plane.uv_scale();
    if !(scale.x.is_finite() && scale.y.is_finite() && scale.x > 0. && scale.y > 0.) {
        return false;
    }
    let (Some(a), Some(b), Some(n)) = (
        x::vec(frame.x_axis()),
        x::vec(frame.y_axis()),
        x::vec(frame.z_axis()),
    ) else {
        return false;
    };
    x::cross(&a, &b)
        .and_then(|v| x::dot(&v, &n))
        .and_then(|v| x::sign(&v))
        == Some(1)
}
/// The native Plane normal is its placement Z axis, with the shared exact affine
/// parameter-sense premise above. No cached/generated surface net is consulted.
fn plane_orientation(plane: &Plane, normal: PointBox) -> Result<f64> {
    if !plane_parameter_normal_is_consistent(plane) {
        return Err(refused(
            "actual Plane affine orientation is not its native normal sense",
        ));
    }
    let n = x::vec(plane.position().z_axis())
        .ok_or_else(|| refused("actual Plane Z axis nonfinite"))?;
    let mut dot = Ivl::from(0.);
    for (a, n) in normal.into_iter().zip(&n) {
        let n = x::interval(n).ok_or_else(|| refused("actual Plane normal cannot be enclosed"))?;
        dot = dot + a * n;
    }
    if dot.lo > 0. && dot.is_finite() {
        Ok(dot.lo)
    } else {
        Err(refused(
            "complete actual Plane material orientation not proved positive",
        ))
    }
}
/// Certified bilinear enclosure of the ACTUAL affine Plane on a chosen complete
/// face rectangle. Exact O+u*su*X+v*sv*Y expressions define the four corners; the
/// proxy merely carries floating coefficients with a proved full-domain error.
/// Positive bilinear basis bounds ALL interior points by the largest corner error.
/// Both face and Plane domains are checked, so actual evaluator clamping is inactive.
fn plane_proxy(
    k: &Kernel,
    work: &MeshWork,
    plane: &Plane,
    domain: [f64; 4],
) -> Result<(srf_basic::Surface, f64)> {
    let [umin, umax, vmin, vmax] = domain;
    if !(domain.iter().all(|v| v.is_finite()) && umin < umax && vmin < vmax) {
        return Err(refused("actual Plane rectangle invalid"));
    }
    let full = plane.step_uv_domain();
    if umin < full.u_min() || umax > full.u_max() || vmin < full.v_min() || vmax > full.v_max() {
        return Err(refused(
            "actual side rectangle leaves native Plane clamp domain",
        ));
    }
    let frame = plane.position();
    let scale = plane.uv_scale();
    if !(scale.x.is_finite() && scale.y.is_finite() && scale.x > 0. && scale.y > 0.) {
        return Err(refused("actual Plane scales unsupported"));
    }
    let origin = x::vec(frame.origin()).ok_or_else(|| refused("actual Plane origin nonfinite"))?;
    let a = x::vec(frame.x_axis()).ok_or_else(|| refused("actual Plane X axis nonfinite"))?;
    let b = x::vec(frame.y_axis()).ok_or_else(|| refused("actual Plane Y axis nonfinite"))?;
    let mut error = 0.0_f64;
    let mut rows = Vec::new();
    for u in [umin, umax] {
        let mut row = Vec::new();
        for v in [vmin, vmax] {
            work.spend_core(k, 1)?;
            let mut xyz = Vec::new();
            let mut residual = Vec::new();
            for ((o, a), b) in origin.iter().zip(&a).zip(&b) {
                let q = x::scale(a, scale.x)
                    .and_then(|a| x::scale(&a, u))
                    .and_then(|a| x::add(o, &a))
                    .and_then(|q| x::add(&q, &x::scale(&x::scale(b, scale.y)?, v)?))
                    .ok_or_else(|| refused("exact actual Plane corner outside arithmetic range"))?;
                let range = x::interval(&q)
                    .ok_or_else(|| refused("exact Plane corner cannot be enclosed"))?;
                let middle = 0.5 * range.lo + 0.5 * range.hi;
                if !middle.is_finite() {
                    return Err(refused("actual Plane proxy corner nonfinite"));
                }
                let difference = range - Ivl::from(middle);
                work.reserve_cells_core(k, 2)?;
                xyz.push(middle);
                residual.push(difference);
            }
            let [Some(&x), Some(&y), Some(&z)] = [xyz.first(), xyz.get(1), xyz.get(2)] else {
                return Err(invariant("Plane proxy coordinates missing"));
            };
            let [Some(&a), Some(&b), Some(&c)] =
                [residual.first(), residual.get(1), residual.get(2)]
            else {
                return Err(invariant("Plane proxy residual missing"));
            };
            let bound = (a * a + b * b + c * c).sqrt().hi;
            if !bound.is_finite() {
                return Err(refused("actual Plane proxy error nonfinite"));
            }
            error = error.max(bound);
            work.reserve_cells_core(k, 1)?;
            row.push(CPoint::new(x, y, z, 1.));
        }
        work.reserve_cells_core(k, 1)?;
        rows.push(row);
    }
    Ok((
        srf_basic::Surface::new(
            rows,
            1,
            1,
            vec![umin, umin, umax, umax],
            vec![vmin, vmin, vmax, vmax],
        )?,
        error,
    ))
}
/// A complete requested face rectangle. Net-evaluator families must use their
/// certified natural rectangle; Plane uses its ACTUAL affine definition restricted
/// to this whole clamp-inactive rectangle, never its cached/generated NURBS net.
pub(crate) fn actual_ruling_rectangle_with_work<'a>(
    k: &'a Kernel,
    work: &MeshWork,
    surface: &'a Surface,
    domain: [f64; 4],
    normal: &x::P,
    low: &x::E,
    direction: &x::P,
    ruling_is_u: bool,
    reverse: bool,
) -> Result<Option<ActualRulingBand<'a>>> {
    work.spend_core(k, 0)?;
    if surface.has_kept_definition()
        || surface.procedural_blend().is_some()
        || surface.procedural_sweep().is_some()
    {
        return Ok(None);
    }
    if let SurfaceKind::Plane(plane) = surface.kind_with_nurb(k)? {
        let (proxy, error) = plane_proxy(k, work, plane, domain)?;
        let Some(mut band) = prove_ruling_band_with_work(
            k,
            work,
            &proxy,
            normal,
            low,
            direction,
            ruling_is_u,
            reverse,
        )?
        else {
            return Ok(None);
        };
        band.definition_error_upper =
            (Ivl::from(band.definition_error_upper) + Ivl::from(error)).hi;
        if !band.definition_error_upper.is_finite() {
            return Ok(None);
        }
        return Ok(finish(surface, band, reverse));
    }
    let band = actual_ruling_band_with_work(
        k,
        work,
        surface,
        normal,
        low,
        direction,
        ruling_is_u,
        reverse,
    )?;
    Ok(band.filter(|b| b.domain() == domain))
}
fn finish(
    surface: &Surface,
    band: RulingBand,
    reverse_ruling: bool,
) -> Option<ActualRulingBand<'_>> {
    let degree = band.profile_degree;
    let count = band.base_controls.len();
    let [Some(&a), Some(&b)] = [
        band.profile_knots.get(degree),
        band.profile_knots.get(count),
    ] else {
        return None;
    };
    if !(a.is_finite() && b.is_finite() && a < b) {
        return None;
    }
    let [lo, hi] = band.ruling_parameters;
    let domain = if band.ruling_is_u {
        [lo, hi, a, b]
    } else {
        [a, b, lo, hi]
    };
    Some(ActualRulingBand {
        definition: surface,
        band,
        domain,
        reverse_ruling,
        authority: None,
    })
}
/// The orientation/axis switches are candidates only; every whole-net equation
/// and positive basis condition is independently checked by `RulingBand`.
pub(crate) fn actual_ruling_band_with_work<'a>(
    k: &'a Kernel,
    work: &MeshWork,
    surface: &'a Surface,
    normal: &x::P,
    low: &x::E,
    direction: &x::P,
    ruling_is_u: bool,
    reverse: bool,
) -> Result<Option<ActualRulingBand<'a>>> {
    work.spend_core(k, 0)?;
    if surface.has_kept_definition()
        || surface.procedural_blend().is_some()
        || surface.procedural_sweep().is_some()
    {
        return Ok(None);
    }
    // Representation event, before any attempt to prove a net band. The actual
    // stored slope must be zero; the cylinder flag is not evaluator authority.
    // Frustums require a different common model and are not retried here.
    if let SurfaceKind::Cone(cone) = surface.kind_with_nurb(k)? {
        if cone.semi_angle_deg() != 0. {
            return Ok(None);
        }
        let authority = prove_analytic_net_with_work(k, work, surface, f64::MAX)?;
        let Some(net) = cone.rev().base().gw_nurb() else {
            return Ok(None);
        };
        let Some(mut band) = prove_ruling_band_with_work(
            k,
            work,
            net,
            normal,
            low,
            direction,
            ruling_is_u,
            reverse,
        )?
        else {
            return Ok(None);
        };
        // The net-to-model residual and S-to-net authority are distinct terms.
        // The final consumer checks this outward sum against the unchanged band.
        band.definition_error_upper =
            (Ivl::from(band.definition_error_upper) + Ivl::from(authority.distance_upper())).hi;
        if !band.definition_error_upper.is_finite() {
            return Ok(None);
        }
        let Some(mut actual) = finish(surface, band, reverse) else {
            return Ok(None);
        };
        if actual.domain != authority.domain()
            || !core::ptr::eq(authority.definition(), surface)
            || !core::ptr::eq(authority.kernel(), k)
        {
            return Err(invariant(
                "analytic ruling authority does not bind the complete same net",
            ));
        }
        actual.authority = Some(authority);
        return Ok(Some(actual));
    }
    let band = match surface.kind_with_nurb(k)? {
        SurfaceKind::BSpline(base) => {
            let Some(net) = base.gw_nurb() else {
                return Ok(None);
            };
            prove_ruling_band_with_work(k, work, net, normal, low, direction, ruling_is_u, reverse)?
        }
        SurfaceKind::SurfOfExtrusion(_) => {
            // This is EXACTLY the accessor used by Surface::evaluate_point for
            // this family (surface/surface/p2.rs), not a generic approximation.
            let base = surface.extrusion_base_with_nurb(k)?;
            let Some(net) = base.gw_nurb() else {
                return Ok(None);
            };
            prove_ruling_band_with_work(k, work, net, normal, low, direction, ruling_is_u, reverse)?
        }
        _ => return Ok(None),
    };
    work.spend_core(k, 0)?;
    Ok(band.and_then(|band| finish(surface, band, reverse)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::KernelOptions;
    use crate::nurbs::{b_spline_surface::BSplineSurface, math::CPoint, srf_basic};
    fn surface(shift: f64) -> Surface {
        let net = srf_basic::Surface::new(
            vec![
                vec![CPoint::new(0., 0., 0., 1.), CPoint::new(2., 0., 0., 1.)],
                vec![
                    CPoint::new(0., 0., 5., 1.),
                    CPoint::new(2., 0., 5. + shift, 1.),
                ],
            ],
            1,
            1,
            vec![0., 0., 1., 1.],
            vec![0., 0., 1., 1.],
        )
        .unwrap();
        Surface::from(BSplineSurface::from_nurb(net, true))
    }
    #[test]
    fn authoritative_actual_net_band_covers_its_complete_parameter_rectangle() {
        let k = Kernel::new(&KernelOptions::default());
        let work = MeshWork::new();
        let s = surface(0.125);
        let p = actual_ruling_band_with_work(
            &k,
            &work,
            &s,
            &x::point([0., 0., 1.]).unwrap(),
            &x::scalar(0.).unwrap(),
            &x::point([0., 0., 5.]).unwrap(),
            true,
            false,
        )
        .unwrap()
        .unwrap();
        assert_eq!(p.domain(), [0., 1., 0., 1.]);
        assert!(core::ptr::eq(p.definition(), &raw const s));
        assert!(
            p.band().definition_error_upper >= 0.125 && p.band().definition_error_upper < 0.126
        );
    }
    #[test]
    fn one_actual_net_cannot_be_proved_by_another_direction_label() {
        let k = Kernel::new(&KernelOptions::default());
        let work = MeshWork::new();
        let s = surface(0.);
        let p = actual_ruling_band_with_work(
            &k,
            &work,
            &s,
            &x::point([0., 0., 1.]).unwrap(),
            &x::scalar(0.).unwrap(),
            &x::point([0., 0., 7.]).unwrap(),
            true,
            false,
        )
        .unwrap()
        .unwrap();
        assert!(p.band().definition_error_upper >= 2.);
        // A body consumer must compare this REAL bound to the unchanged face
        // allowance. Merely recognizing degree1 or a generator direction is no fit.
    }
    #[test]
    fn whole_actual_side_normal_sign_uses_native_parameter_order() {
        let k = Kernel::new(&KernelOptions::default());
        let work = MeshWork::new();
        let s = surface(0.);
        let band = actual_ruling_band_with_work(
            &k,
            &work,
            &s,
            &x::point([0., 0., 1.]).unwrap(),
            &x::scalar(0.).unwrap(),
            &x::point([0., 0., 5.]).unwrap(),
            true,
            false,
        )
        .unwrap()
        .unwrap();
        // Native u is ruling +Z, native v is profile +X: Su cross Sv=+Y.
        assert!(
            band.orientation_lower_with_work(
                &k,
                &work,
                0,
                [0., 1.],
                [Ivl::from(0.), Ivl::from(1.), Ivl::from(0.)]
            )
            .unwrap()
                > 0.
        );
        assert!(band
            .orientation_lower_with_work(
                &k,
                &work,
                0,
                [0., 1.],
                [Ivl::from(0.), Ivl::from(-1.), Ivl::from(0.)]
            )
            .is_err());
    }
    #[test]
    fn complete_actual_plane_rectangle_ignores_unrelated_cached_net_and_rejects_clamp_escape() {
        use crate::geom::extent2d::Extent2d;
        use crate::math::{Vec2, Vec3};
        let k = Kernel::new(&KernelOptions::default());
        let work = MeshWork::new();
        let domain = Extent2d::from_bounds(0., 0., 2., 5.);
        let plane = Plane::new(
            Vec3::ZERO,
            Vec3::new(1., 0., 0.),
            Vec3::new(0., 0., 1.),
            Vec2::new(1., 1.),
            &domain,
        );
        let wrong = srf_basic::Surface::new(
            vec![
                vec![
                    CPoint::new(0., 0., 1000., 1.),
                    CPoint::new(0., 0., 1001., 1.),
                ],
                vec![
                    CPoint::new(1., 0., 1000., 1.),
                    CPoint::new(1., 0., 1001., 1.),
                ],
            ],
            1,
            1,
            vec![0., 0., 1., 1.],
            vec![0., 0., 1., 1.],
        )
        .unwrap();
        let stored = Plane::from_stored(
            *plane.position(),
            plane.uv_scale(),
            domain,
            BSplineSurface::from_nurb(wrong, true),
        );
        let surface = Surface::from(stored);
        let n = x::point([0., 0., 1.]).unwrap();
        let lo = x::scalar(0.).unwrap();
        let d = x::point([0., 0., 5.]).unwrap();
        let band = actual_ruling_rectangle_with_work(
            &k,
            &work,
            &surface,
            [0., 2., 0., 5.],
            &n,
            &lo,
            &d,
            false,
            false,
        )
        .unwrap()
        .unwrap();
        assert_eq!(band.domain(), [0., 2., 0., 5.]);
        assert!(band.band().definition_error_upper < 1e-9);
        assert!(
            band.orientation_lower_with_work(
                &k,
                &work,
                0,
                [0., 1.],
                [Ivl::from(0.), Ivl::from(-1.), Ivl::from(0.)]
            )
            .unwrap()
                > 0.
        );
        assert!(band
            .orientation_lower_with_work(
                &k,
                &work,
                0,
                [0., 1.],
                [Ivl::from(0.), Ivl::from(1.), Ivl::from(0.)]
            )
            .is_err());
        assert!(actual_ruling_rectangle_with_work(
            &k,
            &work,
            &surface,
            [-1., 2., 0., 5.],
            &n,
            &lo,
            &d,
            false,
            false
        )
        .is_err());
    }

    fn cylindrical_side(k: &Kernel, swap: bool, reverse: bool, unclamped: bool) -> Surface {
        let mut cone = crate::surface::cone::Cone::new_cylinder_bounded(
            crate::math::Vec3::ZERO,
            crate::math::Vec3::X,
            crate::math::Vec3::Y,
            3.,
            0.,
            360.,
            5.,
            swap,
            reverse,
            false,
        );
        cone.make_nurb(k).unwrap();
        cone.set_out_of_bounds_enabled(unclamped);
        Surface::from(cone)
    }
    #[test]
    fn complete_cylinder_adapter_retains_actual_authority_and_one_additive_error() {
        let k = Kernel::default();
        let n = x::point([0., 0., 1.]).unwrap();
        let lo = x::scalar(0.).unwrap();
        let direction = x::point([0., 0., 5.]).unwrap();
        for swap in [false, true] {
            for reverse in [false, true] {
                for unclamped in [false, true] {
                    let work = MeshWork::new();
                    let s = cylindrical_side(&k, swap, reverse, unclamped);
                    let proof = actual_ruling_band_with_work(
                        &k, &work, &s, &n, &lo, &direction, swap, reverse,
                    )
                    .unwrap()
                    .unwrap();
                    let authority = proof.authority.as_ref().unwrap();
                    assert!(core::ptr::eq(authority.definition(), &raw const s));
                    assert!(core::ptr::eq(authority.kernel(), &raw const k));
                    assert_eq!(authority.domain(), proof.domain());
                    assert_eq!(authority.covered_roots(), 4);
                    let SurfaceKind::Cone(c) = s.kind() else {
                        panic!()
                    };
                    let raw = prove_ruling_band_with_work(
                        &k,
                        &work,
                        c.rev().base().gw_nurb().unwrap(),
                        &n,
                        &lo,
                        &direction,
                        swap,
                        reverse,
                    )
                    .unwrap()
                    .unwrap();
                    let once = (Ivl::from(raw.definition_error_upper)
                        + Ivl::from(authority.distance_upper()))
                    .hi;
                    assert_eq!(
                        proof.band().definition_error_upper.to_bits(),
                        once.to_bits()
                    );
                    assert!(once > 0. && once < 1e-6);
                    let sign = if swap == reverse { 1. } else { -1. };
                    let normal = [Ivl::from(sign), Ivl::from(sign), Ivl::from(0.)];
                    let context = CurveBounds::new(&k, &work).unwrap();
                    assert!(
                        proof
                            .orientation_lower_in_bounds(&context, 0, [0., 1.], normal)
                            .unwrap()
                            > 0.
                    );
                    let other_kernel = Kernel::default();
                    let other_context = CurveBounds::new(&other_kernel, &work).unwrap();
                    assert!(matches!(
                        proof.orientation_lower_in_bounds(&other_context, 0, [0., 1.], normal),
                        Err(SolidError::PortInvariant { .. })
                    ));
                    let mut partial_domain = proof.domain();
                    partial_domain[usize::from(swap) * 2 + 1] *= 0.5;
                    assert!(actual_ruling_rectangle_with_work(
                        &k,
                        &work,
                        &s,
                        partial_domain,
                        &n,
                        &lo,
                        &direction,
                        swap,
                        reverse,
                    )
                    .unwrap()
                    .is_none());
                    work.check(&k).unwrap();
                }
            }
        }
    }
    #[test]
    fn cylinder_adapter_never_substitutes_a_flag_for_the_actual_radius_law() {
        let k = Kernel::default();
        let work = MeshWork::new();
        let n = x::point([0., 0., 1.]).unwrap();
        let lo = x::scalar(0.).unwrap();
        let direction = x::point([0., 0., 5.]).unwrap();
        let s = cylindrical_side(&k, false, false, false);
        let SurfaceKind::Cone(c) = s.kind() else {
            panic!()
        };
        let mut changed = c.clone();
        changed.semi_angle_deg = 10.;
        let changed = Surface::from(*changed);
        assert!(actual_ruling_band_with_work(
            &k, &work, &changed, &n, &lo, &direction, false, false
        )
        .unwrap()
        .is_none());
        let mut cone_class = c.clone();
        cone_class.cylinder = false;
        let cone_class = Surface::from(*cone_class);
        assert!(actual_ruling_band_with_work(
            &k,
            &work,
            &cone_class,
            &n,
            &lo,
            &direction,
            false,
            false
        )
        .unwrap()
        .is_some());
        work.check(&k).unwrap();
    }
}
