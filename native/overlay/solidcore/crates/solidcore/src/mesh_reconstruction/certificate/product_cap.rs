//! Full selected-cap native S/CW witness for a certified source product.
//!
//! ONE immutable final Plane face and ALL its actual native edge/use/UV roots
//! are assigned once to the SAME complete sewn 3D cap model. The model's exact
//! Gram UV loop is domain-contained, coherently C0, embedded and nested; the
//! exact injective affine transport of the ALREADY proved original cap-chain
//! motion/winding fixes its filled-domain/material
//! meaning. Its whole filled cap lies in the unchanged native face band. This
//! is the exact tolerant face witness, not an assertion nominal native pcurves
//! have exactly identical endpoints or themselves form an exact Jordan loop.
//!
//! EVERY actual UV-root image is bounded against that SAME ordered model edge
//! and its real native vertices in unchanged tubes/balls. Independently proved
//! COMPLETE affine definitions (including unit-weight degree1 splines) consume
//! the actual Plane clamp's full exact event partition; a non-ISO clamp kink is
//! never replaced by the segment between clamped endpoints. General curved roots
//! must still prove clamp inactive by their full positive control hull. No domain
//! expansion, tolerance growth, sample-based acceptance or hidden root is allowed.
//!
//! Whole-source/model cap coverage follows the complete oriented source chain and
//! embedded rim-motion/winding. Complete stored native UV boundary correspondence
//! includes certified clamp displacement. Actual S on the WHOLE chosen UV domain
//! is clamp inactive and has the proved model normal-band error. Both caps, every
//! side and the full native CW/material consumer remain necessary before adoption.
//! Deviations: none. Degree1..8, <=6 exact affine-clamp events, shared `MeshWork`.
use super::super::actual_roots::{actual_used_roots, actual_uv_roots};
use super::super::work::MeshWork;
use super::actual_ruling::plane_parameter_normal_is_consistent;
use super::exact_geometry as x;
use super::exact_planar::affine_ends;
use super::hulls::{paired_curve_upper, point_distance_upper};
use super::native_profile::NativeProfile;
use super::plane_trim_image::plane_trim_image_with_work;
use super::sewn_curve::{enclose_controls_with_work, ProjectivePoint};
use crate::blend::fillet_section::interval::Ivl;
use crate::geom::extent2d::Extent2d;
use crate::geom::tol::zone_tol3d;
use crate::nurbs::b_spline_surface_n_lib::p2::OrientType;
use crate::surface::{plane::Plane, surface::SurfaceKind};
use crate::topology::{edge, edgeuse::p1 as eu, vertex, FaceId};
use crate::{Kernel, Result, SolidError};
const OP: &str = "mesh_reconstruction::certificate::product_cap";
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
fn native<T>(k: &Kernel, work: &MeshWork, result: super::super::Result<T>) -> Result<T> {
    work.spend_core(k, 0)?;
    match result {
        Ok(v) => Ok(v),
        Err(super::super::MeshError::Kernel(e)) => Err(e),
        Err(
            super::super::MeshError::Refused { .. } | super::super::MeshError::Undecided { .. },
        ) => Err(refused("actual root extraction unresolved")),
        Err(_) => Err(invariant(
            "actual root helper returned unexpected non-kernel failure",
        )),
    }
}
fn enclosure(e: &x::E) -> Option<Ivl> {
    let mut v = Ivl::from(0.);
    for &term in e {
        v = v.add_ulp(Ivl::from(term));
    }
    v.is_finite().then_some(v)
}
fn norm(p: [Ivl; 3]) -> Option<f64> {
    let [a, b, c] = p.map(|v| Ivl::from(v.lo.abs().max(v.hi.abs())));
    let value = (a * a + b * b + c * c).sqrt().hi;
    value.is_finite().then_some(value)
}
fn pt(p: [f64; 3]) -> Option<ProjectivePoint> {
    Some(ProjectivePoint {
        xyz: x::point(p)?,
        w: x::scalar(1.)?,
    })
}
// Exact rational controls are blended in homogeneous coordinates. This helper's
// weights use the ORIGINAL endpoint weights; no Euclidean averaging occurs.
fn lerp(a: &ProjectivePoint, b: &ProjectivePoint, t: f64) -> Option<ProjectivePoint> {
    let one = x::sub(&x::scalar(1.)?, &x::scalar(t)?)?;
    let t = x::scalar(t)?;
    let mut xyz = Vec::new();
    for (a, b) in a.xyz.iter().zip(&b.xyz) {
        xyz.push(x::add(&x::mul(a, &one)?, &x::mul(b, &t)?)?);
    }
    let [Some(ax), Some(ay), Some(az)] = [xyz.first(), xyz.get(1), xyz.get(2)] else {
        return None;
    };
    Some(ProjectivePoint {
        xyz: [ax.clone(), ay.clone(), az.clone()],
        w: x::add(&x::mul(&a.w, &one)?, &x::mul(&b.w, &t)?)?,
    })
}
/// Exact Bernstein blossom on a complete positive rational root. Native actual
/// root extraction already verifies the basis/controls. Each restricted control
/// is blossom(a repeated n-j,b repeated j); native de Casteljau's multi-affine
/// identity (NURBS Book§1.4) requires NO division or rounded knot insertion.
fn restrict(
    k: &Kernel,
    work: &MeshWork,
    root: &[ProjectivePoint],
    range: [f64; 2],
) -> Result<Vec<ProjectivePoint>> {
    let [a, b] = range;
    let degree = root
        .len()
        .checked_sub(1)
        .filter(|&n| (1..=8).contains(&n))
        .ok_or_else(|| refused("UV root degree is unsupported"))?;
    if !(a.is_finite() && b.is_finite() && 0. <= a && a < b && b <= 1.) {
        return Err(refused("complete UV restriction is invalid"));
    }
    let mut out = Vec::new();
    for j in 0..=degree {
        work.reserve_cells_core(k, root.len())?;
        let mut row: Vec<_> = root
            .iter()
            .map(|p| ProjectivePoint {
                xyz: p.xyz.clone(),
                w: p.w.clone(),
            })
            .collect();
        for level in 0..degree {
            let t = if level < degree.saturating_sub(j) {
                a
            } else {
                b
            };
            let mut next = Vec::new();
            for pair in row.windows(2) {
                work.spend_core(k, 1)?;
                let [a, b] = pair else {
                    return Err(invariant("literal two-control window failed"));
                };
                let p = lerp(a, b, t)
                    .ok_or_else(|| refused("exact UV restriction arithmetic unresolved"))?;
                work.reserve_cells_core(k, 1)?;
                next.push(p);
            }
            row = next;
        }
        let p = row
            .into_iter()
            .next()
            .ok_or_else(|| invariant("exact restricted UV root missing"))?;
        work.reserve_cells_core(k, 1)?;
        out.push(p);
    }
    Ok(out)
}
struct Chart {
    origin: x::P,
    a: x::P,
    b: x::P,
    g00: x::E,
    g01: x::E,
    g11: x::E,
    det: x::E,
    lipschitz: f64,
    orientation: i32,
}
impl Chart {
    /// Exact injective chart on the original/model cap plane. With B=[A C],
    /// J=(B^T B)^-1 B^T has kernel span(A×C). A nonzero N·(A×C) means no nonzero
    /// direction tangent to N·P=level lies in that kernel. Therefore J restricts
    /// to an affine homeomorphism of the COMPLETE plane (and every rim-motion
    /// time level/filling); orientation is the exact stored sign below.
    fn new(plane: &Plane, source_normal: &x::P) -> Option<Self> {
        if !plane_parameter_normal_is_consistent(plane) {
            return None;
        }
        let frame = plane.position();
        let scale = plane.uv_scale();
        if !(scale.x.is_finite() && scale.y.is_finite() && scale.x > 0. && scale.y > 0.) {
            return None;
        }
        let origin = x::vec(frame.origin())?;
        let a = x::vec(frame.x_axis())?;
        let b = x::vec(frame.y_axis())?;
        let scale_vec = |v: &x::P, s: f64| -> Option<x::P> {
            let [a, b, c] = v;
            Some([x::scale(a, s)?, x::scale(b, s)?, x::scale(c, s)?])
        };
        let a = scale_vec(&a, scale.x)?;
        let b = scale_vec(&b, scale.y)?;
        let g00 = x::dot(&a, &a)?;
        let g01 = x::dot(&a, &b)?;
        let g11 = x::dot(&b, &b)?;
        let det = x::sub(&x::mul(&g00, &g11)?, &x::mul(&g01, &g01)?)?;
        if x::sign(&det) != Some(1) {
            return None;
        }
        let orientation = x::dot(source_normal, &x::cross(&a, &b)?).and_then(|v| x::sign(&v))?;
        if orientation == 0 {
            return None;
        }
        let lipschitz = (enclosure(&g00)? + enclosure(&g11)?).sqrt().hi;
        lipschitz.is_finite().then_some(Self {
            origin,
            a,
            b,
            g00,
            g01,
            g11,
            det,
            lipschitz,
            orientation,
        })
    }
    /// Coordinates scaled by detGram, with the ORIGINAL homogeneous weight.
    fn scaled_uv(&self, p: &ProjectivePoint) -> Option<ProjectivePoint> {
        let mut relative = Vec::new();
        for (h, o) in p.xyz.iter().zip(&self.origin) {
            relative.push(x::sub(h, &x::mul(o, &p.w)?)?);
        }
        let [Some(a), Some(b), Some(c)] = [relative.first(), relative.get(1), relative.get(2)]
        else {
            return None;
        };
        let relative = [a.clone(), b.clone(), c.clone()];
        let da = x::dot(&self.a, &relative)?;
        let db = x::dot(&self.b, &relative)?;
        let u = x::sub(&x::mul(&self.g11, &da)?, &x::mul(&self.g01, &db)?)?;
        let v = x::sub(&x::mul(&self.g00, &db)?, &x::mul(&self.g01, &da)?)?;
        Some(ProjectivePoint {
            xyz: [u, v, x::scalar(0.)?],
            w: p.w.clone(),
        })
    }
    fn uv(&self, p: &ProjectivePoint) -> Option<ProjectivePoint> {
        let mut q = self.scaled_uv(p)?;
        q.w = x::mul(&q.w, &self.det)?;
        Some(q)
    }
    fn image(&self, p: &ProjectivePoint) -> Option<[Ivl; 3]> {
        let [u, v, _] = &p.xyz;
        let weight = enclosure(&p.w)?;
        if !weight.is_positive() {
            return None;
        }
        let mut image = Vec::new();
        for ((o, a), b) in self.origin.iter().zip(&self.a).zip(&self.b) {
            let value = x::add(&x::add(&x::mul(o, &p.w)?, &x::mul(a, u)?)?, &x::mul(b, v)?)?;
            image.push(enclosure(&value)? / weight);
        }
        Some([*image.first()?, *image.get(1)?, *image.get(2)?])
    }
    fn support_error(&self, p: &ProjectivePoint) -> Option<f64> {
        let uv = self.uv(p)?;
        let [u, v, _] = &uv.xyz;
        let mut difference = Vec::new();
        for (((o, a), b), h) in self.origin.iter().zip(&self.a).zip(&self.b).zip(&p.xyz) {
            let image = x::add(&x::add(&x::mul(o, &uv.w)?, &x::mul(a, u)?)?, &x::mul(b, v)?)?;
            difference.push(x::sub(&image, &x::mul(h, &self.det)?)?);
        }
        let [Some(a), Some(b), Some(c)] = [
            difference.first().and_then(enclosure),
            difference.get(1).and_then(enclosure),
            difference.get(2).and_then(enclosure),
        ] else {
            return None;
        };
        let w = enclosure(&uv.w)?;
        if !w.is_positive() {
            return None;
        }
        norm([a / w, b / w, c / w])
    }
}
fn inside(p: &ProjectivePoint, domain: Extent2d) -> bool {
    if !domain.is_bounded() || x::sign(&p.w) != Some(1) {
        return false;
    }
    let [u, v, _] = &p.xyz;
    [
        (u, domain.u_min(), domain.u_max()),
        (v, domain.v_min(), domain.v_max()),
    ]
    .into_iter()
    .all(|(h, a, b)| {
        a.is_finite()
            && b.is_finite()
            && a < b
            && x::scale(&p.w, a)
                .and_then(|v| x::sub(h, &v))
                .and_then(|v| x::sign(&v))
                .is_some_and(|v| v >= 0)
            && x::scale(&p.w, b)
                .and_then(|v| x::sub(&v, h))
                .and_then(|v| x::sign(&v))
                .is_some_and(|v| v >= 0)
    })
}
/// The ACTUAL affine UV root may cross a native Plane clamp boundary. Formula
/// changes occur only at the existing helper's exact crossing ratios (<=6). On
/// every complete resulting cell, clamped S(UV(t)) and unclamped affine image
/// differ affinely, so convexity of norm bounds the FULL clamp displacement by
/// all event endpoints. This never substitutes the line between clamped endpoints.
struct AffineClampBound {
    upper: f64,
    endpoints: [[Ivl; 3]; 2],
}
fn affine_clamp_bound(
    k: &Kernel,
    work: &MeshWork,
    plane: &Plane,
    chart: &Chart,
    uv: &[ProjectivePoint],
) -> Result<AffineClampBound> {
    work.spend_core(k, 0)?;
    let [a, z] = uv else {
        return Err(refused(
            "actual affine UV root does not have two exact controls",
        ));
    };
    let one = x::scalar(1.).ok_or_else(|| invariant("one exact scalar unavailable"))?;
    for p in [a, z] {
        if !x::sub(&p.w, &one).is_some_and(|w| x::zero(&w)) || !p.xyz.get(2).is_some_and(x::zero) {
            return Err(refused(
                "actual affine UV root lacks its exact unit-weight native definition",
            ));
        }
    }
    work.reserve_cells_core(k, 2)?;
    let image = plane_trim_image_with_work(k, work, plane, &[a.xyz.clone(), z.xyz.clone()])?;
    let a = chart
        .image(a)
        .ok_or_else(|| refused("actual unbounded affine UV start cannot be enclosed"))?;
    let z = chart
        .image(z)
        .ok_or_else(|| refused("actual unbounded affine UV end cannot be enclosed"))?;
    let [ax, ay, az] = a;
    let [zx, zy, zz] = z;
    let mut upper = 0.0_f64;
    for knot in &image.knots {
        work.spend_core(k, 1)?;
        let t = knot.parameter;
        let unbounded = [ax + (zx - ax) * t, ay + (zy - ay) * t, az + (zz - az) * t];
        upper = upper.max(point_distance_upper(unbounded, knot.point)?);
    }
    let (Some(a), Some(z)) = (image.knots.first(), image.knots.last()) else {
        return Err(invariant("complete native Plane image has no endpoints"));
    };
    Ok(AffineClampBound {
        upper,
        endpoints: [a.point, z.point],
    })
}
pub(crate) struct ProductCap<'a, 'b, 'g, 's, 'raw> {
    profile: &'a NativeProfile<'b, 'g, 's, 'raw>,
    face: FaceId,
    source_actual_upper: f64,
    model_band_upper: f64,
}
impl<'a, 'b, 'g, 's, 'raw> ProductCap<'a, 'b, 'g, 's, 'raw> {
    pub(crate) fn profile(&self) -> &'a NativeProfile<'b, 'g, 's, 'raw> {
        self.profile
    }
    pub(crate) fn face(&self) -> FaceId {
        self.face
    }
    pub(crate) fn source_actual_upper(&self) -> f64 {
        self.source_actual_upper
    }
    pub(crate) fn model_band_upper(&self) -> f64 {
        self.model_band_upper
    }
}
/// The selected original low/high cap plane, ONE native face and ALL its loops.
/// Its original source end comes from the bound `NativeProfileDraft`, not a guessed
/// face label. Full product proof must still unify both caps to ONE common model.
pub(crate) fn prove_product_cap_with_work<'a, 'b, 'g, 's, 'raw>(
    k: &Kernel,
    work: &MeshWork,
    profile: &'a NativeProfile<'b, 'g, 's, 'raw>,
    tolerance: f64,
) -> Result<ProductCap<'a, 'b, 'g, 's, 'raw>> {
    work.spend_core(k, 0)?;
    if !tolerance.is_finite() || tolerance <= 0. {
        return Err(refused("invalid cap tolerance"));
    }
    let draft = profile.draft();
    let complex = draft.complex();
    let b = complex.brep();
    let patch = complex
        .patches
        .get(draft.patch())
        .ok_or_else(|| invariant("proved native profile patch missing"))?;
    let [face] = patch.faces.as_slice() else {
        return Err(refused(
            "full cap chart currently requires one actual native Plane face",
        ));
    };
    let face = *face;
    let record = b.face(face)?;
    let surface = record
        .surface
        .as_ref()
        .ok_or_else(|| refused("actual cap surface missing"))?;
    if surface.has_kept_definition()
        || surface.procedural_blend().is_some()
        || surface.procedural_sweep().is_some()
    {
        return Err(refused(
            "actual carried cap definition cannot be replaced by Plane label",
        ));
    }
    let SurfaceKind::Plane(plane) = surface.kind_with_nurb(k)? else {
        return Err(refused("actual cap is not a Plane definition"));
    };
    let chart = Chart::new(plane, draft.source().cap_normal())
        .ok_or_else(|| refused("actual Plane chart is not nonsingular on whole model cap"))?;
    let native_radius = zone_tol3d(k, record.tolerance);
    if !native_radius.is_finite() || native_radius <= 0. {
        return Err(refused("actual cap face allowance is invalid"));
    }
    let first = patch
        .rims
        .first()
        .and_then(|v| v.first())
        .ok_or_else(|| invariant("proved native cap rim empty"))?;
    let fu = first.faceuse;
    let sense = match b.faceuse(fu)?.orientation {
        OrientType::Same => 1,
        OrientType::Opposite => -1,
        OrientType::Unknown => return Err(refused("actual cap face normal unresolved")),
    };
    let expected = match draft.level() {
        0 => -1,
        1 => 1,
        _ => return Err(invariant("proved source cap end is invalid")),
    };
    if chart.orientation * sense != expected {
        return Err(refused(
            "actual selected cap material normal differs from its original source product end",
        ));
    }
    let native_loops = &b.faceuse(fu)?.loopuses;
    if native_loops.len() != patch.rims.len() {
        return Err(refused("actual full cap loop family differs"));
    }
    let mut assigned = std::collections::BTreeSet::new();
    let mut model_band_upper = 0.0_f64;
    let mut boundary_uv_upper = 0.0_f64;
    let mut boundary_clamp_upper = 0.0_f64;
    for (ri, graph) in draft.graphs().iter().enumerate() {
        let rim = patch
            .rims
            .get(ri)
            .ok_or_else(|| invariant("proved native profile rim missing"))?;
        let model = profile
            .controls_3d()
            .get(ri)
            .ok_or_else(|| invariant("proved model rim controls missing"))?;
        let lu = rim
            .first()
            .and_then(|u| eu::loopuse(b, u.use_id).transpose())
            .transpose()?
            .ok_or_else(|| refused("actual cap loop owner missing"))?;
        if !assigned.insert(lu) {
            return Err(refused("actual cap loop is duplicated"));
        }
        let loop_index = native_loops
            .iter()
            .position(|&v| v == lu)
            .ok_or_else(|| refused("actual cap rim loop outside selected faceuse"))?;
        let mut area = x::scalar(0.).ok_or_else(|| invariant("zero exact scalar unavailable"))?;
        for (i, p) in graph.source.iter().enumerate() {
            let next_index = i
                .checked_add(1)
                .ok_or_else(|| invariant("source loop index overflow"))?;
            let next = graph
                .source
                .get(next_index)
                .or_else(|| graph.source.first())
                .ok_or_else(|| invariant("source closed loop missing"))?;
            work.reserve_cells_core(k, 2)?;
            let a = chart
                .scaled_uv(&ProjectivePoint {
                    xyz: super::source_view::copy_point_with_work(k, work, p)?,
                    w: x::scalar(1.).ok_or_else(|| invariant("one scalar unavailable"))?,
                })
                .ok_or_else(|| refused("source cap UV chart arithmetic unresolved"))?;
            let z = chart
                .scaled_uv(&ProjectivePoint {
                    xyz: super::source_view::copy_point_with_work(k, work, next)?,
                    w: x::scalar(1.).ok_or_else(|| invariant("one scalar unavailable"))?,
                })
                .ok_or_else(|| refused("source cap UV chart arithmetic unresolved"))?;
            let [ax, ay, _] = &a.xyz;
            let [zx, zy, _] = &z.xyz;
            area = x::mul(ax, zy)
                .and_then(|a| x::sub(&a, &x::mul(ay, zx)?))
                .and_then(|v| x::add(&area, &v))
                .ok_or_else(|| refused("full source cap winding arithmetic unresolved"))?;
        }
        if x::sign(&area) != Some(if loop_index == 0 { sense } else { -sense }) {
            return Err(refused(
                "actual outer/hole loop order differs from full source cap winding",
            ));
        }
        let mut uv_roots = Vec::new();
        for (usage, target) in graph.uses.iter().zip(rim) {
            if target.face != face
                || target.faceuse != fu
                || eu::loopuse(b, target.use_id)? != Some(lu)
            {
                return Err(refused(
                    "actual cap rim has unmatched face/use/loop incidence",
                ));
            }
            let (trim, owner) = eu::uv_trim_curve(b, target.use_id)?;
            let trim = trim.ok_or_else(|| refused("actual cap UV trim missing"))?;
            let owner = owner
                .and_then(|v| eu::faceuse(b, v).transpose())
                .transpose()?
                .ok_or_else(|| refused("actual UV trim owner missing"))?;
            if b.faceuse(owner)?.face != Some(face) {
                return Err(refused("actual cap UV curve belongs to a different face"));
            }
            let used = edge::interval(b, target.edge)?;
            let natural = trim.natural_interval();
            if natural.min() != used.min() || natural.max() != used.max() {
                return Err(refused("actual UV/edge used parameter domains differ"));
            }
            let roots = native(k, work, actual_uv_roots(k, work, trim, usage.forward))?;
            let world = native(
                k,
                work,
                actual_used_roots(k, work, usage.curve, usage.interval, usage.forward),
            )?;
            if roots.len() != world.len()
                || roots
                    .iter()
                    .zip(&world)
                    .any(|(a, b)| a.native_interval != b.native_interval)
            {
                return Err(refused("actual UV/edge complete knot partitions differ"));
            }
            // Reuse the existing COMPLETE actual affine-definition proof:
            // Line with native parameter semantics, or one full degree1
            // BSpline span with exactly2 controls and native unit weights.
            // A label or merely degree1 with varying weights is not a proof.
            let affine = affine_ends(trim, used, true);
            if affine.is_some() && roots.len() != 1 {
                return Err(invariant(
                    "proved full affine curve has multiple actual roots",
                ));
            }
            let mut exact = Vec::new();
            for root in &roots {
                let mut controls = Vec::new();
                if let Some(ends) = affine.as_ref() {
                    let [a, z] = ends;
                    let ordered = if usage.forward { [a, z] } else { [z, a] };
                    work.reserve_cells_core(k, 2)?;
                    for p in ordered {
                        controls.push(ProjectivePoint {
                            xyz: p.clone(),
                            w: x::scalar(1.)
                                .ok_or_else(|| invariant("one exact scalar unavailable"))?,
                        });
                    }
                } else {
                    if root.piece.err != 0. {
                        return Err(refused("actual UV root requires an unprovided exact coefficient representation"));
                    }
                    let [a, b, c, w] = &root.piece.h;
                    for (((&a, &b), &c), &w) in a
                        .coefficients()
                        .iter()
                        .zip(b.coefficients())
                        .zip(c.coefficients())
                        .zip(w.coefficients())
                    {
                        work.spend_core(k, 1)?;
                        work.reserve_cells_core(k, 1)?;
                        controls.push(ProjectivePoint {
                            xyz: x::point([a, b, c])
                                .ok_or_else(|| refused("actual UV coefficient nonfinite"))?,
                            w: x::scalar(w).ok_or_else(|| refused("actual UV weight nonfinite"))?,
                        });
                    }
                }
                work.reserve_cells_core(k, 1)?;
                exact.push(controls);
            }

            work.reserve_cells_core(k, 1)?;
            uv_roots.push((roots, exact, affine.is_some()));
        }
        for (ci, cell) in graph.cells.iter().enumerate() {
            work.spend_core(k, 1)?;
            let claim = &cell.claim;
            let (roots, exact, affine) = uv_roots
                .get(claim.curve)
                .ok_or_else(|| invariant("complete actual UV curve missing"))?;
            let root = roots
                .get(claim.span)
                .ok_or_else(|| invariant("complete actual UV root missing"))?;
            let exact = exact
                .get(claim.span)
                .ok_or_else(|| invariant("exact actual UV controls missing"))?;
            let uv = restrict(k, work, exact, claim.target_unit)?;
            let [ta, tb] = claim.target_unit;
            let actual = root.piece.restricted_u(ta, tb)?;
            let model = model
                .get(ci)
                .ok_or_else(|| invariant("complete sewn model span missing"))?;
            let mut projected = Vec::new();
            for p in model {
                work.spend_core(k, 1)?;
                let chart_point = chart
                    .uv(p)
                    .ok_or_else(|| refused("full model UV projection unresolved"))?;
                if !inside(&chart_point, plane.step_uv_domain())
                    || !inside(&chart_point, record.uv_domain)
                {
                    return Err(refused(
                        "full model cap chart leaves unchanged actual Plane/face domain",
                    ));
                }
                model_band_upper = model_band_upper.max(
                    chart
                        .support_error(p)
                        .ok_or_else(|| refused("full model cap normal band unresolved"))?,
                );
                work.reserve_cells_core(k, 1)?;
                projected.push(chart_point);
            }
            if model_band_upper > native_radius {
                return Err(refused(
                    "full chosen cap model exceeds unchanged native face band",
                ));
            }
            let clamp = if *affine {
                Some(affine_clamp_bound(k, work, plane, &chart, &uv)?)
            } else {
                // A curved root's image needs its own certified clamp-event
                // isolation. Positive hull containment is still required here;
                // never clamp arbitrary rational endpoint controls as a proof.
                for p in &uv {
                    if !inside(p, plane.step_uv_domain()) || !inside(p, record.uv_domain) {
                        return Err(refused("actual curved UV definition is not proved clamp-inactive over complete cap boundary"));
                    }
                }
                None
            };
            let clamp_upper = clamp.as_ref().map_or(0., |c| c.upper);
            boundary_clamp_upper = boundary_clamp_upper.max(clamp_upper);
            let model_piece = enclose_controls_with_work(k, work, &projected, &actual)?
                .ok_or_else(|| refused("full model UV coefficient enclosure unavailable"))?;
            let curve_upper = paired_curve_upper(&actual, &model_piece, 0., 0.)?;
            boundary_uv_upper = boundary_uv_upper.max(curve_upper);
            let target = rim
                .get(claim.curve)
                .ok_or_else(|| invariant("complete cap edge binding missing"))?;
            let radius = zone_tol3d(k, edge::tolerance(b, target.edge)?);
            let whole_image = (Ivl::from(chart.lipschitz) * Ivl::from(curve_upper)
                + Ivl::from(model_band_upper)
                + Ivl::from(clamp_upper))
            .hi;
            if !radius.is_finite() || radius <= 0. || whole_image > radius {
                return Err(refused(
                    "WHOLE actual cap S/UV image leaves its unchanged native edge tube",
                ));
            }
            let [start, end] = claim.target_unit;
            let last = claim.span.checked_add(1).is_some_and(|n| n == roots.len());
            for (real, point, vertex, is_start) in [
                (
                    claim.span == 0 && start == 0.,
                    uv.first(),
                    target.start,
                    true,
                ),
                (last && end == 1., uv.last(), target.end, false),
            ] {
                if !real {
                    continue;
                }
                let point =
                    point.ok_or_else(|| invariant("complete actual UV endpoint missing"))?;
                let image = if let Some(clamp) = clamp.as_ref() {
                    if is_start {
                        *clamp
                            .endpoints
                            .first()
                            .ok_or_else(|| invariant("actual clamp start missing"))?
                    } else {
                        *clamp
                            .endpoints
                            .get(1)
                            .ok_or_else(|| invariant("actual clamp end missing"))?
                    }
                } else {
                    chart
                        .image(point)
                        .ok_or_else(|| refused("complete actualS endpoint enclosure unresolved"))?
                };
                let actual_vertex = vertex::point(b, vertex)?;
                let radius = zone_tol3d(k, vertex::tolerance(b, vertex)?);
                let distance = point_distance_upper(
                    image,
                    [actual_vertex.x, actual_vertex.y, actual_vertex.z].map(Ivl::from),
                )?;
                if !radius.is_finite() || radius <= 0. || distance > radius {
                    return Err(refused(
                        "actual cap S/UV real join leaves its unchanged native vertex ball",
                    ));
                }
            }
        }
    }
    if assigned.len() != native_loops.len() {
        return Err(refused("some actual cap loop is unmatched"));
    }
    // NativeProfile ALREADY certifies the complete original source→SAME model
    // rim motion in the original cap plane, with exact C0, embedding/nesting and
    // one full source/target cell cover. All its model controls lie on that plane.
    // Chart::new proves this affine map restricted to that plane is injective:
    // ker(UV Gram projection)=span(A×B), and N·(A×B) !=0. Thus the same ENTIRE
    // motion and filled oriented cap chain transport to UV, not just endpoints.
    // The whole model UV domain containment and material orientation above stay
    // mandatory. Do not rerun a basis-dependent sufficient sector predicate and
    // pretend its possible refusal means the proved affine image ceased embedding.
    let model_actual = (Ivl::from(chart.lipschitz) * Ivl::from(boundary_uv_upper)
        + Ivl::from(model_band_upper)
        + Ivl::from(boundary_clamp_upper))
    .hi;
    let source_actual_upper =
        (Ivl::from(profile.source_model_upper()) + Ivl::from(model_actual)).hi;
    if !source_actual_upper.is_finite() || source_actual_upper > tolerance {
        return Err(refused(
            "complete filled cap source/S correspondence exceeds tolerance",
        ));
    }
    work.spend_core(k, 0)?;
    Ok(ProductCap {
        profile,
        face,
        source_actual_upper,
        model_band_upper,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::curve::curve::CurveKind;
    use crate::math::{Point3, Vec3};
    #[test]
    fn exact_blossom_restriction_preserves_complete_polynomial_coefficients() {
        let k = Kernel::default();
        let work = MeshWork::new();
        let root = vec![
            pt([1., 0., 0.]).unwrap(),
            pt([0., 0., 0.]).unwrap(),
            pt([0., 1., 0.]).unwrap(),
        ];
        let controls = restrict(&k, &work, &root, [0.25, 0.75]).unwrap();
        let expected = [
            [0.5625, 0.0625, 0.],
            [0.1875, 0.1875, 0.],
            [0.0625, 0.5625, 0.],
        ];
        assert_eq!(controls.len(), 3);
        for (p, q) in controls.iter().zip(expected) {
            assert!(x::equal_point(&p.xyz, q));
            assert!(x::zero(&x::sub(&p.w, &x::scalar(1.).unwrap()).unwrap()));
        }
    }
    #[test]
    fn actual_uv_line_noz_is_zeroed_before_any_exact_arithmetic() {
        let line = crate::curve::line::Line::from_points(
            Point3::new(0., 0., crate::nurbs::math::NOZ),
            Point3::new(2., 0., crate::nurbs::math::NOZ),
            2,
        );
        let curve = crate::curve::curve::Curve::new(CurveKind::Line(line));
        assert_eq!(curve.dim(), 2);
        let ends = affine_ends(&curve, curve.natural_interval(), true).unwrap();
        assert!(x::equal_point(&ends[0], [0., 0., 0.]));
        assert!(x::equal_point(&ends[1], [2., 0., 0.]));
    }
    #[test]
    fn whole_actual_plane_gram_chart_preserves_projected_model_and_nonzero_band() {
        let plane = Plane::from_normal(Point3::new(1., 2., 3.), Vec3::new(0., 0., 1.));
        let chart = Chart::new(&plane, &x::point([0., 0., 1.]).unwrap()).unwrap();
        let p = pt([10., 20., 3.125]).unwrap();
        let error = chart.support_error(&p).unwrap();
        assert!((0.125..0.126).contains(&error));
        let image = chart.image(&chart.uv(&p).unwrap()).unwrap();
        for (c, v) in image.into_iter().zip([10., 20., 3.]) {
            assert!(c.lo <= v && c.hi >= v);
        }
    }
    #[test]
    fn complete_affine_cap_image_accounts_for_actual_small_domain_clamp() {
        use crate::geom::extent2d::Extent2d;
        use crate::math::Vec2;
        let k = Kernel::default();
        let work = MeshWork::new();
        let plane = Plane::new(
            Point3::ZERO,
            Vec3::new(1., 0., 0.),
            Vec3::new(0., 1., 0.),
            Vec2::new(1., 1.),
            &Extent2d::from_bounds(0., 0., 10., 20.),
        );
        let chart = Chart::new(&plane, &x::point([0., 0., 1.]).unwrap()).unwrap();
        let delta = 2.220446049250313e-15; // actual native-box diagnostic, a stored input value
        let uv = [pt([10., -delta, 0.]).unwrap(), pt([10., 20., 0.]).unwrap()];
        let b = affine_clamp_bound(&k, &work, &plane, &chart, &uv).unwrap();
        assert!(b.upper >= delta && b.upper < 1e-11);
        let [u, v, _] = b.endpoints[0];
        assert!(u.lo <= 10. && u.hi >= 10. && v.lo <= 0. && v.hi >= 0.);
        let mut not_native = uv;
        not_native[0].w = x::scalar(2.).unwrap();
        assert!(affine_clamp_bound(&k, &work, &plane, &chart, &not_native).is_err());
    }
    #[test]
    fn complete_affine_cap_bound_does_not_replace_an_interior_clamp_kink_by_its_chord() {
        use crate::geom::extent2d::Extent2d;
        use crate::math::Vec2;
        let k = Kernel::default();
        let work = MeshWork::new();
        let plane = Plane::new(
            Point3::ZERO,
            Vec3::new(1., 0., 0.),
            Vec3::new(0., 1., 0.),
            Vec2::new(1., 1.),
            &Extent2d::from_bounds(0., 0., 5., 20.),
        );
        let chart = Chart::new(&plane, &x::point([0., 0., 1.]).unwrap()).unwrap();
        let uv = [pt([-1., 0., 0.]).unwrap(), pt([1., 2., 0.]).unwrap()];
        let b = affine_clamp_bound(&k, &work, &plane, &chart, &uv).unwrap();
        assert!(b.upper >= 1. && b.upper < 1.001);
        // Actual midpoint=(0,1); interpolation of CLAMPED endpoints=(.5,1).
        // Their .5 gap cannot disappear behind exact endpoint agreement.
        let image =
            plane_trim_image_with_work(&k, &work, &plane, &[uv[0].xyz.clone(), uv[1].xyz.clone()])
                .unwrap();
        assert_eq!(image.knots.len(), 3);
        let gap = point_distance_upper(
            image.knots[1].point,
            [Ivl::from(0.5), Ivl::from(1.), Ivl::from(0.)],
        )
        .unwrap();
        assert!(gap >= 0.5 && b.upper >= gap);
    }
    #[test]
    fn chosen_cap_chart_rejects_a_noninjective_source_plane_projection() {
        use crate::geom::extent2d::Extent2d;
        use crate::math::Vec2;
        let plane = Plane::new(
            Point3::ZERO,
            Vec3::new(1., 0., 0.),
            Vec3::new(0., 1., 0.),
            Vec2::new(3., 2.),
            &Extent2d::from_bounds(0., 0., 10., 20.),
        );
        assert!(Chart::new(&plane, &x::point([0., 0., 1.]).unwrap()).is_some());
        // Projection to XY collapses the source plane normal to X: no filled
        // cap or rim topology may be transported under this singular restriction.
        assert!(Chart::new(&plane, &x::point([1., 0., 0.]).unwrap()).is_none());
    }
    #[test]
    fn cap_chart_refuses_native_normal_fallback_in_near_degenerate_stored_frame() {
        use crate::geom::{axis2_placement::Axis2Placement, extent2d::Extent2d};
        use crate::math::Vec2;
        use crate::nurbs::b_spline_surface::BSplineSurface;
        // The exact affine cross is −Y*1e−14, while native unitize_or_z returns
        // +Z on this noncanonical stored frame. Gram det is positive, so its
        // nonsingular chart alone would not justify the native MATERIAL normal.
        let frame = Axis2Placement::from_stored(
            Point3::ZERO,
            Vec3::new(1., 0., 0.),
            Vec3::new(1., 0., 1e-14),
        );
        let plane = Plane::from_stored(
            frame,
            Vec2::new(1., 1.),
            Extent2d::from_bounds(0., 0., 1., 1.),
            BSplineSurface::new(),
        );
        assert_eq!(plane.evaluate_normal(), Vec3::new(0., 0., 1.));
        assert!(!plane_parameter_normal_is_consistent(&plane));
        assert!(Chart::new(&plane, &x::point([0., -1., 0.]).unwrap()).is_none());
    }
    #[test]
    fn proved_full_affine_bspline_uses_existing_definition_helper_not_its_label() {
        use crate::geom::extent2d::Extent2d;
        use crate::math::Vec2;
        use crate::nurbs::{
            b_spline_curve::BSplineCurve,
            crv_basic::Curve as NCurve,
            math::{CPoint, NOZ},
        };
        let k = Kernel::default();
        let work = MeshWork::new();
        let delta = 2.220446049250313e-15;
        let make = |weight: f64| {
            crate::curve::curve::Curve::from(BSplineCurve::from_nurb(
                NCurve::new(
                    vec![
                        CPoint::new(0., 0., NOZ, 1.),
                        CPoint::new(10. * weight, -delta * weight, NOZ, weight),
                    ],
                    1,
                    vec![0., 0., 1., 1.],
                )
                .unwrap(),
                2,
                true,
            ))
        };
        let curve = make(1.);
        let ends = affine_ends(&curve, curve.natural_interval(), true).unwrap();
        let plane = Plane::new(
            Point3::ZERO,
            Vec3::new(1., 0., 0.),
            Vec3::new(0., 1., 0.),
            Vec2::new(1., 1.),
            &Extent2d::from_bounds(0., 0., 10., 20.),
        );
        let chart = Chart::new(&plane, &x::point([0., 0., 1.]).unwrap()).unwrap();
        let uv = ends.map(|xyz| ProjectivePoint {
            xyz,
            w: x::scalar(1.).unwrap(),
        });
        let b = affine_clamp_bound(&k, &work, &plane, &chart, &uv).unwrap();
        assert!(b.upper >= delta && b.upper < 1e-11);
        let rational = make(2.);
        assert!(affine_ends(&rational, rational.natural_interval(), true).is_none());
        // Varying positive weights keep a geometric line but make its native
        // PARAMETER map nonlinear: its midpoint must not become the affine5.
        assert!(rational.evaluate_point(&k, 0.5).unwrap().x > 6.);
    }
}
