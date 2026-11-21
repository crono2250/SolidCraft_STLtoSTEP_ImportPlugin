//! One-way complete original-region support/orientation proof against ACTUAL built tool data.
//!
//! Core's `AnalyticSupport::check` binds the cached form to the analytic SET
//! defined by the actual native data (owner rule13564), not a caller's fitted
//! Primitive. Sphere uses center/radius in a world Euclidean frame: its stored
//! transverse axes cannot turn that support into an ellipsoid. Torus uses the same
//! literal implicit axis, with complete set-distance AND oriented-gradient bounds
//! to its Euclidean analysis frame. Cone/Cylinder retain their stored radius law.
//!
//! Caps/margins are intentionally extended. This is finite source-region -> untrimmed actual
//! support, not reverse infinite-surface coverage or a whole-body reconstruction theorem.
//! Existing exact-class semantics are used as-is; this does not strengthen `lies_on` into a new
//! general NURBS construction/decomposition theorem. Nonzero native definition offset without
//! a derivative enclosure is refused, rather than using positional slack to invent normals.
use super::primitive_certificate::{
    cross, dot, norm, norm2_range, normalized, quarters, scale, sub, PointBox, Triangle,
};
use super::types::{FittedTool, MeshError, MeshInput, Result, SurfaceKind};
use super::MeshWork;
use crate::blend::fillet_section::interval::Ivl;
use crate::geom::axis2_placement::Axis2Placement;
use crate::nurbs::b_spline_surface_n_lib::p2::OrientType;
use crate::surface::implicit::{AnalyticSupport, Implicit};
use crate::surface::surface::{Surface, SurfaceKind as NativeKind};
use crate::surface::surface_cache::p3::definition_bound;
use crate::topology::{brep, face, Brep, FaceId};
use crate::{math::Vec3, Kernel};
use std::collections::BTreeSet;
const OP: &str = "mesh_reconstruction::certify_fitted_tool";
const MAX_DEPTH: u8 = 20;

/// Scoped to the exact original arrays, tool selection and untouched actual B-rep. No Clone,
/// serde, caller-authored boolean, or proof reuse after a mutation.
pub struct FittedToolCertificate<'a> {
    source: &'a MeshInput,
    selection: &'a FittedTool,
    body: &'a Brep,
    face: FaceId,
    support: AnalyticSupport,
    upper: f64,
    cells: usize,
}
impl FittedToolCertificate<'_> {
    /// Certified world-space upper distance for every complete selected source triangle
    /// to the actual untrimmed analytic side, including its stored definition bound.
    #[must_use]
    pub fn upper_bound(&self) -> f64 {
        self.upper
    }
    /// Complete barycentric cells processed, including parents subsequently subdivided.
    /// These consume the same workflow-owned cell and work budgets.
    #[must_use]
    pub fn cells(&self) -> usize {
        self.cells
    }
    /// The unchanged original arrays, selected tool data and actual B-rep borrowed by
    /// this proof. The borrow prevents adopting the token after changing any of them.
    #[must_use]
    pub fn source(&self) -> (&MeshInput, &FittedTool, &Brep) {
        (self.source, self.selection, self.body)
    }
    /// The actual certified face and its stored analytic definition in this same B-rep.
    /// The returned definition is descriptive data, not a transferable proof token.
    #[must_use]
    pub fn actual_support(&self) -> (FaceId, AnalyticSupport) {
        (self.face, self.support)
    }
}

fn invalid(detail: &'static str) -> MeshError {
    MeshError::InvalidInput {
        stage: OP,
        detail: detail.into(),
    }
}
fn undecided(work: usize) -> MeshError {
    MeshError::Undecided { stage: OP, work }
}
fn point(p: Vec3) -> PointBox {
    [Ivl::from(p.x), Ivl::from(p.y), Ivl::from(p.z)]
}
fn square(x: Ivl) -> Ivl {
    if x.lo >= 0. {
        x.mul_ulp(x)
    } else if x.hi <= 0. {
        let y = Ivl::new(-x.hi, -x.lo);
        y.mul_ulp(y)
    } else {
        Ivl::new(0., Ivl::from(x.mag()).mul_ulp(Ivl::from(x.mag())).hi)
    }
}
fn hull(t: &Triangle) -> PointBox {
    let [a, b, c] = *t;
    [
        a[0].hull(b[0]).hull(c[0]),
        a[1].hull(b[1]).hull(c[1]),
        a[2].hull(b[2]).hull(c[2]),
    ]
}
fn mat(rows: &[PointBox; 3], v: PointBox) -> PointBox {
    [dot(rows[0], v), dot(rows[1], v), dot(rows[2], v)]
}

struct FrameBound {
    origin: Vec3,
    inverse: [PointBox; 3],
    operator: f64,
    inverse_operator: f64,
    det_sign: i32,
}
impl FrameBound {
    fn from_axes(origin: Vec3, x: Vec3, y: Vec3, z: Vec3) -> Result<Self> {
        if [origin, x, y, z]
            .iter()
            .any(|v| !v.x.is_finite() || !v.y.is_finite() || !v.z.is_finite())
        {
            return Err(invalid("actual analytic placement is non-finite"));
        }
        let (x, y, z) = (point(x), point(y), point(z));
        let det = dot(x, cross(y, z));
        let det_sign = if det.lo > 0. {
            1
        } else if det.hi < 0. {
            -1
        } else {
            return Err(undecided(0));
        };
        let inverse = [cross(y, z), cross(z, x), cross(x, y)].map(|v| v.map(|v| v.div_ulp(det)));
        if inverse.iter().flatten().any(|x| !x.is_finite()) {
            return Err(undecided(0));
        }
        let axes = [x, y, z];
        let mut gram = 0f64;
        for a in axes {
            let mut row = Ivl::from(0.);
            for b in axes {
                row = row.add_ulp(Ivl::new(0., dot(a, b).mag()));
            }
            gram = gram.max(row.hi);
        }
        let operator = Ivl::from(gram).sqrt().hi;
        let mut inverse_norm2 = Ivl::from(0.);
        for row in inverse {
            for coefficient in row {
                inverse_norm2 = inverse_norm2.add_ulp(square(coefficient));
            }
        }
        let inverse_operator = inverse_norm2.sqrt().hi;
        if !operator.is_finite()
            || operator <= 0.
            || !inverse_operator.is_finite()
            || inverse_operator <= 0.
        {
            return Err(undecided(0));
        }
        Ok(Self {
            origin,
            inverse,
            operator,
            inverse_operator,
            det_sign,
        })
    }
    fn new(p: Axis2Placement) -> Result<Self> {
        Self::from_axes(p.origin(), p.x_axis(), p.y_axis(), p.z_axis())
    }
    /// One coherent exact orthonormal analysis frame about the SAME literal
    /// implicit axis. Returns its enclosed length separately: normalization is
    /// not silently treated as a set identity.
    fn about_axis(origin: Vec3, axis: Vec3) -> Result<(Self, Ivl)> {
        if !origin.to_array().into_iter().all(f64::is_finite)
            || !axis.to_array().into_iter().all(f64::is_finite)
        {
            return Err(invalid("analytic axis or origin is non-finite"));
        }
        let length = norm(point(axis));
        let z = normalized(point(axis)).ok_or_else(|| undecided(0))?;
        let index = axis
            .to_array()
            .into_iter()
            .enumerate()
            .min_by(|(_, a), (_, b)| a.abs().total_cmp(&b.abs()))
            .map(|(i, _)| i)
            .ok_or_else(|| undecided(0))?;
        let guide = [Vec3::X, Vec3::Y, Vec3::Z]
            .get(index)
            .copied()
            .ok_or_else(|| undecided(0))?;
        let x = normalized(cross(point(guide), z)).ok_or_else(|| undecided(0))?;
        let y = cross(z, x);
        if !length.is_finite()
            || length.lo <= 0.
            || [x, y, z].iter().flatten().any(|v| !v.is_finite())
        {
            return Err(undecided(0));
        }
        Ok((
            Self {
                origin,
                inverse: [x, y, z],
                operator: 1.,
                inverse_operator: 1.,
                det_sign: 1,
            },
            length,
        ))
    }
    fn local(&self, p: Vec3) -> PointBox {
        // Exact equality is used only for the actual canonical apex identity, not as a
        // distance shortcut for a near point. It avoids widening a known exact 0 to a star.
        if p == self.origin {
            [Ivl::from(0.); 3]
        } else {
            mat(&self.inverse, sub(point(p), point(self.origin)))
        }
    }
}

#[derive(Clone, Copy)]
enum LocalSupport {
    Plane,
    Radial {
        radius: f64,
        tangent: Ivl,
    },
    /// SAME literal implicit set in a Euclidean unit-axis analysis frame.
    QuadricRadial {
        radius: f64,
        law: Ivl,
        a: Ivl,
        b: Ivl,
        c: Ivl,
    },
    Sphere {
        radius: f64,
    },
    Torus {
        major: f64,
        minor: f64,
    },
}
struct Prepared {
    frame: FrameBound,
    shape: LocalSupport,
    orientation: i32,
    definition: f64,
    metric_defect: f64,
    normal_defect: f64,
}

/// Rigorous Taylor enclosure of tan of the stored angle converted from degrees. The
/// adjacent-double pi interval brackets real pi. Including the actual native floating slope
/// also binds `Cone::radius`'s stored evaluation convention without assuming libm accuracy.
fn tangent(degrees: f64, native_slope: f64) -> Result<Ivl> {
    if !degrees.is_finite() || degrees.abs() >= 90. || !native_slope.is_finite() {
        return Err(invalid("actual cone angle is not finite and acute"));
    }
    let x = Ivl::from(degrees)
        .mul_ulp(Ivl::new(core::f64::consts::PI, 3.1415926535897936))
        .div_ulp(Ivl::from(180.));
    let (sine, cosine) = super::interval_trig::sin_cos(x).ok_or_else(|| undecided(0))?;
    if !cosine.is_finite() || cosine.lo <= 0. {
        return Err(undecided(0));
    }
    Ok(sine.div_ulp(cosine).hull(Ivl::from(native_slope)))
}
fn family(a: &AnalyticSupport) -> SurfaceKind {
    match a {
        AnalyticSupport::Plane { .. } => SurfaceKind::Plane,
        AnalyticSupport::Cylinder { .. } => SurfaceKind::Cylinder,
        AnalyticSupport::Cone { .. } => SurfaceKind::Cone,
        AnalyticSupport::Sphere { .. } => SurfaceKind::Sphere,
        AnalyticSupport::Torus { .. } => SurfaceKind::Torus,
    }
}
fn parameter_sign(surface: &Surface, support: &AnalyticSupport) -> Result<i32> {
    match surface.kind() {
        NativeKind::Plane(_) => {
            let AnalyticSupport::Plane { uv_scale, .. } = support else {
                return Err(invalid("actual plane label mismatch"));
            };
            let p = Ivl::from(uv_scale.x).mul_ulp(Ivl::from(uv_scale.y));
            if p.lo > 0. {
                Ok(1)
            } else if p.hi < 0. {
                Ok(-1)
            } else {
                Err(undecided(0))
            }
        }
        NativeKind::Cone(c) => Ok(if c.rev().swap_uv() == c.inside_out() {
            1
        } else {
            -1
        }),
        NativeKind::Sphere(s) => Ok(if s.base().swap_uv() == s.inside_out() {
            1
        } else {
            -1
        }),
        NativeKind::Torus(t) => Ok(if t.base().swap_uv() == t.inside_out() {
            1
        } else {
            -1
        }),
        _ => Err(invalid("actual side is not a supported analytic surface")),
    }
}
/// S first: a retained definition is not certified by a label/net identity test.
fn bare_analytic(surface: &Surface) -> Result<()> {
    if surface.has_kept_definition() || surface.procedural_definition().is_some() {
        return Err(MeshError::Undecided {
            stage: "actual fitted side has a retained mathematical definition",
            work: 0,
        });
    }
    Ok(())
}

/// Full literal-implicit torus / unit-direction torus bridge, not samples.
/// Write A=lambda*n and Q=rho²+h²-R²-r². The SAME stored equation is
/// Q²+4R²*lambda²*h²-4R²*r²=0. Its whole ring is parametrized by
/// h=(r/lambda)sin(phi), rho²=(R+r*cos(phi))²+(1-1/lambda²)r²*sin²(phi).
/// A strictly positive whole rho lower bound gives a bijection for all phi and
/// all azimuths, including the reverse direction; no hidden axial branch exists.
///
/// Relative to rho0=R+r*cos(phi), h0=r*sin(phi), use the difference of squares
/// for the radial gap and the exact height gap. Dividing its actual gradient by
/// the POSITIVE 8R*rho0*r gives components (rho/rho0)cos(phi) and
/// (r*cos(phi)+R*lambda²)/(lambda*rho0)*sin(phi). Their difference from the
/// canonical unit normal is bounded by the returned second value. Requiring
/// that value<1 proves regularity and a consistent outward hemisphere.
fn torus_set_defect(major: f64, minor: f64, lambda: Ivl) -> Result<[f64; 2]> {
    if !(major.is_finite()
        && minor.is_finite()
        && major > minor
        && minor > 0.
        && lambda.is_finite()
        && lambda.lo > 0.)
    {
        return Err(invalid("literal torus set has no finite ring data"));
    }
    let one = Ivl::from(1.);
    let (r_major, r) = (Ivl::from(major), Ivl::from(minor));
    let m = r_major - r;
    let inverse = one / lambda;
    let coefficient = one - square(inverse);
    let radial_min2 = square(m) + Ivl::from(coefficient.lo.min(0.)) * square(r);
    if !m.is_finite() || m.lo <= 0. || !radial_min2.is_finite() || radial_min2.lo <= 0. {
        return Err(undecided(0));
    }
    let radial_min = radial_min2.sqrt();
    let radial_gap = Ivl::from(coefficient.mag()) * square(r) / (radial_min + m);
    let height_gap = r * Ivl::from((inverse - one).mag());
    let distance = norm([radial_gap, height_gap, Ivl::from(0.)]).hi;
    let radial_normal = radial_gap / m;
    let height_normal = Ivl::from((lambda - one).mag()) * (r_major * lambda + r) / (lambda * m);
    let normal = norm([radial_normal, height_normal, Ivl::from(0.)]).hi;
    if !distance.is_finite()
        || distance < 0.
        || !normal.is_finite()
        || !(0.0..1.0).contains(&normal)
    {
        return Err(undecided(0));
    }
    Ok([distance, normal])
}
/// In n=A/|A| coordinates the SAME implicit radial set is rho²=Q(h),
/// Q(h)=r²+2*r*t*lambda*h+[lambda²*(1+t²)-1]*h². Raw transverse
/// placement scales are not a Euclidean metric and never deform this set.
fn literal_radial_shape(radius: f64, tangent: Ivl, lambda: Ivl) -> Result<LocalSupport> {
    let one = Ivl::from(1.);
    let law = tangent.mul_ulp(lambda);
    let a = square(lambda)
        .mul_ulp(one.add_ulp(square(tangent)))
        .sub_ulp(one);
    let b = Ivl::from(radius).mul_ulp(law);
    let c = square(Ivl::from(radius));
    if ![a, b, c, law].into_iter().all(Ivl::is_finite) || !radius.is_finite() {
        return Err(undecided(0));
    }
    if radius == 0. {
        // Only a canonical zero-radius pole has the homogeneous apex theorem.
        // The actual implicit gradient on its selected nappe is a positive
        // multiple of the existing signed-slope normal; keep the raw-star proof.
        if a.lo <= 0. {
            return Err(undecided(0));
        }
        let slope = if tangent.lo > 0. {
            a.sqrt()
        } else if tangent.hi < 0. {
            {
                let value = a.sqrt();
                Ivl::new(-value.hi, -value.lo)
            }
        } else {
            return Err(undecided(0));
        };
        Ok(LocalSupport::Radial {
            radius,
            tangent: slope,
        })
    } else {
        Ok(LocalSupport::QuadricRadial {
            radius,
            law,
            a,
            b,
            c,
        })
    }
}

fn prepare(surface: &Surface, support: AnalyticSupport, use_sign: i32) -> Result<Prepared> {
    bare_analytic(surface)?;
    let definition = definition_bound(surface);
    // Existing analytic kinds have definition_bound=0. A future nonzero positional-only
    // offset supplies no derivative bound and may not establish material orientation.
    if !definition.is_finite() || definition != 0. {
        return Err(undecided(0));
    }
    let (placement, mut shape) = match support {
        AnalyticSupport::Plane { placement, .. } => (placement, LocalSupport::Plane),
        AnalyticSupport::Cylinder { placement, radius } if radius.is_finite() && radius > 0. => {
            let NativeKind::Cone(cone) = surface.kind() else {
                return Err(invalid("actual cylinder definition mismatch"));
            };
            if cone.semi_angle_deg() != 0. {
                return Err(invalid(
                    "Cylinder class contradicts the stored native radius law",
                ));
            }
            (
                placement,
                LocalSupport::Radial {
                    radius,
                    tangent: Ivl::from(0.),
                },
            )
        }
        AnalyticSupport::Cone {
            placement,
            base_radius,
            semi_angle_deg,
        } if base_radius.is_finite() => {
            let NativeKind::Cone(cone) = surface.kind() else {
                return Err(invalid("actual cone definition mismatch"));
            };
            (
                placement,
                LocalSupport::Radial {
                    radius: base_radius,
                    tangent: tangent(semi_angle_deg, cone.tan_semi_angle())?,
                },
            )
        }
        AnalyticSupport::Sphere { placement, radius } if radius.is_finite() && radius > 0. => {
            (placement, LocalSupport::Sphere { radius })
        }
        AnalyticSupport::Torus {
            placement,
            major_radius,
            minor_radius,
        } if major_radius.is_finite()
            && minor_radius.is_finite()
            && major_radius > minor_radius
            && minor_radius > 0. =>
        {
            (
                placement,
                LocalSupport::Torus {
                    major: major_radius,
                    minor: minor_radius,
                },
            )
        }
        _ => return Err(invalid("actual side has invalid or singular radii")),
    };
    // A coordinate change is not a geometry edit. Sphere is its Euclidean
    // center/radius set. Torus uses the SAME literal Implicit axis, with BOTH
    // positional and oriented-gradient defects retained after unitization.
    // Radial supports retain their full literal radius/height law after unitization.
    let (frame, metric_defect, normal_defect) = match support {
        AnalyticSupport::Sphere { .. } => (
            FrameBound::from_axes(placement.origin(), Vec3::X, Vec3::Y, Vec3::Z)?,
            0.,
            0.,
        ),
        AnalyticSupport::Torus {
            major_radius,
            minor_radius,
            ..
        } => {
            let Implicit::Torus { axis, .. } = support.implicit() else {
                return Err(invalid("actual torus implicit kind mismatch"));
            };
            let (frame, lambda) = FrameBound::about_axis(placement.origin(), axis)?;
            let [position, normal] = torus_set_defect(major_radius, minor_radius, lambda)?;
            (frame, position, normal)
        }
        AnalyticSupport::Cylinder { .. } | AnalyticSupport::Cone { .. } => {
            let Implicit::Cone {
                axis,
                radius,
                tan_angle,
                ..
            } = support.implicit()
            else {
                return Err(invalid("actual radial implicit kind mismatch"));
            };
            let LocalSupport::Radial { tangent, .. } = shape else {
                return Err(invalid("actual radial support kind mismatch"));
            };
            let (frame, lambda) = FrameBound::about_axis(placement.origin(), axis)?;
            // Enclose the SAME literal coefficient, the mathematical angle and
            // the native radius-law slope; never assume their libm paths agree.
            shape = literal_radial_shape(radius, tangent.hull(Ivl::from(tan_angle)), lambda)?;
            (frame, 0., 0.)
        }
        AnalyticSupport::Plane { .. } => (FrameBound::new(placement)?, 0., 0.),
    };
    let orientation = parameter_sign(surface, &support)? * use_sign * frame.det_sign;
    Ok(Prepared {
        frame,
        shape,
        orientation,
        definition,
        metric_defect,
        normal_defect,
    })
}

fn radial_triangle(t: &Triangle) -> Triangle {
    t.map(|p| [p[0], p[1], Ivl::from(0.)])
}
fn radial_polynomial(t: &Triangle, r: [Ivl; 3]) -> Ivl {
    let points = radial_triangle(t);
    let mut lo = f64::INFINITY;
    let mut hi = f64::NEG_INFINITY;
    for (i, (a, ra)) in points.iter().zip(r).enumerate() {
        for (b, rb) in points.iter().zip(r).skip(i) {
            let c = dot(*a, *b).sub_ulp(ra.mul_ulp(rb));
            lo = lo.min(c.lo);
            hi = hi.max(c.hi);
        }
    }
    Ivl::new(lo, hi)
}
fn radial_error(t: &Triangle, radius: f64, tangent: Ivl) -> (Ivl, bool) {
    let rr = t.map(|p| Ivl::from(radius).add_ulp(tangent.mul_ulp(p[2])));
    let mut positive = rr.iter().all(|r| r.lo >= 0.);
    // Exact zero-radius canonical apex law. Outward 0*t widening is not negative radius.
    if radius == 0.
        && ((tangent.lo > 0. && t.iter().all(|p| p[2].lo >= 0.))
            || (tangent.hi < 0. && t.iter().all(|p| p[2].hi <= 0.)))
    {
        positive = true;
    }
    if !positive {
        return (Ivl::whole(), false);
    }
    // rr is scalar: its hull is written explicitly to avoid correlation assumptions.
    let r = rr[0].hull(rr[1]).hull(rr[2]);
    let rho = norm2_range(&radial_triangle(t)).sqrt();
    let denominator = rho.add_ulp(Ivl::new(r.lo.max(0.), r.hi));
    if denominator.lo > 0. {
        let q = radial_polynomial(t, rr).div_ulp(denominator);
        return (Ivl::new(q.mig(), q.mag()), true);
    }
    // Apex triangle homogeneity: p/h lies on the convex segment of the two non-apex
    // generator slopes. Cancelling h analytically avoids dividing an apex interval by 0.
    if radius == 0. {
        let nonzero: Vec<_> = t
            .iter()
            .filter(|p| p.iter().any(|v| *v != Ivl::from(0.)))
            .collect();
        if let [a, b] = nonzero.as_slice() {
            if [a, b].iter().all(|p| p[2].lo > 0. || p[2].hi < 0.) {
                let slopes = [
                    [a[0].div_ulp(a[2]), a[1].div_ulp(a[2]), Ivl::from(0.)],
                    [b[0].div_ulp(b[2]), b[1].div_ulp(b[2]), Ivl::from(0.)],
                ];
                let st = [slopes[0], slopes[1], slopes[0]];
                let rho = norm2_range(&st).sqrt();
                let target = Ivl::new(tangent.mig(), tangent.mag());
                let den = rho.add_ulp(target);
                if den.lo > 0. {
                    let difference = radial_polynomial(&st, [target; 3]).div_ulp(den);
                    let height = t.iter().map(|p| p[2].mag()).fold(0., f64::max);
                    let upper = Ivl::from(height).mul_ulp(Ivl::from(difference.mag())).hi;
                    return (Ivl::new(0., upper), true);
                }
            }
        }
    }
    let difference = rho.sub_ulp(r);
    (Ivl::new(difference.mig(), difference.mag()), true)
}

/// For any root y of this quadratic F, |F(x)| <= |grad F(x)|*d + M*d²,
/// M=max(1,|a|), d=|x-y|. The rationalized positive root is therefore a
/// GLOBAL distance lower, not a lower bound inferred from a fixed-height witness.
fn quadratic_distance_lower(residual: Ivl, source_gradient: PointBox, a: Ivl) -> f64 {
    let f = residual.mig();
    let g = norm(source_gradient).hi;
    let m = a.mag().max(1.);
    if !(f.is_finite() && f > 0. && g.is_finite() && m.is_finite()) {
        return 0.;
    }
    let g = Ivl::from(g);
    let root = square(g)
        .add_ulp(Ivl::from(4.).mul_ulp(Ivl::from(m)).mul_ulp(Ivl::from(f)))
        .sqrt();
    let den = g.add_ulp(root);
    if !den.is_finite() || den.lo <= 0. {
        return 0.;
    }
    let bound = Ivl::from(2.).mul_ulp(Ivl::from(f)).div_ulp(den);
    if bound.is_finite() {
        bound.lo.max(0.)
    } else {
        0.
    }
}

/// Whole triangular Bernstein Q/F ranges and SAME-height radial witness. Its
/// normal is evaluated at the TARGET witness, not at the off-surface source.
fn literal_radial_cell(
    t: &Triangle,
    n: PointBox,
    radius: f64,
    law: Ivl,
    a: Ivl,
    b: Ivl,
    c: Ivl,
) -> (Ivl, Ivl) {
    let box_ = hull(t);
    let positive = Ivl::from(radius).add_ulp(law.mul_ulp(box_[2]));
    if !positive.is_finite() || positive.lo <= 0. {
        return (Ivl::whole(), Ivl::whole());
    }
    let (mut qlo, mut qhi, mut flo, mut fhi) = (
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::INFINITY,
        f64::NEG_INFINITY,
    );
    for (i, p) in t.iter().enumerate() {
        for z in t.iter().skip(i) {
            let q = a
                .mul_ulp(p[2])
                .mul_ulp(z[2])
                .add_ulp(b.mul_ulp(p[2].add_ulp(z[2])))
                .add_ulp(c);
            let f = p[0].mul_ulp(z[0]).add_ulp(p[1].mul_ulp(z[1])).sub_ulp(q);
            if !q.is_finite() || !f.is_finite() {
                return (Ivl::whole(), Ivl::whole());
            }
            qlo = qlo.min(q.lo);
            qhi = qhi.max(q.hi);
            flo = flo.min(f.lo);
            fhi = fhi.max(f.hi);
        }
    }
    let q = Ivl::new(qlo, qhi);
    let rho = norm2_range(&radial_triangle(t)).sqrt();
    if q.lo <= 0. || !rho.is_finite() || rho.lo <= 0. {
        return (Ivl::whole(), Ivl::whole());
    }
    let target_radius = q.sqrt();
    let f = Ivl::new(flo, fhi);
    let residual = f.div_ulp(rho.add_ulp(target_radius));
    let axial_value = a.mul_ulp(box_[2]).add_ulp(b);
    let axial = Ivl::new(-axial_value.hi, -axial_value.lo);
    let target_scale = target_radius.div_ulp(rho);
    let orientation = dot(
        n,
        [
            box_[0].mul_ulp(target_scale),
            box_[1].mul_ulp(target_scale),
            axial,
        ],
    );
    let source_gradient = scale([box_[0], box_[1], axial], Ivl::from(2.));
    let lower = quadratic_distance_lower(f, source_gradient, a);
    (Ivl::new(lower, residual.mag()), orientation)
}

/// A complete cell distance upper and a strict actual normal-dot enclosure. The lower is
/// used only to discard a noncorresponding support, never as a sampled acceptance shortcut.
fn cell(t: &Triangle, normal: PointBox, prepared: &Prepared, apex_proven: bool) -> (Ivl, Ivl) {
    let n = scale(
        mat(&prepared.frame.inverse, normal),
        Ivl::from(f64::from(prepared.orientation)),
    );
    let box_ = hull(t);
    let (distance, orientation) = match prepared.shape {
        LocalSupport::Plane => (Ivl::new(box_[2].mig(), box_[2].mag()), n[2]),
        LocalSupport::Sphere { radius } => {
            let d = norm2_range(t).sqrt().sub_ulp(Ivl::from(radius));
            (Ivl::new(d.mig(), d.mag()), dot(n, box_))
        }
        LocalSupport::Radial { radius, tangent } => {
            let (d, positive) = radial_error(t, radius, tangent);
            if !positive {
                return (Ivl::whole(), Ivl::whole());
            }
            let radial = radial_triangle(t);
            let rho = norm2_range(&radial).sqrt();
            let orient = if rho.lo > 0. {
                let r = hull(&radial);
                dot(
                    n,
                    [
                        r[0].div_ulp(rho),
                        r[1].div_ulp(rho),
                        Ivl::new(-tangent.hi, -tangent.lo),
                    ],
                )
            } else {
                let axial = n[2].mul_ulp(tangent).mul_ulp(Ivl::from(-1.));
                let mut lower = f64::INFINITY;
                let mut ok = axial.lo >= 0.;
                let mut regular = false;
                for (original, p) in t.iter().zip(radial) {
                    if p.iter().all(|v| *v == Ivl::from(0.)) {
                        // A different point of the axis is not the singular surface apex.
                        ok &= apex_proven && original.iter().all(|v| *v == Ivl::from(0.));
                        continue;
                    }
                    let value = n[0].mul_ulp(p[0]).add_ulp(n[1].mul_ulp(p[1]));
                    ok &= value.lo > 0.;
                    lower = lower.min(value.lo);
                    regular = true;
                }
                if ok && regular && rho.hi.is_finite() && rho.hi > 0. {
                    // With an exact apex vertex, L and rho both scale by the total weight
                    // beta of the other vertices: L>=beta*Lmin, rho<=beta*rhoMax. Hence
                    // L/rho>=Lmin/rhoMax, including all regular points approaching the apex.
                    // Without an apex this is the ordinary positive numerator/rho bound.
                    let margin = Ivl::from(lower)
                        .div_ulp(Ivl::from(rho.hi))
                        .add_ulp(axial)
                        .lo;
                    Ivl::new(margin, f64::INFINITY)
                } else {
                    Ivl::whole()
                }
            };
            (d, orient)
        }
        LocalSupport::QuadricRadial {
            radius,
            law,
            a,
            b,
            c,
        } => literal_radial_cell(t, n, radius, law, a, b, c),
        LocalSupport::Torus { major, minor } => {
            let rho = norm2_range(&radial_triangle(t)).sqrt();
            let a = rho.sub_ulp(Ivl::from(major));
            let c = square(a).add_ulp(square(box_[2])).sqrt();
            let d = c.sub_ulp(Ivl::from(minor));
            if rho.lo <= 0. {
                return (Ivl::new(d.mig(), d.mag()), Ivl::whole());
            }
            let factor = Ivl::from(1.).sub_ulp(Ivl::from(major).div_ulp(rho));
            (Ivl::new(d.mig(), d.mag()), {
                let canonical = dot(
                    n,
                    [box_[0].mul_ulp(factor), box_[1].mul_ulp(factor), box_[2]],
                );
                // This field is c times the canonical unit normal. The same
                // phi maps to the literal support, whose scaled gradient
                // differs by at most normal_defect. Charge its whole c and
                // whole source-normal bounds; a position-only gap is not a
                // material-orientation certificate.
                let shift = Ivl::from(c.hi) * norm(n) * Ivl::from(prepared.normal_defect);
                if shift.is_finite() {
                    canonical + Ivl::new(-shift.hi, shift.hi)
                } else {
                    Ivl::whole()
                }
            })
        }
    };
    let upper = Ivl::from(distance.hi)
        .mul_ulp(Ivl::from(prepared.frame.operator))
        .add_ulp(Ivl::from(prepared.definition))
        .add_ulp(Ivl::from(prepared.metric_defect))
        .hi;
    // ||M v|| >= ||v||/||M^-1||. A cone's fixed-height radial residual is an
    // UPPER distance witness; divide its lower by sqrt(1+T^2) to obtain a lower
    // distance to the larger double-cone support (hence also to the one-sided side).
    let local_lower = match prepared.shape {
        LocalSupport::Radial { tangent, .. } => Ivl::from(distance.lo)
            .div_ulp(Ivl::from(1.).add_ulp(square(tangent)).sqrt())
            .lo
            .max(0.),
        _ => distance.lo,
    };
    let lower = Ivl::from(local_lower)
        .div_ulp(Ivl::from(prepared.frame.inverse_operator))
        .sub_ulp(Ivl::from(prepared.metric_defect))
        .lo
        .max(0.);
    (Ivl::new(lower, upper), orientation)
}

fn canonical_apex(
    k: &Kernel,
    work: &MeshWork,
    source: &MeshInput,
    tool: &FittedTool,
    prepared: &Prepared,
) -> Result<bool> {
    let LocalSupport::Radial { radius, tangent } = prepared.shape else {
        return Ok(false);
    };
    if radius != 0. || !(tangent.lo > 0. || tangent.hi < 0.) {
        return Ok(false);
    }
    let link = super::certificate::ordered_apex_link_with_work(
        k,
        work,
        source,
        &tool.source_triangles,
        prepared.frame.origin.to_array(),
    )?;
    let Some(link) = link else {
        return Ok(false);
    };
    work.reserve_output(k, link.len())?;
    let local: Vec<_> = link
        .iter()
        .map(|p| prepared.frame.local(Vec3::from_array(*p)))
        .collect();
    for point in &local {
        if tangent.mul_ulp(point[2]).lo <= 0. {
            return Err(undecided(local.len()));
        }
    }
    super::angular_link::certify_angular_link(
        k,
        work,
        &local,
        [Ivl::from(0.), Ivl::from(0.), Ivl::from(1.)],
    )?;
    Ok(true)
}

fn prove(
    k: &Kernel,
    work: &MeshWork,
    source: &MeshInput,
    tool: &FittedTool,
    prepared: &Prepared,
    tolerance: f64,
) -> Result<Option<(f64, usize)>> {
    let apex_proven = canonical_apex(k, work, source, tool, prepared)?;
    let (mut upper, mut cells) = (0f64, 0usize);
    for id in &tool.source_triangles {
        work.spend(k, 1)?;
        let [a, b, c] = source
            .triangles
            .get(*id as usize)
            .copied()
            .ok_or_else(|| invalid("selected original triangle is missing"))?;
        let at = |id: u32| {
            source
                .positions
                .get(id as usize)
                .copied()
                .map(Vec3::from_array)
                .ok_or_else(|| invalid("selected original vertex is missing"))
        };
        let (pa, pb, pc) = (at(a)?, at(b)?, at(c)?);
        let mut normal = cross(sub(point(pb), point(pa)), sub(point(pc), point(pa)));
        if tool.concave {
            normal = scale(normal, Ivl::from(-1.));
        }
        if norm(normal).lo <= 0. {
            return Err(undecided(cells));
        }
        if matches!(prepared.shape, LocalSupport::Plane) {
            // Constant normal uncertainty cannot improve by subdividing a plane. Refuse this
            // correspondence immediately; do not exhaust the whole job on a perpendicular cap.
            let n = scale(
                mat(&prepared.frame.inverse, normal),
                Ivl::from(f64::from(prepared.orientation)),
            );
            if n[2].lo <= 0. {
                return Ok(None);
            }
        }
        let triangle = [
            prepared.frame.local(pa),
            prepared.frame.local(pb),
            prepared.frame.local(pc),
        ];
        let mut pending = vec![(triangle, 0u8)];
        while let Some((triangle, depth)) = pending.pop() {
            work.reserve_cells(k, 1)?;
            work.spend(k, 512)?;
            cells = cells.saturating_add(1);
            let (distance, orientation) = cell(&triangle, normal, prepared, apex_proven);
            if distance.hi.is_finite() && distance.hi <= tolerance && orientation.lo > 0. {
                upper = upper.max(distance.hi);
                continue;
            }
            if distance.lo > tolerance || orientation.hi <= 0. {
                return Ok(None);
            }
            if depth >= MAX_DEPTH {
                return Ok(None);
            }
            for child in quarters(&triangle) {
                pending.push((child, depth + 1));
            }
        }
    }
    work.check(k)?;
    Ok(Some((upper, cells)))
}

/// Prove every complete selected original triangle against one actual analytic side support,
/// including source material winding and actual face-use/parameter orientation.
///
/// # Errors
/// Invalid selected source IDs/data; exact input/work/output/cell budget limits; native
/// construction-support errors or cancellation; typed Undecided when complete correspondence,
/// an invertible actual frame, actual normal direction, or a required apex star is unproved.
pub fn certify_fitted_tool_with_work<'a>(
    k: &Kernel,
    work: &MeshWork,
    source: &'a MeshInput,
    tool: &'a FittedTool,
    candidate: &'a mut Brep,
    tolerance: f64,
) -> Result<FittedToolCertificate<'a>> {
    work.check(k)?;
    super::regions::checked_tolerance(tolerance)?;
    if source.positions.len() > super::source::MAX_POSITIONS {
        return Err(MeshError::InputLimit {
            stage: OP,
            count: source.positions.len(),
            limit: super::source::MAX_POSITIONS,
            unit: "vertices",
        });
    }
    if source.triangles.len() > super::source::MAX_TRIANGLES {
        return Err(MeshError::InputLimit {
            stage: OP,
            count: source.triangles.len(),
            limit: super::source::MAX_TRIANGLES,
            unit: "triangles",
        });
    }
    if tool.source_triangles.is_empty() {
        return Err(invalid("a fitted tool has no selected original triangles"));
    }
    work.reserve_output(k, tool.source_triangles.len())?;
    let mut seen = BTreeSet::new();
    for id in &tool.source_triangles {
        work.spend(k, 1)?;
        if !seen.insert(*id) {
            return Err(invalid("duplicate original triangle in fitted tool"));
        }
        let tri = source
            .triangles
            .get(*id as usize)
            .ok_or_else(|| invalid("a fitted tool names a missing original triangle"))?;
        for id in tri {
            let p = source
                .positions
                .get(*id as usize)
                .ok_or_else(|| invalid("an original triangle names a missing vertex"))?;
            if p.iter().any(|x| !x.is_finite() || x.abs() > 1e9) {
                return Err(invalid(
                    "an original selected vertex is non-finite or exceeds coordinate budget",
                ));
            }
        }
    }
    work.reserve_output(k, candidate.face_list().len())?;
    let faces = brep::faces(candidate, None)?;
    for id in faces {
        work.spend(k, 1)?;
        let surface = face::surface(candidate, id)?
            .ok_or_else(|| invalid("an actual fitted face has no support"))?;
        let Some(label) = AnalyticSupport::of(surface) else {
            continue;
        };
        if family(&label) != tool.surface.kind() {
            continue;
        }
        // Check S before asking about its B/label. Exact retained rounds, drafted faces,
        // sweeps and corners need their own identity/normal proof; epsilon=0 is not one.
        bare_analytic(surface)?;
        let support = AnalyticSupport::check(k, surface)?;
        let outside = face::p2::outer_faceuse(candidate, id)?
            .ok_or_else(|| invalid("an actual fitted support has no exterior face use"))?;
        let use_sign = match candidate.faceuse(outside)?.orientation {
            OrientType::Same => 1,
            OrientType::Opposite => -1,
            OrientType::Unknown => return Err(undecided(0)),
        };
        work.spend(k, 1024)?;
        let prepared = prepare(surface, support, use_sign)?;
        if let Some((upper, cells)) = prove(k, work, source, tool, &prepared, tolerance)? {
            work.check(k)?;
            return Ok(FittedToolCertificate {
                source,
                selection: tool,
                body: candidate,
                face: id,
                support,
                upper,
                cells,
            });
        }
    }
    Err(undecided(tool.source_triangles.len()))
}

#[cfg(test)]
mod tests {
    use super::super::types::{Primitive, ToolGeometry};
    use super::*;
    fn cylinder_selection(reverse: bool, concave: bool) -> (MeshInput, FittedTool) {
        let angle = 0.005f64;
        let source = MeshInput {
            positions: vec![
                [10., 0., 0.],
                [10. * angle.cos(), 10. * angle.sin(), 0.],
                [10., 0., 10.],
            ],
            triangles: vec![if reverse { [0, 2, 1] } else { [0, 1, 2] }],
        };
        let selected = FittedTool {
            surface: Primitive::Cylinder {
                point: Vec3::ZERO,
                axis: Vec3::Z,
                radius: 10.,
            },
            geometry: ToolGeometry::Cylinder {
                origin: Vec3::ZERO,
                axis: Vec3::Z,
                radius: 10.,
                length: 10.,
            },
            source_triangles: vec![0],
            concave,
        };
        (source, selected)
    }
    #[test]
    fn actual_cylinder_support_passes_but_an_ideal_label_cannot_hide_a_moved_tool() {
        let (mut k, work) = (Kernel::default(), MeshWork::new());
        let (source, selected) = cylinder_selection(false, false);
        let mut correct = super::super::build_tool::build_tool(&mut k, &selected.geometry).unwrap();
        let certificate =
            certify_fitted_tool_with_work(&k, &work, &source, &selected, &mut correct, 0.05)
                .unwrap();
        assert!(certificate.upper_bound() <= 0.05);
        let moved = ToolGeometry::Cylinder {
            origin: Vec3::new(50., 0., 0.),
            axis: Vec3::Z,
            radius: 10.,
            length: 10.,
        };
        let mut wrong = super::super::build_tool::build_tool(&mut k, &moved).unwrap();
        assert!(certify_fitted_tool_with_work(
            &k,
            &MeshWork::new(),
            &source,
            &selected,
            &mut wrong,
            0.05
        )
        .is_err());
    }
    #[test]
    fn source_material_side_and_actual_faceuse_are_not_ignored() {
        let mut k = Kernel::default();
        let (source, mut selected) = cylinder_selection(true, false);
        let mut body = super::super::build_tool::build_tool(&mut k, &selected.geometry).unwrap();
        assert!(certify_fitted_tool_with_work(
            &k,
            &MeshWork::new(),
            &source,
            &selected,
            &mut body,
            0.05
        )
        .is_err());
        selected.concave = true;
        assert!(certify_fitted_tool_with_work(
            &k,
            &MeshWork::new(),
            &source,
            &selected,
            &mut body,
            0.05
        )
        .is_ok());
    }
    #[test]
    fn a_sphere_chords_interior_is_checked_even_when_every_vertex_is_on_the_sphere() {
        let mut k = Kernel::default();
        let source = MeshInput {
            positions: vec![[1., 0., 0.], [0., 1., 0.], [0., 0., 1.]],
            triangles: vec![[0, 1, 2]],
        };
        let selected = FittedTool {
            surface: Primitive::Sphere {
                center: Vec3::ZERO,
                radius: 1.,
            },
            geometry: ToolGeometry::Sphere {
                center: Vec3::ZERO,
                radius: 1.,
            },
            source_triangles: vec![0],
            concave: false,
        };
        let mut body = super::super::build_tool::build_tool(&mut k, &selected.geometry).unwrap();
        assert!(certify_fitted_tool_with_work(
            &k,
            &MeshWork::new(),
            &source,
            &selected,
            &mut body,
            0.01
        )
        .is_err());
    }
    #[test]
    fn actual_inverse_frame_encloses_rounding_and_keeps_reflected_parametric_sense() {
        let x = Vec3::new(1. + 4. * f64::EPSILON, 0., 0.);
        let y = Vec3::new(2. * f64::EPSILON, 1., 0.);
        let frame = FrameBound::from_axes(Vec3::ZERO, x, y, Vec3::Z).unwrap();
        let local = frame.local(x);
        assert!(local[0].lo <= 1. && local[0].hi >= 1.);
        assert!(local[1].lo <= 0. && local[1].hi >= 0.);
        assert!(frame.operator >= 1.);
        assert_eq!(frame.det_sign, 1);
        let reflected = FrameBound::from_axes(Vec3::ZERO, Vec3::X, Vec3::Y, -Vec3::Z).unwrap();
        assert_eq!(reflected.det_sign, -1);
        // du cross dv stays +Z for the reflected XY parameter plane: det(M) M^-T ez.
        let dual = scale(
            mat(&reflected.inverse, point(Vec3::Z)),
            Ivl::from(f64::from(reflected.det_sign)),
        );
        assert!(dual[2].lo > 0.);
        assert!(FrameBound::from_axes(Vec3::ZERO, Vec3::X, Vec3::X, Vec3::Z).is_err());
    }
    #[test]
    fn canonical_apex_cells_need_the_independent_star_proof() {
        let angle = 59f64;
        let slope = (angle * std::f64::consts::PI / 180.).tan();
        let h = 10.;
        let radius = h * slope;
        let turn = 0.005f64;
        let a = Vec3::ZERO;
        let b = Vec3::new(radius * turn.cos(), radius * turn.sin(), h);
        let c = Vec3::new(radius, 0., h);
        let triangle = [point(a), point(b), point(c)];
        let normal = cross(sub(point(b), point(a)), sub(point(c), point(a)));
        let prepared = Prepared {
            frame: FrameBound::from_axes(Vec3::ZERO, Vec3::X, Vec3::Y, Vec3::Z).unwrap(),
            shape: LocalSupport::Radial {
                radius: 0.,
                tangent: tangent(angle, slope).unwrap(),
            },
            orientation: 1,
            definition: 0.,
            metric_defect: 0.,
            normal_defect: 0.,
        };
        let (distance, oriented) = cell(&triangle, normal, &prepared, true);
        assert!(distance.hi <= 0.05);
        assert!(oriented.lo > 0.);
        let (_, unproved) = cell(&triangle, normal, &prepared, false);
        assert!(unproved.lo <= 0.);
        // A proved apex elsewhere cannot authorize a different source point on the axis.
        let axial = [point(Vec3::new(0., 0., 1.)), point(b), point(c)];
        let (_, not_apex) = cell(&axial, normal, &prepared, true);
        assert!(not_apex.lo <= 0.);
    }

    #[test]
    fn retained_definition_is_not_hidden_by_an_analytic_label_and_zero_net_bound() {
        use crate::surface::plane::Plane;
        use crate::surface::procedural_blend::corner::{CornerDefinition, EndDefinition};
        let mut k = Kernel::default();
        let (source, selected) = cylinder_selection(false, false);
        let mut body = super::super::build_tool::build_tool(&mut k, &selected.geometry).unwrap();
        for face in brep::faces(&body, None).unwrap() {
            let surface = body.face_mut(face).unwrap().surface.as_mut().unwrap();
            if matches!(
                AnalyticSupport::of(surface),
                Some(AnalyticSupport::Cylinder { .. })
            ) {
                surface.set_corner_definition(CornerDefinition::End(EndDefinition {
                    support: Box::new(Surface::from(Plane::from_normal(Vec3::ZERO, Vec3::Z))),
                    boundary: Vec::new(),
                }));
                assert!(matches!(
                    AnalyticSupport::of(surface),
                    Some(AnalyticSupport::Cylinder { .. })
                ));
                assert_eq!(definition_bound(surface), 0.0);
                assert!(surface.has_kept_definition());
            }
        }
        assert!(certify_fitted_tool_with_work(
            &k,
            &MeshWork::new(),
            &source,
            &selected,
            &mut body,
            0.05
        )
        .is_err());
    }

    #[test]
    fn sphere_support_is_not_the_affine_ellipsoid_of_independently_scaled_stored_axes() {
        let mut k = Kernel::default();
        let angle = 0.005_f64;
        let source = MeshInput {
            positions: vec![
                [2., 0., 0.],
                [2. * angle.cos(), angle.sin(), 0.],
                [2. * angle.cos(), 0., 2. * angle.sin()],
            ],
            triangles: vec![[0, 1, 2]],
        };
        let selected = FittedTool {
            surface: Primitive::Sphere {
                center: Vec3::ZERO,
                radius: 1.,
            },
            geometry: ToolGeometry::Sphere {
                center: Vec3::ZERO,
                radius: 1.,
            },
            source_triangles: vec![0],
            concave: false,
        };
        let mut body = super::super::build_tool::build_tool(&mut k, &selected.geometry).unwrap();
        let mut changed = 0;
        for id in brep::faces(&body, None).unwrap() {
            let s = body.face_mut(id).unwrap().surface.as_mut().unwrap();
            if let NativeKind::Sphere(sphere) = s.kind_mut() {
                let p = sphere.base.position;
                sphere.base.position =
                    Axis2Placement::from_stored(p.origin(), p.x_axis() * 2., p.y_axis());
                changed += 1;
                // Its definition is still the same radius-one implicit sphere,
                // and its retained evaluated net has not become an ellipsoid.
                assert!(AnalyticSupport::check(&k, s).is_ok());
                let NativeKind::Sphere(sphere) = s.kind() else {
                    panic!()
                };
                let uv = sphere.base().base().natural_uv_domain();
                let value = s
                    .evaluate_point(
                        &k,
                        crate::math::Point2::new(
                            0.5 * (uv.u_min() + uv.u_max()),
                            0.5 * (uv.v_min() + uv.v_max()),
                        ),
                    )
                    .unwrap();
                assert!((value.length() - 1.).abs() < 1e-12);
            }
        }
        assert_eq!(changed, 1);
        let result = certify_fitted_tool_with_work(
            &k,
            &MeshWork::new(),
            &source,
            &selected,
            &mut body,
            0.05,
        );
        let detail = match &result {
            Ok(p) => format!("false support bound {}", p.upper_bound()),
            Err(e) => format!("{e:?}"),
        };
        assert!(
            result.is_err(),
            "source is near x=2 but actual spherical support has radius1: {detail}"
        );
    }
    #[test]
    fn torus_support_is_not_the_affine_image_of_axis_rescalings_that_keep_the_same_axis() {
        let mut k = Kernel::default();
        let angle = 0.005_f64;
        let source = MeshInput {
            positions: vec![
                [8., 0., 0.],
                [8. * angle.cos(), 2. * angle.sin(), 0.],
                [2. * (3. + angle.cos()), 0., angle.sin()],
            ],
            triangles: vec![[0, 1, 2]],
        };
        let selected = FittedTool {
            surface: Primitive::Torus {
                center: Vec3::ZERO,
                axis: Vec3::Z,
                major: 3.,
                minor: 1.,
            },
            geometry: ToolGeometry::Torus {
                frame: crate::eval::Frame {
                    origin: [0.; 3],
                    x_axis: [1., 0., 0.],
                    y_axis: [0., 1., 0.],
                },
                major: 3.,
                minor: 1.,
            },
            source_triangles: vec![0],
            concave: false,
        };
        let mut body = super::super::build_tool::build_tool(&mut k, &selected.geometry).unwrap();
        let mut changed = 0;
        for id in brep::faces(&body, None).unwrap() {
            let s = body.face_mut(id).unwrap().surface.as_mut().unwrap();
            if let NativeKind::Torus(torus) = s.kind_mut() {
                let p = torus.base.position;
                torus.base.position =
                    Axis2Placement::from_stored(p.origin(), p.x_axis() * 2., p.y_axis() * 0.5);
                changed += 1;
                assert_eq!(torus.base.position.z_axis(), p.z_axis());
                assert!(AnalyticSupport::check(&k, s).is_ok());
            }
        }
        assert_eq!(changed, 1);
        let result = certify_fitted_tool_with_work(
            &k,
            &MeshWork::new(),
            &source,
            &selected,
            &mut body,
            0.05,
        );
        let detail = match &result {
            Ok(p) => format!("false support bound {}", p.upper_bound()),
            Err(e) => format!("{e:?}"),
        };
        assert!(
            result.is_err(),
            "source near x=8 is far outside radius4 toroidal support: {detail}"
        );
    }
    #[test]
    fn a_cylinder_label_cannot_authorize_a_contradictory_native_radius_law() {
        let mut k = Kernel::default();
        let (source, selected) = cylinder_selection(false, false);
        let mut body = super::super::build_tool::build_tool(&mut k, &selected.geometry).unwrap();
        let mut changed = 0;
        for id in brep::faces(&body, None).unwrap() {
            let s = body.face_mut(id).unwrap().surface.as_mut().unwrap();
            if let NativeKind::Cone(c) = s.kind_mut() {
                assert!(c.is_cylinder_class());
                c.semi_angle_deg = 10.;
                changed += 1;
                assert!(AnalyticSupport::check(&k, s).is_ok());
            }
        }
        assert_eq!(changed, 1);
        let result = certify_fitted_tool_with_work(
            &k,
            &MeshWork::new(),
            &source,
            &selected,
            &mut body,
            0.05,
        );
        let detail = match &result {
            Ok(p) => format!("contradictory definition bound {}", p.upper_bound()),
            Err(e) => format!("{e:?}"),
        };
        assert!(
            result.is_err(),
            "actual Cylinder class and Cone evaluator radius law disagree: {detail}"
        );
    }

    #[test]
    fn sphere_set_support_does_not_depend_on_irrelevant_stored_axis_scales() {
        let mut k = Kernel::default();
        let a = 0.005_f64;
        let source = MeshInput {
            positions: vec![[1., 0., 0.], [a.cos(), a.sin(), 0.], [a.cos(), 0., a.sin()]],
            triangles: vec![[0, 1, 2]],
        };
        let selected = FittedTool {
            surface: Primitive::Sphere {
                center: Vec3::ZERO,
                radius: 1.,
            },
            geometry: ToolGeometry::Sphere {
                center: Vec3::ZERO,
                radius: 1.,
            },
            source_triangles: vec![0],
            concave: false,
        };
        let mut body = super::super::build_tool::build_tool(&mut k, &selected.geometry).unwrap();
        for id in brep::faces(&body, None).unwrap() {
            let s = body.face_mut(id).unwrap().surface.as_mut().unwrap();
            if let NativeKind::Sphere(sphere) = s.kind_mut() {
                let p = sphere.base.position;
                sphere.base.position =
                    Axis2Placement::from_stored(p.origin(), p.x_axis() * 2., p.y_axis());
            }
        }
        let proof = certify_fitted_tool_with_work(
            &k,
            &MeshWork::new(),
            &source,
            &selected,
            &mut body,
            0.05,
        )
        .unwrap();
        assert!(proof.upper_bound() > 0. && proof.upper_bound() < 0.05);
    }

    #[test]
    fn torus_set_support_keeps_the_same_literal_axis_under_transverse_rescaling() {
        let mut k = Kernel::default();
        let a = 0.005_f64;
        let source = MeshInput {
            positions: vec![
                [4., 0., 0.],
                [4. * a.cos(), 4. * a.sin(), 0.],
                [3. + a.cos(), 0., a.sin()],
            ],
            triangles: vec![[0, 1, 2]],
        };
        let selected = FittedTool {
            surface: Primitive::Torus {
                center: Vec3::ZERO,
                axis: Vec3::Z,
                major: 3.,
                minor: 1.,
            },
            geometry: ToolGeometry::Torus {
                frame: crate::eval::Frame {
                    origin: [0.; 3],
                    x_axis: [1., 0., 0.],
                    y_axis: [0., 1., 0.],
                },
                major: 3.,
                minor: 1.,
            },
            source_triangles: vec![0],
            concave: false,
        };
        let mut body = super::super::build_tool::build_tool(&mut k, &selected.geometry).unwrap();
        for id in brep::faces(&body, None).unwrap() {
            let s = body.face_mut(id).unwrap().surface.as_mut().unwrap();
            if let NativeKind::Torus(torus) = s.kind_mut() {
                let p = torus.base.position;
                torus.base.position =
                    Axis2Placement::from_stored(p.origin(), p.x_axis() * 2., p.y_axis() * 0.5);
            }
        }
        let proof = certify_fitted_tool_with_work(
            &k,
            &MeshWork::new(),
            &source,
            &selected,
            &mut body,
            0.05,
        )
        .unwrap();
        assert!(proof.upper_bound() > 0. && proof.upper_bound() < 0.05);
    }
    #[test]
    fn literal_torus_axis_defect_bounds_set_distance_and_normal_without_an_exact_unit_restriction()
    {
        for lambda in [0.99, 1., 1.01] {
            let [distance, normal] = torus_set_defect(3., 1., Ivl::from(lambda)).unwrap();
            assert!(distance.is_finite() && distance >= 0.);
            assert!(normal.is_finite() && (0.0..1.0).contains(&normal));
            // phi=pi/2 gives the exact height and gradient changes below.
            // The global proof above covers ALL phi; these are validation only.
            assert!(distance >= (1. / lambda - 1.).abs());
            assert!(normal >= (lambda - 1.).abs());
            let h = Ivl::from(1.) / Ivl::from(lambda);
            let rho2 = Ivl::from(10.) - square(h);
            let f = square(rho2 + square(h) + Ivl::from(8.))
                - Ivl::from(36.) * (rho2 + (Ivl::from(1.) - square(Ivl::from(lambda))) * square(h));
            assert!(f.lo <= 0. && f.hi >= 0.);
        }
        for lambda in [
            Ivl::from(0.),
            Ivl::from(0.1),
            Ivl::from(f64::INFINITY),
            Ivl::whole(),
        ] {
            assert!(torus_set_defect(3., 1., lambda).is_err());
        }
        assert!(torus_set_defect(1., 1., Ivl::from(1.)).is_err());
    }
    fn radial_set_selection(cone: bool) -> (MeshInput, FittedTool) {
        if !cone {
            return cylinder_selection(false, false);
        }
        let angle = 0.005_f64;
        let input = MeshInput {
            positions: vec![
                [10., 0., 10.],
                [9.95, 0., 9.95],
                [10. * angle.cos(), 10. * angle.sin(), 10.],
            ],
            triangles: vec![[0, 1, 2]],
        };
        let selected = FittedTool {
            surface: Primitive::Cone {
                apex: Vec3::ZERO,
                axis: Vec3::Z,
                half_angle: std::f64::consts::FRAC_PI_4,
            },
            geometry: ToolGeometry::Cone {
                origin: Vec3::ZERO,
                axis: Vec3::Z,
                radius: 10.,
                length: 10.,
            },
            source_triangles: vec![0],
            concave: false,
        };
        (input, selected)
    }
    fn rescale_radial_frame_keep_same_set(k: &Kernel, body: &mut Brep) {
        let mut changed = 0;
        for id in brep::faces(body, None).unwrap() {
            let s = body.face_mut(id).unwrap().surface.as_mut().unwrap();
            if let NativeKind::Cone(c) = s.kind_mut() {
                let p = c.rev.position;
                c.rev.position =
                    Axis2Placement::from_stored(p.origin(), p.x_axis() * 2., p.y_axis() * 0.5);
                assert_eq!(
                    c.rev.position.x_axis().cross(c.rev.position.y_axis()),
                    p.x_axis().cross(p.y_axis())
                );
                changed += 1;
                assert!(
                    AnalyticSupport::check(k, s).is_ok(),
                    "same actual net and literal analytic SET"
                );
            }
        }
        assert_eq!(changed, 1);
    }
    #[test]
    fn radial_support_is_not_an_affine_image_when_transverse_scales_keep_the_same_axis() {
        for cone in [false, true] {
            let mut k = Kernel::default();
            let (mut source, selected) = radial_set_selection(cone);
            for p in &mut source.positions {
                p[0] *= 2.;
                p[1] *= 0.5;
            }
            let mut body =
                super::super::build_tool::build_tool(&mut k, &selected.geometry).unwrap();
            rescale_radial_frame_keep_same_set(&k, &mut body);
            // Closed-form Euclidean distance to the SAME radius10 cylinder or
            // rho=h cone is far above0.05; no cached-parameter distance oracle.
            assert!(source.positions.iter().all(|p| {
                let rho = p[0].hypot(p[1]);
                let distance = if cone {
                    (rho - p[2]).abs() / 2f64.sqrt()
                } else {
                    (rho - 10.).abs()
                };
                distance > 6.
            }));
            let result = certify_fitted_tool_with_work(
                &k,
                &MeshWork::new(),
                &source,
                &selected,
                &mut body,
                0.05,
            );
            let detail = match &result {
                Ok(p) => format!("false upper {}", p.upper_bound()),
                Err(e) => format!("{e:?}"),
            };
            assert!(
                result.is_err(),
                "transverse metadata cannot stretch the same radial set: cone={cone}, {detail}"
            );
        }
    }
    #[test]
    fn radial_set_support_survives_transverse_metadata_scaling_without_geometry_motion() {
        for cone in [false, true] {
            let mut k = Kernel::default();
            let (source, selected) = radial_set_selection(cone);
            let mut body =
                super::super::build_tool::build_tool(&mut k, &selected.geometry).unwrap();
            rescale_radial_frame_keep_same_set(&k, &mut body);
            let proof = certify_fitted_tool_with_work(
                &k,
                &MeshWork::new(),
                &source,
                &selected,
                &mut body,
                0.05,
            )
            .unwrap();
            assert!(proof.upper_bound() <= 0.05);
        }
    }
    #[test]
    fn literal_radial_witness_and_global_lower_follow_the_same_quadratic_definition() {
        let p = [Ivl::from(20.), Ivl::from(0.), Ivl::from(3.)];
        let (distance, oriented) = literal_radial_cell(
            &[p; 3],
            point(Vec3::X),
            10.,
            Ivl::from(0.),
            Ivl::from(0.),
            Ivl::from(0.),
            Ivl::from(100.),
        );
        assert!(
            distance.lo > 6.
                && distance.lo <= 10.
                && distance.hi >= 10.
                && distance.hi < 10.000000001
        );
        assert!(oriented.lo > 0.);
        assert_eq!(
            quadratic_distance_lower(Ivl::new(-1., 1.), point(Vec3::X), Ivl::from(0.)),
            0.
        );
        assert_eq!(
            quadratic_distance_lower(Ivl::whole(), point(Vec3::X), Ivl::from(0.)),
            0.
        );
        for lambda in [0.99, 1., 1.01] {
            let LocalSupport::Radial { tangent, radius } =
                literal_radial_shape(0., Ivl::from(1.), Ivl::from(lambda)).unwrap()
            else {
                panic!("canonical apex needs its homogeneous branch")
            };
            let expected = (2. * lambda * lambda - 1.).sqrt();
            assert!(tangent.lo <= expected && tangent.hi >= expected);
            assert_eq!(radius, 0.);
        }
        assert!(literal_radial_shape(0., Ivl::from(0.), Ivl::from(1.)).is_err());
        assert!(literal_radial_shape(0., Ivl::from(1.), Ivl::from(0.5)).is_err());
    }

    fn rectangular_stock_selection() -> (MeshInput, FittedTool) {
        let source = MeshInput {
            positions: vec![[2., 2., 0.], [18., 2., 0.], [18., 8., 0.], [2., 8., 0.]],
            triangles: vec![[0, 1, 2], [0, 2, 3]],
        };
        let prism = super::super::PrismTool {
            frame: crate::eval::Frame {
                origin: [0.; 3],
                x_axis: [1., 0., 0.],
                y_axis: [0., 1., 0.],
            },
            regions: vec![crate::prism::profile::Region2 {
                outer: super::super::profile::polygon(&[
                    crate::math::Vec2::new(0., 0.),
                    crate::math::Vec2::new(20., 0.),
                    crate::math::Vec2::new(20., 10.),
                    crate::math::Vec2::new(0., 10.),
                ]),
                holes: Vec::new(),
            }],
            start: -3.,
            end: 0.,
        };
        let tool = FittedTool {
            surface: Primitive::Plane {
                point: Vec3::ZERO,
                normal: Vec3::Z,
            },
            geometry: ToolGeometry::Prism(prism),
            source_triangles: vec![0, 1],
            concave: false,
        };
        (source, tool)
    }
    #[test]
    fn requested_finite_rectangle_stock_consumes_whole_recipe_and_original_region() {
        let mut k = Kernel::default();
        let work = MeshWork::new();
        let (source, tool) = rectangular_stock_selection();
        let before = source.positions.clone();
        let triangles = source.triangles.clone();
        let mut body = super::super::build_tool(&mut k, &tool.geometry).unwrap();
        let body_id = core::ptr::from_ref(&body);
        let tool_id = core::ptr::from_ref(&tool);
        let proof = super::super::certify_finite_fitted_tool_with_work(
            &mut k, &work, &source, &tool, &mut body, 0.05,
        )
        .unwrap();
        let (raw, selected, actual) = proof.source();
        assert!(core::ptr::eq(raw, &source));
        assert!(core::ptr::eq(selected, tool_id));
        assert!(core::ptr::eq(actual, body_id));
        assert!(proof.selected_finite_upper().is_finite() && proof.selected_finite_upper() <= 0.05);
        assert!(proof.recipe_boundary_upper().is_finite() && proof.recipe_boundary_upper() < 1e-8);
        assert_eq!(raw.positions, before);
        assert_eq!(raw.triangles, triangles);
        work.check(&k).unwrap();
    }
    #[test]
    fn same_untrimmed_plane_with_wrong_finite_stock_extent_cannot_be_accepted() {
        let mut k = Kernel::default();
        let work = MeshWork::new();
        let (source, tool) = rectangular_stock_selection();
        let mut wrong = tool.geometry.clone();
        let ToolGeometry::Prism(prism) = &mut wrong else {
            panic!("stock")
        };
        prism.start = -0.1; // SAME upper analytic plane, genuinely wrong requested depth.
        let mut body = super::super::build_tool(&mut k, &wrong).unwrap();
        {
            let limited =
                certify_fitted_tool_with_work(&k, &work, &source, &tool, &mut body, 0.05).unwrap();
            assert!(limited.upper_bound() <= 0.05); // Limited support contract is still valid.
        }
        assert!(super::super::certify_finite_fitted_tool_with_work(
            &mut k, &work, &source, &tool, &mut body, 0.05,
        )
        .is_err());
        work.check(&k).unwrap();
    }
    #[test]
    fn exact_requested_stock_does_not_make_outside_source_triangles_finitely_covered() {
        let mut k = Kernel::default();
        let work = MeshWork::new();
        let (mut source, tool) = rectangular_stock_selection();
        for p in &mut source.positions {
            p[0] += 100.;
        }
        let mut body = super::super::build_tool(&mut k, &tool.geometry).unwrap();
        {
            let limited =
                certify_fitted_tool_with_work(&k, &work, &source, &tool, &mut body, 0.05).unwrap();
            assert!(limited.upper_bound() <= 0.05); // Same infinite plane, outside finite recipe.
        }
        assert!(super::super::certify_finite_fitted_tool_with_work(
            &mut k, &work, &source, &tool, &mut body, 0.05,
        )
        .is_err());
        work.check(&k).unwrap();
    }
    #[test]
    fn finite_stock_preserves_complete_domain_rejection_and_native_cancel_precedence() {
        let mut k = Kernel::default();
        let work = MeshWork::new();
        let (source, mut tool) = rectangular_stock_selection();
        let mut body = super::super::build_tool(&mut k, &tool.geometry).unwrap();
        let ToolGeometry::Prism(prism) = &mut tool.geometry else {
            panic!("stock")
        };
        prism.regions[0]
            .holes
            .push(super::super::profile::polygon(&[
                crate::math::Vec2::new(3., 3.),
                crate::math::Vec2::new(3., 4.),
                crate::math::Vec2::new(4., 4.),
                crate::math::Vec2::new(4., 3.),
            ]));
        assert!(super::super::certify_finite_fitted_tool_with_work(
            &mut k, &work, &source, &tool, &mut body, 0.05,
        )
        .is_err()); // Unsupported full recipe, never silently discard a hole.
        let scarce = MeshWork::new();
        assert!(!scarce.try_reserve_cells(2_000_001));
        let token = crate::kernel::CancelToken::new();
        k.set_cancel_token(token.clone());
        token.cancel();
        assert!(matches!(super::super::certify_finite_fitted_tool_with_work(
            &mut k,&scarce,&source,&tool,&mut body,0.05,
        ),Err(MeshError::Kernel(error)) if error.is_cancelled()));
    }

    #[test]
    fn finite_stock_signed_frames_and_offset_levels_bind_the_actual_upper_cap() {
        let frames = [
            (Vec3::Y, Vec3::Z),
            (-Vec3::Y, Vec3::Z),
            (Vec3::Z, Vec3::X),
            (-Vec3::Z, Vec3::X),
            (Vec3::X, Vec3::Y),
            (-Vec3::X, Vec3::Y),
        ];
        for (a, b) in frames {
            let mut k = Kernel::default();
            let work = MeshWork::new();
            let (mut source, mut tool) = rectangular_stock_selection();
            let ToolGeometry::Prism(prism) = &mut tool.geometry else {
                panic!("rectangle")
            };
            prism.frame = crate::eval::Frame {
                origin: [11., -7., 3.],
                x_axis: a.to_array(),
                y_axis: b.to_array(),
            };
            prism.start = -1.;
            prism.end = 2.;
            let frame = prism.frame.clone();
            let (_, _, _, normal) = crate::prism::profile::axes(&frame);
            let top = crate::prism::profile::to_world(&frame, crate::math::Vec2::ZERO, 2.);
            tool.surface = Primitive::Plane { point: top, normal };
            for p in &mut source.positions {
                *p =
                    crate::prism::profile::to_world(&frame, crate::math::Vec2::new(p[0], p[1]), 2.)
                        .to_array();
            }
            let raw_positions = source.positions.clone();
            let raw_triangles = source.triangles.clone();
            let mut actual = super::super::build_tool(&mut k, &tool.geometry).unwrap();
            {
                let proof = super::super::certify_finite_fitted_tool_with_work(
                    &mut k,
                    &work,
                    &source,
                    &tool,
                    &mut actual,
                    0.05,
                )
                .unwrap();
                assert!(
                    proof.selected_finite_upper() <= 0.05 && proof.recipe_boundary_upper() <= 0.05
                );
                assert!(core::ptr::eq(proof.source().0, &source));
                assert!(core::ptr::eq(proof.source().1, &tool));
            }
            let mut wrong = tool.geometry.clone();
            let ToolGeometry::Prism(prism) = &mut wrong else {
                panic!("rectangle")
            };
            prism.start = 1.5; // The same actual upper plane, but a different finite depth.
            let mut wrong = super::super::build_tool(&mut k, &wrong).unwrap();
            {
                let support =
                    certify_fitted_tool_with_work(&k, &work, &source, &tool, &mut wrong, 0.05)
                        .unwrap();
                assert!(support.upper_bound() <= 0.05);
            }
            assert!(super::super::certify_finite_fitted_tool_with_work(
                &mut k, &work, &source, &tool, &mut wrong, 0.05
            )
            .is_err());
            work.check(&k).unwrap();
            assert_eq!(source.positions, raw_positions);
            assert_eq!(source.triangles, raw_triangles);
        }
    }
}
