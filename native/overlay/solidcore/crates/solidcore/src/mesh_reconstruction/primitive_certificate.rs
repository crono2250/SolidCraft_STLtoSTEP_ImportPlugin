//! Complete one-way source-region support and material orientation bounds.
//!
//! This proves a finite source patch lies near an untrimmed primitive. It does not prove a
//! whole body, a trimmed-face correspondence, or the reverse distance from an infinite
//! surface. Every admitted cell is a complete barycentric triangle. Subdivision covers its
//! parent exactly; residuals at a few selected points never constitute acceptance.
//!
//! Plane residuals are affine. Squared sphere/cylinder radial norms have degree-two
//! triangular Bernstein coefficients `v_i dot v_j`, whose convex hull encloses the whole
//! triangle. Torus distance is enclosed through its exact radial/axial expression. A cone
//! uses an affine correspondence to one fixed generator, with a bounded correction for
//! the one-sided apex. These bounds are sharpened only by complete-triangle subdivision.
//!
//! Axes are the exact real normalization A/sqrt(A dot A) of the supplied finite vector,
//! enclosed outward. No stored floating vector is assumed to have exact unit length.
//! Transcendental cone coefficients use alternating Taylor series with a rigorous next-term
//! remainder; std trig is used solely to choose the candidate generator/height.
//!
//! A cone apex belongs to the distance-set closure only. A constant generator normal is
//! never accepted as an orientation/local-degree proof. Apex-containing selections require
//! independently verified circular source incidence and a certified angular degree of one.
//! Regular cells use the actual radial normal field or a positive radial-cone sign proof.
//!
//! References: Farin, Curves and Surfaces for CAGD, 5th ed., chapter 10 (triangular Bernstein
//! convex hull); Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., chapter 3
//! (outward arithmetic); Apostol, Calculus vol.1, alternating-series remainder theorem.
use super::numeric::Vec3Numeric;
use super::types::{invalid, MeshError, MeshInput, Primitive, Result};
use crate::blend::fillet_section::interval::Ivl;
use crate::math::Vec3;
use crate::Kernel;

pub(crate) type PointBox = [Ivl; 3];
pub(crate) type Triangle = [PointBox; 3];
const MAX_CELLS: usize = 2_000_000;
const MAX_DEPTH: u8 = 20;
const MAX_REGION_TRIANGLES: usize = 200_000;
const OP: &str = "mesh_reconstruction::primitive_certificate";

/// A complete directed support/orientation proof bound to the exact borrowed source and
/// primitive. Fields are private so a caller cannot replace a sampled statistic with a token.
#[derive(Debug)]
pub struct PrimitiveFitCertificate<'a> {
    input: &'a MeshInput,
    /// Fitted analytic support; not a final-body acceptance proof.
    surface: &'a Primitive,
    triangles: &'a [u32],
    /// Whether source material lies on the support axis side.
    concave: bool,
    /// Requested model-space bound.
    tolerance: f64,
    upper: f64,
    cells: usize,
}
impl PrimitiveFitCertificate<'_> {
    /// A rigorous upper bound for the whole finite source patch's directed support distance.
    pub fn upper_bound(&self) -> f64 {
        self.upper
    }
    /// Complete barycentric cells processed, including subdivided parents.
    pub fn cells(&self) -> usize {
        self.cells
    }
    /// The certificate applies only to these unchanged source arrays and primitive data.
    pub fn source(&self) -> (&MeshInput, &Primitive, &[u32], bool, f64) {
        (
            self.input,
            self.surface,
            self.triangles,
            self.concave,
            self.tolerance,
        )
    }
}

fn point(v: Vec3) -> PointBox {
    [Ivl::from(v.x), Ivl::from(v.y), Ivl::from(v.z)]
}
fn add(a: PointBox, b: PointBox) -> PointBox {
    let [ax, ay, az] = a;
    let [bx, by, bz] = b;
    [ax.add_ulp(bx), ay.add_ulp(by), az.add_ulp(bz)]
}
pub(crate) fn sub(a: PointBox, b: PointBox) -> PointBox {
    let [ax, ay, az] = a;
    let [bx, by, bz] = b;
    [ax.sub_ulp(bx), ay.sub_ulp(by), az.sub_ulp(bz)]
}
pub(crate) fn scale(a: PointBox, b: Ivl) -> PointBox {
    a.map(|x| x.mul_ulp(b))
}
pub(crate) fn dot(a: PointBox, b: PointBox) -> Ivl {
    let [ax, ay, az] = a;
    let [bx, by, bz] = b;
    ax.mul_ulp(bx)
        .add_ulp(ay.mul_ulp(by))
        .add_ulp(az.mul_ulp(bz))
}
pub(crate) fn cross(a: PointBox, b: PointBox) -> PointBox {
    let [ax, ay, az] = a;
    let [bx, by, bz] = b;
    [
        ay.mul_ulp(bz).sub_ulp(az.mul_ulp(by)),
        az.mul_ulp(bx).sub_ulp(ax.mul_ulp(bz)),
        ax.mul_ulp(by).sub_ulp(ay.mul_ulp(bx)),
    ]
}
fn square(x: Ivl) -> Ivl {
    if x.lo >= 0. {
        x.mul_ulp(x)
    } else if x.hi <= 0. {
        let n = Ivl::new(-x.hi, -x.lo);
        n.mul_ulp(n)
    } else {
        let m = x.mag();
        Ivl::new(0., Ivl::from(m).mul_ulp(Ivl::from(m)).hi)
    }
}
pub(crate) fn norm(x: PointBox) -> Ivl {
    let [a, b, c] = x;
    square(a).add_ulp(square(b)).add_ulp(square(c)).sqrt()
}
pub(crate) fn normalized(v: PointBox) -> Option<PointBox> {
    let length = norm(v);
    if !length.is_finite() || length.lo <= 0. {
        return None;
    }
    Some(v.map(|x| x.div_ulp(length)))
}
fn hull_points(points: &Triangle) -> PointBox {
    let [a, b, c] = *points;
    [
        a[0].hull(b[0]).hull(c[0]),
        a[1].hull(b[1]).hull(c[1]),
        a[2].hull(b[2]).hull(c[2]),
    ]
}
fn hull_scalar(values: [Ivl; 3]) -> Ivl {
    let [a, b, c] = values;
    a.hull(b).hull(c)
}
pub(crate) fn quarters(t: &Triangle) -> [Triangle; 4] {
    let [a, b, c] = *t;
    let middle = |x, y| scale(add(x, y), Ivl::from(0.5));
    let (ab, ac, bc) = (middle(a, b), middle(a, c), middle(b, c));
    [[a, ab, ac], [ab, b, bc], [ac, bc, c], [ab, bc, ac]]
}
fn centre(t: &Triangle) -> Vec3 {
    let box_ = hull_points(t);
    let [x, y, z] = box_;
    Vec3::new(x.mid(), y.mid(), z.mid())
}
pub(crate) fn norm2_range(v: &Triangle) -> Ivl {
    let [a, b, c] = *v;
    let coefficients = [
        dot(a, a),
        dot(b, b),
        dot(c, c),
        dot(a, b),
        dot(a, c),
        dot(b, c),
    ];
    let lo = coefficients
        .iter()
        .map(|c| c.lo)
        .fold(f64::INFINITY, f64::min)
        .max(0.);
    let hi = coefficients
        .iter()
        .map(|c| c.hi)
        .fold(f64::NEG_INFINITY, f64::max);
    Ivl::new(lo, hi)
}
fn radial(points: &Triangle, axis: PointBox) -> (Triangle, [Ivl; 3]) {
    let [a, b, c] = *points;
    let heights = [dot(a, axis), dot(b, axis), dot(c, axis)];
    let [ha, hb, hc] = heights;
    (
        [
            sub(a, scale(axis, ha)),
            sub(b, scale(axis, hb)),
            sub(c, scale(axis, hc)),
        ],
        heights,
    )
}
fn positive_normal(normal: PointBox, field: PointBox) -> bool {
    let d = dot(normal, field);
    d.is_finite() && d.lo > 0.
}
fn oriented_linear(normal: PointBox, field: &Triangle) -> bool {
    field.iter().all(|v| positive_normal(normal, *v))
}
fn magnitude(x: Ivl) -> f64 {
    if x.is_finite() {
        x.mag()
    } else {
        f64::INFINITY
    }
}

/// Sine/cosine of one finite exact double angle in [0,pi/2), with next-term remainder.
fn cone_trig(angle: f64) -> Option<(Ivl, Ivl)> {
    // This exact double lies below real pi/2, preserving the existing acute-cone contract.
    if !(angle.is_finite() && angle > 0.0 && angle < core::f64::consts::FRAC_PI_2) {
        return None;
    }
    let (sine, cosine) = super::interval_trig::sin_cos(Ivl::from(angle))?;
    (sine.lo > 0.0 && cosine.lo > 0.0).then_some((sine, cosine))
}

struct Prepared {
    anchor: Vec3,
    axis: Option<PointBox>,
    sine: Option<Ivl>,
    cosine: Option<Ivl>,
}
fn prepare(surface: &Primitive) -> Result<Prepared> {
    let finite = |v: Vec3| v.is_finite();
    let axis = |v: Vec3| {
        normalized(point(v)).ok_or_else(|| invalid("primitive has no finite nonzero axis"))
    };
    match *surface {
        Primitive::Plane { point: p, normal } if finite(p) && finite(normal) => Ok(Prepared {
            anchor: p,
            axis: Some(axis(normal)?),
            sine: None,
            cosine: None,
        }),
        Primitive::Cylinder {
            point: p,
            axis: a,
            radius,
        } if finite(p) && finite(a) && radius.is_finite() && radius > 0. => Ok(Prepared {
            anchor: p,
            axis: Some(axis(a)?),
            sine: None,
            cosine: None,
        }),
        Primitive::Cone {
            apex,
            axis: a,
            half_angle,
        } if finite(apex) && finite(a) => {
            let (sine, cosine) = cone_trig(half_angle)
                .ok_or_else(|| invalid("cone angle has no one-sided acute enclosure"))?;
            Ok(Prepared {
                anchor: apex,
                axis: Some(axis(a)?),
                sine: Some(sine),
                cosine: Some(cosine),
            })
        }
        Primitive::Sphere { center, radius }
            if finite(center) && radius.is_finite() && radius > 0. =>
        {
            Ok(Prepared {
                anchor: center,
                axis: None,
                sine: None,
                cosine: None,
            })
        }
        Primitive::Torus {
            center,
            axis: a,
            major,
            minor,
        } if finite(center)
            && finite(a)
            && major.is_finite()
            && minor.is_finite()
            && major > minor
            && minor > 0. =>
        {
            Ok(Prepared {
                anchor: center,
                axis: Some(axis(a)?),
                sine: None,
                cosine: None,
            })
        }
        _ => Err(invalid(
            "invalid primitive parameters for support certificate",
        )),
    }
}

/// Orientation over every regular source point, using its actual radial direction.
/// For a positive radial cone, N dot r(P)>0 is affine over the triangle and N dot axis<0;
/// therefore cos(angle) N dot r/rho - sin(angle) N dot axis is strictly positive throughout.
fn cone_orientation(t: &Triangle, normal: PointBox, prepared: &Prepared) -> bool {
    let Some(axis) = prepared.axis else {
        return false;
    };
    let Some(sine) = prepared.sine else {
        return false;
    };
    let Some(cosine) = prepared.cosine else {
        return false;
    };
    let (radials, heights) = radial(t, axis);
    if heights.iter().any(|h| h.lo < 0.) {
        return false;
    }
    let rho = norm2_range(&radials).sqrt();
    if rho.is_finite() && rho.lo > 0. {
        let unit = scale(hull_points(&radials), Ivl::from(1.).div_ulp(rho));
        if positive_normal(normal, sub(scale(unit, cosine), scale(axis, sine))) {
            return true;
        }
    }
    let axial = dot(normal, axis);
    if !axial.is_finite() || axial.hi >= 0. {
        return false;
    }
    let mut regular = false;
    for (p, radial) in t.iter().zip(radials) {
        if p.iter().all(|v| *v == Ivl::from(0.)) {
            continue;
        }
        if !positive_normal(normal, radial) {
            return false;
        }
        regular = true;
    }
    regular
}

/// The source fan's incidence was independently proved by `certificate::ordered_apex_link`.
/// Strict adjacent projected cross signs plus winding degree +/-1 prove one angular fan,
/// without a sum of approximate atan2 samples or a caller-supplied orientation flag.
fn certify_cone_link(
    k: &Kernel,
    budget: &super::MeshWork,
    prepared: &Prepared,
    link: &[[f64; 3]],
) -> Result<()> {
    if link.len() < 3 || link.len() > MAX_REGION_TRIANGLES {
        return Err(MeshError::Undecided {
            stage: "cone apex link size",
            work: link.len(),
        });
    }
    let axis = prepared
        .axis
        .ok_or_else(|| invalid("cone apex has no certified axis"))?;
    let anchor = point(prepared.anchor);
    budget.reserve_output(k, link.len())?;
    let mut relative = Vec::new();
    for p in link {
        budget.spend(k, 1)?;
        let w = sub(p.map(Ivl::from), anchor);
        let height = dot(w, axis);
        if !height.is_finite() || height.lo <= 0. {
            return Err(MeshError::Undecided {
                stage: "cone apex one-sided link height",
                work: relative.len(),
            });
        }
        relative.push(w);
    }
    super::angular_link::certify_angular_link(k, budget, &relative, axis)
}

fn cone_cell(t: &Triangle, normal: PointBox, prepared: &Prepared) -> Option<(f64, bool)> {
    let axis = prepared.axis?;
    let sine = prepared.sine?;
    let cosine = prepared.cosine?;
    let tangent = sine.div_ulp(cosine);
    let c = centre(t);
    let mut guesses = vec![c];
    guesses.extend(t.iter().map(|p| {
        let [x, y, z] = *p;
        Vec3::new(x.mid(), y.mid(), z.mid())
    }));
    guesses.extend([Vec3::X, Vec3::Y, Vec3::Z]);
    let mut best: Option<(f64, bool)> = None;
    for guess in guesses {
        let raw = point(guess);
        let projected = sub(raw, scale(axis, dot(raw, axis)));
        let Some(radial) = normalized(projected) else {
            continue;
        };
        let (mut upper, mut min_height) = (0f64, f64::INFINITY);
        for p in t {
            let h = dot(*p, axis);
            min_height = min_height.min(h.lo);
            let q = add(scale(axis, h), scale(radial, tangent.mul_ulp(h)));
            upper = upper.max(norm(sub(*p, q)).hi);
        }
        // h+ = max(h,0) makes the map one-sided. The affine residual on h is bounded
        // at corners. Its correction has norm max(0,-h)/cos(angle), bounded here.
        let negative = Ivl::from((-min_height).max(0.)).div_ulp(cosine);
        upper = Ivl::from(upper).add_ulp(negative).hi;
        if upper.is_finite() && best.is_none_or(|(old, _)| upper < old) {
            best = Some((upper, cone_orientation(t, normal, prepared)));
        }
    }
    best
}

fn cell(t: &Triangle, normal: PointBox, surface: &Primitive, prepared: &Prepared) -> (f64, bool) {
    match *surface {
        Primitive::Plane { .. } => {
            let Some(axis) = prepared.axis else {
                return (f64::INFINITY, false);
            };
            let upper = t
                .iter()
                .map(|p| magnitude(dot(*p, axis)))
                .fold(0., f64::max);
            (upper, positive_normal(normal, axis))
        }
        Primitive::Sphere { radius, .. } => {
            let distances = norm2_range(t).sqrt().sub_ulp(Ivl::from(radius));
            (magnitude(distances), oriented_linear(normal, t))
        }
        Primitive::Cylinder { radius, .. } => {
            let Some(axis) = prepared.axis else {
                return (f64::INFINITY, false);
            };
            let (r, _) = radial(t, axis);
            let distances = norm2_range(&r).sqrt().sub_ulp(Ivl::from(radius));
            (magnitude(distances), oriented_linear(normal, &r))
        }
        Primitive::Cone { .. } => cone_cell(t, normal, prepared).unwrap_or((f64::INFINITY, false)),
        Primitive::Torus { major, minor, .. } => {
            let Some(axis) = prepared.axis else {
                return (f64::INFINITY, false);
            };
            let (r, h) = radial(t, axis);
            let rho = norm2_range(&r).sqrt();
            let height = hull_scalar(h);
            let centreline = square(rho.sub_ulp(Ivl::from(major)))
                .add_ulp(square(height))
                .sqrt();
            let upper = magnitude(centreline.sub_ulp(Ivl::from(minor)));
            if !rho.is_finite() || rho.lo <= 0. {
                return (upper, false);
            }
            let factor = Ivl::from(1.).sub_ulp(Ivl::from(major).div_ulp(rho));
            let field = add(scale(hull_points(&r), factor), scale(axis, height));
            (upper, positive_normal(normal, field))
        }
    }
}

/// Certify every complete original triangle of a finite selected region against its
/// untrimmed primitive and supplied material-side orientation. Closed-body acceptance and
/// reverse infinite-surface coverage are deliberately outside this API.
///
/// Refuses malformed/duplicate ids and invalid primitive data. Work/depth exhaustion returns
/// typed Undecided, never a sampled success. Native cancellation remains its original error.
/// Standalone single-job convenience; multi-stage callers share one `MeshWork`.
pub fn certify_primitive_region<'a>(
    k: &Kernel,
    input: &'a MeshInput,
    surface: &'a Primitive,
    triangles: &'a [u32],
    concave: bool,
    tolerance: f64,
) -> Result<PrimitiveFitCertificate<'a>> {
    let work_budget = super::work::MeshWork::new();
    certify_primitive_region_with_work(
        k,
        &work_budget,
        input,
        surface,
        triangles,
        concave,
        tolerance,
    )
}

/// Bound support distance and material-side orientation over each complete original triangle.
/// Uses the caller's shared budget and proves the proposed primitive, not a built B-rep.
pub fn certify_primitive_region_with_work<'a>(
    k: &Kernel,
    work_budget: &super::work::MeshWork,
    input: &'a MeshInput,
    surface: &'a Primitive,
    triangles: &'a [u32],
    concave: bool,
    tolerance: f64,
) -> Result<PrimitiveFitCertificate<'a>> {
    work_budget.check(k)?;
    let answer = (|| {
        super::regions::checked_tolerance(tolerance)?;
        if triangles.is_empty() || triangles.len() > MAX_REGION_TRIANGLES {
            return Err(MeshError::BudgetExceeded {
                stage: OP,
                limit: MAX_REGION_TRIANGLES,
            });
        }
        if input.positions.len() > super::source::MAX_POSITIONS
            || input.triangles.len() > MAX_REGION_TRIANGLES
        {
            return Err(MeshError::BudgetExceeded {
                stage: OP,
                limit: MAX_REGION_TRIANGLES,
            });
        }
        let prepared = prepare(surface)?;
        let anchor = point(prepared.anchor);
        let mut seen = std::collections::BTreeSet::new();
        if matches!(surface, Primitive::Cone { .. }) {
            if let Some(link) = super::certificate::ordered_apex_link_with_work(
                k,
                work_budget,
                input,
                triangles,
                prepared.anchor.to_array(),
            )? {
                certify_cone_link(k, work_budget, &prepared, &link)?;
            }
        }

        let (mut cells, mut upper) = (0usize, 0f64);
        let work = super::work::Work::with_budget(k, work_budget)?;
        for id in triangles {
            if !seen.insert(*id) {
                return Err(invalid("duplicate source triangle in selected region"));
            }
            let indices = input
                .triangles
                .get(*id as usize)
                .copied()
                .ok_or_else(|| invalid("missing original source triangle"))?;
            let corner = |id: u32| -> Result<PointBox> {
                let p = input
                    .positions
                    .get(id as usize)
                    .copied()
                    .ok_or_else(|| invalid("missing original source vertex"))?;
                if p.iter().any(|v| !v.is_finite() || v.abs() > 1e9) {
                    return Err(invalid(
                        "selected source vertex is non-finite or exceeds coordinate budget",
                    ));
                }
                Ok(sub(p.map(Ivl::from), anchor))
            };
            let [a, b, c] = indices;
            let root = [corner(a)?, corner(b)?, corner(c)?];
            let [pa, pb, pc] = root;
            let mut normal = cross(sub(pb, pa), sub(pc, pa));
            if concave {
                normal = scale(normal, Ivl::from(-1.));
            }
            if !normal.iter().all(|v| v.is_finite()) || norm(normal).lo <= 0. {
                return Err(invalid("source triangle has no certified orientation"));
            }
            let mut pending = vec![(root, 0u8)];
            while let Some((triangle, depth)) = pending.pop() {
                work_budget.reserve_cells(k, 1)?;
                work.spend(1)?;
                cells = cells.saturating_add(1);
                if cells > MAX_CELLS {
                    return Err(MeshError::Undecided {
                        stage: OP,
                        work: cells,
                    });
                }
                let (distance, oriented) = cell(&triangle, normal, surface, &prepared);
                if distance.is_finite() && distance <= tolerance && oriented {
                    upper = upper.max(distance);
                    continue;
                }
                if depth >= MAX_DEPTH {
                    return Err(MeshError::Undecided {
                        stage: OP,
                        work: cells,
                    });
                }
                for child in quarters(&triangle) {
                    pending.push((child, depth + 1));
                }
            }
        }
        k.check_cancelled(OP)?;
        Ok(PrimitiveFitCertificate {
            input,
            surface,
            triangles,
            concave,
            tolerance,
            upper,
            cells,
        })
    })();
    work_budget.check(k)?;
    answer
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn sphere_corners_alone_do_not_certify_the_chord_interior() {
        let input = MeshInput {
            positions: vec![[1., 0., 0.], [0., 1., 0.], [0., 0., 1.]],
            triangles: vec![[0, 1, 2]],
        };
        let surface = Primitive::Sphere {
            center: Vec3::ZERO,
            radius: 1.,
        };
        assert!(
            certify_primitive_region(&Kernel::default(), &input, &surface, &[0], false, 0.01)
                .is_err()
        );
    }
    #[test]
    fn cylinder_proof_normalizes_the_real_axis_instead_of_assuming_unit_length() {
        let angle = 0.005f64;
        let input = MeshInput {
            positions: vec![
                [10., 0., 0.],
                [10. * angle.cos(), 10. * angle.sin(), 0.],
                [10., 0., 20.],
            ],
            triangles: vec![[0, 1, 2]],
        };
        let surface = Primitive::Cylinder {
            point: Vec3::ZERO,
            axis: Vec3::new(0., 0., 2.),
            radius: 10.,
        };
        let k = Kernel::default();
        let ids = [0];
        let certificate =
            certify_primitive_region(&k, &input, &surface, &ids, false, 0.05).unwrap();
        assert!(certificate.upper_bound() <= 0.05);
    }
    #[test]
    fn unproved_apex_link_is_not_accepted_by_a_limiting_normal() {
        let half_angle = 59f64.to_radians();
        let depth = 10.;
        let radius = depth * half_angle.tan();
        let turn = 0.005f64;
        let input = MeshInput {
            positions: vec![
                [0., 0., 0.],
                [radius, 0., depth],
                [radius * turn.cos(), radius * turn.sin(), depth],
            ],
            triangles: vec![[0, 2, 1]],
        };
        let surface = Primitive::Cone {
            apex: Vec3::ZERO,
            axis: Vec3::new(0., 0., 2.),
            half_angle,
        };
        let k = Kernel::default();
        let ids = [0];
        assert!(certify_primitive_region(&k, &input, &surface, &ids, false, 0.05).is_err());
    }
    #[test]
    fn source_winding_and_torus_ring_validity_are_not_ignored() {
        let input = MeshInput {
            positions: vec![[0., 0., 0.], [0., 1., 0.], [1., 0., 0.]],
            triangles: vec![[0, 1, 2]],
        };
        let plane = Primitive::Plane {
            point: Vec3::ZERO,
            normal: Vec3::Z,
        };
        assert!(
            certify_primitive_region(&Kernel::default(), &input, &plane, &[0], false, 0.01)
                .is_err()
        );
        assert!(
            certify_primitive_region(&Kernel::default(), &input, &plane, &[0], true, 0.01).is_ok()
        );
        let horn = Primitive::Torus {
            center: Vec3::ZERO,
            axis: Vec3::Z,
            major: 1.,
            minor: 1.,
        };
        assert!(
            certify_primitive_region(&Kernel::default(), &input, &horn, &[0], false, 0.01).is_err()
        );
    }
}

#[cfg(test)]
mod apex_fan_tests {
    use super::*;
    #[test]
    fn complete_cone_fan_has_oriented_degree_one_and_whole_triangle_support() {
        let angle = 59f64.to_radians();
        let depth = 10.;
        let radius = depth * angle.tan();
        let count = 128usize;
        let mut positions = vec![[0., 0., 0.]];
        for i in 0..count {
            let t = std::f64::consts::TAU * i as f64 / count as f64;
            positions.push([radius * t.cos(), radius * t.sin(), depth]);
        }
        let mut triangles = Vec::new();
        for i in 0..count {
            triangles.push([0, ((i + 1) % count + 1) as u32, (i + 1) as u32]);
        }
        let ids: Vec<_> = (0..count).map(|i| i as u32).collect();
        let input = MeshInput {
            positions,
            triangles,
        };
        let surface = Primitive::Cone {
            apex: Vec3::ZERO,
            axis: Vec3::new(0., 0., 2.),
            half_angle: angle,
        };
        let k = Kernel::default();
        let proof = certify_primitive_region(&k, &input, &surface, &ids, false, 0.05).unwrap();
        assert!(proof.upper_bound() <= 0.05);
    }
}
