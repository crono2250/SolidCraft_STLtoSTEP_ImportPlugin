//! Native source alignment planning. The caller applies the returned rigid move.
use super::numeric::{Bounds3, Vec3Numeric};
use super::regions::checked_tolerance;
use super::types::{invalid, Alignment, MeshInput, Primitive, Result};
use crate::math::Vec3;
/// Standalone single-job convenience; multi-stage callers share one `MeshWork`.
pub fn align_to_axes(
    k: &crate::Kernel,
    input: &MeshInput,
    tolerance: f64,
    centred: bool,
) -> Result<Alignment> {
    let work_budget = super::work::MeshWork::new();
    align_to_axes_with_work(k, &work_budget, input, tolerance, centred)
}

/// Compute a source-space alignment from the fitted support directions using the same complete-workflow budget.
pub fn align_to_axes_with_work(
    k: &crate::Kernel,
    work_budget: &super::work::MeshWork,
    input: &MeshInput,
    tolerance: f64,
    centred: bool,
) -> Result<Alignment> {
    work_budget.check(k)?;
    let answer = (|| {
        {
            checked_tolerance(tolerance)?;
            let mut regions =
                super::regions::recognize_all_with_work(k, work_budget, input, tolerance)?;
            super::regions::regularize(&mut regions, 0.);
            // Directions by the area behind them; a plane's (with its outward normal) and an axis's.
            let mut votes: Vec<(Vec3, f64, bool)> = Vec::new();
            for r in &regions {
                let (d, flat) = match r.surface {
                    Primitive::Plane { normal, .. } => (normal, true),
                    Primitive::Cylinder { axis, .. }
                    | Primitive::Cone { axis, .. }
                    | Primitive::Torus { axis, .. } => (axis, false),
                    Primitive::Sphere { .. } => continue,
                };
                match votes
                    .iter_mut()
                    .find(|v| v.0.dot(d).abs() > 0.5f64.to_radians().cos())
                {
                    Some(v) => v.1 += r.area,
                    None => votes.push((d, r.area, flat)),
                }
            }
            votes.sort_by(|a, b| b.1.total_cmp(&a.1));
            // The largest flat face lies down: its outward normal becomes -Z.
            let largest_plane = regions
                .iter()
                .filter_map(|r| match r.surface {
                    Primitive::Plane { normal, .. } => Some((normal, r.area)),
                    _ => None,
                })
                .max_by(|a, b| a.1.total_cmp(&b.1));
            let z = match largest_plane {
                Some((n, _)) => -n,
                None => votes
                    .first()
                    .map(|v| v.0)
                    .ok_or_else(|| invalid("no surface recognised to align by"))?,
            };
            let x = votes
                .iter()
                .map(|v| v.0)
                .find(|d| d.dot(z).abs() < 1f64.to_radians().sin())
                .and_then(|d| (d - z * d.dot(z)).normalized())
                .or_else(|| z.any_perp().normalized())
                .ok_or_else(|| invalid("degenerate direction"))?;
            let y = z.cross(x);
            // Rows x, y, z: the rotation taking the part's frame onto the model's.
            let m = [[x.x, x.y, x.z], [y.x, y.y, y.z], [z.x, z.y, z.z]];
            let get = |i: usize, j: usize| m.get(i).and_then(|r| r.get(j)).copied().unwrap_or(0.);
            let trace = get(0, 0) + get(1, 1) + get(2, 2);
            let angle = ((trace - 1.) / 2.).clamp(-1., 1.).acos();
            let axis = if angle < 1e-9 {
                Vec3::Z
            } else if (std::f64::consts::PI - angle).abs() < 1e-6 {
                // A half turn: the axis from the diagonal.
                let d = |i: usize| ((get(i, i) + 1.) / 2.).max(0.).sqrt();
                let mut a = Vec3::new(d(0), d(1), d(2));
                if get(0, 1) < 0. {
                    a.y = -a.y;
                }
                if get(0, 2) < 0. {
                    a.z = -a.z;
                }
                a.normalized().unwrap_or(Vec3::Z)
            } else {
                Vec3::new(
                    get(2, 1) - get(1, 2),
                    get(0, 2) - get(2, 0),
                    get(1, 0) - get(0, 1),
                )
                .normalized()
                .unwrap_or(Vec3::Z)
            };
            let mesh = super::source::SourceMesh::checked(input)?;
            let mut b = Bounds3::new();
            for p in &mesh.positions {
                b.add_point(Vec3::new(p.dot(x), p.dot(y), p.dot(z)));
            }
            let t = if centred {
                Vec3::new(
                    -(b.min.x + b.max.x) / 2.,
                    -(b.min.y + b.max.y) / 2.,
                    -b.min.z,
                )
            } else {
                -b.min
            };
            Ok(Alignment {
                translation: t,
                axis,
                angle,
                angle_degrees: angle.to_degrees(),
                rotate: angle.to_degrees().abs() > 1e-9,
            })
        }
    })();
    work_budget.check(k)?;
    answer
}
