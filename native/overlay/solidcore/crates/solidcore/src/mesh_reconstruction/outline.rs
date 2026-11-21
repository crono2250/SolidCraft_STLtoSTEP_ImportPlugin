//! Native fitted outlines. Uncertain loop orientation or nesting is a typed refusal.
use super::frame::FrameGeometry;
use super::numeric::Vec3Numeric;
use super::regions::{checked_tolerance, Ctx};
use super::types::{invalid, MeshError, MeshInput, MeshRegion, Primitive, Result, SurfaceKind};
use crate::eval::Frame;
use crate::math::{Vec2, Vec3};
use crate::prism::profile::{Loop2, Region2};
pub(crate) fn nest_oriented_loops(loops: Vec<Loop2>) -> Result<Vec<Region2>> {
    let mut signed = Vec::new();
    for lp in loops {
        let area = lp.signed_area()?;
        let sign = area.sign().ok_or(MeshError::Undecided {
            stage: "outline orientation",
            work: lp.segs.len(),
        })?;
        signed.push((lp, area.value, sign));
    }
    let mut out: Vec<Region2> = signed
        .iter()
        .filter(|(_, _, positive)| *positive)
        .map(|(lp, _, _)| Region2 {
            outer: lp.clone(),
            holes: Vec::new(),
        })
        .collect();
    for (hole, _, _) in signed.iter().filter(|(_, _, positive)| !*positive) {
        let probe = hole
            .segs
            .first()
            .ok_or_else(|| invalid("empty outline loop"))?
            .start();
        let mut owner = None;
        for (i, region) in out.iter().enumerate() {
            match region.outer.holds(probe) {
                None => {
                    return Err(MeshError::Undecided {
                        stage: "outline nesting",
                        work: loops_len(&signed),
                    })
                }
                Some(false) => {}
                Some(true) => {
                    let area = region.outer.signed_area()?.value;
                    if owner.is_none_or(|(_, old)| area < old) {
                        owner = Some((i, area));
                    }
                }
            }
        }
        let (index, _) =
            owner.ok_or_else(|| invalid("a section hole lies outside the material"))?;
        out.get_mut(index)
            .ok_or_else(|| invalid("missing outline owner"))?
            .holes
            .push(hole.clone());
    }
    Ok(out)
}
fn loops_len(loops: &[(Loop2, f64, bool)]) -> usize {
    loops.iter().map(|(lp, _, _)| lp.segs.len()).sum()
}
/// The boundary of a planar region in `plane`'s coordinates, fitted as lines, arcs and circles
/// (no facets): outer loops counter-clockwise seen along the normal, holes clockwise.
pub(crate) fn planar_outline(
    ctx: &Ctx,
    region: &MeshRegion,
    plane: &Frame,
    tolerance: f64,
) -> Result<Vec<Region2>> {
    let inside: std::collections::BTreeSet<(u32, u32)> = region
        .triangles
        .iter()
        .flat_map(|t| {
            let [a, b, c] = ctx.triangles.get(*t as usize).copied().unwrap_or([0, 0, 0]);
            [(a, b), (b, c), (c, a)]
        })
        .collect();
    let mut next = std::collections::BTreeMap::<u32, u32>::new();
    for &(a, b) in &inside {
        if !inside.contains(&(b, a)) {
            next.insert(a, b);
        }
    }
    let fit = (tolerance * 0.1).max(1e-9);
    let mut loops: Vec<Loop2> = Vec::new();
    while let Some((&start, _)) = next.first_key_value() {
        let mut points = Vec::new();
        let mut current = start;
        for _ in 0..=ctx.positions.len() {
            let Some(to) = next.remove(&current) else {
                break;
            };
            points.push(
                plane.to_local(
                    ctx.positions
                        .get(current as usize)
                        .copied()
                        .unwrap_or(Vec3::ZERO),
                ),
            );
            current = to;
            if current == start {
                break;
            }
        }
        let points = super::profile::drop_collinear(&points, fit * 0.5);
        if points.len() >= 3 {
            loops.push(super::profile::fit_profile(&points, tolerance, fit));
        }
    }
    let regions = nest_oriented_loops(loops)?;
    if regions.is_empty() {
        return Err(invalid("the picked plane has no closed outline"));
    }
    Ok(regions)
}
/// A cylinder or cone region's axial range from its point or apex and its angular range
/// around the axis: (along from, along to, start angle, sweep), the sweep a whole turn when
/// the region goes all round. Angles are in the frame `u`, `v` across the axis.
pub(crate) fn around(
    points: &[Vec3],
    origin: Vec3,
    axis: Vec3,
    u: Vec3,
    v: Vec3,
) -> (f64, f64, f64, f64) {
    let (mut a, mut b) = (f64::INFINITY, f64::NEG_INFINITY);
    let mut angles: Vec<f64> = Vec::new();
    for p in points {
        let w = *p - origin;
        let h = w.dot(axis);
        a = a.min(h);
        b = b.max(h);
        angles.push(w.dot(v).atan2(w.dot(u)));
    }
    angles.sort_by(f64::total_cmp);
    let tau = std::f64::consts::TAU;
    let mut gap = (0f64, 0f64);
    for (i, x) in angles.iter().enumerate() {
        let y = angles
            .get(i + 1)
            .copied()
            .unwrap_or_else(|| angles.first().copied().unwrap_or(0.) + tau);
        if y - x > gap.1 - gap.0 {
            gap = (*x, y);
        }
    }
    if gap.1 - gap.0 < 30f64.to_radians() {
        (a, b, 0., tau)
    } else {
        (a, b, gap.1, tau - (gap.1 - gap.0))
    }
}

/// Standalone single-job convenience; multi-stage callers share one `MeshWork`.
pub fn surface_outline(
    k: &crate::Kernel,
    input: &MeshInput,
    point: Vec3,
    kind: SurfaceKind,
    tolerance: f64,
    round: f64,
) -> Result<(Frame, Vec<Region2>)> {
    let work_budget = super::work::MeshWork::new();
    surface_outline_with_work(k, &work_budget, input, point, kind, tolerance, round)
}

/// Plan an outline or analytic section of a recognized region using the caller's budget.
/// Planning alone is not a certificate for the actual constructed sketch or sheet.
pub fn surface_outline_with_work(
    k: &crate::Kernel,
    work_budget: &super::work::MeshWork,
    input: &MeshInput,
    point: Vec3,
    kind: SurfaceKind,
    tolerance: f64,
    round: f64,
) -> Result<(Frame, Vec<Region2>)> {
    work_budget.check(k)?;
    let answer = (|| {
        checked_tolerance(tolerance)?;
        if !point.is_finite() {
            return Err(invalid("the point must be finite"));
        }
        let ctx = super::regions::context_with_work(k, work_budget, input, tolerance)?;
        let mut regions = super::regions::picked_regions(&ctx, &[(point, kind)], tolerance)?;
        super::regions::regularize(&mut regions, tolerance);
        super::regions::round_sizes(&mut regions, round, tolerance);
        let region = regions
            .first()
            .ok_or_else(|| invalid("nothing recognised there"))?;
        let own = super::regions::vertices(&ctx, &region.triangles);
        match region.surface {
            Primitive::Plane { point, normal } => {
                let plane =
                    Frame::from_normal(point, normal).ok_or_else(|| invalid("degenerate plane"))?;
                let outline = planar_outline(&ctx, region, &plane, tolerance)?;
                Ok((plane, outline))
            }
            Primitive::Cylinder {
                point,
                axis,
                radius,
            } => {
                let (a, ..) = around(&own, point, axis, Vec3::X, Vec3::Y);
                let plane = Frame::from_normal(point + axis * a, axis)
                    .ok_or_else(|| invalid("degenerate axis"))?;
                Ok((
                    plane,
                    vec![Region2 {
                        outer: super::profile::circle(Vec2::new(0., 0.), radius),
                        holes: Vec::new(),
                    }],
                ))
            }
            Primitive::Cone {
                apex,
                axis,
                half_angle,
            } => {
                let (a, b, ..) = around(&own, apex, axis, Vec3::X, Vec3::Y);
                let at = if a > 1e-9 { a } else { b };
                let plane = Frame::from_normal(apex + axis * at, axis)
                    .ok_or_else(|| invalid("degenerate axis"))?;
                Ok((
                    plane,
                    vec![Region2 {
                        outer: super::profile::circle(Vec2::new(0., 0.), at * half_angle.tan()),
                        holes: Vec::new(),
                    }],
                ))
            }
            Primitive::Sphere { .. } => Err(invalid("a sphere has no outline to sketch")),
            Primitive::Torus {
                center,
                axis,
                major,
                ..
            } => {
                let plane =
                    Frame::from_normal(center, axis).ok_or_else(|| invalid("degenerate axis"))?;
                Ok((
                    plane,
                    vec![Region2 {
                        outer: super::profile::circle(Vec2::new(0., 0.), major),
                        holes: Vec::new(),
                    }],
                ))
            }
        }
    })();
    work_budget.check(k)?;
    answer
}
