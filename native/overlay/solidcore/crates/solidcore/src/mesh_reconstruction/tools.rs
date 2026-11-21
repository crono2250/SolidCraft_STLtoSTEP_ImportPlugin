//! Native fitted-tool planning. No body state or modelling workflow enters this module.
use super::frame::FrameGeometry;
use super::numeric::{Bounds3, Vec3Numeric};
use super::types::{
    invalid, FittedTool, MeshInput, MeshPick, Primitive, PrismTool, Result, ToolGeometry,
};
use crate::eval::Frame;
use crate::math::{Vec2, Vec3};
use crate::prism::profile::{Region2, Seg2};

/// Compute an extended analytic tool from its selected source support.
pub fn primitive_tool(surface: &Primitive, points: &[Vec3]) -> Result<ToolGeometry> {
    match *surface {
        Primitive::Sphere { center, radius } => Ok(ToolGeometry::Sphere { center, radius }),
        Primitive::Cone {
            apex,
            axis,
            half_angle,
        } => {
            let depth = points
                .iter()
                .map(|p| (*p - apex).dot(axis))
                .fold(0f64, f64::max);
            if !crate::geom::certified::above(depth, 0.) {
                return Err(invalid("a recognised cone has no depth"));
            }
            let radius = depth * half_angle.tan();
            if !radius.is_finite() || radius <= 0. {
                return Err(invalid(
                    "a recognised cone has no finite positive base radius",
                ));
            }
            Ok(ToolGeometry::Cone {
                origin: apex,
                axis,
                radius,
                length: depth,
            })
        }
        _ => Err(invalid(
            "only cones and spheres are cut as recognised features",
        )),
    }
}

/// Standalone single-job convenience; multi-stage callers share one `MeshWork`.
pub fn fit_tools(
    k: &crate::Kernel,
    input: &MeshInput,
    tolerance: f64,
    picks: &[MeshPick],
    surfaces: bool,
    round: f64,
) -> Result<Vec<FittedTool>> {
    let work_budget = super::work::MeshWork::new();
    fit_tools_with_work(k, &work_budget, input, tolerance, picks, surfaces, round)
}

/// Plan separately fitted analytic tools with original triangle attribution using the same complete-workflow budget.
pub fn fit_tools_with_work(
    k: &crate::Kernel,
    work_budget: &super::work::MeshWork,
    input: &MeshInput,
    tolerance: f64,
    picks: &[MeshPick],
    surfaces: bool,
    round: f64,
) -> Result<Vec<FittedTool>> {
    work_budget.check(k)?;
    let answer = (|| {
        super::regions::checked_tolerance(tolerance)?;
        if picks.is_empty()
            || picks.len() > 10_000
            || picks.iter().any(|p| p.point.iter().any(|x| !x.is_finite()))
        {
            return Err(invalid(
                "pick at least one surface, at most10000, at finite points",
            ));
        }
        let ctx = super::regions::context_with_work(k, work_budget, input, tolerance)?;
        let picks: Vec<_> = picks
            .iter()
            .map(|p| (Vec3::from_array(p.point), p.kind))
            .collect();
        let mut regions = super::regions::picked_regions(&ctx, &picks, tolerance)?;
        work_budget.spend(k, regions.len().saturating_mul(regions.len()))?;
        super::regions::regularize_picked_regions(&ctx, &mut regions, round, tolerance)?;
        let mut bounds = Bounds3::new();
        for p in &ctx.positions {
            bounds.add_point(*p);
        }
        let margin = bounds.size().len().max(1.) * 0.02;
        let mut out = Vec::new();
        for region in regions {
            ctx.work
                .spend(ctx.positions.len().saturating_add(region.triangles.len()))?;
            let source_triangles = super::regions::source_triangle_ids(&ctx, &region.triangles)?;
            let _proof = super::primitive_certificate::certify_primitive_region_with_work(
                k,
                work_budget,
                input,
                &region.surface,
                &source_triangles,
                region.concave,
                tolerance,
            )?;

            let own = super::regions::vertices(&ctx, &region.triangles);
            let geometry = if surfaces {
                match region.surface {
                    Primitive::Plane { point, normal } => {
                        let frame = Frame::from_normal(point, normal)
                            .ok_or_else(|| invalid("degenerate plane"))?;
                        let outline =
                            super::outline::planar_outline(&ctx, &region, &frame, tolerance)?;
                        ToolGeometry::PlanarSheet {
                            frame,
                            regions: outline,
                        }
                    }
                    Primitive::Cylinder {
                        point,
                        axis,
                        radius,
                    } => {
                        let u = axis
                            .any_perp()
                            .normalized()
                            .ok_or_else(|| invalid("degenerate axis"))?;
                        let v = axis.cross(u);
                        let (a, b, start, sweep) = super::outline::around(&own, point, axis, u, v);
                        if !crate::geom::certified::above(b, a) {
                            return Err(invalid("a picked cylinder has no length"));
                        }
                        let frame = Frame::new(point + axis * a, u, v)
                            .ok_or_else(|| invalid("degenerate axis"))?;
                        let chain = if sweep >= std::f64::consts::TAU {
                            super::profile::circle(Vec2::new(0., 0.), radius).segs
                        } else {
                            vec![Seg2::Arc {
                                center: Vec2::new(0., 0.),
                                radius,
                                start,
                                sweep,
                            }]
                        };
                        ToolGeometry::CylindricalSheet {
                            frame,
                            chain,
                            start: 0.,
                            end: b - a,
                        }
                    }
                    _ => {
                        return Err(invalid(
                            "cone/sphere/torus sheets are not supported; make a body instead",
                        ))
                    }
                }
            } else {
                match region.surface {
                    Primitive::Plane { point, normal } => {
                        let u = normal
                            .any_perp()
                            .normalized()
                            .ok_or_else(|| invalid("degenerate plane"))?;
                        let v = normal.cross(u);
                        let frame =
                            Frame::new(point, u, v).ok_or_else(|| invalid("degenerate plane"))?;
                        let (mut lo, mut hi) = (
                            Vec2::new(f64::INFINITY, f64::INFINITY),
                            Vec2::new(f64::NEG_INFINITY, f64::NEG_INFINITY),
                        );
                        let mut depth = 0f64;
                        for p in &ctx.positions {
                            let q = frame.to_local(*p);
                            lo = Vec2::new(lo.x.min(q.x), lo.y.min(q.y));
                            hi = Vec2::new(hi.x.max(q.x), hi.y.max(q.y));
                            depth = depth.max(-(*p - point).dot(normal));
                        }
                        lo -= Vec2::new(margin, margin);
                        hi += Vec2::new(margin, margin);
                        let outer = super::profile::polygon(&[
                            lo,
                            Vec2::new(hi.x, lo.y),
                            hi,
                            Vec2::new(lo.x, hi.y),
                        ]);
                        ToolGeometry::Prism(PrismTool {
                            frame,
                            regions: vec![Region2 {
                                outer,
                                holes: Vec::new(),
                            }],
                            start: -(depth + margin),
                            end: 0.,
                        })
                    }
                    Primitive::Cylinder {
                        point,
                        axis,
                        radius,
                    } => {
                        let (a, b) = own
                            .iter()
                            .map(|p| (*p - point).dot(axis))
                            .fold((f64::INFINITY, f64::NEG_INFINITY), |(a, b), h| {
                                (a.min(h), b.max(h))
                            });
                        if !crate::geom::certified::above(b, a) {
                            return Err(invalid("a picked cylinder has no length"));
                        }
                        ToolGeometry::Cylinder {
                            origin: point + axis * (a - margin),
                            axis,
                            radius,
                            length: b - a + 2. * margin,
                        }
                    }
                    Primitive::Cone { .. } | Primitive::Sphere { .. } => {
                        primitive_tool(&region.surface, &own)?
                    }
                    Primitive::Torus {
                        center,
                        axis,
                        major,
                        minor,
                    } => ToolGeometry::Torus {
                        frame: Frame::from_normal(center, axis)
                            .ok_or_else(|| invalid("degenerate torus axis"))?,
                        major,
                        minor,
                    },
                }
            };
            out.push(FittedTool {
                surface: region.surface,
                geometry,
                source_triangles,
                concave: region.concave,
            });
        }
        Ok(out)
    })();
    work_budget.check(k)?;
    answer
}
