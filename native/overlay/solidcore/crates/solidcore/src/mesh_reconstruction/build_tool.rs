//! One exact tool's geometry, built with the existing primitive/profile/sweep APIs.
//! This is not a modelling workflow or a reconstruction acceptance test. Ops owns tool
//! sequencing, regions' unions, cuts, finish contracts and the final source certificate.
//!
use crate::curve::curve::Curve;
use crate::eval::Frame;
use crate::kernel::Kernel;
use crate::math::Vec3;
use crate::primitive::{api_primitives, api_trim_ops};
use crate::prism::{extrude, profile};
use crate::sweep::{api_brep, directed};
use crate::topology::brep::mirror::transform_matrix;
use crate::{Brep, Transform};

use super::frame::FrameGeometry;
use super::types::{invalid, MeshError, Result, ToolGeometry};

const OP: &str = "mesh_reconstruction::build_tool";
const MAX_TOOL_SEGMENTS: usize = 60_000;

fn one_region(regions: &[profile::Region2]) -> Result<&profile::Region2> {
    match regions {
        [region] => Ok(region),
        _ => Err(invalid(
            "build each tool region separately and unite the results in ops",
        )),
    }
}

fn curves(k: &Kernel, frame: &Frame, region: &profile::Region2) -> Result<Vec<Curve>> {
    let count = region
        .loops()
        .map(|lp| lp.segs.len())
        .try_fold(0usize, usize::checked_add)
        .ok_or(MeshError::BudgetExceeded {
            stage: OP,
            limit: MAX_TOOL_SEGMENTS,
        })?;
    if count > MAX_TOOL_SEGMENTS {
        return Err(MeshError::BudgetExceeded {
            stage: OP,
            limit: MAX_TOOL_SEGMENTS,
        });
    }
    region
        .loops()
        .flat_map(|lp| &lp.segs)
        .map(|segment| {
            k.check_cancelled(OP)?;
            profile::curve_on_frame(k, frame, 0.0, segment).map_err(MeshError::from)
        })
        .collect()
}

fn on_frame(k: &mut Kernel, mut body: Brep, frame: &Frame) -> Result<Brep> {
    if !profile::frame_is_orthonormal(frame) {
        return Err(invalid("a tool frame must be finite and orthonormal"));
    }
    let (origin, x, y, normal) = profile::axes(frame);
    let transform = Transform::from_axes(x, y, normal, origin);
    transform_matrix(k, &mut body, &transform.m, false)?;
    Ok(body)
}

/// Construct a single analytic tool. `Prism`, `Revolve` and `PlanarSheet` take exactly one
/// region here; ops builds/unites multiple regions explicitly. A result has no acceptance
/// proof and must pass the caller's expected-solid/sheet finish and source certificate.
///
/// # Errors
/// Invalid data, a bounded work refusal, cancellation or an existing native construction error.
pub fn build_tool(k: &mut Kernel, tool: &ToolGeometry) -> Result<Brep> {
    k.check_cancelled(OP)?;
    let body = match tool {
        ToolGeometry::Prism(tool) => {
            let region = one_region(&tool.regions)?;
            extrude::extrude_region(k, &tool.frame, region, tool.start, tool.end)?
        }
        ToolGeometry::Cylinder {
            origin,
            axis,
            radius,
            length,
        } => {
            let frame = Frame::from_normal(*origin, *axis)
                .ok_or_else(|| invalid("a cylinder axis must be finite and nonzero"))?;
            let body = api_primitives::create_cylinder(k, Vec3::ZERO, *radius, *length)?;
            on_frame(k, body, &frame)?
        }
        ToolGeometry::Cone {
            origin,
            axis,
            radius,
            length,
        } => {
            let frame = Frame::from_normal(*origin, *axis)
                .ok_or_else(|| invalid("a cone axis must be finite and nonzero"))?;
            // This event is a cone, not a generic revolution whose analytic
            // class depends on an unrelated compatibility flag.
            let body = api_primitives::create_cone(k, Vec3::ZERO, 0., *radius, *length)?;
            on_frame(k, body, &frame)?
        }
        ToolGeometry::Sphere { center, radius } => {
            api_primitives::create_sphere(k, *center, *radius)?
        }
        ToolGeometry::Torus {
            frame,
            major,
            minor,
        } => {
            let body = api_primitives::create_torus(k, Vec3::ZERO, *major, *minor)?;
            on_frame(k, body, frame)?
        }
        ToolGeometry::Revolve {
            frame,
            regions,
            axis_origin,
            axis_direction,
            angle,
        } => {
            if !(angle.is_finite() && *angle > 0.0 && *angle <= std::f64::consts::TAU) {
                return Err(invalid(
                    "a tool revolution angle must be finite and in (0, one turn]",
                ));
            }
            let region = one_region(regions)?;
            let curves = curves(k, frame, region)?;
            let refs: Vec<_> = curves.iter().map(Some).collect();
            let origin = profile::to_world(frame, *axis_origin, 0.0);
            let (_, x, y, _) = profile::axes(frame);
            let axis = x * axis_direction.x + y * axis_direction.y;
            directed::revolve(k, &refs, origin, axis, angle.to_degrees(), true)?
        }
        ToolGeometry::PlanarSheet { frame, regions } => {
            let region = one_region(regions)?;
            let curves = curves(k, frame, region)?;
            api_trim_ops::create_planar_faces(k, &curves)?
        }
        ToolGeometry::CylindricalSheet {
            frame,
            chain,
            start,
            end,
        } => {
            if !(start.is_finite() && end.is_finite() && start < end) {
                return Err(invalid(
                    "a cylindrical sheet needs finite increasing levels",
                ));
            }
            if chain.len() > MAX_TOOL_SEGMENTS {
                return Err(MeshError::BudgetExceeded {
                    stage: OP,
                    limit: MAX_TOOL_SEGMENTS,
                });
            }
            let curves: Vec<_> = chain
                .iter()
                .map(|segment| {
                    k.check_cancelled(OP)?;
                    profile::curve_on_frame(k, frame, *start, segment)
                })
                .collect::<crate::Result<_>>()?;
            let refs: Vec<_> = curves.iter().map(Some).collect();
            let (_, _, _, normal) = profile::axes(frame);
            api_brep::create_linear_sweep(k, &refs, normal, end - start, false)?
        }
    };
    k.check_cancelled(OP)?;
    Ok(body)
}
