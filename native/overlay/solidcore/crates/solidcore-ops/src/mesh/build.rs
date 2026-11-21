//! Ops finish/union policy over the kernel's single exact tool builder. This module never
//! computes coordinates, dimensions or transforms. Constructed tools carry no source proof.
//!
use solidcore::mesh_reconstruction::{self as kernel, ToolGeometry};

use crate::body::{finish, Body, Expect};
use crate::session::{run, Answer};

use super::{check_cancelled, refused, Error, Result};

struct Built(Result<solidcore::Brep>);
impl Answer for Built {
    fn refusal(&self) -> Option<crate::Error> {
        self.0.as_ref().err().map(Error::session_refusal)
    }
}

fn one(tool: &ToolGeometry) -> Result<Body> {
    check_cancelled()?;
    let expect = match tool {
        ToolGeometry::PlanarSheet { .. } | ToolGeometry::CylindricalSheet { .. } => Expect::FACES,
        _ => Expect::SOLID,
    };
    let answer = run("mesh::build_tool", |k| {
        let body = match kernel::build_tool(k, tool) {
            Ok(body) => body,
            Err(error) => return Ok(Built(Err(super::geometry_error(error)))),
        };
        Ok(Built(finish(k, body, expect)?.map_err(Error::Operation)))
    })?;
    check_cancelled()?;
    answer.0.map(Body::new)
}

/// Build each requested profile region separately, then unite using the existing ops recipe.
/// Splitting copies fields only; geometry and the expected result contract stay unchanged.
pub(super) fn tool(tool: &ToolGeometry) -> Result<Body> {
    let pieces: Vec<ToolGeometry> = match tool {
        ToolGeometry::Prism(prism) => prism
            .regions
            .iter()
            .map(|region| {
                let mut part = prism.clone();
                part.regions = vec![region.clone()];
                ToolGeometry::Prism(part)
            })
            .collect(),
        ToolGeometry::Revolve {
            frame,
            regions,
            axis_origin,
            axis_direction,
            angle,
        } => regions
            .iter()
            .map(|region| ToolGeometry::Revolve {
                frame: frame.clone(),
                regions: vec![region.clone()],
                axis_origin: *axis_origin,
                axis_direction: *axis_direction,
                angle: *angle,
            })
            .collect(),
        ToolGeometry::PlanarSheet { frame, regions } => regions
            .iter()
            .map(|region| ToolGeometry::PlanarSheet {
                frame: frame.clone(),
                regions: vec![region.clone()],
            })
            .collect(),
        other => vec![other.clone()],
    };
    if pieces.is_empty() {
        return Err(refused(
            "tool construction",
            "the tool has no profile regions",
        ));
    }
    let bodies = pieces.iter().map(one).collect::<Result<Vec<_>>>()?;
    check_cancelled()?;
    Ok(crate::boolean::union_all(bodies)?)
}
