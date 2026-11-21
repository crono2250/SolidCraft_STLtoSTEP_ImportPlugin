//! Constant-section planning uses the existing AnalyticV1 proposal algorithm.
//! This file owns only the public plan data; no second graph/fitting implementation.
use super::milled::ProfileNesting;
use super::source::SourceMesh;
use super::types::{PrismTool, Result};
use crate::math::Vec3;
#[derive(Clone, Debug)]
/// Constant-section candidate with explicit cap and nesting claims.
pub struct PrismaticPlan {
    /// Proposed constant-section construction.
    pub tool: PrismTool,
    /// Unresolved source/profile nesting obligations.
    pub nesting: ProfileNesting,
    /// Cap loops indexed into the retained weld table.
    pub cap_loops: Vec<Vec<u32>>,
    /// Proposed immediate parent of each cap loop.
    pub cap_loop_parents: Vec<Option<usize>>,
}
pub(crate) fn extrusion_with_work(
    k: &crate::Kernel,
    work: &super::MeshWork,
    mesh: &SourceMesh,
    axis: Vec3,
    tolerance: f64,
) -> Result<Option<PrismaticPlan>> {
    work.check(k)?;
    let result = super::analytic::propose_prism_with_work(
        k,
        work,
        super::analytic::MeshView {
            positions: &mesh.positions,
            triangles: &mesh.triangles,
        },
        axis,
        tolerance,
    )
    .and_then(|p| p.map(|p| p.into_plan(k, work)).transpose());
    work.check(k)?;
    result.map_err(super::MeshError::from)
}
