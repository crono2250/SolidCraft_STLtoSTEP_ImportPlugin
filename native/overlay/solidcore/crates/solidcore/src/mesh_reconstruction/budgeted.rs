//! Shared-budget views for finite profile helpers. Ops sequences these; it computes no math.
use super::milled::{
    FittedShadowRuns, MilledSetup, NestingIntersection, ProfileNesting, SlabShadow,
};
use super::types::{MeshError, Primitive, PrismTool, Result, ToolGeometry};
use super::work::MeshWork;
use crate::prism::profile::Region2;
use crate::Kernel;
/// Count every borrowed container before traversal, including empty loops.
/// Counts bound subsequent work; this does not allocate or authorize a copy.
fn refs(k: &Kernel, work: &MeshWork, regions: &[Region2]) -> Result<usize> {
    work.spend(k, regions.len())?;
    let mut count = regions.len();
    for region in regions {
        let loops = region.holes.len().saturating_add(1);
        work.spend(k, loops)?;
        count = count.saturating_add(loops);
        for boundary in region.loops() {
            work.spend(k, boundary.segs.len())?;
            count = count.saturating_add(boundary.segs.len());
        }
    }
    Ok(count)
}

fn charge(
    k: &Kernel,
    work: &MeshWork,
    references: usize,
    square: bool,
    outputs: usize,
) -> Result<()> {
    work.spend(
        k,
        if square {
            references.saturating_mul(references.saturating_add(1))
        } else {
            references.saturating_add(1)
        },
    )?;
    work.reserve_output(k, outputs)
}
/// Shared workflow view of adjacency comparison.
pub fn can_merge_runs_with_work(
    k: &Kernel,
    work: &MeshWork,
    a: &SlabShadow,
    b: &SlabShadow,
    tolerance: f64,
) -> Result<bool> {
    work.check(k)?;
    let answer = (|| {
        work.spend(k, 1)?;
        let result = super::milled::can_merge_runs(a, b, tolerance);
        work.check(k)?;
        result
    })();
    work.check(k)?;
    answer
}
/// Shared workflow view of complete-shadow comparison.
pub fn same_shadow_with_work(
    k: &Kernel,
    work: &MeshWork,
    a: &[Region2],
    b: &[Region2],
    snap: f64,
    tolerance: f64,
) -> Result<Option<bool>> {
    work.check(k)?;
    let answer = (|| {
        charge(
            k,
            work,
            refs(k, work, a)?.saturating_add(refs(k, work, b)?),
            true,
            0,
        )?;
        let result = super::milled::same_shadow(a, b, snap, tolerance);
        work.check(k)?;
        result
    })();
    work.check(k)?;
    answer
}
/// Shared workflow view of exact symmetric-difference decisions.
pub fn shadow_differences_agree_with_work(
    k: &Kernel,
    work: &MeshWork,
    a: &[Region2],
    b: &[Region2],
    ab: &[Region2],
    ba: &[Region2],
    snap: f64,
    tolerance: f64,
) -> Result<bool> {
    work.check(k)?;
    let answer = (|| {
        charge(
            k,
            work,
            refs(k, work, a)?
                .saturating_add(refs(k, work, b)?)
                .saturating_add(refs(k, work, ab)?)
                .saturating_add(refs(k, work, ba)?),
            false,
            0,
        )?;
        let result = super::milled::shadow_differences_agree(a, b, ab, ba, snap, tolerance);
        work.check(k)?;
        result
    })();
    work.check(k)?;
    answer
}
/// Shared workflow view of pocket-area eligibility.
pub fn keep_fresh_tool_with_work(
    k: &Kernel,
    work: &MeshWork,
    region: &Region2,
    difference: &[Region2],
    tolerance: f64,
) -> Result<bool> {
    work.check(k)?;
    let answer = (|| {
        charge(
            k,
            work,
            refs(k, work, std::slice::from_ref(region))?.saturating_add(refs(k, work, difference)?),
            false,
            0,
        )?;
        let result = super::milled::keep_fresh_tool(region, difference, tolerance);
        work.check(k)?;
        result
    })();
    work.check(k)?;
    answer
}
/// Shared workflow view of sliver filtering, reserved before output materialization.
pub fn filter_pocket_regions_with_work(
    k: &Kernel,
    work: &MeshWork,
    regions: Vec<Region2>,
    tolerance: f64,
) -> Result<Vec<Region2>> {
    work.check(k)?;
    let answer = (|| {
        let n = refs(k, work, &regions)?;
        charge(k, work, n, false, n)?;
        let result = super::milled::filter_pocket_regions(regions, tolerance);
        work.check(k)?;
        result
    })();
    work.check(k)?;
    answer
}
/// Shared workflow view of planar-result filtering.
pub fn filter_planar_result_with_work(
    k: &Kernel,
    work: &MeshWork,
    regions: Vec<Region2>,
    tolerance: f64,
) -> Result<Vec<Region2>> {
    work.check(k)?;
    let answer = (|| {
        let n = refs(k, work, &regions)?;
        charge(k, work, n, false, n)?;
        let result = super::milled::filter_planar_result(regions, tolerance);
        work.check(k)?;
        result
    })();
    work.check(k)?;
    answer
}
/// Shared workflow view of exact gap sealing; every arc-arc join may add one segment.
pub fn seal_regions_with_work(
    k: &Kernel,
    work: &MeshWork,
    regions: &[Region2],
) -> Result<Vec<Region2>> {
    work.check(k)?;
    let answer = (|| {
        let n = refs(k, work, regions)?;
        charge(k, work, n, false, n.saturating_mul(2))?;
        Ok(super::milled::seal_regions(regions))
    })();
    work.check(k)?;
    answer
}
/// Shared workflow view of deepest-first tool ordering.
pub fn order_tools_deepest_first_with_work(
    k: &Kernel,
    work: &MeshWork,
    tools: &mut [PrismTool],
) -> Result<()> {
    work.check(k)?;
    let answer = (|| {
        work.spend(k, tools.len().saturating_mul(tools.len().saturating_add(1)))?;
        super::milled::order_tools_deepest_first(tools);
        work.check(k)
    })();
    work.check(k)?;
    answer
}
/// Shared workflow view of the first material stock.
pub fn stock_tool_with_work(
    k: &Kernel,
    work: &MeshWork,
    setup: &MilledSetup,
    outline: &[Region2],
) -> Result<PrismTool> {
    work.check(k)?;
    let answer = (|| {
        let n = refs(k, work, outline)?;
        charge(k, work, n, false, n.saturating_mul(2))?;
        Ok(super::milled::stock_tool(setup, outline))
    })();
    work.check(k)?;
    answer
}
/// Shared workflow view of a setup's outside cutter.
pub fn outside_stock_tool_with_work(
    k: &Kernel,
    work: &MeshWork,
    setup: &MilledSetup,
    regions: &[Region2],
) -> Result<PrismTool> {
    work.check(k)?;
    let answer = (|| {
        let n = refs(k, work, regions)?;
        charge(k, work, n, false, n.saturating_mul(2))?;
        Ok(super::milled::outside_stock_tool(setup, regions))
    })();
    work.check(k)?;
    answer
}
/// Shared workflow view of a pocket's exact native axial span.
pub fn pocket_tool_with_work(
    k: &Kernel,
    work: &MeshWork,
    setup: &MilledSetup,
    floor: f64,
    from_top: bool,
    regions: Vec<Region2>,
) -> Result<PrismTool> {
    work.check(k)?;
    let answer = (|| {
        charge(k, work, refs(k, work, &regions)?, false, 0)?;
        Ok(super::milled::pocket_tool(setup, floor, from_top, regions))
    })();
    work.check(k)?;
    answer
}
/// Shared workflow view of whole-circle conservative stock bounds.
pub fn stock_rectangle_with_work(
    k: &Kernel,
    work: &MeshWork,
    outline: &[Region2],
) -> Result<Region2> {
    work.check(k)?;
    let answer = (|| {
        charge(k, work, refs(k, work, outline)?, false, 4)?;
        let result = super::milled::stock_rectangle(outline);
        work.check(k)?;
        result
    })();
    work.check(k)?;
    answer
}
/// Shared workflow view of the original pairwise nesting obligations.
pub fn nesting_intersections_with_work(
    k: &Kernel,
    work: &MeshWork,
    obligation: &ProfileNesting,
) -> Result<Vec<NestingIntersection>> {
    work.check(k)?;
    let answer = (|| {
        let n = obligation
            .raw
            .iter()
            .chain(&obligation.fitted)
            .fold(0usize, |s, l| s.saturating_add(l.segs.len()));
        let outputs = n
            .saturating_mul(obligation.raw.len().saturating_sub(1))
            .saturating_mul(2);
        charge(k, work, n, true, outputs)?;
        let result = super::milled::nesting_intersections(obligation);
        work.check(k)?;
        result
    })();
    work.check(k)?;
    answer
}
/// Shared workflow view of checking an executed exact nesting intersection.
pub fn check_nesting_intersection_with_work(
    k: &Kernel,
    work: &MeshWork,
    request: &NestingIntersection,
    overlap: &[Region2],
) -> Result<()> {
    work.check(k)?;
    let answer = (|| {
        charge(k, work, refs(k, work, overlap)?, false, 0)?;
        let result = super::milled::check_nesting_intersection(request, overlap);
        work.check(k)?;
        result
    })();
    work.check(k)?;
    answer
}
/// Shared workflow view of one cone/sphere candidate tool.
pub fn primitive_tool_with_work(
    k: &Kernel,
    work: &MeshWork,
    surface: &Primitive,
    points: &[crate::math::Vec3],
) -> Result<ToolGeometry> {
    work.check(k)?;
    let answer = (|| {
        charge(k, work, points.len(), false, 4)?;
        let result = super::tools::primitive_tool(surface, points);
        work.check(k)?;
        result
    })();
    work.check(k)?;
    answer
}
/// Extract exactly one section's regions after the caller discharged its nesting obligations.
/// Empty and multi-run outputs refuse; no arbitrary concatenation or run dropping occurs.
pub fn single_section_regions_with_work(
    k: &Kernel,
    work: &MeshWork,
    fitted: FittedShadowRuns,
) -> Result<Vec<Region2>> {
    work.check(k)?;
    let answer = (|| {
        work.spend(k, fitted.runs.len())?;
        let mut runs = fitted.runs.into_iter();
        let Some(run) = runs.next() else {
            return Err(MeshError::Refused {
                stage: "mesh section",
                detail: "the plane does not cut the mesh".into(),
            });
        };
        if runs.next().is_some() {
            return Err(MeshError::InvalidInput {
                stage: "mesh section",
                detail: "single-section extraction requires exactly one run".into(),
            });
        }
        charge(k, work, refs(k, work, &run.regions)?, false, 0)?;
        Ok(run.regions)
    })();
    work.check(k)?;
    answer
}

/// Materialized proof-net inventory only. Full B-rep owned payloads and lazy
/// constructors need their own pre-operation admission; this is not that gate.
pub(crate) fn admit_surface_control_storage_with_work(
    k: &Kernel,
    work: &MeshWork,
    net: &crate::nurbs::srf_basic::Surface,
) -> crate::Result<()> {
    const OP: &str = "mesh_reconstruction::surface_control_storage";
    let invalid = || crate::SolidError::Unsupported {
        operation: OP,
        reason: "surface active storage dimensions unproved",
    };
    work.spend_core(k, 0)?;
    let admitted = net.visit_stored_payload(&mut |count| {
        work.spend_core(k, count)?;
        work.reserve_cells_core(k, count)
    });
    work.spend_core(k, 0)?;
    admitted?;
    let rows = net.n().checked_add(1).ok_or_else(invalid)?;
    let columns = net.m().checked_add(1).ok_or_else(invalid)?;
    let uk = net.r().checked_add(1).ok_or_else(invalid)?;
    let vk = net.s().checked_add(1).ok_or_else(invalid)?;
    if net.n() < net.p()
        || net.m() < net.q()
        || net.n().checked_add(net.p()).and_then(|v| v.checked_add(1)) != Some(net.r())
        || net.m().checked_add(net.q()).and_then(|v| v.checked_add(1)) != Some(net.s())
    {
        return Err(invalid());
    }
    work.reserve_cells_core(k, rows.checked_mul(columns).ok_or_else(invalid)?)?;
    work.spend_core(k, rows)?;
    if net.u_knots().len() != uk || net.v_knots().len() != vk {
        return Err(invalid());
    }
    for row in 0..rows {
        work.spend_core(k, 1)?;
        if net.row(row)?.len() != columns {
            return Err(invalid());
        }
    }
    Ok(())
}
