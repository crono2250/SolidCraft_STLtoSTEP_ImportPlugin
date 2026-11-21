//! Explicit ops recipe for native machining setups: planar booleans here, every geometric
//! quantity/fit/depth/eligibility decision in the kernel. No coordinate arithmetic occurs here.
//!
//! The private candidate is not an accepted reconstruction. Every planning helper borrows
//! the command's same ledger, without resetting counters. Native constructor, boolean,
//! copy/export workspace admission and final source/body acceptance remain separate
//! obligations. This function grants no permission to adopt a candidate.
use solidcore::mesh_reconstruction as kernel;
use solidcore::mesh_reconstruction::milled as plan;
use solidcore::prism::profile::Region2;
use solidcore_convert as convert;

use crate::boolean::BooleanOp;
use crate::Body;

use super::{check_cancelled, native, refused, Result};

struct Stack {
    outline: Vec<Region2>,
    tools: Vec<kernel::PrismTool>,
}

/// A normal exact planar boolean, followed by the native degeneracy/refusal policy.
fn planar(
    work: &kernel::MeshWork,
    a: &[Region2],
    b: &[Region2],
    operation: BooleanOp,
    tolerance: f64,
) -> Result<Vec<Region2>> {
    check_cancelled()?;
    let ar: Vec<_> = a.iter().map(convert::record_region2).collect();
    let br: Vec<_> = b.iter().map(convert::record_region2).collect();
    let result = crate::prism::planar_regions_boolean(&ar, &br, operation, tolerance)?;
    let result = result.iter().map(convert::region2).collect();
    native("mesh::planar_result", |k| {
        kernel::filter_planar_result_with_work(k, work, result, tolerance)
    })
}

fn same_shadow(
    work: &kernel::MeshWork,
    setup: &plan::MilledSetup,
    a: &[Region2],
    b: &[Region2],
) -> Result<bool> {
    if let Some(same) = native("mesh::same_shadow", |k| {
        kernel::same_shadow_with_work(k, work, a, b, setup.snap, setup.boolean_tolerance)
    })? {
        return Ok(same);
    }
    let ab = planar(work, a, b, BooleanOp::Subtract, setup.boolean_tolerance)?;
    let ba = planar(work, b, a, BooleanOp::Subtract, setup.boolean_tolerance)?;
    native("mesh::shadow_differences", |k| {
        kernel::shadow_differences_agree_with_work(
            k,
            work,
            a,
            b,
            &ab,
            &ba,
            setup.snap,
            setup.boolean_tolerance,
        )
    })
}

/// Run every supplied nesting obligation before using any fitted run.
fn check_nesting(work: &kernel::MeshWork, obligations: &[plan::ProfileNesting]) -> Result<()> {
    for obligation in obligations {
        let requests = native("mesh::nesting_requests", |k| {
            kernel::nesting_intersections_with_work(k, work, obligation)
        })?;
        for request in requests {
            let overlap = planar(
                work,
                std::slice::from_ref(&request.a),
                std::slice::from_ref(&request.b),
                BooleanOp::Intersect,
                request.boolean_tolerance,
            )?;
            native("mesh::nesting_intersection", |k| {
                kernel::check_nesting_intersection_with_work(k, work, &request, &overlap)
            })?;
        }
    }
    Ok(())
}

fn direction_stack(work: &kernel::MeshWork, setup: &plan::MilledSetup) -> Result<Stack> {
    let mut raw: Vec<plan::SlabShadow> = Vec::new();
    for slab in &setup.slabs {
        let mut shadow = Vec::new();
        for section in &slab.sections {
            shadow = planar(
                work,
                &shadow,
                section,
                BooleanOp::Union,
                setup.boolean_tolerance,
            )?;
        }
        if shadow.is_empty() {
            continue;
        }
        let next = plan::SlabShadow {
            lo: slab.lo,
            hi: slab.hi,
            regions: shadow,
        };
        if let Some(previous) = raw.last_mut() {
            let adjacent = native("mesh::adjacent_runs", |k| {
                kernel::can_merge_runs_with_work(k, work, previous, &next, setup.geometry_tolerance)
            })?;
            if adjacent && same_shadow(work, setup, &previous.regions, &next.regions)? {
                previous.hi = next.hi;
                continue;
            }
        }
        raw.push(next);
    }
    // Shared circular/corner fits run once across this direction's complete runs in Core.
    let fitted = native("mesh::fit_shadow_runs", |k| {
        plan::fit_shadow_runs_with_work(k, work, setup, raw)
    })?;
    check_nesting(work, &fitted.nesting)?;
    let mut outline = Vec::new();
    for slab in &fitted.runs {
        outline = planar(
            work,
            &outline,
            &slab.regions,
            BooleanOp::Union,
            setup.boolean_tolerance,
        )?;
    }
    if outline.is_empty() {
        return Err(refused(
            "milled sections",
            "no section along a machining direction",
        ));
    }
    let removed = fitted
        .runs
        .iter()
        .map(|slab| {
            planar(
                work,
                &outline,
                &slab.regions,
                BooleanOp::Subtract,
                setup.boolean_tolerance,
            )
        })
        .collect::<Result<Vec<_>>>()?;
    let mut tools = Vec::new();
    for from_top in [true, false] {
        let order: Vec<usize> = if from_top {
            (0..fitted.runs.len()).rev().collect()
        } else {
            (0..fitted.runs.len()).collect()
        };
        let mut levels: Vec<(f64, Vec<Region2>)> = Vec::new();
        for index in order {
            let (Some(slab), Some(here)) = (fitted.runs.get(index), removed.get(index)) else {
                return Err(refused(
                    "milled sections",
                    "section correspondence is incomplete",
                ));
            };
            let now = match levels.last() {
                None => here.clone(),
                Some((_, open)) => planar(
                    work,
                    open,
                    here,
                    BooleanOp::Intersect,
                    setup.boolean_tolerance,
                )?,
            };
            let now = native("mesh::pocket_regions", |k| {
                kernel::filter_pocket_regions_with_work(k, work, now, setup.geometry_tolerance)
            })?;
            if now.is_empty() {
                break;
            }
            levels.push((if from_top { slab.lo } else { slab.hi }, now));
        }
        for (index, (floor, regions)) in levels.iter().enumerate() {
            let deeper = levels
                .get(index + 1)
                .map_or(&[][..], |(_, regions)| regions.as_slice());
            let mut fresh = Vec::new();
            for region in regions {
                let difference = planar(
                    work,
                    std::slice::from_ref(region),
                    deeper,
                    BooleanOp::Subtract,
                    setup.boolean_tolerance,
                )?;
                if native("mesh::fresh_pocket_tool", |k| {
                    kernel::keep_fresh_tool_with_work(
                        k,
                        work,
                        region,
                        &difference,
                        setup.boolean_tolerance,
                    )
                })? {
                    fresh.push(region.clone());
                }
            }
            if !fresh.is_empty() {
                tools.push(native("mesh::pocket_tool", |k| {
                    kernel::pocket_tool_with_work(k, work, setup, *floor, from_top, fresh)
                })?);
            }
        }
    }
    native("mesh::order_tools", |k| {
        kernel::order_tools_deepest_first_with_work(k, work, &mut tools)
    })?;
    Ok(Stack { outline, tools })
}

fn extrude(tool: &kernel::PrismTool) -> Result<Body> {
    check_cancelled()?;
    super::build::tool(&kernel::ToolGeometry::Prism(tool.clone()))
}

fn cut(body: Body, tool: Body, stage: &'static str) -> Result<Body> {
    check_cancelled()?;
    crate::boolean::boolean(body, tool, BooleanOp::Subtract)?
        .ok_or_else(|| refused(stage, "the tool removes the entire candidate"))
}

/// Build only the machining stock/pockets. No accepted result leaves this private helper.
pub(crate) fn milled_stock_candidate(
    work: &kernel::MeshWork,
    mesh: &kernel::MeshInput,
    tolerance: f64,
) -> Result<Body> {
    let setups = native("mesh::milled_setups", |k| {
        plan::milled_setups_with_work(k, work, mesh, tolerance)
    })?;
    let mut result = None;
    for setup in &setups {
        let stack = direction_stack(work, setup)?;
        let mut body = match result {
            None => {
                let stock = native("mesh::stock_tool", |k| {
                    kernel::stock_tool_with_work(k, work, setup, &stack.outline)
                })?;
                extrude(&stock)?
            }
            Some(mut body) => {
                let rectangle = native("mesh::stock_rectangle", |k| {
                    kernel::stock_rectangle_with_work(k, work, &stack.outline)
                })?;
                let outside = planar(
                    work,
                    &[rectangle],
                    &stack.outline,
                    BooleanOp::Subtract,
                    setup.boolean_tolerance,
                )?;
                let outside = native("mesh::outside_regions", |k| {
                    kernel::filter_pocket_regions_with_work(
                        k,
                        work,
                        outside,
                        setup.geometry_tolerance,
                    )
                })?;
                for region in outside {
                    let tool = native("mesh::outside_tool", |k| {
                        kernel::outside_stock_tool_with_work(
                            k,
                            work,
                            setup,
                            std::slice::from_ref(&region),
                        )
                    })?;
                    body = cut(body, extrude(&tool)?, "machining directions")?;
                }
                body
            }
        };
        for tool in &stack.tools {
            // Touching pieces are built/cut separately, retaining the existing modelling recipe.
            for region in &tool.regions {
                let mut piece = tool.clone();
                piece.regions = native("mesh::seal_pocket_regions", |k| {
                    kernel::seal_regions_with_work(k, work, std::slice::from_ref(region))
                })?;
                body = cut(body, extrude(&piece)?, "milled pocket")?;
            }
        }
        result = Some(body);
    }
    result.ok_or_else(|| refused("milled setups", "no machining direction found"))
}
