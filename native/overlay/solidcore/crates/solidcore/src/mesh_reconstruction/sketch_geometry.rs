//! Definition-based sketch entities from already-fitted profile curves. Circle joining reuses
//! the kernel's certified analytic arc-joining API; it does not fit a second circle.
//! Profile copies and local drawing buffers share one ledger; source acceptance is separate.
use crate::curve::arc::{join_arcs, ArcDefinition, Join};
use crate::curve::path::PathPiece;
use crate::geom::certified::{gamma, Bounded};
use crate::kernel::Kernel;
use crate::math::{Vec2, Vec3};
use crate::prism::profile::{Loop2, Region2, Seg2, MAX_SEGMENTS};

use super::types::{invalid, MeshError, Result};
use super::MeshWork;

/// Exact sketch entity fields; no source acceptance proof is represented by these descriptors.
#[derive(Clone, Debug, PartialEq)]
pub enum SketchGeometry {
    /// A straight directed segment.
    Line {
        /// First endpoint.
        a: Vec2,
        /// Second endpoint.
        b: Vec2,
    },
    /// A directed circular arc.
    Arc {
        /// Centre in model coordinates.
        center: Vec2,
        /// First endpoint.
        a: Vec2,
        /// Second endpoint.
        b: Vec2,
    },
    /// A complete circle.
    Circle {
        /// Centre in model coordinates.
        center: Vec2,
        /// Radius in model units.
        radius: f64,
    },
}

/// The drawing entities and precomputed join tolerance passed to the existing import command.
#[derive(Clone, Debug, PartialEq)]
pub struct SketchDrawing {
    /// Precomputed entities in the profile frame.
    pub geometry: Vec<SketchGeometry>,
    /// Computed endpoint-join allowance for the snapshot drawing.
    pub join_tolerance: f64,
}

/// Purpose-specific DATA COPY resource admission, never a geometry certificate.
/// All counts are borrowed metadata; the native factory independently checks the
/// actual materialized profile. These variants expose no generic budget mutator.
#[derive(Clone, Copy, Debug)]
pub enum SketchCopyPart {
    /// Region entry plus its outer/holes Vec descriptors.
    Regions,
    /// Each retained hole Loop2 descriptor, including empty holes.
    Holes,
    /// Full inline segment representation; previous is the same profile's total.
    Segments {
        /// Segments already counted in this SAME complete profile.
        previous: usize,
    },
    /// One returned drawing entity copied into its record representation.
    Drawing,
}
/// Charge BEFORE scanning/copying the indicated immutable profile container.
/// Returns the cumulative segment count for Segments, otherwise the input count.
/// It establishes resource admission only, no geometry/ownership/proof claim.
///
/// # Errors
/// Original cancellation/Core errors, shared budget exhaustion, count overflow,
/// or more than the existing MAX_SEGMENTS across the complete profile.
pub fn admit_sketch_copy_with_work(
    k: &Kernel,
    work: &MeshWork,
    part: SketchCopyPart,
    count: usize,
) -> Result<usize> {
    work.check(k)?;
    let total = match part {
        SketchCopyPart::Segments { previous } => {
            let total = previous
                .checked_add(count)
                .ok_or(MeshError::BudgetExceeded {
                    stage: "mesh sketch entities",
                    limit: MAX_SEGMENTS,
                })?;
            if total > MAX_SEGMENTS {
                return Err(MeshError::BudgetExceeded {
                    stage: "mesh sketch entities",
                    limit: MAX_SEGMENTS,
                });
            }
            total
        }
        _ => count,
    };
    // Full Bezier[10] is copied even when n<9:20 coordinates+degree+tag.
    // Native/record Seg2 currently have identical fixed inline layouts.
    let units = match part {
        SketchCopyPart::Regions => 3,
        SketchCopyPart::Holes => 1,
        SketchCopyPart::Segments { .. } => crate::prism::profile::MAX_BEZIER_CTRL
            .checked_mul(2)
            .and_then(|n| n.checked_add(2))
            .ok_or_else(|| invalid("sketch segment representation count overflow"))?,
        // Arc is largest:centre+a+b=6 coordinates, plus variant tag.
        SketchCopyPart::Drawing => 7,
    };
    let slots = count
        .checked_mul(units)
        .and_then(|n| n.checked_add(1))
        .ok_or_else(|| invalid("sketch copy representation count overflow"))?;
    work.spend(k, slots)?;
    work.reserve_cells(k, slots)?;
    work.reserve_output(k, count)?;
    Ok(total)
}

fn whole_circle(k: &Kernel, work: &MeshWork, lp: &Loop2) -> Result<Option<SketchGeometry>> {
    work.check(k)?;
    let Some(Seg2::Arc { sweep, .. }) = lp.segs.first() else {
        return Ok(None);
    };
    work.check(k)?;
    let reversed;
    let lp = if *sweep < 0.0 {
        // Reversal copies ALL inline segments before the later kind refusal.
        admit_sketch_copy_with_work(
            k,
            work,
            SketchCopyPart::Segments { previous: 0 },
            lp.segs.len(),
        )?;
        reversed = lp.reversed();
        &reversed
    } else {
        lp
    };
    work.reserve_cells(k, 1)?;
    let mut definitions = Vec::new();
    let mut total = 0.0;
    let mut magnitude = 0.0;
    for segment in &lp.segs {
        work.spend(k, 7)?; // Arc's fixed scalar/tag input; no geometry sampling.
        let Seg2::Arc {
            center,
            radius,
            start,
            sweep,
        } = *segment
        else {
            return Ok(None);
        };
        if !sweep.is_finite() || sweep <= 0.0 {
            return Ok(None);
        }
        let definition = ArcDefinition {
            centre: Vec3::new(center.x, center.y, 0.0),
            axis: Vec3::Z,
            reference: Vec3::X,
            radius,
            start,
            end: start + sweep,
        };
        // One Curve descriptor + Option tag +12 ArcDefinition scalar fields.
        // Ellipse's internal constructor/evaluator scratch is NOT qualified by
        // this local container charge; its existing native bounds remain separate.
        work.reserve_cells(k, 14)?;
        work.reserve_output(k, 1)?;
        definitions.push(PathPiece::of_arc(k, &definition)?);
        total += sweep;
        magnitude += sweep.abs();
    }
    let turn_error = Bounded {
        value: (total - std::f64::consts::TAU).abs(),
        bound: gamma(definitions.len().saturating_add(2)) * (magnitude + std::f64::consts::TAU),
    };
    if !turn_error.at_most(1e-6).is_yes() {
        return Ok(None);
    }
    // join_arcs copies N arc references and running() writes N scalar pairs:
    // N+2N entries, two Vec descriptors, before either internal materialization.
    let join_slots = definitions
        .len()
        .checked_mul(3)
        .and_then(|n| n.checked_add(2))
        .ok_or_else(|| invalid("sketch join temporary count overflow"))?;
    let join_refs = definitions
        .len()
        .checked_mul(2)
        .ok_or_else(|| invalid("sketch join reference count overflow"))?;
    work.spend(k, join_slots)?;
    work.reserve_cells(k, join_slots)?;
    work.reserve_output(k, join_refs)?;
    match join_arcs(k, &definitions, Join::ClosedAtFrameStart, 1e-9) {
        Ok((circle, _)) => Ok(Some(SketchGeometry::Circle {
            center: Vec2::new(circle.centre.x, circle.centre.y),
            radius: circle.radius,
        })),
        // Joining may refuse distinct valid arcs. Keep each exact arc, never coerce them to a
        // circle; cancellation/internal/other errors are not swallowed as this benign choice.
        Err(crate::SolidError::InvalidInput {
            operation: "curve::arc::join_arcs",
            ..
        }) => Ok(None),
        Err(error) => Err(error.into()),
    }
}

/// Convert existing analytic line/arc definitions to sketch entities, preserving unsupported
/// geometry as a typed refusal rather than silently omitting a curve.
///
/// # Errors
/// Invalid tolerance, too many segments, unsupported curve kind, cancellation or native refusal.
pub fn sketch_geometry(k: &Kernel, regions: &[Region2], tolerance: f64) -> Result<SketchDrawing> {
    let work = MeshWork::new();
    sketch_geometry_with_work(k, &work, regions, tolerance)
}
/// Same factory using the complete command's ledger. Resource accounting here
/// covers profile reads, explicit local buffers and drawing entries; it does NOT
/// qualify analytic constructor/evaluator lazy scratch or source/profile geometry.
///
/// # Errors
/// Invalid/unsupported profile, count/shared-budget refusal, cancellation or native errors.
pub fn sketch_geometry_with_work(
    k: &Kernel,
    work: &MeshWork,
    regions: &[Region2],
    tolerance: f64,
) -> Result<SketchDrawing> {
    work.check(k)?;
    let answer = sketch_geometry_impl(k, work, regions, tolerance);
    work.check(k)?;
    answer
}
fn sketch_geometry_impl(
    k: &Kernel,
    work: &MeshWork,
    regions: &[Region2],
    tolerance: f64,
) -> Result<SketchDrawing> {
    super::regions::checked_tolerance(tolerance)?;
    // No allocation/curve evaluation: charge each metadata traversal before it.
    work.spend(k, regions.len())?;
    let mut count = 0usize;
    for region in regions {
        let loops = region
            .holes
            .len()
            .checked_add(1)
            .ok_or_else(|| invalid("sketch loop count overflow"))?;
        work.spend(k, loops)?;
        for lp in region.loops() {
            count = count
                .checked_add(lp.segs.len())
                .ok_or(MeshError::BudgetExceeded {
                    stage: "mesh sketch entities",
                    limit: MAX_SEGMENTS,
                })?;
            if count > MAX_SEGMENTS {
                return Err(MeshError::BudgetExceeded {
                    stage: "mesh sketch entities",
                    limit: MAX_SEGMENTS,
                });
            }
            let fields = lp
                .segs
                .len()
                .checked_mul(crate::prism::profile::MAX_BEZIER_CTRL)
                .and_then(|n| n.checked_mul(2))
                .and_then(|n| n.checked_add(lp.segs.len()))
                .and_then(|n| n.checked_add(lp.segs.len()))
                .ok_or_else(|| invalid("sketch profile read count overflow"))?;
            work.spend(k, fields)?;
        }
    }
    crate::prism::profile::check_regions(regions.iter(), 1e-9, k.tolerances.zone_tol_3d).map_err(
        |error| MeshError::InvalidInput {
            stage: "mesh sketch entities",
            detail: format!("invalid fitted profile: {error:?}"),
        },
    )?;
    admit_sketch_copy_with_work(k, work, SketchCopyPart::Drawing, 0)?;
    let mut geometry = Vec::new();
    for lp in regions.iter().flat_map(Region2::loops) {
        work.spend(k, 1)?;
        if let Some(circle) = whole_circle(k, work, lp)? {
            admit_sketch_copy_with_work(k, work, SketchCopyPart::Drawing, 1)?;
            geometry.push(circle);
            continue;
        }
        for segment in &lp.segs {
            // The fixed inline Seg2 value may copy all Bezier coordinates.
            work.spend(k, crate::prism::profile::MAX_BEZIER_CTRL * 2 + 2)?;
            match *segment {
                Seg2::Line { a, b } => {
                    admit_sketch_copy_with_work(k, work, SketchCopyPart::Drawing, 1)?;
                    geometry.push(SketchGeometry::Line { a, b });
                }
                Seg2::Arc { center, sweep, .. } => {
                    let (a, b) = if sweep > 0.0 {
                        (segment.start(), segment.end())
                    } else {
                        (segment.end(), segment.start())
                    };
                    admit_sketch_copy_with_work(k, work, SketchCopyPart::Drawing, 1)?;
                    geometry.push(SketchGeometry::Arc { center, a, b });
                }
                _ => {
                    return Err(invalid(
                        "this fitted curve kind cannot be imported as a line, arc or circle",
                    ))
                }
            }
        }
    }
    Ok(SketchDrawing {
        geometry,
        join_tolerance: (tolerance * 0.01).clamp(1e-9, 0.01),
    })
}
