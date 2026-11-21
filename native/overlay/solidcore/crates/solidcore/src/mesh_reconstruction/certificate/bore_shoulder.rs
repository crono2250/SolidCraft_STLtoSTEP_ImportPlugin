//! A certified planar shoulder between two distinct radial bore rings.
//! Both full source bands and their exact interfaces bind one axial chart.
use super::super::work::MeshWork;
use super::exact_geometry as x;
use super::radial_source::SourceRadialPatch;
use super::radial_stack::{opposite_ring, rim_at};
use super::source_cells::SourceCellPatch;
use crate::blend::fillet_section::interval::Ivl;
use crate::{Kernel, Result, SolidError};

fn refused(reason: &'static str) -> SolidError {
    SolidError::Unsupported {
        operation: "mesh_reconstruction::certificate::bore_shoulder",
        reason,
    }
}

/// Partition and bound the full source annulus. The boundaries must be the
/// very same reversed original edge cycles as the adjacent diameter bands.
pub(crate) fn prove_source_bore_shoulder_with_work(
    k: &Kernel,
    w: &MeshWork,
    lower: &SourceRadialPatch<'_, '_, '_, '_>,
    upper: &SourceRadialPatch<'_, '_, '_, '_>,
    cells: &SourceCellPatch,
) -> Result<f64> {
    let a = lower.claim();
    let b = upper.claim();
    let z = a.law.height[1];
    if z != b.law.height[0]
        || a.center != b.center
        || !a.concave
        || !b.concave
        || !core::ptr::eq(lower.source(), upper.source())
    {
        return Err(refused("bore shoulder does not join one axis and height"));
    }
    let ar = Ivl::from(a.law.radius[1]);
    let br = Ivl::from(b.law.radius[0]);
    let gap = br - ar;
    if gap.lo <= 0. && gap.hi >= 0. {
        return Err(refused(
            "a bore shoulder requires distinct proven diameters",
        ));
    }
    if !gap.is_finite()
        || !(Ivl::from(gap.lo.abs().min(gap.hi.abs()))
            - Ivl::from(lower.local_upper())
            - Ivl::from(upper.local_upper()))
        .is_positive()
    {
        return Err(refused("the moving bore shoulder can disappear or invert"));
    }
    let expected = if gap.is_positive() { 1 } else { -1 };
    let source = lower.source();
    for &id in &cells.triangles {
        w.spend_core(k, 2048)?;
        w.reserve_cells_core(k, 256)?;
        let Some(&Some([a, b, c])) = source.world().source().aliases.get(id) else {
            return Err(refused("original shoulder triangle is absent"));
        };
        let [a, b, c] = [
            source.row_with_work(k, w, a)?,
            source.row_with_work(k, w, b)?,
            source.row_with_work(k, w, c)?,
        ];
        if [a, b, c].iter().any(|x| x[2] != z) {
            return Err(refused(
                "whole original bore shoulder is not on the common plane",
            ));
        }
        let sign = (|| {
            let p = x::point(a)?;
            let q = x::difference(&x::point(b)?, &p)?;
            let r = x::difference(&x::point(c)?, &p)?;
            let [_, _, area] = x::cross(&q, &r)?;
            x::sign(&area)
        })();
        if sign != Some(expected) {
            return Err(refused(
                "original annular shoulder faces the wrong material side",
            ));
        }
    }
    let [a, b] = cells.rims.as_slice() else {
        return Err(refused("bore shoulder must be a complete two-rim annulus"));
    };
    let first = rim_at(k, w, lower, z)?;
    let second = rim_at(k, w, upper, z)?;
    if !(opposite_ring(k, w, a, first)? && opposite_ring(k, w, b, second)?
        || opposite_ring(k, w, a, second)? && opposite_ring(k, w, b, first)?)
    {
        return Err(refused(
            "shoulder loops are not the exact shared source rings",
        ));
    }
    // Each complete bore rim has a degree-one radial link; the rings remain
    // nested throughout their motion. The embedded planar annulus between
    // them is covered ray by ray by linear interpolation of both radii.
    Ok(lower.world_upper().max(upper.world_upper()))
}
