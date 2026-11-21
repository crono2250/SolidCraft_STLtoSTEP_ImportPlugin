//! Complete retained-source coverage for a standalone axial cone or frustum.
//!
//! The radial side already proves degree one at every height. Classify each
//! remaining retained triangle as part of an exactly horizontal end disk.
//! The complete original cell partition cancels every boundary edge. Each
//! positive-radius end has exactly the same reversed edge cycle as the side and
//! all its triangles have the correct strict orientation. Since the original
//! source motion proved an embedded complex and the axial chart is invertible,
//! that planar one-boundary component fills exactly its polygon by planar degree.
//! Each cap can move radially by scaling along each ray to its moved rim. Its
//! displacement never exceeds the rim displacement. The one source motion and
//! whole side bounds therefore cover the entire filled solid boundary.
//!
//! Actual Native surface, trim, edge-tube and complete target-body proof remain
//! mandatory. Deviations: none. Iterative exact source-cell partition.
use super::super::work::MeshWork;
use super::exact_geometry as x;
use super::radial_source::SourceRadialPatch;
use super::radial_stack::{opposite_ring, rim_at};
use super::source_cells::{source_cells_with_work, SourceCellsCover};
use crate::{Kernel, Result, SolidError};
use std::collections::BTreeSet;

const OP: &str = "mesh_reconstruction::certificate::radial_solid_source";
fn refusal(reason: &'static str) -> SolidError {
    SolidError::Unsupported {
        operation: OP,
        reason,
    }
}

pub(crate) struct SourceRadialSolid<'a, 's, 'v, 'f, 'r> {
    side: &'a SourceRadialPatch<'s, 'v, 'f, 'r>,
    filled_caps: usize,
}

impl<'a, 's, 'v, 'f, 'r> SourceRadialSolid<'a, 's, 'v, 'f, 'r> {
    pub(crate) fn side(&self) -> &'a SourceRadialPatch<'s, 'v, 'f, 'r> {
        self.side
    }
    pub(crate) fn filled_caps(&self) -> usize {
        self.filled_caps
    }
}

pub(crate) fn prove_source_radial_solid_with_work<'a, 's, 'v, 'f, 'r>(
    k: &Kernel,
    w: &MeshWork,
    side: &'a SourceRadialPatch<'s, 'v, 'f, 'r>,
) -> Result<SourceRadialSolid<'a, 's, 'v, 'f, 'r>> {
    w.spend_core(k, 1)?;
    if side.claim().concave {
        return Err(refusal("a standalone radial solid needs its outward side"));
    }
    let [lo, hi] = side.claim().law.height;
    let [r0, r1] = side.claim().law.radius;
    let mut side_ids = BTreeSet::new();
    let mut side_claim = Vec::new();
    for &id in &side.claim().triangles {
        w.spend_core(k, 4_096)?;
        w.reserve_cells_core(k, 3)?;
        if !side_ids.insert(id) {
            return Err(refusal("retained side triangle appears twice"));
        }
        side_claim.push(
            u32::try_from(id)
                .map_err(|_| refusal("triangle index exceeds the supported inventory"))?,
        );
    }
    let source = side.source();
    let mut lower = Vec::new();
    let mut upper = Vec::new();
    for (id, [a, b, c]) in source.world().triangles() {
        w.spend_core(k, 4_096)?;
        if side_ids.contains(&id) {
            continue;
        }
        let [ax, ay, ah] = source.row_with_work(k, w, a)?;
        let [bx, by, bh] = source.row_with_work(k, w, b)?;
        let [cx, cy, ch] = source.row_with_work(k, w, c)?;
        let (disk, expected) = if ah == lo && bh == lo && ch == lo && r0 > 0. {
            (&mut lower, -1)
        } else if ah == hi && bh == hi && ch == hi && r1 > 0. {
            (&mut upper, 1)
        } else {
            return Err(refusal(
                "a retained source cell is outside the side and its finite end disks",
            ));
        };
        w.reserve_cells_core(k, 256)?;
        let sense = (|| {
            let a = x::point([ax, ay, 0.])?;
            let b = x::difference(&x::point([bx, by, 0.])?, &a)?;
            let c = x::difference(&x::point([cx, cy, 0.])?, &a)?;
            let [_, _, area] = x::cross(&b, &c)?;
            x::sign(&area)
        })();
        if sense != Some(expected) {
            return Err(refusal(
                "a whole planar end triangle has invalid material orientation",
            ));
        }
        disk.push(
            u32::try_from(id)
                .map_err(|_| refusal("triangle index exceeds the supported inventory"))?,
        );
    }
    let end_levels = [lo, hi]
        .into_iter()
        .zip([r0, r1])
        .filter_map(|(h, r)| (r > 0.).then_some(h));
    let mut groups = vec![side_claim];
    for group in [lower, upper] {
        if !group.is_empty() {
            groups.push(group);
        }
    }
    let cover = match source_cells_with_work(k, w, source.world().source(), &groups)? {
        SourceCellsCover::Proven(cover) => cover,
        SourceCellsCover::Undecided(reason) => return Err(refusal(reason)),
    };
    let expected_count = usize::from(r0 > 0.) + usize::from(r1 > 0.);
    if cover.patches.len() != expected_count + 1 || side.rims().len() != expected_count {
        return Err(refusal(
            "the source has the wrong number of filled end disks",
        ));
    }
    for (cap, level) in cover.patches.iter().skip(1).zip(end_levels) {
        let [single] = cap.rims.as_slice() else {
            return Err(refusal("a source end disk has extra boundary cycles"));
        };
        if !opposite_ring(k, w, rim_at(k, w, side, level)?, single)? {
            return Err(refusal(
                "the end disk is not joined to the same original side rim",
            ));
        }
    }
    Ok(SourceRadialSolid {
        side,
        filled_caps: expected_count,
    })
}
