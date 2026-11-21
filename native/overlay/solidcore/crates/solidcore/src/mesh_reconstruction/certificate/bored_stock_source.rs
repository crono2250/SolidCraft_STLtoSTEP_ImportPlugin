//! Full original rectangular stock walls, caps and bore-band material coverage.
//!
//! Every retained cell belongs to one specific outer planar patch or radial
//! wall band. Each cap has exactly its rectangle and the reversed source rings
//! of all through-holes. Strict wall and inter-bore clearance yields disjoint
//! cap collars on which each hole's radial boundary motion extends by monotone
//! interpolation to the fixed outside. Thus the entire cap material moves at
//! most the maximum of the rim bounds, retaining holes and wall thickness.
//! Deviations: none. Full cells and one shared MeshWork.

use super::super::work::MeshWork;
use super::bored_stock_proposal::BoredStockProposal;
use super::exact_geometry as x;
use super::radial_frame::AxialSourceView;
use super::radial_source::prove_source_radial_patch_with_work;
use super::radial_stack::{
    opposite_ring, prove_source_radial_stack_with_work, rim_at,
    separate_source_radial_stacks_with_work,
};
use super::radial_stock::prove_convex_stock_radial_collar_with_work;
use super::source_cells::{source_cells_with_work, SourceCellsCover};
use crate::{Kernel, Result, SolidError};
use std::collections::BTreeSet;

fn refused(reason: &'static str) -> SolidError {
    SolidError::Unsupported {
        operation: "mesh_reconstruction::certificate::bored_stock_source",
        reason,
    }
}

/// Whole axis-aligned rectangle boundary from four interval partitions.
/// Collinear subdivisions may differ along each source wall and cap.
fn rectangular_ring(
    k: &Kernel,
    w: &MeshWork,
    view: &AxialSourceView<'_, '_, '_>,
    rim: &[u32],
    axes: [usize; 2],
    bounds: [[f64; 3]; 2],
) -> Result<bool> {
    let [ix, iy] = axes;
    let [[x0, y0], [x1, y1]] = bounds.map(|p| [p[ix], p[iy]]);
    let mut intervals: [Vec<[f64; 2]>; 4] = core::array::from_fn(|_| Vec::new());
    for (&a, &b) in rim.iter().zip(rim.iter().cycle().skip(1)) {
        w.spend_core(k, 32)?;
        w.reserve_cells_core(k, 2)?;
        let [p, q] = [view.row_with_work(k, w, a)?, view.row_with_work(k, w, b)?];
        let [x, z] = [p[ix], q[ix]];
        let [y, v] = [p[iy], q[iy]];
        let (side, a, b) = if x == z && y != v {
            (
                if x == x0 {
                    0
                } else if x == x1 {
                    1
                } else {
                    return Ok(false);
                },
                y,
                v,
            )
        } else if y == v && x != z {
            (
                if y == y0 {
                    2
                } else if y == y1 {
                    3
                } else {
                    return Ok(false);
                },
                x,
                z,
            )
        } else {
            return Ok(false);
        };
        intervals[side].push([a.min(b), a.max(b)]);
    }
    for (r, [lo, hi]) in intervals
        .iter_mut()
        .zip([[y0, y1], [y0, y1], [x0, x1], [x0, x1]])
    {
        w.spend_core(k, r.len().saturating_mul(64))?;
        r.sort_by(|a, b| a[0].total_cmp(&b[0]));
        let mut end = lo;
        for &[a, b] in &*r {
            if a != end || a >= b || b > hi {
                return Ok(false);
            }
            end = b;
        }
        if end != hi {
            return Ok(false);
        }
    }
    Ok(true)
}

pub(crate) fn prove_bored_stock_source_with_work(
    k: &Kernel,
    w: &MeshWork,
    view: &AxialSourceView<'_, '_, '_>,
    proposal: &BoredStockProposal,
    tolerance: f64,
) -> Result<f64> {
    if !core::ptr::eq(view.model().proposal(), &proposal.chart) {
        return Err(refused(
            "stock and bore claims do not bind the same source chart",
        ));
    }
    let ids = |group: &Vec<usize>| -> Result<Vec<u32>> {
        w.reserve_cells_core(k, group.len())?;
        group
            .iter()
            .map(|&i| u32::try_from(i).map_err(|_| refused("stock original cell index overflow")))
            .collect()
    };
    let mut groups = proposal
        .planes
        .iter()
        .map(ids)
        .collect::<Result<Vec<_>>>()?;
    let mut bore_faces = Vec::new();
    for bore in &proposal.bores {
        w.reserve_output_core(k, bore.len())?;
        let mut faces = Vec::new();
        for band in bore {
            groups.push(ids(&band.triangles)?);
            faces.push(prove_source_radial_patch_with_work(
                k, w, view, band, tolerance,
            )?);
        }
        bore_faces.push(faces);
    }
    let stacks = bore_faces
        .iter()
        .map(|faces| prove_source_radial_stack_with_work(k, w, faces))
        .collect::<Result<Vec<_>>>()?;
    let source = match source_cells_with_work(k, w, view.world().source(), &groups)? {
        SourceCellsCover::Proven(s) => s,
        SourceCellsCover::Undecided(reason) => return Err(refused(reason)),
    };
    let [lo, hi] = proposal.bounds;
    let [a, b, _] = lo;
    let [c, d, _] = hi;
    let outline = [[a, b], [c, b], [c, d], [a, d]];
    let mut upper = view.world_error_upper(0.)?;
    for (i, stack) in stacks.iter().enumerate() {
        // The outer walls are exactly fixed in local coordinates. Prior source
        // motion is accounted separately when mapping this model to raw arrays.
        prove_convex_stock_radial_collar_with_work(k, w, &outline, 0., stack)?;
        for earlier in stacks.iter().take(i) {
            separate_source_radial_stacks_with_work(k, w, earlier, stack)?;
        }
        upper = upper.max(stack.world_upper());
    }
    for (i, (cells, ids)) in source.patches.iter().zip(&proposal.planes).enumerate() {
        let coordinate = i / 2;
        let level = proposal.bounds[i % 2][coordinate];
        let axes = [(coordinate + 1) % 3, (coordinate + 2) % 3];
        let expected = if i % 2 == 0 { -1 } else { 1 };
        for &cell in ids {
            w.spend_core(k, 4096)?;
            w.reserve_cells_core(k, 256)?;
            let &Some([a, b, c]) = view
                .world()
                .source()
                .aliases
                .get(cell)
                .ok_or_else(|| refused("stock original plane cell missing"))?
            else {
                return Err(refused("stock plane names an omitted original cell"));
            };
            let points = [
                view.row_with_work(k, w, a)?,
                view.row_with_work(k, w, b)?,
                view.row_with_work(k, w, c)?,
            ];
            if points.iter().any(|p| {
                p[coordinate] != level
                    || p.iter()
                        .zip(lo.into_iter().zip(hi))
                        .any(|(&x, (a, b))| x < a || x > b)
            }) {
                return Err(refused("stock cell does not lie on its finite exact plane"));
            }
            let sense = (|| {
                let [a, b, c] = points.map(x::point);
                let a = a?;
                let d = x::difference(&b?, &a)?;
                let e = x::difference(&c?, &a)?;
                x::sign(x::cross(&d, &e)?.get(coordinate)?)
            })();
            if sense != Some(expected) {
                return Err(refused("stock plane cells have the wrong material side"));
            }
        }
        let mut used = BTreeSet::new();
        for (j, rim) in cells.rims.iter().enumerate() {
            if rectangular_ring(k, w, view, rim, axes, proposal.bounds)? {
                if !used.is_empty() {
                    return Err(refused("duplicate stock rectangle rim"));
                }
                used.insert(j);
            }
        }
        if used.len() != 1 {
            return Err(refused(
                "stock plane does not have one complete outer rectangle",
            ));
        }
        if coordinate == 2 {
            for stack in &stacks {
                let band = if i % 2 == 0 {
                    stack.patches().first()
                } else {
                    stack.patches().last()
                }
                .ok_or_else(|| refused("bore stack lost its cap band"))?;
                let hole = rim_at(k, w, band, level)?;
                let mut matched = None;
                for (j, rim) in cells.rims.iter().enumerate() {
                    if !used.contains(&j) && opposite_ring(k, w, rim, hole)? {
                        if matched.replace(j).is_some() {
                            return Err(refused("two cap loops claim one through bore"));
                        }
                    }
                }
                used.insert(
                    matched.ok_or_else(|| refused("cap does not cover a full through-hole rim"))?,
                );
            }
        }
        if used.len() != cells.rims.len() {
            return Err(refused("unattributed original stock wall or cap boundary"));
        }
    }
    Ok(upper)
}
