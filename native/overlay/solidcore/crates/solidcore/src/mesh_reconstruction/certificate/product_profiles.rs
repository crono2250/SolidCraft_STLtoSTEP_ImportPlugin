//! ONE lower model and its exact translated upper model, bound to one candidate.
//!
//! Both original cap drafts already bind all actual root/edge/native-zone inputs.
//! Independently match every high original alias to its proved low partner, then
//! match EVERY source cell's directed edge and exact `source_unit` partition. Native
//! face/root order is never an identity. Reverse orientation is an event decided
//! from original aliases, not a failed fit fallback. Translate the ALREADY proved
//! low controls by exact `SourcePrism` D, and let the SAME `NativeProfile` model checker
//! verify complete upper source/actual curve domains, balls/tubes, embedding and
//! tolerance. No independent upper model is silently accepted as the product.
//!
//! This sufficient partition class requires matching stored source boundaries
//! (including exact representable reversal). Unmatched partitions refuse; no new
//! rounded intermediate source vertex or guessed parameter identity is introduced.
//! Upper/cap S charts, ALL side faces, native material/region forest and final
//! canonical unchanged-body acceptance still must consume this common-model token.
//! Deviations: none. No recursion; same workflow `MeshWork` and existing model checks.
use super::super::work::MeshWork;
use super::exact_geometry as x;
use super::native_profile::{
    prove_native_profile_model_with_work, NativeProfile, NativeProfileDraft,
};
use super::sewn_curve::ProjectivePoint;
use crate::{Kernel, Result, SolidError};
use std::collections::{BTreeMap, BTreeSet};
const OP: &str = "mesh_reconstruction::certificate::product_profiles";
fn refused(reason: &'static str) -> SolidError {
    SolidError::Unsupported {
        operation: OP,
        reason,
    }
}
fn invariant(reason: &'static str) -> SolidError {
    SolidError::PortInvariant {
        operation: OP,
        reason,
    }
}
fn unit(v: f64) -> u64 {
    if v == 0. {
        0
    } else {
        v.to_bits()
    }
}
pub(crate) fn exact_source_unit_complement(v: f64) -> Option<f64> {
    if !v.is_finite() || !(0.0..=1.0).contains(&v) {
        return None;
    }
    let r = 1. - v;
    x::sub(&x::scalar(1.)?, &x::scalar(v)?)
        .and_then(|d| x::sub(&d, &x::scalar(r)?))
        .is_some_and(|d| x::zero(&d))
        .then_some(r)
}
fn translate(
    k: &Kernel,
    work: &MeshWork,
    controls: &[ProjectivePoint],
    d: &x::P,
    reverse: bool,
) -> Result<Vec<ProjectivePoint>> {
    let mut out = Vec::new();
    for index in 0..controls.len() {
        work.spend_core(k, 1)?;
        let index = if reverse {
            controls
                .len()
                .checked_sub(index)
                .and_then(|i| i.checked_sub(1))
                .ok_or_else(|| invariant("reversed model control index underflow"))?
        } else {
            index
        };
        let p = controls
            .get(index)
            .ok_or_else(|| invariant("proved low model control missing"))?;
        let mut xyz = Vec::new();
        for (h, d) in p.xyz.iter().zip(d) {
            xyz.push(x::mul(d, &p.w).and_then(|v| x::add(h, &v)).ok_or_else(|| {
                refused("exact common model translation outside arithmetic range")
            })?);
        }
        let [Some(a), Some(b), Some(c)] = [xyz.first(), xyz.get(1), xyz.get(2)] else {
            return Err(invariant("translated common model lacks coordinates"));
        };
        work.reserve_cells_core(k, 1)?;
        out.push(ProjectivePoint {
            xyz: [a.clone(), b.clone(), c.clone()],
            w: p.w.clone(),
        });
    }
    Ok(out)
}
/// Verified correspondence of ONE original source cell across the product.
/// It is recorded only after alias/partition checks and the whole upper model proof.
/// Indices identify immutable proven cap graph cells, never native face ordering.
pub(crate) struct ProductCell {
    pub(crate) lower: [usize; 2],
    pub(crate) upper: [usize; 2],
    pub(crate) reverse: bool,
}
pub(crate) struct ProductProfiles<'l, 'ld, 'ud, 'g, 's, 'raw> {
    lower: &'l NativeProfile<'ld, 'g, 's, 'raw>,
    upper: NativeProfile<'ud, 'g, 's, 'raw>,
    cells: Vec<ProductCell>,
}
impl<'l, 'ld, 'ud, 'g, 's, 'raw> ProductProfiles<'l, 'ld, 'ud, 'g, 's, 'raw> {
    pub(crate) fn lower(&self) -> &'l NativeProfile<'ld, 'g, 's, 'raw> {
        self.lower
    }
    pub(crate) fn cells(&self) -> &[ProductCell] {
        &self.cells
    }
    pub(crate) fn upper(&self) -> &NativeProfile<'ud, 'g, 's, 'raw> {
        &self.upper
    }
}
/// One immutable source product + one final candidate/complex. Pointer equality
/// binds borrowed objects ONLY; every original geometric/parameter relation below
/// is independently verified. This is not a pointer hash or a geometry identity.
pub(crate) fn prove_product_profiles_with_work<'l, 'ld, 'ud, 'g, 's, 'raw>(
    k: &Kernel,
    work: &MeshWork,
    lower: &'l NativeProfile<'ld, 'g, 's, 'raw>,
    upper: &'ud NativeProfileDraft<'g, 's, 'raw>,
) -> Result<ProductProfiles<'l, 'ld, 'ud, 'g, 's, 'raw>> {
    work.spend_core(k, 0)?;
    let low = lower.draft();
    if low.level() != 0 || upper.level() != 1 {
        return Err(refused(
            "common product requires proven low and high source ends",
        ));
    }
    if !low.source().same_owner(upper.source()) || !core::ptr::eq(low.complex(), upper.complex()) {
        return Err(refused(
            "common profile drafts are not bound to the same immutable source/actual complex",
        ));
    }
    let source = low.source();
    let mut directions = BTreeMap::new();
    let mut cells = BTreeMap::new();
    let mut total = 0usize;
    for (ri, graph) in low.graphs().iter().enumerate() {
        for (ci, cell) in graph.cells.iter().enumerate() {
            work.spend_core(k, 1)?;
            let aliases = low
                .source_aliases()
                .get(ri)
                .ok_or_else(|| invariant("proved low graph alias ring missing"))?;
            let &a = aliases
                .get(cell.claim.source_edge)
                .ok_or_else(|| invariant("proved low source cell alias missing"))?;
            let next = cell
                .claim
                .source_edge
                .checked_add(1)
                .ok_or_else(|| invariant("low source edge overflow"))?;
            let &b = aliases
                .get(next)
                .or_else(|| aliases.first())
                .ok_or_else(|| invariant("proved low next source alias missing"))?;
            work.reserve_cells_core(k, 1)?;
            if let Some(old) = directions.insert((a.min(b), a.max(b)), (a, b)) {
                if old != (a, b) {
                    return Err(invariant(
                        "proved low source edge has inconsistent directions",
                    ));
                }
            }
            let [s, e] = cell.claim.source_unit;
            work.reserve_output_core(k, 1)?;
            if cells.insert((a, b, unit(s), unit(e)), (ri, ci)).is_some() {
                return Err(invariant(
                    "proved low source cells duplicate a parameter domain",
                ));
            }
            total = total
                .checked_add(1)
                .ok_or_else(|| refused("low source cell count overflow"))?;
        }
    }
    let mut used = BTreeSet::new();
    let mut model = Vec::new();
    let mut correspondence = Vec::new();
    for (upper_ri, graph) in upper.graphs().iter().enumerate() {
        let mut row = Vec::new();
        for (upper_ci, cell) in graph.cells.iter().enumerate() {
            work.spend_core(k, 1)?;
            let aliases = upper
                .source_aliases()
                .get(upper_ri)
                .ok_or_else(|| invariant("proved upper graph alias ring missing"))?;
            let &start = aliases
                .get(cell.claim.source_edge)
                .ok_or_else(|| invariant("proved upper source cell alias missing"))?;
            let next = cell
                .claim
                .source_edge
                .checked_add(1)
                .ok_or_else(|| invariant("upper source edge overflow"))?;
            let &end = aliases
                .get(next)
                .or_else(|| aliases.first())
                .ok_or_else(|| invariant("proved upper next source alias missing"))?;
            let a = *source
                .upper_to_lower()
                .get(&start)
                .ok_or_else(|| invariant("proved upper alias lacks low partner"))?;
            let b = *source
                .upper_to_lower()
                .get(&end)
                .ok_or_else(|| invariant("proved upper next alias lacks low partner"))?;
            let &(la, lb) = directions
                .get(&(a.min(b), a.max(b)))
                .ok_or_else(|| refused("high source edge has no complete low partner"))?;
            let reverse = if (a, b) == (la, lb) {
                false
            } else if (a, b) == (lb, la) {
                true
            } else {
                return Err(invariant(
                    "undirected original edge key returned another edge",
                ));
            };
            let [s, e] = cell.claim.source_unit;
            let [s, e] = if reverse {
                [
                    exact_source_unit_complement(e).ok_or_else(|| {
                        refused("source cell reversal needs an exact parameter partition")
                    })?,
                    exact_source_unit_complement(s).ok_or_else(|| {
                        refused("source cell reversal needs an exact parameter partition")
                    })?,
                ]
            } else {
                [s, e]
            };
            let &(ri, ci) = cells
                .get(&(la, lb, unit(s), unit(e)))
                .ok_or_else(|| refused("upper/lower complete source cell partitions differ"))?;
            work.reserve_cells_core(k, 1)?;
            if !used.insert((ri, ci)) {
                return Err(refused(
                    "a low model source cell is duplicated in the upper cap",
                ));
            }
            let lower_controls = lower
                .controls_3d()
                .get(ri)
                .and_then(|r| r.get(ci))
                .ok_or_else(|| invariant("proved lower model cell missing"))?;
            let controls = translate(k, work, lower_controls, source.translation(), reverse)?;
            work.reserve_output_core(k, 1)?;
            correspondence.push(ProductCell {
                lower: [ri, ci],
                upper: [upper_ri, upper_ci],
                reverse,
            });
            work.reserve_cells_core(k, 1)?;
            row.push(controls);
        }
        work.reserve_cells_core(k, 1)?;
        model.push(row);
    }
    if used.len() != total {
        return Err(refused(
            "some low common model cell is absent from upper cap",
        ));
    }
    let upper = prove_native_profile_model_with_work(k, work, upper, model)?;
    work.spend_core(k, 0)?;
    Ok(ProductProfiles {
        lower,
        upper,
        cells: correspondence,
    })
}
