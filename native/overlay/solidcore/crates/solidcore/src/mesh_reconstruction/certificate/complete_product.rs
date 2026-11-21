//! Complete single-source-component product witness and native material binding.
//!
//! Shared geometry is factored below into ONE private cap/side/native-CW consumer.
//! The original wrapper still requires the SAME original positive embedded source
//! component and adds its motion exactly once. A distinct recipe wrapper accepts
//! only an opaque independently proved finite rectangle-product domain; it cannot
//! supply any original source token/identity, and needs separate selected-region
//! finite membership before the fitted-tool result. No source predicate is erased.
//!
//! This consumes BOTH whole actual cap S/UV charts and EVERY actual side support,
//! full trim, generator tube and native-vertex-zone proof on ONE immutable common
//! model. No actual face or source cap-edge cell may be unmatched or duplicated.
//! Every original cap rim has the ORIGINAL boundary orientation (low −N, high +N),
//! rather than independently reversing loops to fit an actual hole/outer ordering.
//!
//! `SourcePrism` proves the entire SAME exact-view connected embedded boundary is a true
//! finite product of its complete filled planar cap and interval D. `NativeProfile`
//! gives one complete embedded/nested Jordan rim family, preserving all original
//! source cells; `ProductProfiles` gives its EXACT translated copy. Filled cap charts
//! bind those same boundaries, while each side is their product and generators sew
//! at the SAME exact model joins. Consequently the chosen exact product is one
//! embedded closed oriented boundary with the SAME complete native CW incidence.
//! A proven whole-source motion retains the original alias complex and material
//! isotopy. Its displacement bound is added ONCE, outward, after the maximum of
//! all endpoint-to-actual boundary bounds. Raw and endpoint coordinates are never
//! mixed in a cap, profile, normal, side or parameter correspondence.
//! This is stronger than a component/genus/volume count: all geometry and cell maps
//! are consumed before the native region test. The original positive component and
//! oriented outward cap/side proofs bind its interior to the single actual material
//! region; every void-side actual use must border the actual infinite void. No
//! hidden finite void/material region, face, edge cell or reversed source hole is
//! permitted. Holes and thin walls remain in the SAME embedded rim family.
//!
//! The final public constructor must still check its normal standing native solid
//! validity/positive-volume contract and exact raw/prepared/final identity. This
//! immutable private witness supplies its geometry/topology/material obligation;
//! it is not an alternate public adoption entry or a serialized cache.
//!
//! Strict class: one connected original product, one actual Plane face per cap,
//! each actual side a proved four-use full rectangle. Multiple products/cavities,
//! raw sources without a proved motion into that SAME product, and multi-axis
//! milled boundaries, require their own
//! complete theorem, never a retry after this one refuses. No approximation samples.
//! Deviations: none. No recursion; same workflow `MeshWork` and actual target limits.
use super::super::work::MeshWork;
use super::product_cap::ProductCap;
use super::product_profiles::ProductProfiles;
use super::product_side_band::ProductSideBand;
use super::source_topology::SourceManifold;
use crate::blend::fillet_section::interval::Ivl;
use crate::mass::integrator::properties::region_material;
use crate::topology::{
    brep, edgeuse::p1 as eu, face::p2 as face, Brep, EdgeId, FaceId, FaceuseId, RegionId,
};
use crate::{Kernel, Result, SolidError};
use std::collections::BTreeSet;
const OP: &str = "mesh_reconstruction::certificate::complete_product";
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
pub(crate) struct CommonProductWitness<'c, 'p, 'l, 'ld, 'ud, 'g, 's, 'raw> {
    profiles: &'p ProductProfiles<'l, 'ld, 'ud, 'g, 's, 'raw>,
    _lower: &'c ProductCap<'l, 'ld, 'g, 's, 'raw>,
    _upper: &'c ProductCap<'p, 'ud, 'g, 's, 'raw>,
    _sides: &'c [ProductSideBand<'p, 'l, 'ld, 'ud, 'g, 's, 'raw>],
    endpoint_boundary_error_upper: f64,
    boundary_error_upper: f64,
}
impl<'g, 'raw> CommonProductWitness<'_, '_, '_, '_, '_, 'g, '_, 'raw> {
    pub(crate) fn candidate(&self) -> &'g Brep {
        self.profiles.lower().draft().complex().brep()
    }
    pub(crate) fn endpoint_boundary_error_upper(&self) -> f64 {
        self.endpoint_boundary_error_upper
    }
    pub(crate) fn boundary_error_upper(&self) -> f64 {
        self.boundary_error_upper
    }
}
fn cap_edges(
    k: &Kernel,
    work: &MeshWork,
    profiles: &ProductProfiles<'_, '_, '_, '_, '_, '_>,
    high: bool,
) -> Result<BTreeSet<EdgeId>> {
    let p = if high {
        profiles.upper()
    } else {
        profiles.lower()
    };
    let d = p.draft();
    let patch = d
        .complex()
        .patches
        .get(d.patch())
        .ok_or_else(|| invariant("proved cap patch missing"))?;
    let mut out = BTreeSet::new();
    for rim in &patch.rims {
        for usage in rim {
            work.spend_core(k, 1)?;
            work.reserve_cells_core(k, 1)?;
            if !out.insert(usage.edge) {
                return Err(refused(
                    "one common cap edge occurs more than once in its native rim family",
                ));
            }
        }
    }
    Ok(out)
}
fn cap_use(profiles: &ProductProfiles<'_, '_, '_, '_, '_, '_>, high: bool) -> Result<FaceuseId> {
    let p = if high {
        profiles.upper()
    } else {
        profiles.lower()
    };
    let d = p.draft();
    d.complex()
        .patches
        .get(d.patch())
        .and_then(|p| p.rims.first())
        .and_then(|r| r.first())
        .map(|u| u.faceuse)
        .ok_or_else(|| invariant("proved cap has no native material use"))
}
fn regions(b: &Brep, u: FaceuseId, f: FaceId) -> Result<(RegionId, RegionId)> {
    let record = b.faceuse(u)?;
    if record.face != Some(f) {
        return Err(invariant("proven product face use owner changed"));
    }
    let mate = record
        .mate
        .ok_or_else(|| refused("actual product face has no mate"))?;
    if b.faceuse(mate)?.face != Some(f) || b.faceuse(mate)?.mate != Some(u) {
        return Err(refused("actual product face mates inconsistent"));
    }
    let (Some(v), Some(m)) = (eu::faceuse_region(b, u)?, eu::faceuse_region(b, mate)?) else {
        return Err(refused("actual product face has missing regions"));
    };
    let (Some(a), Some(z)) = face::faceuses(b, f)? else {
        return Err(refused("actual product face has incomplete use pair"));
    };
    if !((a == u && z == mate) || (z == u && a == mate)) {
        return Err(refused("actual product face has extra or different uses"));
    }
    if region_material(b, v)? || !region_material(b, m)? {
        return Err(refused(
            "actual product material side differs from verified outward side",
        ));
    }
    Ok((v, m))
}
/// No fallback or candidate mutation: all tokens must borrow precisely the same
/// source/model/candidate. Native standing validity remains the final caller's gate.
fn common_product_with_work<'c, 'p, 'l, 'ld, 'ud, 'g, 's, 'raw>(
    k: &Kernel,
    work: &MeshWork,
    profiles: &'p ProductProfiles<'l, 'ld, 'ud, 'g, 's, 'raw>,
    lower: &'c ProductCap<'l, 'ld, 'g, 's, 'raw>,
    upper: &'c ProductCap<'p, 'ud, 'g, 's, 'raw>,
    sides: &'c [ProductSideBand<'p, 'l, 'ld, 'ud, 'g, 's, 'raw>],
    tolerance: f64,
) -> Result<CommonProductWitness<'c, 'p, 'l, 'ld, 'ud, 'g, 's, 'raw>> {
    work.spend_core(k, 0)?;
    if !tolerance.is_finite() || tolerance <= 0. {
        return Err(refused("complete product tolerance invalid"));
    }
    if !core::ptr::eq(lower.profile(), profiles.lower())
        || !core::ptr::eq(upper.profile(), profiles.upper())
    {
        return Err(refused(
            "filled cap proofs do not bind the SAME common model",
        ));
    }
    let low = profiles.lower().draft();
    let high = profiles.upper().draft();
    if low.level() != 0
        || high.level() != 1
        || low.source_senses().iter().any(|&s| s != -1)
        || high.source_senses().iter().any(|&s| s != 1)
    {
        return Err(refused(
            "complete original cap rim/material orientation differs from product ends",
        ));
    }
    let b = low.complex().brep();
    if lower.face() == upper.face() {
        return Err(refused(
            "the two product cap faces are the same native face",
        ));
    }
    let expected_low = cap_edges(k, work, profiles, false)?;
    let expected_high = cap_edges(k, work, profiles, true)?;
    let mut low_used = BTreeSet::new();
    let mut high_used = BTreeSet::new();
    let mut faces = BTreeSet::new();
    work.reserve_cells_core(k, 2)?;
    faces.insert(lower.face());
    faces.insert(upper.face());
    let mut error = lower.source_actual_upper().max(upper.source_actual_upper());
    for profile in [profiles.lower(), profiles.upper()] {
        let rim =
            (Ivl::from(profile.source_model_upper()) + Ivl::from(profile.actual_model_upper())).hi;
        error = error.max(rim);
    }
    let infinite = b
        .infinite_region()
        .ok_or_else(|| refused("actual product infinite region missing"))?;
    let mut material = None;
    for (u, f) in [
        (cap_use(profiles, false)?, lower.face()),
        (cap_use(profiles, true)?, upper.face()),
    ] {
        work.spend_core(k, 1)?;
        let (v, m) = regions(b, u, f)?;
        if v != infinite || material.is_some_and(|old| old != m) {
            return Err(refused(
                "actual cap region assignment differs from complete product material",
            ));
        }
        material = Some(m);
    }
    for side in sides {
        work.spend_core(k, 1)?;
        if !core::ptr::eq(side.profiles(), profiles) {
            return Err(refused("actual side proof belongs to another common model"));
        }
        let r = side.rectangle();
        if !core::ptr::eq(r.rebuilt, b) || r.edges.len() != 4 {
            return Err(refused(
                "actual side is not the same whole four-use product face",
            ));
        }
        work.reserve_cells_core(k, 3)?;
        let [a, z] = side.cap_edges();
        if !low_used.insert(a) || !high_used.insert(z) || !faces.insert(r.face) {
            return Err(refused(
                "a complete product face or native cap edge is duplicated",
            ));
        }
        let (v, m) = regions(b, r.faceuse, r.face)?;
        if v != infinite || Some(m) != material {
            return Err(refused(
                "actual side region assignment changes original product material",
            ));
        }
        if !(side.orientation_numerator_lower().is_finite()
            && side.orientation_numerator_lower() > 0.)
        {
            return Err(invariant("proved actual side orientation not positive"));
        }
        if !(side.model_orientation_numerator_lower().is_finite()
            && side.model_orientation_numerator_lower() > 0.)
        {
            return Err(invariant(
                "same sewn common model side orientation not positive",
            ));
        }
        error = error.max(side.source_actual_upper());
    }
    if low_used != expected_low || high_used != expected_high {
        return Err(refused(
            "some complete original/common cap edge has no actual side",
        ));
    }
    let mut actual_faces = BTreeSet::new();
    for &f in b.face_list() {
        work.spend_core(k, 1)?;
        work.reserve_cells_core(k, 1)?;
        actual_faces.insert(f);
    }
    if faces != actual_faces {
        return Err(refused(
            "some actual final face has no complete source/model cell",
        ));
    }
    let material = material.ok_or_else(|| invariant("proved product material region absent"))?;
    if material == infinite {
        return Err(refused("actual product has no distinct material interior"));
    }
    let mut actual_regions = BTreeSet::new();
    for r in brep::p1::regions(b, None)? {
        work.spend_core(k, 1)?;
        work.reserve_cells_core(k, 1)?;
        actual_regions.insert(r);
    }
    work.reserve_cells_core(k, 2)?;
    let assigned: BTreeSet<_> = [infinite, material].into_iter().collect();
    if actual_regions != assigned {
        return Err(refused(
            "some actual finite region has no original product material cell",
        ));
    }
    let endpoint_boundary_error_upper = error;
    if !error.is_finite() || error > tolerance {
        return Err(refused(
            "whole stored boundary product bound exceeds requested tolerance",
        ));
    }
    work.spend_core(k, 0)?;
    Ok(CommonProductWitness {
        profiles,
        _lower: lower,
        _upper: upper,
        _sides: sides,
        endpoint_boundary_error_upper,
        boundary_error_upper: error,
    })
}

/// Original-source acceptance wrapper. Source origin, embedded positive component,
/// SAME raw identity and prior displacement are never inferred from a recipe.
pub(crate) struct CompleteProductWitness<'c, 'p, 'l, 'ld, 'ud, 'g, 's, 'raw> {
    common: CommonProductWitness<'c, 'p, 'l, 'ld, 'ud, 'g, 's, 'raw>,
    source: &'s SourceManifold<'raw>,
    boundary_error_upper: f64,
}
impl<'g, 'raw> CompleteProductWitness<'_, '_, '_, '_, '_, 'g, '_, 'raw> {
    pub(crate) fn source(&self) -> &SourceManifold<'raw> {
        self.source
    }
    pub(crate) fn candidate(&self) -> &'g Brep {
        self.common.candidate()
    }
    pub(crate) fn endpoint_boundary_error_upper(&self) -> f64 {
        self.common.endpoint_boundary_error_upper()
    }
    pub(crate) fn boundary_error_upper(&self) -> f64 {
        self.boundary_error_upper
    }
}
pub(crate) fn complete_product_with_work<'c, 'p, 'l, 'ld, 'ud, 'g, 's, 'raw>(
    k: &Kernel,
    work: &MeshWork,
    profiles: &'p ProductProfiles<'l, 'ld, 'ud, 'g, 's, 'raw>,
    lower: &'c ProductCap<'l, 'ld, 'g, 's, 'raw>,
    upper: &'c ProductCap<'p, 'ud, 'g, 's, 'raw>,
    sides: &'c [ProductSideBand<'p, 'l, 'ld, 'ud, 'g, 's, 'raw>],
    tolerance: f64,
) -> Result<CompleteProductWitness<'c, 'p, 'l, 'ld, 'ud, 'g, 's, 'raw>> {
    work.spend_core(k, 0)?;
    let reference = profiles.lower().draft().source();
    let source = reference
        .original_source()
        .ok_or_else(|| refused("a finite recipe cannot supply an original source product proof"))?;
    if source.components.len() != 1
        || source.signed_volumes.len() != 1
        || !source
            .signed_volumes
            .first()
            .is_some_and(|v| v.is_finite() && v.is_positive())
    {
        return Err(refused(
            "complete product class requires one original positive embedded component",
        ));
    }
    let prior = reference
        .prior_motion_upper()
        .ok_or_else(|| invariant("original source motion origin missing"))?;
    if !prior.is_finite() || prior < 0. {
        return Err(invariant("proven source motion bound invalid"));
    }
    let common = common_product_with_work(k, work, profiles, lower, upper, sides, tolerance)?;
    let error = (Ivl::from(prior) + Ivl::from(common.endpoint_boundary_error_upper())).hi;
    if !error.is_finite() || error > tolerance {
        return Err(refused(
            "whole stored boundary product bound exceeds requested tolerance",
        ));
    }
    work.spend_core(k, 0)?;
    Ok(CompleteProductWitness {
        common,
        source,
        boundary_error_upper: error,
    })
}
/// Distinct finite-recipe origin, already proven by the opaque rectangle factory.
/// Every cap, side, tube, native use, material region and stored bound is consumed
/// by the SAME common geometry/CW implementation above. No source is fabricated.
pub(crate) fn complete_recipe_product_with_work<'c, 'p, 'l, 'ld, 'ud, 'g, 's, 'raw>(
    k: &Kernel,
    work: &MeshWork,
    profiles: &'p ProductProfiles<'l, 'ld, 'ud, 'g, 's, 'raw>,
    lower: &'c ProductCap<'l, 'ld, 'g, 's, 'raw>,
    upper: &'c ProductCap<'p, 'ud, 'g, 's, 'raw>,
    sides: &'c [ProductSideBand<'p, 'l, 'ld, 'ud, 'g, 's, 'raw>],
    tolerance: f64,
) -> Result<CommonProductWitness<'c, 'p, 'l, 'ld, 'ud, 'g, 's, 'raw>> {
    work.spend_core(k, 0)?;
    if profiles.lower().draft().source().recipe_owner().is_none() {
        return Err(refused(
            "original source cannot masquerade as a finite recipe",
        ));
    }
    common_product_with_work(k, work, profiles, lower, upper, sides, tolerance)
}
