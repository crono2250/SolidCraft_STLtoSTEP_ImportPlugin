//! One explicitly declared constant-section construction's complete proof.
//! Requests contain data only. All curves, source aliases, filled caps, sides and
//! native material incidence are reverified on the SAME immutable final body.
//! Intermediates stay local; only the fully consumed witness yields a final bound.
use super::super::profile_chain::{
    chain_graph_cover_from_cursor, ChainGraphCover, CurveUse, GraphClaim, SourceCursor,
};
use super::super::{MeshError, MeshWork};
use super::exact_geometry as x;
use super::native_profile::{
    native_reference_profile_draft_at_level_with_work, prove_native_profile_with_work,
};
use super::product_cap::prove_product_cap_with_work;
use super::product_profiles::prove_product_profiles_with_work;
use super::product_reference::ProductReference;
use super::product_side_band::{prove_product_side_band_with_work, BandCellClaim};
use super::source_prism::prove_source_prism_with_work;
use super::source_view::ExactSourceView;
use super::target_complex::{
    target_complex_with_work, TargetCover, TargetPatch, TargetPatchClaim, MAX_FACES,
};
use crate::topology::{Brep, FaceId};
use crate::{Kernel, Result, SolidError};
const OP: &str = "mesh_reconstruction::certificate::product_driver";
fn refused(reason: &'static str) -> SolidError {
    SolidError::Unsupported {
        operation: OP,
        reason,
    }
}

/// Untrusted complete ordered correspondence for ONE actual cap rim.
#[derive(Clone, Debug)]
pub struct ProductRimClaim {
    /// Reference-product vertex IDs in the claimed ring order. Original-source
    /// entries interpret these ONLY as their original retained weld-alias IDs.
    pub aliases: Vec<u32>,
    /// Exact stored source-edge start, possibly in an original edge interior.
    pub cursor: SourceCursor,
    /// Complete source-edge/actual-root interval claims, never a proof token.
    pub cells: Vec<GraphClaim>,
}
/// Untrusted complete ordered rims for ONE actual cap face.
#[derive(Clone, Debug)]
pub struct ProductCapClaim {
    /// Actual face ID in the SAME final candidate, after materialization.
    pub face: FaceId,
    /// Every rim, in this cap's own native order. Opposite caps may order holes differently.
    pub rims: Vec<ProductRimClaim>,
}
/// Data declaring ONE constructed constant-section family before acceptance.
/// This entry currently requires an exact original source product. Unproved
/// coordinate snapping or a separately rewelded endpoint mesh cannot authorize it.
#[derive(Clone, Debug)]
pub struct PrismaticConstructionClaim {
    /// Chosen finite nonzero source cap normal; exact product identities are proved.
    pub normal: [f64; 3],
    /// Actual lower cap and its own ordered rim claims.
    pub lower: ProductCapClaim,
    /// Actual upper cap and its independently ordered rim claims.
    pub upper: ProductCapClaim,
}
#[derive(Clone, Copy)]
pub(crate) enum ProductRequest<'a> {
    Explicit(&'a PrismaticConstructionClaim),
    NativeCaps {
        normal: [f64; 3],
        caps: Option<[FaceId; 2]>,
    },
    NativeEndpointCaps {
        proposal: &'a super::endpoint_proposal::PrismaticEndpointProposal,
        caps: Option<[FaceId; 2]>,
    },
}
impl<'a> ProductRequest<'a> {
    pub(crate) fn original_normal(self) -> Option<[f64; 3]> {
        match self {
            Self::Explicit(v) => Some(v.normal),
            Self::NativeCaps { normal, .. } => Some(normal),
            Self::NativeEndpointCaps { .. } => None,
        }
    }
    pub(crate) fn endpoint_proposal(
        self,
    ) -> Option<&'a super::endpoint_proposal::PrismaticEndpointProposal> {
        match self {
            Self::NativeEndpointCaps { proposal, .. } => Some(proposal),
            _ => None,
        }
    }
    fn caps(self) -> Option<[FaceId; 2]> {
        match self {
            Self::Explicit(v) => Some([v.lower.face, v.upper.face]),
            Self::NativeCaps { caps, .. } | Self::NativeEndpointCaps { caps, .. } => caps,
        }
    }
}
/// Claim-count admission only, BEFORE standing/native materialization. Full
/// native owned-payload/lazy-allocation admission remains a separate obligation.
pub(crate) fn admit_product_claim_counts(
    k: &Kernel,
    work: &MeshWork,
    body: &Brep,
    request: ProductRequest<'_>,
) -> Result<()> {
    work.spend_core(k, 0)?;
    if body.face_list().is_empty() || body.face_list().len() > MAX_FACES {
        return Err(refused("product construction has invalid face counts"));
    }
    if request.caps().is_some_and(|[lower, upper]| lower == upper) {
        return Err(refused("product construction has duplicate caps"));
    }
    let request = match request {
        ProductRequest::Explicit(request) => request,
        ProductRequest::NativeCaps { .. } | ProductRequest::NativeEndpointCaps { .. } => {
            return Ok(())
        }
    };
    if request.lower.rims.is_empty() || request.lower.rims.len() != request.upper.rims.len() {
        return Err(refused("product construction has invalid rim counts"));
    }
    for cap in [&request.lower, &request.upper] {
        work.spend_core(k, cap.rims.len())?;
        work.reserve_output_core(k, cap.rims.len())?;
        for rim in &cap.rims {
            let count = rim
                .aliases
                .len()
                .checked_add(rim.cells.len())
                .ok_or_else(|| refused("product correspondence input size overflow"))?;
            work.spend_core(k, count)?;
            work.reserve_output_core(k, count)?;
        }
    }
    Ok(())
}
fn uses<'a>(
    k: &Kernel,
    work: &MeshWork,
    body: &'a Brep,
    patch: &TargetPatch,
) -> Result<Vec<Vec<CurveUse<'a>>>> {
    work.reserve_output_core(k, patch.rims.len())?;
    let mut all = Vec::new();
    all.try_reserve_exact(patch.rims.len())
        .map_err(|_| refused("product proof workspace allocation refused"))?;
    for rim in &patch.rims {
        work.reserve_output_core(k, rim.len())?;
        let mut current = Vec::new();
        current
            .try_reserve_exact(rim.len())
            .map_err(|_| refused("product proof workspace allocation refused"))?;
        for usage in rim {
            work.spend_core(k, 1)?;
            let edge = body.edge(usage.edge)?;
            current.push(CurveUse {
                curve: edge
                    .curve
                    .as_ref()
                    .ok_or_else(|| refused("a cap edge lacks its actual curve"))?,
                interval: edge.interval,
                forward: usage.forward,
            });
        }
        all.push(current);
    }
    Ok(all)
}
fn graphs<'g>(
    k: &Kernel,
    work: &MeshWork,
    source: &ProductReference<'_, '_, '_>,
    uses: &'g [Vec<CurveUse<'g>>],
    claims: &[ProductRimClaim],
    tolerance: f64,
) -> Result<Vec<ChainGraphCover<'g>>> {
    if uses.len() != claims.len() {
        return Err(refused("cap/rim correspondence is incomplete"));
    }
    work.reserve_output_core(k, uses.len())?;
    let mut out = Vec::new();
    out.try_reserve_exact(uses.len())
        .map_err(|_| refused("product proof workspace allocation refused"))?;
    for (uses, claim) in uses.iter().zip(claims) {
        for &alias in &claim.aliases {
            work.spend_core(k, 1)?;
            if !source.has_vertex(alias) {
                return Err(refused("a source rim claims a missing original alias"));
            }
        }
        let points = source.points_with_work(k, work, &claim.aliases)?;
        let answer = chain_graph_cover_from_cursor(
            k,
            work,
            uses,
            points,
            &claim.cells,
            tolerance,
            claim.cursor,
        );
        // Preserve native errors/cancellation and the authoritative shared-budget
        // latch before classifying an ordinary unproved graph claim.
        work.spend_core(k, 0)?;
        let proof = match answer {
            Ok(proof) => proof,
            Err(MeshError::Kernel(error)) => return Err(error),
            Err(_) => {
                return Err(refused(
                    "complete source/actual cap graph correspondence was not proved",
                ))
            }
        };
        out.push(proof);
    }
    Ok(out)
}

/// One candidate choice from original cap heights and actual boundary vertices.
/// Projection scores are numerical steering, NEVER support/face/cap evidence.
/// The selected pair is fixed before the complete product theorem is attempted.
fn propose_cap_pair(
    k: &Kernel,
    work: &MeshWork,
    source: &ProductReference<'_, '_, '_>,
    complex: &super::target_complex::TargetComplex<'_>,
    normal: [f64; 3],
) -> Result<[FaceId; 2]> {
    let levels = source
        .cap_levels()
        .each_ref()
        .map(|v| crate::geom::expansion::to_f64(v));
    if !levels.into_iter().all(f64::is_finite) {
        return Err(refused("source cap steering heights nonfinite"));
    }
    let axis = crate::math::Vec3::from_array(normal);
    let mut best: [Option<(FaceId, f64)>; 2] = [None, None];
    let mut ambiguous = [false, false];
    for patch in &complex.patches {
        work.spend_core(k, 1)?;
        let [face] = patch.faces.as_slice() else {
            return Err(refused("automatic cap needs singleton actual faces"));
        };
        let mut scores = [0f64; 2];
        let mut vertices = 0usize;
        for rim in &patch.rims {
            for usage in rim {
                work.spend_core(k, 32)?;
                let point = complex.brep().vertex(usage.start)?.point;
                let height = point.dot(axis);
                if !height.is_finite() {
                    return Err(refused("native cap steering coordinate nonfinite"));
                }
                vertices = vertices
                    .checked_add(1)
                    .ok_or_else(|| refused("native cap vertex count overflow"))?;
                for (score, level) in scores.iter_mut().zip(levels) {
                    *score = score.max((height - level).abs());
                }
            }
        }
        if vertices == 0 {
            return Err(refused("native face has no cap steering vertices"));
        }
        for ((best, ambiguous), score) in best.iter_mut().zip(&mut ambiguous).zip(scores) {
            if !score.is_finite() {
                return Err(refused("native cap steering score nonfinite"));
            }
            if best.is_none_or(|(_, old)| score < old) {
                *best = Some((*face, score));
                *ambiguous = false;
            } else if best.is_some_and(|(_, old)| score == old) {
                *ambiguous = true;
            }
        }
    }
    if ambiguous.into_iter().any(|v| v) {
        return Err(refused("actual cap assignment ambiguous"));
    }
    let [Some((lower, _)), Some((upper, _))] = best else {
        return Err(refused("actual caps absent"));
    };
    if lower == upper {
        return Err(refused("actual cap assignment collapsed"));
    }
    Ok([lower, upper])
}

fn candidate<T>(k: &Kernel, work: &MeshWork, value: super::super::types::Result<T>) -> Result<T> {
    work.spend_core(k, 0)?;
    match value {
        Ok(value) => Ok(value),
        Err(MeshError::Kernel(error)) => Err(error),
        Err(_) => Err(refused("native cap correspondence proposal unresolved")),
    }
}
struct RimProposal {
    owner: usize,
    aliases: Vec<u32>,
    points: Vec<[f64; 3]>,
}
fn steering_points(
    k: &Kernel,
    work: &MeshWork,
    source: &ProductReference<'_, '_, '_>,
    aliases: &[u32],
) -> Result<Vec<[f64; 3]>> {
    work.reserve_output_core(k, aliases.len())?;
    let mut out = Vec::new();
    for &alias in aliases {
        let p = source
            .position_with_work(k, work, alias)?
            .ok_or_else(|| refused("same-view source alias absent"))?;
        let terms = p
            .iter()
            .try_fold(0usize, |n, c| n.checked_add(c.len()))
            .ok_or_else(|| refused("source steering expansion count overflow"))?;
        work.spend_core(k, terms)?;
        let point = p
            .as_ref()
            .each_ref()
            .map(|c| crate::geom::expansion::to_f64(c));
        if !point.iter().all(|v| v.is_finite()) {
            return Err(refused("source steering coordinate nonfinite"));
        }
        out.push(point);
    }
    Ok(out)
}
/// One fixed numerical rim assignment. Complete original-rim binding, curve
/// coverage, both cap charts and every side remain independent obligations.
fn rim_assignment(
    k: &Kernel,
    work: &MeshWork,
    uses: &[CurveUse<'_>],
    rings: &[Vec<u32>],
    source: &ProductReference<'_, '_, '_>,
) -> Result<RimProposal> {
    let steering = candidate(
        k,
        work,
        super::super::profile_chain::TargetProposals::new_with_work(k, work, uses),
    )?;
    let [point, tangent, _] = candidate(k, work, steering.steering_jet_with_work(k, work))?;
    let mut best: Option<(usize, f64, f64)> = None;
    let mut ambiguous = false;
    for (owner, aliases) in rings.iter().enumerate() {
        let points = steering_points(k, work, source, aliases)?;
        let mut edge_best: Option<(f64, f64)> = None;
        for (index, a) in points.iter().enumerate() {
            work.spend_core(k, 128)?;
            let next = index
                .checked_add(1)
                .ok_or_else(|| refused("source rim edge overflow"))?;
            let b = points
                .get(if next == points.len() { 0 } else { next })
                .ok_or_else(|| refused("source rim edge missing"))?;
            let [ax, ay, az] = *a;
            let [bx, by, bz] = *b;
            let a = crate::math::Vec3::new(ax, ay, az);
            let d = crate::math::Vec3::new(bx, by, bz) - a;
            let square = d.dot(d);
            if !square.is_finite() || square <= 0. {
                return Err(refused("source steering edge degenerate"));
            }
            let unit = (point - a).dot(d) / square;
            if !unit.is_finite() {
                return Err(refused("source steering parameter nonfinite"));
            }
            let delta = point - (a + d * unit.clamp(0., 1.));
            let distance = delta.dot(delta);
            let direction = d.dot(tangent);
            if !distance.is_finite() || !direction.is_finite() {
                return Err(refused("source steering value nonfinite"));
            }
            if edge_best.is_none_or(|(old, _)| distance < old) {
                edge_best = Some((distance, direction));
            }
        }
        let (distance, direction) = edge_best.ok_or_else(|| refused("empty source rim"))?;
        if best.is_none_or(|(_, _, old)| distance < old) {
            best = Some((owner, direction, distance));
            ambiguous = false;
        } else if best.is_some_and(|(_, _, old)| distance == old) {
            ambiguous = true;
        }
    }
    if ambiguous {
        return Err(refused("native/source rim assignment ambiguous"));
    }
    let (owner, direction, _) =
        best.ok_or_else(|| refused("native/source rim assignment absent"))?;
    if direction == 0. {
        return Err(refused("source/native rim steering orientation unresolved"));
    }
    let reverse = direction < 0.;
    let aliases = rings
        .get(owner)
        .ok_or_else(|| refused("selected source rim missing"))?;
    work.reserve_output_core(k, aliases.len())?;
    let mut aliases = aliases.clone();
    if reverse {
        aliases.reverse();
    }
    let points = steering_points(k, work, source, &aliases)?;
    Ok(RimProposal {
        owner,
        aliases,
        points,
    })
}
fn propose_native_cap_claims(
    k: &Kernel,
    work: &MeshWork,
    source: &ProductReference<'_, '_, '_>,
    uses: [&[Vec<CurveUse<'_>>]; 2],
    normal: [f64; 3],
    faces: [FaceId; 2],
    tolerance: f64,
) -> Result<PrismaticConstructionClaim> {
    use super::super::profile_chain::{joint_cap_graph_proposals_with_work, CapProposalInput};
    use std::collections::{BTreeMap, BTreeSet};
    let count = source.profile_rims().len();
    let [lower, upper] = uses;
    if count == 0 || lower.len() != count || upper.len() != count {
        return Err(refused("complete native/source rim counts differ"));
    }
    work.reserve_cells_core(k, source.upper_to_lower().len())?;
    let aliases = source.upper_to_lower().len();
    let bits = usize::try_from(aliases.max(1).ilog2())
        .map_err(|_| refused("partner map logarithm overflow"))?
        .checked_add(1)
        .ok_or_else(|| refused("partner map logarithm overflow"))?;
    work.spend_core(
        k,
        aliases
            .checked_mul(bits)
            .and_then(|n| n.checked_mul(4))
            .ok_or_else(|| refused("partner map work overflow"))?,
    )?;
    let mut inverse = BTreeMap::new();
    for (&upper, &lower) in source.upper_to_lower() {
        work.spend_core(k, 1)?;
        if inverse.insert(lower, upper).is_some() {
            return Err(refused("source alias partner inverse ambiguous"));
        }
    }
    work.reserve_output_core(
        k,
        count
            .checked_mul(4)
            .ok_or_else(|| refused("source ring row overflow"))?,
    )?;
    let mut upper_rings = Vec::new();
    upper_rings
        .try_reserve_exact(count)
        .map_err(|_| refused("product proof workspace allocation refused"))?;
    for ring in source.profile_rims() {
        work.reserve_output_core(k, ring.len())?;
        let mut upper = Vec::new();
        upper
            .try_reserve_exact(ring.len())
            .map_err(|_| refused("product proof workspace allocation refused"))?;
        for &alias in ring {
            work.spend_core(k, 1)?;
            upper.push(
                *inverse
                    .get(&alias)
                    .ok_or_else(|| refused("upper original alias absent"))?,
            );
        }
        upper_rings.push(upper);
    }
    let mut lower_proposals = Vec::new();
    lower_proposals
        .try_reserve_exact(count)
        .map_err(|_| refused("product proof workspace allocation refused"))?;
    let mut upper_proposals = Vec::new();
    upper_proposals
        .try_reserve_exact(count)
        .map_err(|_| refused("product proof workspace allocation refused"))?;
    for (native, rings, out) in [
        (lower, source.profile_rims(), &mut lower_proposals),
        (upper, &upper_rings, &mut upper_proposals),
    ] {
        let mut used = BTreeSet::new();
        work.reserve_cells_core(k, count)?;
        for rim in native {
            let proposal = rim_assignment(k, work, rim, rings, source)?;
            if !used.insert(proposal.owner) {
                return Err(refused("source rim assigned more than once"));
            }
            out.push(proposal);
        }
    }
    work.reserve_output_core(
        k,
        count
            .checked_mul(4)
            .ok_or_else(|| refused("native rim output overflow"))?,
    )?;
    let mut lower_claims: Vec<Option<ProductRimClaim>> = (0..count).map(|_| None).collect();
    let mut upper_claims: Vec<Option<ProductRimClaim>> = (0..count).map(|_| None).collect();
    for (low_index, low) in lower_proposals.into_iter().enumerate() {
        work.spend_core(k, count)?;
        let high_index = upper_proposals
            .iter()
            .position(|v| v.owner == low.owner)
            .ok_or_else(|| refused("opposite source rim missing"))?;
        let high = upper_proposals
            .get(high_index)
            .ok_or_else(|| refused("upper rim proposal missing"))?;
        let [low_graph, high_graph] = candidate(
            k,
            work,
            joint_cap_graph_proposals_with_work(
                k,
                work,
                [
                    CapProposalInput {
                        uses: lower
                            .get(low_index)
                            .ok_or_else(|| refused("lower native rim absent"))?,
                        aliases: &low.aliases,
                        points: &low.points,
                    },
                    CapProposalInput {
                        uses: upper
                            .get(high_index)
                            .ok_or_else(|| refused("upper native rim absent"))?,
                        aliases: &high.aliases,
                        points: &high.points,
                    },
                ],
                source.upper_to_lower(),
                tolerance,
            ),
        )?;
        *lower_claims
            .get_mut(low_index)
            .ok_or_else(|| refused("lower claim slot absent"))? = Some(ProductRimClaim {
            aliases: low.aliases,
            cursor: low_graph.source_cursor,
            cells: low_graph.cells,
        });
        work.reserve_output_core(k, high.aliases.len())?;
        *upper_claims
            .get_mut(high_index)
            .ok_or_else(|| refused("upper claim slot absent"))? = Some(ProductRimClaim {
            aliases: high.aliases.clone(),
            cursor: high_graph.source_cursor,
            cells: high_graph.cells,
        });
    }
    // Preserve EACH cap's own native rim order, including independent hole order.
    let lower = lower_claims
        .into_iter()
        .map(|v| v.ok_or_else(|| refused("lower cap rim unmatched")))
        .collect::<Result<Vec<_>>>()?;
    let upper = upper_claims
        .into_iter()
        .map(|v| v.ok_or_else(|| refused("upper cap rim unmatched")))
        .collect::<Result<Vec<_>>>()?;
    let [low, high] = faces;
    Ok(PrismaticConstructionClaim {
        normal,
        lower: ProductCapClaim {
            face: low,
            rims: lower,
        },
        upper: ProductCapClaim {
            face: high,
            rims: upper,
        },
    })
}

pub(crate) fn prove_product_request_with_work(
    k: &Kernel,
    work: &MeshWork,
    view: ExactSourceView<'_, '_>,
    exact_normal: &x::P,
    steering_normal: [f64; 3],
    body: &Brep,
    request: ProductRequest<'_>,
    tolerance: f64,
) -> Result<f64> {
    work.spend_core(k, 0)?;
    let source = view.source();
    let source_product =
        prove_source_prism_with_work(k, work, view, exact_normal)?.ok_or_else(|| {
            refused("same original complex/view is not the declared exact complete product")
        })?;
    let reference = ProductReference::original(&source_product);
    let bound = prove_reference_request_with_work(
        k,
        work,
        &reference,
        steering_normal,
        body,
        request,
        tolerance,
    )?;
    if !bound.source.is_some_and(|s| core::ptr::eq(s, source)) || !core::ptr::eq(bound.body, body) {
        return Err(SolidError::port_invariant(
            OP,
            "complete product witness changed original source or final native body identity",
        ));
    }
    Ok(bound.upper)
}
/// Only a full common cap/side/native CW/material consumer constructs this.
struct ProductBound<'g, 's, 'raw> {
    body: &'g Brep,
    source: Option<&'s super::source_topology::SourceManifold<'raw>>,
    upper: f64,
    caps: [FaceId; 2],
}
/// Body-bound finite recipe result, distinct from an original-source certificate.
pub(crate) struct RecipeProductBound<'g> {
    body: &'g Brep,
    upper: f64,
    caps: [FaceId; 2],
}
impl<'g> RecipeProductBound<'g> {
    pub(crate) fn body(&self) -> &'g Brep {
        self.body
    }
    pub(crate) fn upper_bound(&self) -> f64 {
        self.upper
    }
    pub(crate) fn upper_cap(&self) -> FaceId {
        let [_, high] = self.caps;
        high
    }
}
pub(crate) fn prove_recipe_product_request_with_work<'g>(
    k: &Kernel,
    work: &MeshWork,
    recipe: &super::fitted_recipe::RectangularRecipe<'_>,
    body: &'g Brep,
    tolerance: f64,
) -> Result<RecipeProductBound<'g>> {
    let reference = ProductReference::recipe(recipe);
    let steering_normal = recipe.normal_hint();
    let bound = prove_reference_request_with_work(
        k,
        work,
        &reference,
        steering_normal,
        body,
        ProductRequest::NativeCaps {
            normal: steering_normal,
            caps: None,
        },
        tolerance,
    )?;
    if bound.source.is_some() || !core::ptr::eq(bound.body, body) {
        return Err(SolidError::port_invariant(
            OP,
            "finite recipe acquired a false source origin",
        ));
    }
    Ok(RecipeProductBound {
        body,
        upper: bound.upper,
        caps: bound.caps,
    })
}
fn prove_reference_request_with_work<'g, 's, 'raw>(
    k: &Kernel,
    work: &MeshWork,
    reference: &ProductReference<'_, 's, 'raw>,
    steering_normal: [f64; 3],
    body: &'g Brep,
    request: ProductRequest<'_>,
    tolerance: f64,
) -> Result<ProductBound<'g, 's, 'raw>> {
    work.spend_core(k, 0)?;
    let face_count = body.face_list().len();
    work.reserve_output_core(
        k,
        face_count
            .checked_mul(2)
            .ok_or_else(|| refused("actual face count overflow"))?,
    )?;
    work.spend_core(
        k,
        face_count
            .checked_mul(3)
            .ok_or_else(|| refused("actual face scan overflow"))?,
    )?;
    let claims: Vec<_> = body
        .face_list()
        .iter()
        .map(|&face| TargetPatchClaim { faces: vec![face] })
        .collect();
    let complex = match target_complex_with_work(k, work, body, &claims)? {
        TargetCover::Proven(complex) => complex,
        TargetCover::Undecided(_) => {
            return Err(refused("actual product face complex is unproved"))
        }
    };
    let cap = |face: FaceId| {
        complex
            .patches
            .iter()
            .position(|p| p.faces.as_slice() == [face])
            .ok_or_else(|| refused("claimed cap is not one complete actual face"))
    };
    let [lower_face, upper_face] = match request.caps() {
        Some(caps) => caps,
        None => propose_cap_pair(k, work, reference, &complex, steering_normal)?,
    };
    let low = cap(lower_face)?;
    let high = cap(upper_face)?;
    let lower_patch = complex
        .patches
        .get(low)
        .ok_or_else(|| refused("lower actual cap absent"))?;
    let upper_patch = complex
        .patches
        .get(high)
        .ok_or_else(|| refused("upper actual cap absent"))?;
    let lower_uses = uses(k, work, body, lower_patch)?;
    let upper_uses = uses(k, work, body, upper_patch)?;
    // Same source analysis and native complex as acceptance. This local owner
    // holds DATA only; every proof below reads the original source and body.
    let generated;
    let request = match request {
        ProductRequest::Explicit(request) => request,
        ProductRequest::NativeCaps { .. } | ProductRequest::NativeEndpointCaps { .. } => {
            generated = propose_native_cap_claims(
                k,
                work,
                reference,
                [&lower_uses, &upper_uses],
                steering_normal,
                [lower_face, upper_face],
                tolerance,
            )?;
            &generated
        }
    };
    let lower_graphs = graphs(
        k,
        work,
        reference,
        &lower_uses,
        &request.lower.rims,
        tolerance,
    )?;
    let upper_graphs = graphs(
        k,
        work,
        reference,
        &upper_uses,
        &request.upper.rims,
        tolerance,
    )?;
    // Coordinate projection is candidate data; both complete filled-cap Gram
    // charts independently prove injectivity and geometry in unchanged zones.
    let axes = match request
        .normal
        .iter()
        .enumerate()
        .max_by(|(_, a), (_, b)| a.abs().total_cmp(&b.abs()))
        .map(|(i, _)| i)
    {
        Some(0) => [1, 2],
        Some(1) => [0, 2],
        Some(2) => [0, 1],
        _ => return Err(refused("product normal absent")),
    };
    let lower = native_reference_profile_draft_at_level_with_work(
        k,
        work,
        *reference,
        &complex,
        low,
        &lower_graphs,
        axes,
        tolerance,
        0,
    )?;
    let upper = native_reference_profile_draft_at_level_with_work(
        k,
        work,
        *reference,
        &complex,
        high,
        &upper_graphs,
        axes,
        tolerance,
        1,
    )?;
    let lower_model = prove_native_profile_with_work(k, work, &lower)?;
    let profiles = prove_product_profiles_with_work(k, work, &lower_model, &upper)?;
    let low_cap = prove_product_cap_with_work(k, work, &lower_model, tolerance)?;
    let high_cap = prove_product_cap_with_work(k, work, profiles.upper(), tolerance)?;
    let sides_count = lower_patch
        .rims
        .iter()
        .try_fold(0usize, |n, r| n.checked_add(r.len()))
        .ok_or_else(|| refused("product side count overflow"))?;
    work.reserve_output_core(k, sides_count)?;
    let mut sides = Vec::new();
    sides
        .try_reserve_exact(sides_count)
        .map_err(|_| refused("product proof workspace allocation refused"))?;
    for (ring, rim) in lower_patch.rims.iter().enumerate() {
        for (use_index, cap_use) in rim.iter().enumerate() {
            work.spend_core(k, 1)?;
            let pair = complex
                .edges
                .get(&cap_use.edge)
                .ok_or_else(|| refused("cap edge incidence absent"))?;
            let side = pair
                .iter()
                .find(|(_, u)| u.face != low_cap.face())
                .ok_or_else(|| refused("actual cap/side adjacency absent"))?
                .1;
            let rectangle = super::rectangular_trim::rectangle_layout_claim_with_work(
                k,
                work,
                body,
                side.face,
                side.faceuse,
            )?
            .ok_or_else(|| refused("actual side has no complete rectangle layout"))?;
            let low_edge = rectangle
                .edges
                .iter()
                .find(|e| e.edge == cap_use.edge)
                .ok_or_else(|| refused("actual side lacks its lower cap edge"))?;
            let [a, b] = &low_edge.ends;
            let ruling_is_u = x::sub(&a[0], &b[0]).is_some_and(|v| x::zero(&v));
            let (axis, maximum, profile_axis) = if ruling_is_u {
                (0, rectangle.domain[1], 1)
            } else {
                (1, rectangle.domain[3], 0)
            };
            let maximum = x::scalar(maximum)
                .ok_or_else(|| refused("actual rectangle domain is not finite"))?;
            let reverse_ruling = x::sub(
                a.get(axis).ok_or_else(|| refused("ruling axis absent"))?,
                &maximum,
            )
            .is_some_and(|v| x::zero(&v));
            let sign = x::sub(
                b.get(profile_axis)
                    .ok_or_else(|| refused("profile axis absent"))?,
                a.get(profile_axis)
                    .ok_or_else(|| refused("profile axis absent"))?,
            )
            .and_then(|v| x::sign(&v))
            .ok_or_else(|| refused("actual profile direction unproved"))?;
            if sign == 0 {
                return Err(refused("actual profile direction is degenerate"));
            }
            let graph = lower_graphs
                .get(ring)
                .ok_or_else(|| refused("lower graph absent"))?;
            work.spend_core(
                k,
                graph
                    .cells
                    .len()
                    .checked_mul(2)
                    .ok_or_else(|| refused("side cell scan size overflow"))?,
            )?;
            let count = graph
                .cells
                .iter()
                .filter(|cell| cell.claim.curve == use_index)
                .count();
            work.reserve_output_core(k, count)?;
            let cells: Vec<_> = graph
                .cells
                .iter()
                .filter(|cell| cell.claim.curve == use_index)
                .map(|cell| BandCellClaim {
                    root: cell.claim.span,
                    unit: cell.claim.target_unit,
                })
                .collect();
            sides.push(prove_product_side_band_with_work(
                k,
                work,
                &profiles,
                side.face,
                side.faceuse,
                ruling_is_u,
                reverse_ruling,
                ring,
                use_index,
                sign == 1,
                &cells,
                tolerance,
            )?);
        }
    }
    let (upper, source) =
        if let Some(source) = reference.original_source() {
            let whole = super::complete_product::complete_product_with_work(
                k, work, &profiles, &low_cap, &high_cap, &sides, tolerance,
            )?;
            if !core::ptr::eq(whole.source(), source) || !core::ptr::eq(whole.candidate(), body) {
                return Err(SolidError::port_invariant(OP,
                "complete product witness changed original source or final native body identity"));
            }
            (whole.boundary_error_upper(), Some(source))
        } else {
            if reference.recipe_owner().is_none() {
                return Err(SolidError::port_invariant(
                    OP,
                    "complete product origin missing",
                ));
            }
            let whole = super::complete_product::complete_recipe_product_with_work(
                k, work, &profiles, &low_cap, &high_cap, &sides, tolerance,
            )?;
            if !core::ptr::eq(whole.candidate(), body) {
                return Err(SolidError::port_invariant(
                    OP,
                    "complete recipe body identity changed",
                ));
            }
            (whole.boundary_error_upper(), None)
        };
    work.spend_core(k, 0)?;
    Ok(ProductBound {
        body,
        source,
        upper,
        caps: [lower_face, upper_face],
    })
}
