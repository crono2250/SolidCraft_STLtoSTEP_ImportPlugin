//! Full reconstruction acceptance with immutable source/final identity tokens.
//!
//! Source preflight precedes construction and is reused, not repeated per candidate.
//! The first sufficient final theorem is exact oriented planar-chain equality. It
//! covers complete domains and establishes equal embedded oriented boundaries and
//! material winding. Genuinely moved/curved results return typed Undecided until the
//! coherent UV/CW/product theorem proves them; neither Hausdorff coverage nor a genus
//! count can construct this token. Exact redundant zero-area source facets are covered
//! by the independently validated source regularization, never silently discarded.
//!
//! Deviations: none. No recursion; one opaque shared `MeshWork` across public workflow
//! stages, plus each subproof's secondary bounded-work and cancellation guards.
use super::super::prepare::PreparedMesh;
use super::super::types::{MeshInput, WeldClaim};
use super::super::work::MeshWork;
use super::exact_planar::{self, ExactPlanar};
use super::source_topology::{validate_source_weld_with_work, SourceManifold, SourceTopology};
use crate::kernel::Kernel;
use crate::topology::Brep;
use crate::{Result, SolidError};

/// The required complete statement was not established. No variant authorizes fallback
/// to a less strict adoption certificate; only the workflow's ordinary Refused branch
/// may choose a separately certified supported construction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReconstructionRefusal {
    /// Malformed or unsupported input values.
    InvalidInput,
    /// The original source exceeds the admitted input count.
    InputBudget {
        /// The enforced count or work limit.
        limit: usize,
    },
    /// Prepared data no longer refers to the source held by the preflight proof.
    SourceIdentity,
    /// Complete source embedding and orientation were not established.
    SourceTopology {
        /// The unresolved original-source obligation.
        reason: super::source_topology::SourceRefusal,
    },
    /// The actual constructed B-rep lacks the required native soundness.
    NativeSolidValidity,
    /// Complete boundary and material correspondence remain unproved.
    GeometryCorrespondence {
        /// The unresolved whole-domain obligation.
        reason: &'static str,
    },
}
/// Source preflight result, before native construction is attempted.
pub enum SourceVerdict<'source, 'proof> {
    /// The complete statement holds on the borrowed, unchanged inputs.
    Proven(SourceCertificate<'source, 'proof>),
    /// The required bounded proof was not established.
    Undecided(ReconstructionRefusal),
}

/// Select exact axis-aligned planar stock before any construction. Each retained
/// triangle must already be horizontal to one coordinate plane as stored.
/// A tessellated curved wall cannot qualify by fitting its facets individually.
/// The resulting Native faces still require the complete exact planar proof.
pub fn choose_orthogonal_stock_from_source_with_work(
    k: &Kernel,
    work: &MeshWork,
    source: &SourceCertificate<'_, '_>,
    prepared: &PreparedMesh,
) -> super::super::Result<Option<super::super::FacetedPlan>> {
    use super::super::{source::SourceMesh, types::invalid, MeshError};
    use crate::math::Vec3;
    work.check(k)?;
    let raw = source.source;
    let count = raw
        .positions
        .len()
        .checked_add(raw.triangles.len())
        .and_then(|n| n.checked_mul(3))
        .ok_or_else(|| invalid("orthogonal stock source count overflow"))?;
    work.spend(k, count)?;
    if raw != &prepared.original {
        return Err(MeshError::Refused {
            stage: "orthogonal stock",
            detail: "source identity differs".into(),
        });
    }
    if !prepared.features.is_empty()
        || !prepared.provenance.patches.is_empty()
        || !prepared.provenance.faceted_source_patches.is_empty()
    {
        return Ok(None);
    }
    let view = source.original_view();
    let get = |alias| {
        view.source()
            .position(alias)
            .ok_or_else(|| invalid("proved orthogonal stock alias disappeared"))
    };
    for (_, [a, b, c]) in view.triangles() {
        work.spend(k, 9)?;
        let ([ax, ay, az], [bx, by, bz], [cx, cy, cz]) = (get(a)?, get(b)?, get(c)?);
        if !(ax == bx && bx == cx || ay == by && by == cy || az == bz && bz == cz) {
            return Ok(None);
        }
    }
    let mut positions = Vec::new();
    for id in 0..view.alias_count() {
        work.spend(k, 3)?;
        work.reserve_cells(k, 3)?;
        positions.push(Vec3::from_array(get(
            u32::try_from(id).map_err(|_| invalid("alias index overflow"))?
        )?));
    }
    let (mut triangles, mut source_triangles) = (Vec::new(), Vec::new());
    for (id, tri) in view.triangles() {
        work.spend(k, 4)?;
        work.reserve_cells(k, 4)?;
        triangles.push(tri);
        source_triangles.push(Some(
            u32::try_from(id).map_err(|_| invalid("source triangle id overflow"))?,
        ));
    }
    // Plan over the SAME retained quotient. No alternate positional tolerance
    // or second weld can turn a curved source into this exact planar family.
    let candidate = SourceMesh {
        positions,
        triangles,
        source_triangles,
        vertex_sources: Vec::new(),
        weld_tolerance: 0.,
    };
    let plan = super::super::faceted::faceted_plan_of(k, work, &candidate)?;
    work.check(k)?;
    Ok(Some(plan))
}

/// Verified exact raw arrays and weld claim remain immutable while construction runs.
/// No Kernel borrow, Clone, serialization, owner-address hash or cached `passed` flag.
pub struct SourceCertificate<'source, 'proof> {
    source: &'source MeshInput,
    proof: SourceManifold<'proof>,
}
impl<'source, 'proof> SourceCertificate<'source, 'proof> {
    /// Borrow the SAME proven original retained complex; no replacement arrays or weld.
    pub(crate) fn original_view(&self) -> super::source_view::ExactSourceView<'_, 'proof> {
        super::source_view::ExactSourceView::original(&self.proof)
    }
}
/// Final complete geometry/material/topology result.
pub enum ReconstructionVerdict<'a> {
    /// The complete statement holds on the borrowed, unchanged inputs.
    Proven(ReconstructionCertificate<'a>),
    /// The required bounded proof was not established.
    Undecided(ReconstructionRefusal),
}
/// Privately borrows the exact original source and final untouched native candidate.
pub struct ReconstructionCertificate<'a> {
    _source: &'a MeshInput,
    _candidate: &'a Brep,
    stored_boundary_error_upper: f64,
}
impl ReconstructionCertificate<'_> {
    /// Certified complete-domain bound to actual stored definitions/curves and
    /// their coherent tolerant-solid witness, never a sampled deviation estimate.
    pub fn boundary_error_upper(&self) -> f64 {
        self.stored_boundary_error_upper
    }
}

/// Verify source embedding/regularization before any native candidate construction.
/// The proof borrows only source+weld, so other `PreparedMesh` provenance may evolve.
///
/// # Errors
/// Unexpected/internal native defects and cancellation propagate unchanged. Ops must
/// check `MeshWork`'s authoritative `NativeBudgetExceeded` latch after every stage.
pub fn certify_source_with_work<'source, 'proof>(
    k: &Kernel,
    work: &MeshWork,
    source: &'source MeshInput,
    weld: &'proof WeldClaim,
) -> Result<SourceVerdict<'source, 'proof>>
where
    'source: 'proof,
{
    work.spend_core(k, 0)?;
    let limit = super::super::source::MAX_CONVERSION_TRIANGLES;
    let result = if source.triangles.len() > limit {
        Ok(SourceVerdict::Undecided(
            ReconstructionRefusal::InputBudget { limit },
        ))
    } else {
        match validate_source_weld_with_work(k, work, &source.positions, &source.triangles, weld)? {
            SourceTopology::Proven(proof) => {
                Ok(SourceVerdict::Proven(SourceCertificate { source, proof }))
            }
            SourceTopology::Undecided(reason) => Ok(SourceVerdict::Undecided(
                ReconstructionRefusal::SourceTopology { reason },
            )),
        }
    };
    work.spend_core(k, 0)?;
    result
}

fn final_impl<'a, 'source: 'a, 'proof>(
    k: &mut Kernel,
    work: &MeshWork,
    source_proof: &SourceCertificate<'source, 'proof>,
    prepared: &PreparedMesh,
    candidate: &'a mut Brep,
    tolerance: f64,
    product: Option<super::product_driver::ProductRequest<'_>>,
) -> Result<ReconstructionVerdict<'a>> {
    macro_rules! refuse {
        ($why:expr) => {
            return Ok(ReconstructionVerdict::Undecided($why))
        };
    }
    if !(tolerance > 0.0 && tolerance.is_finite()) {
        refuse!(ReconstructionRefusal::InvalidInput);
    }
    let source = source_proof.source;
    let comparisons = source
        .positions
        .len()
        .checked_add(source.triangles.len())
        .and_then(|n| n.checked_mul(3))
        .ok_or(SolidError::Unsupported {
            operation: "mesh_reconstruction::source_identity",
            reason: "source identity comparison count overflow",
        })?;
    work.spend_core(k, comparisons)?;
    if source != &prepared.original {
        refuse!(ReconstructionRefusal::SourceIdentity);
    }
    // The chosen construction family is declared BEFORE any required proof.
    // A product refusal never falls through to exact-planar/faceted acceptance.
    if let Some(request) = product {
        if !prepared.provenance.faceted_source_patches.is_empty() {
            refuse!(ReconstructionRefusal::GeometryCorrespondence {
                reason: "contradictory faceted and prismatic construction families"
            });
        }
        match super::product_driver::admit_product_claim_counts(k, work, candidate, request) {
            Ok(()) => {}
            Err(SolidError::Unsupported { reason, .. }) => {
                refuse!(ReconstructionRefusal::GeometryCorrespondence { reason })
            }
            Err(error) => return Err(error),
        }
    }
    // Endpoint construction is selected as DATA before its mandatory proof. It
    // borrows the SAME source preflight; no moved MeshInput/weld/preflight exists.
    let endpoint_model = if let Some(proposal) =
        product.and_then(super::product_driver::ProductRequest::endpoint_proposal)
    {
        match super::endpoint_proposal::build_endpoint_model(
            k,
            work,
            source_proof.proof.alias_count(),
            proposal,
        ) {
            Ok(model) => Some(model),
            Err(SolidError::Unsupported { reason, .. }) => {
                refuse!(ReconstructionRefusal::GeometryCorrespondence { reason })
            }
            Err(error) => return Err(error),
        }
    } else {
        None
    };
    let motion = if let Some(model) = &endpoint_model {
        match super::source_motion::prove_source_motion_with_work(
            k,
            work,
            &source_proof.proof,
            &model.points,
            tolerance,
        )? {
            super::source_motion::SourceMotionVerdict::Proven(motion) => Some(motion),
            super::source_motion::SourceMotionVerdict::Undecided(reason) => {
                refuse!(ReconstructionRefusal::GeometryCorrespondence { reason })
            }
        }
    } else {
        None
    };
    // Reuse source_proof's authoritative checked weld/aliases. Extra prepared labels
    // are claims only; exact-planar attribution is recomputed from raw+actual geometry.
    let standing = match crate::topology::brep::validation::soundness(k, candidate) {
        Ok(value) => value,
        Err(SolidError::UnsureRegion { .. }) => {
            refuse!(ReconstructionRefusal::NativeSolidValidity);
        }
        Err(e) if super::errors::expected(&e) => {
            refuse!(ReconstructionRefusal::NativeSolidValidity);
        }
        Err(e) => return Err(e),
    };
    if !standing.manifold || !standing.sound() {
        refuse!(ReconstructionRefusal::NativeSolidValidity);
    }
    if let Some(request) = product {
        let bound = (|| match (&motion, &endpoint_model) {
            (Some(motion), Some(model)) => super::product_driver::prove_product_request_with_work(
                k,
                work,
                super::source_view::ExactSourceView::motion(motion),
                &model.normal,
                model.normal_hint,
                candidate,
                request,
                tolerance,
            ),
            (None, None) => {
                let hint = request.original_normal().ok_or_else(|| {
                    SolidError::port_invariant(
                        "mesh_reconstruction::source_view",
                        "product source choice lacks normal",
                    )
                })?;
                work.reserve_cells_core(k, 4)?;
                let normal = super::exact_geometry::point(hint).ok_or(SolidError::Unsupported {
                    operation: "mesh_reconstruction::product_driver",
                    reason: "product normal is not finite",
                })?;
                super::product_driver::prove_product_request_with_work(
                    k,
                    work,
                    super::source_view::ExactSourceView::original(&source_proof.proof),
                    &normal,
                    hint,
                    candidate,
                    request,
                    tolerance,
                )
            }
            _ => Err(SolidError::port_invariant(
                "mesh_reconstruction::source_view",
                "endpoint model/proof choice differs",
            )),
        })();
        return match bound {
            Ok(stored_boundary_error_upper) => {
                Ok(ReconstructionVerdict::Proven(ReconstructionCertificate {
                    _source: source,
                    _candidate: candidate,
                    stored_boundary_error_upper,
                }))
            }
            Err(SolidError::Unsupported { reason, .. }) => Ok(ReconstructionVerdict::Undecided(
                ReconstructionRefusal::GeometryCorrespondence { reason },
            )),
            Err(error) if super::errors::expected(&error) => Ok(ReconstructionVerdict::Undecided(
                ReconstructionRefusal::GeometryCorrespondence {
                    reason: "complete actual product correspondence was not established",
                },
            )),
            Err(error) => Err(error),
        };
    }
    // The workflow declares the faceted construction family through untrusted
    // original cell groups. Choosing this theorem is not retry/fallback on failed
    // geometry: all claims are independently re-verified on this exact candidate.
    if !prepared.provenance.faceted_source_patches.is_empty() {
        return match super::faceted_witness::prove_faceted_witness_with_work(
            k,
            work,
            &source_proof.proof,
            &prepared.provenance.faceted_source_patches,
            candidate,
            tolerance,
        ) {
            Ok(super::faceted_witness::FacetedWitness::Proven(proof)) => {
                let stored_boundary_error_upper = proof.stored_boundary_error_upper;
                Ok(ReconstructionVerdict::Proven(ReconstructionCertificate {
                    _source: source,
                    _candidate: candidate,
                    stored_boundary_error_upper,
                }))
            }
            Ok(super::faceted_witness::FacetedWitness::Undecided(reason)) => {
                Ok(ReconstructionVerdict::Undecided(
                    ReconstructionRefusal::GeometryCorrespondence { reason },
                ))
            }
            Err(SolidError::Unsupported { reason, .. }) => Ok(ReconstructionVerdict::Undecided(
                ReconstructionRefusal::GeometryCorrespondence { reason },
            )),
            Err(e) => Err(e),
        };
    }
    match exact_planar::prove_with_work(k, work, source, &source_proof.proof, candidate) {
        Ok(ExactPlanar::Proven) => Ok(ReconstructionVerdict::Proven(ReconstructionCertificate {
            _source: source,
            _candidate: candidate,
            stored_boundary_error_upper: 0.0,
        })),
        Ok(ExactPlanar::Undecided(reason)) | Err(SolidError::Unsupported { reason, .. }) => {
            Ok(ReconstructionVerdict::Undecided(
                ReconstructionRefusal::GeometryCorrespondence { reason },
            ))
        }
        Err(e) => Err(e),
    }
}

/// Final candidate proof using the SAME source preflight held across construction.
///
/// # Errors
/// Cancellation/internal native defects propagate. Ops checks `MeshWork` after the call
/// BEFORE fallback/adoption, so a latched workflow budget is its typed native failure.
pub fn certify_reconstruction_from_source_with_work<'a, 'original: 'a, 'proof>(
    k: &mut Kernel,
    work: &MeshWork,
    source: &SourceCertificate<'original, 'proof>,
    prepared: &PreparedMesh,
    candidate: &'a mut Brep,
    tolerance: f64,
) -> Result<ReconstructionVerdict<'a>> {
    work.spend_core(k, 0)?;
    let result = final_impl(k, work, source, prepared, candidate, tolerance, None);
    work.spend_core(k, 0)?;
    result
}
/// Complete geometry/material proof for an explicitly declared constant-section construction.
/// Both complete cap charts and EVERY actual side consume ONE immutable common model.
/// Claims are data only; failed coverage or identity cannot select another theorem.
/// The source must be an exact original product; unproved snapped coordinates refuse.
///
/// # Errors
/// Native cancellation/internal defects propagate unchanged. Ops must check the shared
/// `MeshWork` after this call before classifying a refusal or adopting the same final body.
pub fn certify_prismatic_reconstruction_from_source_with_work<'a, 'original: 'a, 'proof>(
    k: &mut Kernel,
    work: &MeshWork,
    source: &SourceCertificate<'original, 'proof>,
    prepared: &PreparedMesh,
    candidate: &'a mut Brep,
    request: &super::product_driver::PrismaticConstructionClaim,
    tolerance: f64,
) -> Result<ReconstructionVerdict<'a>> {
    work.spend_core(k, 0)?;
    let answer = final_impl(
        k,
        work,
        source,
        prepared,
        candidate,
        tolerance,
        Some(super::product_driver::ProductRequest::Explicit(request)),
    );
    work.spend_core(k, 0)?;
    answer
}
/// Derive constant-section correspondence from two explicitly selected actual
/// caps (or one automatically proposed pair), then consume the SAME source analysis
/// and final native body. Numerical
/// association creates claims only; both filled caps and every side are proved.
/// This construction never retries a different rim assignment or theorem.
///
/// # Errors
/// Native cancellation/internal errors propagate; callers check the shared work
/// latch before adopting the final unchanged candidate or classifying refusal.
pub fn certify_native_prismatic_reconstruction_from_source_with_work<'a, 'original: 'a, 'proof>(
    k: &mut Kernel,
    work: &MeshWork,
    source: &SourceCertificate<'original, 'proof>,
    prepared: &PreparedMesh,
    candidate: &'a mut Brep,
    normal: [f64; 3],
    caps: Option<[crate::topology::FaceId; 2]>,
    tolerance: f64,
) -> Result<ReconstructionVerdict<'a>> {
    work.spend_core(k, 0)?;
    let answer = final_impl(
        k,
        work,
        source,
        prepared,
        candidate,
        tolerance,
        Some(super::product_driver::ProductRequest::NativeCaps { normal, caps }),
    );
    work.spend_core(k, 0)?;
    answer
}
/// Certify ONE explicitly proposed endpoint product using the SAME original
/// source preflight. The proposal supplies geometric data only; Core constructs
/// exact endpoints, proves full-time motion, and consumes both whole caps/every
/// side/material obligation on the unchanged actual candidate. No other theorem
/// is tried after a refusal. The prior displacement is added only by CompleteProduct.
///
/// # Errors
/// Native cancellation/internal errors propagate unchanged; callers check the
/// shared MeshWork latch before adopting or classifying a refusal.
pub fn certify_native_endpoint_prismatic_reconstruction_from_source_with_work<
    'a,
    'original: 'a,
    'proof,
>(
    k: &mut Kernel,
    work: &MeshWork,
    source: &SourceCertificate<'original, 'proof>,
    prepared: &PreparedMesh,
    candidate: &'a mut Brep,
    proposal: &super::endpoint_proposal::PrismaticEndpointProposal,
    caps: Option<[crate::topology::FaceId; 2]>,
    tolerance: f64,
) -> Result<ReconstructionVerdict<'a>> {
    work.spend_core(k, 0)?;
    let answer = final_impl(
        k,
        work,
        source,
        prepared,
        candidate,
        tolerance,
        Some(super::product_driver::ProductRequest::NativeEndpointCaps { proposal, caps }),
    );
    work.spend_core(k, 0)?;
    answer
}

/// Propose ONE normal-translation endpoint model for a chosen construction event.
/// This returns untrusted data only: it neither proves a source motion nor accepts
/// a final body. Pass the result, SAME source token, prepared input and shared work
/// to `certify_native_endpoint_prismatic_reconstruction_from_source_with_work`.
/// No alternative frame, partner assignment or theorem is tried after proof refusal.
///
/// # Errors
/// Typed candidate refusal for nonfinite/tied/ambiguous associations or invalid
/// construction levels, original native cancellation and shared budget exhaustion.
pub fn propose_prismatic_endpoints_with_work(
    k: &Kernel,
    work: &MeshWork,
    source: &SourceCertificate<'_, '_>,
    tool: &super::super::PrismTool,
) -> super::super::Result<super::endpoint_proposal::PrismaticEndpointProposal> {
    work.check(k)?;
    let answer = super::endpoint_proposal::propose_from_source(k, work, &source.proof, tool);
    work.check(k)?;
    answer
}

/// One chosen ordinary product, bound to the same original source and workflow.
/// It is NOT an acceptance token. Its endpoint event is fixed before construction;
/// a final refusal never selects another axis, plan, family or theorem.
pub struct ChosenAnalyticPrism<'selection, 'source, 'proof> {
    source: &'selection SourceCertificate<'source, 'proof>,
    work: &'selection MeshWork,
    plan: super::super::PrismaticPlan,
    endpoints: super::endpoint_proposal::PrismaticEndpointProposal,
    tolerance: f64,
}
impl<'source, 'proof> ChosenAnalyticPrism<'_, 'source, 'proof> {
    /// Borrowed candidate data; neither mutation nor an adoption status is exposed.
    pub fn tool(&self) -> &super::super::PrismTool {
        &self.plan.tool
    }

    /// Build the fixed candidate using the SAME existing AnalyticV1 native builder.
    /// Ops must finish/export/import normally before calling `certify_final`.
    /// # Errors
    /// Existing native errors/cancellation and the shared workflow budget.
    pub fn build_native_candidate(&self, k: &mut Kernel) -> super::super::Result<Brep> {
        self.work.check(k)?;
        let result = super::super::analytic::build_prism_with_work(k, self.work, &self.plan.tool);
        if matches!(&result, Err(SolidError::PortInvariant { .. })) {
            return result.map_err(super::super::MeshError::from);
        }
        self.work.check(k)?;
        result.map_err(super::super::MeshError::from)
    }

    /// Certify ONLY the exact final canonical body supplied by Ops, through the
    /// existing complete product/motion/native-CW/material theorem. The prior
    /// motion bound is added once there; this wrapper adds no bound of its own.
    /// # Errors
    /// Original native errors/cancellation; Undecided is never a fallback signal.
    pub fn certify_final<'body>(
        &self,
        k: &mut Kernel,
        prepared: &PreparedMesh,
        candidate: &'body mut Brep,
    ) -> Result<ReconstructionVerdict<'body>>
    where
        'source: 'body,
    {
        certify_native_endpoint_prismatic_reconstruction_from_source_with_work(
            k,
            self.work,
            self.source,
            prepared,
            candidate,
            &self.endpoints,
            None,
            self.tolerance,
        )
    }
}

/// Choose one source-only product event using the SAME existing reconstruction
/// graph/fitter. The original SourceCertificate is reused; no second weld or
/// topology proof and no moved MeshInput is made. Broader shoulder decomposition
/// remains candidate-only until original cut/cap ancestry and final proof exist.
///
/// # Errors
/// Original cancellation, shared budget, source-identity mismatch, unsupported
/// guided multi-feature data or ambiguous endpoint steering. No retry after choice.
pub fn choose_analytic_prism_from_source_with_work<'selection, 'source: 'proof, 'proof>(
    k: &Kernel,
    work: &'selection MeshWork,
    source: &'selection SourceCertificate<'source, 'proof>,
    prepared: &PreparedMesh,
    tolerance: f64,
) -> super::super::Result<Option<ChosenAnalyticPrism<'selection, 'source, 'proof>>> {
    use super::super::{analytic, MeshError};
    use crate::math::Vec3;
    work.check(k)?;
    super::super::regions::checked_tolerance(tolerance)?;
    let compare = source
        .source
        .positions
        .len()
        .checked_add(source.source.triangles.len())
        .and_then(|n| n.checked_mul(3))
        .ok_or_else(|| super::super::types::invalid("source identity count overflow"))?;
    work.spend(k, compare)?;
    if source.source != &prepared.original {
        return Err(MeshError::Refused {
            stage: "chosen analytic product",
            detail: "prepared input differs from original source certificate".into(),
        });
    }
    if !prepared.features.is_empty() || !prepared.provenance.patches.is_empty() {
        return Err(MeshError::Refused {
            stage: "chosen analytic product",
            detail: "guided multi-feature construction requires its complete final theorem".into(),
        });
    }
    if !prepared.provenance.faceted_source_patches.is_empty() {
        return Err(MeshError::Refused {
            stage: "chosen analytic product",
            detail: "faceted and ordinary product events cannot be combined".into(),
        });
    }
    let v = source.proof.alias_count();
    let t = source.proof.retained_count;
    let slots = v
        .checked_add(t)
        .ok_or_else(|| super::super::types::invalid("source candidate count overflow"))?;
    work.spend(k, slots)?;
    // Point and triangle arrays have three initialized coordinates/indices each,
    // plus two Vec headers (3 logical fields each); no arbitrary expansions.
    work.reserve_cells(
        k,
        slots
            .checked_mul(3)
            .and_then(|n| n.checked_add(6))
            .ok_or_else(|| super::super::types::invalid("source candidate storage overflow"))?,
    )?;
    let mut positions = Vec::new();
    positions
        .try_reserve_exact(v)
        .map_err(|_| super::super::types::invalid("cannot allocate source candidate positions"))?;
    for alias in 0..v {
        work.spend(k, 0)?;
        let alias = u32::try_from(alias)
            .map_err(|_| super::super::types::invalid("alias index overflow"))?;
        let p = source
            .proof
            .position(alias)
            .ok_or_else(|| super::super::types::invalid("missing proved source alias"))?;
        positions.push(Vec3::from_array(p));
    }
    let mut triangles = Vec::new();
    triangles
        .try_reserve_exact(t)
        .map_err(|_| super::super::types::invalid("cannot allocate source candidate triangles"))?;
    for ids in source.proof.aliases.iter().flatten() {
        work.spend(k, 0)?;
        triangles.push(*ids);
    }
    let mesh = analytic::TriMesh {
        positions,
        triangles,
    };
    let axes = analytic::ranked_axes_with_work(k, work, &mesh)?;
    for axis in axes {
        let proposal = analytic::propose_prism_with_work(
            k,
            work,
            analytic::MeshView {
                positions: &mesh.positions,
                triangles: &mesh.triangles,
            },
            axis,
            tolerance,
        )?;
        work.check(k)?;
        if let Some(proposal) = proposal {
            // Selection is complete here. All subsequent failures propagate;
            // neither endpoint steering nor final proof can resume this search.
            let plan = proposal.into_plan(k, work)?;
            let endpoints = propose_prismatic_endpoints_with_work(k, work, source, &plan.tool)?;
            return Ok(Some(ChosenAnalyticPrism {
                source,
                work,
                plan,
                endpoints,
                tolerance,
            }));
        }
    }
    work.check(k)?;
    Ok(None)
}

/// A fixed source-only cone or frustum choice, borrowing the original source proof.
/// Its projected coordinates and fitted circles are construction data only.
pub struct ChosenRadialSolid<'selection, 'source, 'proof> {
    source: &'selection SourceCertificate<'source, 'proof>,
    work: &'selection MeshWork,
    proposal: super::radial_proposal::RadialSolidProposal,
    tolerance: f64,
}

impl<'source, 'proof> ChosenRadialSolid<'_, 'source, 'proof> {
    /// Build the selected Native primitive; only its normal canonical
    /// export/re-import can supply the final body to the complete proof.
    ///
    /// # Errors
    /// Typed Native construction, cancellation or workflow budget failure.
    pub fn build_native_candidate(&self, k: &mut Kernel) -> super::super::Result<Brep> {
        self.proposal.build_candidate(k, self.work)
    }

    /// Prove the source cap-and-band layout and actual Native topology,
    /// trimmed surface and edge geometry against ONE axial model.
    ///
    /// # Errors
    /// Original Native errors, cancellation and workflow bounds propagate.
    pub fn certify_final<'body>(
        &self,
        k: &mut Kernel,
        candidate: &'body mut Brep,
    ) -> Result<ReconstructionVerdict<'body>>
    where
        'source: 'body,
    {
        use super::radial_frame::{build_axial_model, AxialSourceView};
        use super::radial_solid_source::prove_source_radial_solid_with_work;
        use super::radial_source::prove_source_radial_patch_with_work;
        use super::source_motion::{prove_source_motion_with_work, SourceMotionVerdict};
        use crate::blend::fillet_section::interval::Ivl;

        self.work.spend_core(k, 0)?;
        let standing = match crate::topology::brep::validation::soundness(k, candidate) {
            Ok(standing) => standing,
            Err(error) if super::errors::expected(&error) => {
                return Ok(ReconstructionVerdict::Undecided(
                    ReconstructionRefusal::NativeSolidValidity,
                ));
            }
            Err(err) => return Err(err),
        };
        if !standing.manifold || !standing.sound() {
            return Ok(ReconstructionVerdict::Undecided(
                ReconstructionRefusal::NativeSolidValidity,
            ));
        }
        let result = (|| {
            let model = build_axial_model(
                k,
                self.work,
                self.source.proof.alias_count(),
                &self.proposal.chart,
            )?;
            let motion = match prove_source_motion_with_work(
                k,
                self.work,
                &self.source.proof,
                model.points(),
                self.tolerance,
            )? {
                SourceMotionVerdict::Proven(motion) => motion,
                SourceMotionVerdict::Undecided(reason) => {
                    return Ok(ReconstructionVerdict::Undecided(
                        ReconstructionRefusal::GeometryCorrespondence { reason },
                    ));
                }
            };
            let moved = AxialSourceView::bind(&model, &motion)?;
            let patch = prove_source_radial_patch_with_work(
                k,
                self.work,
                &moved,
                &self.proposal.side,
                self.tolerance,
            )?;
            let original = prove_source_radial_solid_with_work(k, self.work, &patch)?;
            if original.filled_caps()
                != self
                    .proposal
                    .side
                    .law
                    .radius
                    .iter()
                    .filter(|&&r| r > 0.)
                    .count()
            {
                return Err(SolidError::Unsupported {
                    operation: "mesh_reconstruction::certificate::chosen_radial_solid",
                    reason: "source caps and the chosen exact pole/rim inventory differ",
                });
            }
            let prior = original.side().world_upper();
            let allowance = (Ivl::from(self.tolerance) - Ivl::from(prior)).lo;
            let repaired = super::native_radial_topology::prove_native_radial_boundary_with_work(
                k,
                self.work,
                candidate,
                &self.proposal.chart,
                self.proposal.side.center,
                self.proposal.side.law,
                allowance,
            )?;
            let bound = Ivl::from(prior) + Ivl::from(repaired);
            if !bound.is_finite() || bound.hi > self.tolerance {
                return Err(SolidError::Unsupported {
                    operation: "mesh_reconstruction::certificate::chosen_radial_solid",
                    reason: "complete radial solid boundary exceeds its supplied tolerance",
                });
            }
            Ok(ReconstructionVerdict::Proven(ReconstructionCertificate {
                _source: self.source.source,
                _candidate: candidate,
                stored_boundary_error_upper: bound.hi,
            }))
        })();
        self.work.spend_core(k, 0)?;
        match result {
            Err(SolidError::Unsupported { reason, .. }) => Ok(ReconstructionVerdict::Undecided(
                ReconstructionRefusal::GeometryCorrespondence { reason },
            )),
            other => other,
        }
    }
}

/// Choose one standalone cone or frustum before construction, using original aliases
/// and deterministic preparation axes. Once a choice is made its refused
/// source or Native certificate never selects another conversion family.
///
/// # Errors
/// Original source identity, cancellation and work constraints.
pub fn choose_radial_solid_from_source_with_work<'selection, 'source, 'proof>(
    k: &Kernel,
    work: &'selection MeshWork,
    source: &'selection SourceCertificate<'source, 'proof>,
    prepared: &PreparedMesh,
    tolerance: f64,
) -> super::super::Result<Option<ChosenRadialSolid<'selection, 'source, 'proof>>> {
    use super::super::{types::invalid, MeshError};
    work.check(k)?;
    super::super::regions::checked_tolerance(tolerance)?;
    let count = source
        .source
        .positions
        .len()
        .checked_add(source.source.triangles.len())
        .and_then(|n| n.checked_mul(3))
        .ok_or_else(|| invalid("radial source identity count overflow"))?;
    work.spend(k, count)?;
    if source.source != &prepared.original {
        return Err(MeshError::Refused {
            stage: "chosen radial solid",
            detail: "source identity differs".into(),
        });
    }
    if !prepared.features.is_empty()
        || !prepared.provenance.patches.is_empty()
        || !prepared.provenance.faceted_source_patches.is_empty()
    {
        return Ok(None);
    }
    let Some(proposal) = super::radial_proposal::propose_radial_solid_with_work(
        k,
        work,
        &source.original_view(),
        &prepared.axes,
        tolerance,
    )?
    else {
        return Ok(None);
    };
    Ok(Some(ChosenRadialSolid {
        source,
        work,
        proposal,
        tolerance,
    }))
}

/// A determined bored-stock candidate, bound to the same original retained
/// inventory; construction never changes the selected side/cap/annulus claim.
pub struct ChosenBoredStock<'s, 'raw, 'proof> {
    source: &'s SourceCertificate<'raw, 'proof>,
    work: &'s MeshWork,
    proposal: super::bored_stock_proposal::BoredStockProposal,
    tolerance: f64,
}
impl<'raw, 'proof> ChosenBoredStock<'_, 'raw, 'proof> {
    /// Create the selected Native body, before canonical record export/reload.
    ///
    /// # Errors
    /// Typed Native construction, cancellation and workflow bounds.
    pub fn build_native_candidate(&self, k: &mut Kernel) -> super::super::Result<Brep> {
        self.proposal.build_candidate(k, self.work)
    }

    /// Verify the original caps/stock and every concave band; then verify the
    /// exact final canonical Native body against that same finite solid.
    ///
    /// # Errors
    /// Original Native, budget and cancellation errors propagate.
    pub fn certify_final<'body>(
        &self,
        k: &mut Kernel,
        candidate: &'body mut Brep,
    ) -> Result<ReconstructionVerdict<'body>>
    where
        'raw: 'body,
    {
        use super::radial_frame::{build_axial_model, AxialSourceView};
        use super::source_motion::{prove_source_motion_with_work, SourceMotionVerdict};
        use crate::blend::fillet_section::interval::Ivl;
        let standing = match crate::topology::brep::validation::soundness(k, candidate) {
            Ok(standing) => standing,
            Err(e) if super::errors::expected(&e) => {
                return Ok(ReconstructionVerdict::Undecided(
                    ReconstructionRefusal::NativeSolidValidity,
                ))
            }
            Err(e) => return Err(e),
        };
        if !standing.manifold || !standing.sound() {
            return Ok(ReconstructionVerdict::Undecided(
                ReconstructionRefusal::NativeSolidValidity,
            ));
        }
        let assembled = (|| {
            let chart = build_axial_model(
                k,
                self.work,
                self.source.proof.alias_count(),
                &self.proposal.charts[2],
            )?;
            let moving = match prove_source_motion_with_work(
                k,
                self.work,
                &self.source.proof,
                chart.points(),
                self.tolerance,
            )? {
                SourceMotionVerdict::Proven(m) => m,
                SourceMotionVerdict::Undecided(reason) => {
                    return Ok(ReconstructionVerdict::Undecided(
                        ReconstructionRefusal::GeometryCorrespondence { reason },
                    ))
                }
            };
            let view = AxialSourceView::bind(&chart, &moving)?;
            let build_chart = |axis| {
                build_axial_model(
                    k,
                    self.work,
                    self.source.proof.alias_count(),
                    &self.proposal.charts[axis],
                )
            };
            let charts = [
                self.proposal
                    .bores
                    .iter()
                    .any(|b| b.axis == 0)
                    .then(|| build_chart(0))
                    .transpose()?,
                self.proposal
                    .bores
                    .iter()
                    .any(|b| b.axis == 1)
                    .then(|| build_chart(1))
                    .transpose()?,
            ];
            let other = [
                charts[0]
                    .as_ref()
                    .map(|m| AxialSourceView::bind_same_world(k, self.work, m, &moving))
                    .transpose()?,
                charts[1]
                    .as_ref()
                    .map(|m| AxialSourceView::bind_same_world(k, self.work, m, &moving))
                    .transpose()?,
            ];
            let views = [other[0].as_ref(), other[1].as_ref(), Some(&view)];
            let original = super::bored_stock_source::prove_bored_stock_source_with_work(
                k,
                self.work,
                views,
                &self.proposal,
                self.tolerance,
            )?;
            let allowance = (Ivl::from(self.tolerance) - Ivl::from(original)).lo;
            let actual = super::native_bored_stock::prove_native_bored_stock_with_work(
                k,
                self.work,
                candidate,
                &self.proposal,
                allowance,
            )?;
            let bound = Ivl::from(original) + Ivl::from(actual);
            if !bound.is_finite() || bound.hi > self.tolerance {
                return Err(SolidError::Unsupported {
                    operation: "mesh_reconstruction::certificate::chosen_bored_stock",
                    reason: "whole native stock boundary exceeds the original tolerance",
                });
            }
            Ok(ReconstructionVerdict::Proven(ReconstructionCertificate {
                _source: self.source.source,
                _candidate: candidate,
                stored_boundary_error_upper: bound.hi,
            }))
        })();
        self.work.spend_core(k, 0)?;
        match assembled {
            Err(SolidError::Unsupported { reason, .. }) => Ok(ReconstructionVerdict::Undecided(
                ReconstructionRefusal::GeometryCorrespondence { reason },
            )),
            other => other,
        }
    }
}

/// Choose one rectangular source stock with a through-hole containing multiple
/// axial bands. This choice is completed before any construction takes place.
///
/// # Errors
/// Typed input, cancellation and work bound failures.
pub fn choose_bored_stock_from_source_with_work<'s, 'raw, 'proof>(
    k: &Kernel,
    work: &'s MeshWork,
    source: &'s SourceCertificate<'raw, 'proof>,
    prepared: &PreparedMesh,
    tolerance: f64,
) -> super::super::Result<Option<ChosenBoredStock<'s, 'raw, 'proof>>> {
    use super::super::{types::invalid, MeshError};
    work.check(k)?;
    let count = source
        .source
        .positions
        .len()
        .checked_add(source.source.triangles.len())
        .and_then(|n| n.checked_mul(3))
        .ok_or_else(|| invalid("stock source identity count overflow"))?;
    work.spend(k, count)?;
    if source.source != &prepared.original {
        return Err(MeshError::Refused {
            stage: "chosen bored stock",
            detail: "source identity differs".into(),
        });
    }
    if !prepared.features.is_empty()
        || !prepared.provenance.patches.is_empty()
        || !prepared.provenance.faceted_source_patches.is_empty()
    {
        return Ok(None);
    }
    let proposal = super::bored_stock_proposal::propose_rectangular_bored_stock_with_work(
        k,
        work,
        &source.original_view(),
        tolerance,
    )?;
    Ok(proposal.map(|proposal| ChosenBoredStock {
        source,
        work,
        proposal,
        tolerance,
    }))
}

/// One candidate convenience using one shared source/final budget. Multi-candidate
/// workflows preflight once and call `certify_reconstruction_from_source_with_work`.
pub fn certify_reconstruction_with_work<'a>(
    k: &mut Kernel,
    work: &MeshWork,
    source: &'a MeshInput,
    prepared: &PreparedMesh,
    candidate: &'a mut Brep,
    tolerance: f64,
) -> Result<ReconstructionVerdict<'a>> {
    let proof = match certify_source_with_work(k, work, source, &prepared.weld)? {
        SourceVerdict::Proven(p) => p,
        SourceVerdict::Undecided(why) => return Ok(ReconstructionVerdict::Undecided(why)),
    };
    certify_reconstruction_from_source_with_work(k, work, &proof, prepared, candidate, tolerance)
}
/// Single-job entry. Public multi-stage Ops commands keep their own shared `MeshWork`.
pub fn certify_reconstruction<'a>(
    k: &mut Kernel,
    source: &'a MeshInput,
    prepared: &PreparedMesh,
    candidate: &'a mut Brep,
    tolerance: f64,
) -> Result<ReconstructionVerdict<'a>> {
    let work = MeshWork::new();
    certify_reconstruction_with_work(k, &work, source, prepared, candidate, tolerance)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::KernelOptions;
    use crate::math::Point3;
    fn original_box() -> MeshInput {
        MeshInput {
            positions: vec![
                [0., 0., 0.],
                [20., 0., 0.],
                [20., 10., 0.],
                [0., 10., 0.],
                [0., 0., 5.],
                [20., 0., 5.],
                [20., 10., 5.],
                [0., 10., 5.],
            ],
            triangles: vec![
                [0, 2, 1],
                [0, 3, 2],
                [4, 5, 6],
                [4, 6, 7],
                [0, 1, 5],
                [0, 5, 4],
                [1, 2, 6],
                [1, 6, 5],
                [2, 3, 7],
                [2, 7, 6],
                [3, 0, 4],
                [3, 4, 7],
            ],
        }
    }
    fn endpoint_proposal_for_box(
        prepared: &PreparedMesh,
        origin_x: f64,
    ) -> super::super::endpoint_proposal::PrismaticEndpointProposal {
        use super::super::endpoint_proposal::{EndpointAlias, PrismaticEndpointProposal};
        PrismaticEndpointProposal {
            origin: [origin_x, 0., 0.],
            a: [1., 0., 0.],
            b: [0., 1., 0.],
            translation_factor: 5.,
            aliases: prepared
                .weld
                .vertices
                .iter()
                .map(|v| EndpointAlias {
                    uv: [v.position[0], v.position[1]],
                    translated: v.position[2] > 4.,
                })
                .collect(),
        }
    }
    #[test]
    fn public_endpoint_entry_keeps_original_source_and_exact_dyadic_box_coordinates() {
        for noise in [0., 1e-9] {
            let mut k = Kernel::new(&KernelOptions::default());
            let work = MeshWork::new();
            let mut input = original_box();
            input.positions[6][2] += noise;
            let prepared = super::super::super::prepare::prepare_conversion_with_work(
                &k,
                &work,
                &input,
                0.05,
                &[],
            )
            .unwrap();
            let source = match certify_source_with_work(&k, &work, &input, &prepared.weld).unwrap()
            {
                SourceVerdict::Proven(p) => p,
                SourceVerdict::Undecided(why) => panic!("{why:?}"),
            };
            let proposal = endpoint_proposal_for_box(&prepared, 2.0_f64.powi(-60));
            let mut body =
                crate::primitive::api_primitives::create_box(&mut k, Point3::ZERO, 20., 10., 5.)
                    .unwrap();
            let expected = core::ptr::from_ref(&body);
            let verdict = certify_native_endpoint_prismatic_reconstruction_from_source_with_work(
                &mut k, &work, &source, &prepared, &mut body, &proposal, None, 0.05,
            )
            .unwrap();
            match verdict {
                ReconstructionVerdict::Proven(p) => {
                    assert!(core::ptr::eq(p._source, core::ptr::from_ref(&input)));
                    assert!(core::ptr::eq(p._candidate, expected));
                    assert!(p.boundary_error_upper() > 0. && p.boundary_error_upper() < 1e-8);
                }
                ReconstructionVerdict::Undecided(why) => panic!("{why:?}"),
            }
            // Original raw arrays and SourceCertificate remain unchanged.
            assert_eq!(source.source.positions[6][2], input.positions[6][2]);
        }
    }
    #[test]
    fn exact_endpoint_frame_and_alias_parameters_do_not_round_away_components() {
        use super::super::endpoint_proposal::{
            build_endpoint_model, EndpointAlias, PrismaticEndpointProposal,
        };
        let k = Kernel::default();
        let work = MeshWork::new();
        let proposal = PrismaticEndpointProposal {
            origin: [20., 0., 0.],
            a: [0.75, 0.5, 0.25],
            b: [-0.5, 0.75, 0.],
            translation_factor: 8.,
            aliases: vec![
                EndpointAlias {
                    uv: [2.0_f64.powi(-60), 0.],
                    translated: false,
                },
                EndpointAlias {
                    uv: [2.0_f64.powi(-60), 0.],
                    translated: true,
                },
            ],
        };
        let model = build_endpoint_model(&k, &work, 2, &proposal).unwrap();
        let [low, high] = model.points.as_slice() else {
            panic!("two points")
        };
        assert_eq!(crate::geom::expansion::to_f64(&low[0]), 20.);
        assert!(!super::super::exact_geometry::zero(
            &super::super::exact_geometry::sub(&low[0], &vec![20.]).unwrap()
        ));
        let translation = super::super::exact_geometry::difference(high, low).unwrap();
        assert!(
            super::super::exact_geometry::cross(&translation, &model.normal)
                .unwrap()
                .iter()
                .all(super::super::exact_geometry::zero)
        );
        assert!(model
            .points
            .iter()
            .flat_map(|p| p.iter())
            .all(|c| c.len() <= 13));
    }
    #[test]
    fn endpoint_factory_refuses_nonfinite_degenerate_out_of_range_and_wrong_alias_inventory() {
        use super::super::endpoint_proposal::{
            build_endpoint_model, EndpointAlias, PrismaticEndpointProposal,
        };
        let k = Kernel::default();
        let base = PrismaticEndpointProposal {
            origin: [0.; 3],
            a: [1., 0., 0.],
            b: [0., 1., 0.],
            translation_factor: 5.,
            aliases: vec![EndpointAlias {
                uv: [0., 0.],
                translated: false,
            }],
        };
        let mut bad = base.clone();
        bad.origin[0] = f64::NAN;
        assert!(build_endpoint_model(&k, &MeshWork::new(), 1, &bad).is_err());
        let mut bad = base.clone();
        bad.aliases[0].uv[1] = f64::INFINITY;
        assert!(build_endpoint_model(&k, &MeshWork::new(), 1, &bad).is_err());
        let mut bad = base.clone();
        bad.b = bad.a;
        assert!(build_endpoint_model(&k, &MeshWork::new(), 1, &bad).is_err());
        let mut bad = base.clone();
        bad.translation_factor = 0.;
        assert!(build_endpoint_model(&k, &MeshWork::new(), 1, &bad).is_err());
        let mut bad = base.clone();
        bad.a[0] = 1e-200;
        bad.b[1] = 1e-200;
        assert!(build_endpoint_model(&k, &MeshWork::new(), 1, &bad).is_err());
        assert!(build_endpoint_model(&k, &MeshWork::new(), 2, &base).is_err());
    }
    #[test]
    fn endpoint_factory_uses_same_budget_and_preserves_native_cancel() {
        use super::super::endpoint_proposal::{
            build_endpoint_model, EndpointAlias, PrismaticEndpointProposal,
        };
        let mut k = Kernel::default();
        let data = PrismaticEndpointProposal {
            origin: [0.; 3],
            a: [1., 0., 0.],
            b: [0., 1., 0.],
            translation_factor: 5.,
            aliases: vec![EndpointAlias {
                uv: [0., 0.],
                translated: false,
            }],
        };
        let work = MeshWork::new();
        work.reserve_cells(&k, 2_000_000 - 10).unwrap();
        assert!(build_endpoint_model(&k, &work, 1, &data).is_err());
        assert!(matches!(
            work.check(&k),
            Err(super::super::super::MeshError::BudgetExceeded { .. })
        ));
        let token = crate::kernel::CancelToken::new();
        k.set_cancel_token(token.clone());
        token.cancel();
        assert!(
            matches!(build_endpoint_model(&k, &MeshWork::new(), 1, &data), Err(e) if e.is_cancelled())
        );
    }

    // The explicit native-box fixture has a UV trim that crosses the Plane clamp
    // boundary by 2^-40. The nominal trim image has a real kink: claiming zero
    // boundary error is false even though a bounded tolerant witness exists.
    fn native_box_has_strict_zero_refusal_and_bounded_witness(input: &MeshInput) {
        let mut k = Kernel::new(&KernelOptions::default());
        let mut prepared =
            super::super::super::prepare::prepare_conversion(&k, input, 0.05, &[]).unwrap();
        let work = MeshWork::new();
        let source = match certify_source_with_work(&k, &work, input, &prepared.weld).unwrap() {
            SourceVerdict::Proven(p) => p,
            SourceVerdict::Undecided(why) => panic!("source proof declined: {why:?}"),
        };
        let mut b = super::super::native_profile::box_with_noniso_clamp_trim(&mut k, &work);
        assert!(
            matches!(
                certify_reconstruction_from_source_with_work(
                    &mut k, &work, &source, &prepared, &mut b, 0.05,
                )
                .unwrap(),
                ReconstructionVerdict::Undecided(
                    ReconstructionRefusal::GeometryCorrespondence { .. }
                )
            ),
            "the actual non-ISO clamp image must not acquire a false exact-zero proof"
        );
        // These are untrusted original triangle-ID groups, independently checked
        // by the complete source-cell and final actual-face incidence proofs.
        // The optional last facet is exactly zero-area and has already been
        // proved redundant by source preflight; it is not a retained 2-cell.
        let plan = super::super::super::faceted_plan_with_work(&k, &work, input, 0.05).unwrap();
        prepared.provenance.faceted_source_patches =
            plan.into_source_patch_claims_with_work(&k, &work).unwrap();
        match certify_reconstruction_from_source_with_work(
            &mut k, &work, &source, &prepared, &mut b, 0.05,
        )
        .unwrap()
        {
            ReconstructionVerdict::Proven(p) => {
                let bound = p.boundary_error_upper();
                assert!(bound.is_finite() && bound > 0.0);
                // This is a computed roundoff-scale enclosure, rather than
                // merely echoing the requested 0.05 conversion tolerance.
                assert!(bound <= 1e-9, "unexpected native box enclosure: {bound}");
            }
            ReconstructionVerdict::Undecided(why) => {
                panic!("complete bounded native box proof declined: {why:?}")
            }
        }
        // The faceted family above is actually provable. Declaring a different
        // required product family must not silently adopt that successful fallback.
        let request = super::super::product_driver::PrismaticConstructionClaim {
            normal: [0., 0., 1.],
            lower: super::super::product_driver::ProductCapClaim {
                face: b.face_list()[0],
                rims: Vec::new(),
            },
            upper: super::super::product_driver::ProductCapClaim {
                face: b.face_list()[1],
                rims: Vec::new(),
            },
        };
        assert!(matches!(
            certify_prismatic_reconstruction_from_source_with_work(
                &mut k, &work, &source, &prepared, &mut b, &request, 0.05
            )
            .unwrap(),
            ReconstructionVerdict::Undecided(ReconstructionRefusal::GeometryCorrespondence {
                reason: "contradictory faceted and prismatic construction families"
            })
        ));
        work.check(&k).unwrap();
    }
    #[test]
    fn native_box_rejects_false_exact_zero_and_proves_a_bounded_witness() {
        native_box_has_strict_zero_refusal_and_bounded_witness(&original_box());
    }
    #[test]
    fn exact_redundant_line_facet_keeps_original_zero_area_behavior() {
        let mut input = original_box();
        input.positions.push([10., 0., 0.]);
        input.triangles.push([0, 8, 1]);
        native_box_has_strict_zero_refusal_and_bounded_witness(&input);
    }
    #[test]
    fn an_epsilon_small_nonzero_facet_is_not_waived_as_zero_area() {
        let k = Kernel::new(&KernelOptions::default());
        let mut input = original_box();
        input.positions.push([10., 1e-12, 0.]);
        input.triangles.push([0, 8, 1]);
        let prepared =
            super::super::super::prepare::prepare_conversion(&k, &input, 0.05, &[]).unwrap();
        let work = MeshWork::new();
        assert!(matches!(
            certify_source_with_work(&k, &work, &input, &prepared.weld).unwrap(),
            SourceVerdict::Undecided(ReconstructionRefusal::SourceTopology { .. })
        ));
    }

    fn automatic_endpoint_box_tool(rotated: bool) -> super::super::super::PrismTool {
        use crate::math::{Vec2, Vec3};
        let turn = Vec3::new(1., 2., 3.);
        let frame = crate::eval::Frame {
            origin: if rotated { [5., -7., 3.] } else { [0.; 3] },
            x_axis: if rotated {
                Vec3::X.rotate_vec_about_axis(turn, 0.8).to_array()
            } else {
                [1., 0., 0.]
            },
            y_axis: if rotated {
                Vec3::Y.rotate_vec_about_axis(turn, 0.8).to_array()
            } else {
                [0., 1., 0.]
            },
        };
        super::super::super::PrismTool {
            frame,
            regions: vec![crate::prism::profile::Region2 {
                outer: super::super::super::profile::polygon(&[
                    Vec2::new(0., 0.),
                    Vec2::new(20., 0.),
                    Vec2::new(20., 10.),
                    Vec2::new(0., 10.),
                ]),
                holes: Vec::new(),
            }],
            start: 0.,
            end: 5.,
        }
    }
    fn exercise_automatic_endpoint_box(rotated: bool, noise: f64, interior: bool) {
        let mut k = Kernel::new(&KernelOptions::default());
        let work = MeshWork::new();
        let tool = automatic_endpoint_box_tool(rotated);
        let mut input = original_box();
        if interior {
            input.positions.push([10., 5., 0.]);
            // Original lower-cap orientation remains outward -Z, with no upper mate.
            input
                .triangles
                .splice(0..2, [[0, 8, 1], [1, 8, 2], [2, 8, 3], [3, 8, 0]]);
        }
        for (index, p) in input.positions.iter_mut().enumerate() {
            let [x, y, z] = *p;
            *p = crate::prism::profile::to_world(&tool.frame, crate::math::Vec2::new(x, y), z)
                .to_array();
            if rotated {
                for c in p.iter_mut() {
                    *c = f64::from(*c as f32);
                }
            }
            for (axis, c) in p.iter_mut().enumerate() {
                *c += if (index + axis) % 2 == 0 {
                    noise
                } else {
                    -noise
                };
            }
        }
        let before_positions = input.positions.clone();
        let before_triangles = input.triangles.clone();
        let prepared = super::super::super::prepare::prepare_conversion_with_work(
            &k,
            &work,
            &input,
            0.05,
            &[],
        )
        .unwrap();
        let source = match certify_source_with_work(&k, &work, &input, &prepared.weld).unwrap() {
            SourceVerdict::Proven(p) => p,
            SourceVerdict::Undecided(why) => panic!("source preflight refused: {why:?}"),
        };
        let proposal = propose_prismatic_endpoints_with_work(&k, &work, &source, &tool).unwrap();
        assert_eq!(proposal.aliases.len(), prepared.weld.vertices.len());
        let lower: Vec<_> = proposal.aliases.iter().filter(|a| !a.translated).collect();
        let upper: Vec<_> = proposal.aliases.iter().filter(|a| a.translated).collect();
        assert_eq!(upper.len(), 4);
        assert_eq!(lower.len(), if interior { 5 } else { 4 });
        for high in upper {
            assert_eq!(lower.iter().filter(|low| low.uv == high.uv).count(), 1);
        }
        let mut body = crate::mesh_reconstruction::build_tool(
            &mut k,
            &crate::mesh_reconstruction::ToolGeometry::Prism(tool),
        )
        .unwrap();
        let expected = core::ptr::from_ref(&body);
        match certify_native_endpoint_prismatic_reconstruction_from_source_with_work(
            &mut k, &work, &source, &prepared, &mut body, &proposal, None, 0.05,
        )
        .unwrap()
        {
            ReconstructionVerdict::Proven(p) => {
                assert!(core::ptr::eq(p._source, core::ptr::from_ref(&input)));
                assert!(core::ptr::eq(p._candidate, expected));
                let bound = p.boundary_error_upper();
                assert!(bound.is_finite() && bound <= 0.05, "{bound}");
            }
            ReconstructionVerdict::Undecided(why) => {
                panic!("complete automatic endpoint proof refused: {why:?}")
            }
        }
        assert_eq!(input.positions, before_positions);
        assert_eq!(input.triangles, before_triangles);
        work.check(&k).unwrap();
    }
    #[test]
    fn automatic_endpoint_proposal_reaches_complete_original_box_entry() {
        exercise_automatic_endpoint_box(false, 0., false);
    }
    #[test]
    fn automatic_endpoint_proposal_keeps_cap_interior_without_an_opposite_vertex() {
        exercise_automatic_endpoint_box(false, 0., true);
    }
    #[test]
    fn automatic_endpoint_proposal_tests_whole_motion_for_shared_xyz_noise() {
        exercise_automatic_endpoint_box(false, 1e-9, false);
    }
    #[test]
    fn automatic_endpoint_proposal_tests_rotated_f32_source_through_full_product() {
        exercise_automatic_endpoint_box(true, 0., false);
    }
    #[test]
    fn automatic_partner_steering_refuses_ties_nonmutual_maps_missing_and_nonfinite_data() {
        use super::super::endpoint_proposal::{candidate_partners, EndpointAlias};
        use std::collections::BTreeSet;
        let k = Kernel::default();
        let mut rows = vec![
            EndpointAlias {
                uv: [0., 0.],
                translated: false,
            },
            EndpointAlias {
                uv: [1., 0.],
                translated: false,
            },
            EndpointAlias {
                uv: [2., 0.],
                translated: false,
            },
            EndpointAlias {
                uv: [0., 0.],
                translated: true,
            },
            EndpointAlias {
                uv: [1., 0.],
                translated: true,
            },
            EndpointAlias {
                uv: [2., 0.],
                translated: true,
            },
        ];
        let lower = BTreeSet::from([0, 1, 2]);
        let upper = BTreeSet::from([3, 4, 5]);
        let pairs = candidate_partners(&k, &MeshWork::new(), &rows, &lower, &upper).unwrap();
        assert_eq!(
            pairs.into_iter().collect::<Vec<_>>(),
            [(3, 0), (4, 1), (5, 2)]
        );
        rows[4].uv = rows[3].uv;
        assert!(matches!(
            candidate_partners(&k, &MeshWork::new(), &rows, &lower, &upper),
            Err(super::super::super::MeshError::Refused { .. })
        ));
        rows[4].uv = [1., 0.];
        rows[5].uv = [100., 0.];
        assert!(candidate_partners(&k, &MeshWork::new(), &rows, &lower, &upper).is_err());
        rows[5].uv = [2., 0.];
        assert!(
            candidate_partners(&k, &MeshWork::new(), &rows, &lower, &BTreeSet::from([3, 4]))
                .is_err()
        );
        assert!(candidate_partners(
            &k,
            &MeshWork::new(),
            &rows,
            &lower,
            &BTreeSet::from([0, 4, 5])
        )
        .is_err());
        rows[4].uv = [f64::INFINITY, 0.];
        assert!(candidate_partners(&k, &MeshWork::new(), &rows, &lower, &upper).is_err());
    }
    #[test]
    fn automatic_endpoint_proposal_refuses_invalid_or_tied_frames_and_preserves_budget_cancel() {
        use super::super::super::MeshError;
        let mut k = Kernel::default();
        let work = MeshWork::new();
        let input = original_box();
        let prepared = super::super::super::prepare::prepare_conversion_with_work(
            &k,
            &work,
            &input,
            0.05,
            &[],
        )
        .unwrap();
        let source = match certify_source_with_work(&k, &work, &input, &prepared.weld).unwrap() {
            SourceVerdict::Proven(p) => p,
            SourceVerdict::Undecided(why) => panic!("{why:?}"),
        };
        let mut tool = automatic_endpoint_box_tool(false);
        tool.start = -5.;
        assert!(matches!(
            propose_prismatic_endpoints_with_work(&k, &work, &source, &tool),
            Err(MeshError::Refused { .. })
        ));
        tool.start = 0.;
        tool.frame.y_axis = tool.frame.x_axis;
        assert!(propose_prismatic_endpoints_with_work(&k, &work, &source, &tool).is_err());
        tool.frame.y_axis = [0., 1., 0.];
        tool.end = f64::INFINITY;
        assert!(propose_prismatic_endpoints_with_work(&k, &work, &source, &tool).is_err());
        let scarce = MeshWork::new();
        scarce.reserve_cells(&k, 2_000_000 - 4).unwrap();
        let valid = automatic_endpoint_box_tool(false);
        assert!(matches!(
            propose_prismatic_endpoints_with_work(&k, &scarce, &source, &valid),
            Err(MeshError::BudgetExceeded { .. })
        ));
        let token = crate::kernel::CancelToken::new();
        k.set_cancel_token(token.clone());
        token.cancel();
        assert!(
            matches!(propose_prismatic_endpoints_with_work(&k, &scarce, &source, &tool),
            Err(MeshError::Kernel(e)) if e.is_cancelled())
        );
    }

    #[test]
    fn shared_8061_chosen_product_uses_original_source_and_complete_final_factory() {
        let mut k = Kernel::new(&KernelOptions::default());
        let work = MeshWork::new();
        let input = original_box();
        let before = input.clone();
        let prepared = super::super::super::prepare::prepare_conversion_with_work(
            &k,
            &work,
            &input,
            0.05,
            &[],
        )
        .unwrap();
        let source = match certify_source_with_work(&k, &work, &input, &prepared.weld).unwrap() {
            SourceVerdict::Proven(p) => p,
            SourceVerdict::Undecided(why) => panic!("{why:?}"),
        };
        let chosen =
            choose_analytic_prism_from_source_with_work(&k, &work, &source, &prepared, 0.05)
                .unwrap()
                .unwrap();
        assert!(core::ptr::eq(chosen.source, &source));
        assert!(core::ptr::eq(chosen.work, &work));
        let mut body = chosen.build_native_candidate(&mut k).unwrap();
        let exact_body = core::ptr::from_ref(&body);
        match chosen.certify_final(&mut k, &prepared, &mut body).unwrap() {
            ReconstructionVerdict::Proven(p) => {
                assert!(core::ptr::eq(p._source, &input));
                assert!(core::ptr::eq(p._candidate, exact_body));
                assert!(p.boundary_error_upper().is_finite() && p.boundary_error_upper() <= 0.05);
            }
            ReconstructionVerdict::Undecided(why) => {
                panic!("complete chosen product refused: {why:?}")
            }
        }
        assert_eq!(input, before);
        // SAME support family but wrong finite extent is not adopted.
        let mut wrong =
            crate::primitive::api_primitives::create_box(&mut k, Point3::ZERO, 20., 10., 6.)
                .unwrap();
        assert!(matches!(
            chosen.certify_final(&mut k, &prepared, &mut wrong).unwrap(),
            ReconstructionVerdict::Undecided(_)
        ));
        work.check(&k).unwrap();
    }

    #[test]
    fn shared_8061_chosen_product_rejects_changed_source_and_preserves_cancel_budget() {
        let mut k = Kernel::default();
        let work = MeshWork::new();
        let input = original_box();
        let prepared = super::super::super::prepare::prepare_conversion_with_work(
            &k,
            &work,
            &input,
            0.05,
            &[],
        )
        .unwrap();
        let source = match certify_source_with_work(&k, &work, &input, &prepared.weld).unwrap() {
            SourceVerdict::Proven(p) => p,
            SourceVerdict::Undecided(why) => panic!("{why:?}"),
        };
        let mut changed = prepared.clone();
        changed.original.triangles.swap(0, 1);
        assert!(matches!(
            choose_analytic_prism_from_source_with_work(&k, &work, &source, &changed, 0.05),
            Err(super::super::super::MeshError::Refused { .. })
        ));
        let mut contradictory = prepared.clone();
        contradictory
            .provenance
            .faceted_source_patches
            .push(vec![0]);
        assert!(matches!(
            choose_analytic_prism_from_source_with_work(&k, &work, &source, &contradictory, 0.05),
            Err(super::super::super::MeshError::Refused { .. })
        ));
        let scarce = MeshWork::new();
        scarce.spend_core(&k, 200_000_000).unwrap();
        assert!(
            choose_analytic_prism_from_source_with_work(&k, &scarce, &source, &prepared, 0.05)
                .is_err()
        );
        assert!(matches!(
            scarce.check(&k),
            Err(super::super::super::MeshError::BudgetExceeded { .. })
        ));
        let token = crate::kernel::CancelToken::new();
        k.set_cancel_token(token.clone());
        token.cancel();
        assert!(
            matches!(choose_analytic_prism_from_source_with_work(&k, &work, &source, &changed, 0.05), Err(super::super::super::MeshError::Kernel(error)) if error.is_cancelled())
        );
    }
}
