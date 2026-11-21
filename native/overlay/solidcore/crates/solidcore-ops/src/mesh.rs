//! Mesh recognition and reconstruction workflows over original indexed source data.
//!
//! Record copies and native stages use one command-owned resource ledger.
//! The private milled stock builder below returns a candidate, never an accepted reconstruction.
//! The single-product constructor returns only its independently certified canonical record.
//! Other reconstruction families and fitted-feature dispatch remain candidate-only.
use std::fmt;

use solidcore::mesh_reconstruction as kernel;
use solidcore_convert::mesh as convert;
use solidcore_record::mesh::{MeshInput, MeshInputRef, MeshRegion, SurfaceKind};
use solidcore_record::Vec3;

use crate::session::{run, Answer};

mod build;
pub(super) mod milled;

/// Evaluation and algorithm identity, also hashed by the application's MeshConvert/MeshFit
/// feature fingerprints. Bump when planning, acceptance or face order semantics change.
pub const ALGORITHM_VERSION: &str = "solidcore-mesh-reconstruction/6";

/// Canonical output-face order and construction-role namespace version. Bump when
/// either changes, including the namespace serialization schema. Applications hash
/// this independently into both durable roles and reconstruction cache keys.
pub const FACE_ORDER_VERSION: &str = "solidcore-mesh-face-order/3";

/// A native planning refusal or an existing modelling/session failure, kept distinct.
#[derive(Debug)]
pub enum Error {
    /// A structured native input/support/budget/correspondence refusal.
    Geometry(GeometryFailure),
    /// The required complete source/final certificate was not established.
    Certificate(CertificateFailure),
    /// An existing ops failure, including cancellation and a caught panic.
    Operation(crate::Error),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Geometry(error) => fmt::Display::fmt(error, f),
            Self::Certificate(error) => fmt::Display::fmt(error, f),
            Self::Operation(error) => fmt::Display::fmt(error, f),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Geometry(error) => Some(error),
            Self::Certificate(error) => Some(error),
            Self::Operation(error) => Some(error),
        }
    }
}

impl From<crate::Error> for Error {
    fn from(error: crate::Error) -> Self {
        Self::Operation(error)
    }
}

/// An opaque native cause. Apps inspect its message and cancellation classification
/// through this Ops-owned type, without depending on Core's internal error types.
#[derive(Debug)]
pub struct GeometryFailure(pub(crate) kernel::MeshError);

impl fmt::Display for GeometryFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl std::error::Error for GeometryFailure {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.0)
    }
}

/// An opaque complete-certificate refusal, retaining the native structured cause.
/// This is not a construction error and never selects another candidate or theorem.
#[derive(Debug)]
pub struct CertificateFailure(pub(crate) kernel::ReconstructionRefusal);

impl fmt::Display for CertificateFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use kernel::ReconstructionRefusal as Refusal;
        match &self.0 {
            Refusal::InvalidInput => f.write_str("mesh certificate: invalid input"),
            Refusal::InputBudget { limit } => write!(f, "mesh certificate: input exceeds {limit}"),
            Refusal::SourceIdentity => f.write_str("mesh certificate: source identity changed"),
            Refusal::SourceTopology { reason } => write!(f, "mesh source topology: {reason:?}"),
            Refusal::NativeSolidValidity => {
                f.write_str("mesh certificate: final body is not a valid solid")
            }
            Refusal::GeometryCorrespondence { reason } => write!(f, "mesh certificate: {reason}"),
        }
    }
}

impl std::error::Error for CertificateFailure {}

fn geometry_error(error: kernel::MeshError) -> Error {
    Error::Geometry(GeometryFailure(error))
}

/// The result of a mesh workflow.
pub type Result<T> = std::result::Result<T, Error>;

/// Preserve cancellation when the application decides whether a result may be adopted.
impl Error {
    #[must_use]
    /// Whether this workflow stopped through either cancellation bridge.
    pub fn is_cancelled(&self) -> bool {
        match self {
            Self::Geometry(error) => error.0.is_cancelled(),
            Self::Certificate(_) => false,
            Self::Operation(error) => matches!(error, crate::Error::Cancelled),
        }
    }

    /// A caught native/session panic, kept distinct from an ordinary geometric refusal.
    #[must_use]
    pub fn internal_message(&self) -> Option<&str> {
        match self {
            Self::Operation(crate::Error::Internal(message)) => Some(message),
            _ => None,
        }
    }
}

/// A classified copy for the session observer; the returned workflow error retains
/// its original typed payload, including counts and complete-certificate causes.
impl Error {
    pub(crate) fn session_refusal(&self) -> crate::Error {
        match self {
            Self::Operation(error) => error.clone(),
            Self::Certificate(_) => crate::Error::Refused {
                operation: "mesh::certificate",
                reason: "complete source/final correspondence was not established",
            },
            Self::Geometry(error) => match &error.0 {
                kernel::MeshError::Kernel(error) => crate::error::status(error.clone()),
                kernel::MeshError::InvalidInput { stage, .. } => crate::Error::Refused {
                    operation: stage,
                    reason: "invalid mesh input",
                },
                kernel::MeshError::Refused { stage, .. } => crate::Error::Refused {
                    operation: stage,
                    reason: "mesh geometry was not established",
                },
                kernel::MeshError::InputLimit { stage, .. } => crate::Error::Refused {
                    operation: stage,
                    reason: "mesh input count exceeds its limit",
                },
                kernel::MeshError::BudgetExceeded { stage, .. } => crate::Error::Refused {
                    operation: stage,
                    reason: "complete mesh workflow budget exhausted",
                },
                kernel::MeshError::Undecided { stage, .. } => crate::Error::Refused {
                    operation: stage,
                    reason: "bounded mesh proof was not established",
                },
            },
        }
    }
}

/// Typed inner refusal carried through the existing session panic/cancellation guard.
struct WorkflowAnswer<T>(Result<T>);
impl<T> Answer for WorkflowAnswer<T> {
    fn refusal(&self) -> Option<crate::Error> {
        self.0.as_ref().err().map(Error::session_refusal)
    }
}

fn check_cancelled() -> Result<()> {
    if crate::cancel::is_cancelled() {
        Err(crate::Error::Cancelled.into())
    } else {
        Ok(())
    }
}

fn guarded<T>(
    call: &'static str,
    f: impl FnOnce(&mut solidcore::Kernel) -> Result<T>,
) -> Result<T> {
    check_cancelled()?;
    let answer = run(call, |k| Ok(WorkflowAnswer(f(k))))?;
    check_cancelled()?;
    answer.0
}

fn native<T>(
    call: &'static str,
    f: impl FnOnce(&mut solidcore::Kernel) -> kernel::Result<T>,
) -> Result<T> {
    guarded(call, |k| f(k).map_err(geometry_error))
}

/// Record counts only: no arrays have been copied to Core yet.
#[derive(Clone, Copy)]
pub(super) struct SourceCounts {
    pub(super) purpose: kernel::InputPurpose,
    pub(super) vertices: usize,
    pub(super) triangles: usize,
}

/// Admission and materialization share the actual command's work ledger. The
/// factory is deliberately invoked only after count and cancellation admission.
pub(super) fn admitted_source_with_work<T>(
    work: &kernel::MeshWork,
    call: &'static str,
    counts: SourceCounts,
    materialize: impl FnOnce() -> kernel::MeshInput,
    f: impl FnOnce(&mut solidcore::Kernel, &kernel::MeshWork, &kernel::MeshInput) -> kernel::Result<T>,
) -> Result<T> {
    native(call, |k| {
        let answer = (|| {
            kernel::admit_input_counts_with_work(
                k,
                work,
                counts.purpose,
                counts.vertices,
                counts.triangles,
            )?;
            let input = materialize();
            f(k, work, &input)
        })();
        // A geometric refusal cannot replace a latched budget/cancel/Core error.
        work.check(k)?;
        answer
    })
}

fn source_counts(mesh: MeshInputRef<'_>) -> SourceCounts {
    SourceCounts {
        purpose: kernel::InputPurpose::Recognition,
        vertices: mesh.positions.len(),
        triangles: mesh.triangles.len(),
    }
}

fn refused(stage: &'static str, detail: &'static str) -> Error {
    geometry_error(kernel::MeshError::Refused {
        stage,
        detail: detail.into(),
    })
}

/// An independently certified single-product result in canonical record order.
///
/// The record was exported normally, imported without healing and certified on
/// that exact final body. Face/edge/vertex indices name this record's order, not
/// a discarded construction body's IDs. The app binds its source and parameters
/// to those indices. Copies or edits are ordinary records, not new certificates.
#[derive(Debug)]
pub struct CertifiedMeshRecord {
    record: solidcore_record::brep::Brep,
    boundary_error_upper: f64,
}

impl CertifiedMeshRecord {
    /// The exact canonical record that preceded and survived the final proof.
    #[must_use]
    pub fn record(&self) -> &solidcore_record::brep::Brep {
        &self.record
    }

    /// Complete-domain boundary error bound, not a sampled deviation estimate.
    #[must_use]
    pub fn boundary_error_upper(&self) -> f64 {
        self.boundary_error_upper
    }

    /// Consume the checked output and retain its exact record, without exporting again.
    #[must_use]
    pub fn into_record(self) -> solidcore_record::brep::Brep {
        self.record
    }
}

fn core_error(error: solidcore::SolidError) -> Error {
    geometry_error(kernel::MeshError::Kernel(error))
}

fn record_error(error: solidcore_convert::brep::Unsupported) -> Error {
    use solidcore_convert::brep::Unsupported;
    match error {
        Unsupported::Kernel(error) => core_error(error),
        Unsupported::Invalid(reason) => crate::Error::Record(reason.to_owned()).into(),
        Unsupported::NotYet(reason) => crate::Error::Unsupported(reason).into(),
    }
}

/// Reconstruct one supported constant-section product from original source arrays.
///
/// `None` means the source-only chooser found no product before any body was
/// constructed. Every input, construction, canonical import and certificate
/// refusal after that choice is an error; it never retries an axis or a theorem.
/// Multi-axis parts, picked features and fitted bodies use other workflows.
///
/// # Errors
/// Typed source/certificate/native/record refusals, shared-budget exhaustion,
/// cancellation or a caught internal failure. The borrowed source is never changed.
pub fn reconstruct_single_product(
    mesh: MeshInputRef<'_>,
    tolerance: f64,
) -> Result<Option<CertifiedMeshRecord>> {
    reconstruct_single_product_with_work(&kernel::MeshWork::new(), mesh, tolerance)
}

pub(crate) fn reconstruct_single_product_with_work(
    work: &kernel::MeshWork,
    mesh: MeshInputRef<'_>,
    tolerance: f64,
) -> Result<Option<CertifiedMeshRecord>> {
    reconstruct_with_families(work, mesh, tolerance, false)
}

/// Reconstruct one certified prismatic product, circular cone or frustum, a rectangular
/// blank with axial bores, or an exactly orthogonal planar solid. Family choice depends only on the source. A failed native,
/// source, or final certificate is returned and never selects another family.
///
/// # Errors
/// A typed geometry, certificate, cancellation or native construction refusal.
pub fn reconstruct_certified_solid(
    mesh: MeshInputRef<'_>,
    tolerance: f64,
) -> Result<Option<CertifiedMeshRecord>> {
    reconstruct_with_families(&kernel::MeshWork::new(), mesh, tolerance, true)
}

fn reconstruct_with_families(
    work: &kernel::MeshWork,
    mesh: MeshInputRef<'_>,
    tolerance: f64,
    allow_extra_families: bool,
) -> Result<Option<CertifiedMeshRecord>> {
    guarded("mesh::reconstruct_certified_solid", |k| {
        let input = decode_reconstruction_input(k, work, mesh)?;
        reconstruct_input(k, work, &input, tolerance, allow_extra_families)
    })
}

fn decode_reconstruction_input(
    k: &solidcore::Kernel,
    work: &kernel::MeshWork,
    mesh: MeshInputRef<'_>,
) -> Result<kernel::MeshInput> {
    kernel::admit_input_counts_with_work(
        k,
        work,
        kernel::InputPurpose::Conversion,
        mesh.positions.len(),
        mesh.triangles.len(),
    )
    .map_err(geometry_error)?;
    Ok(convert::input_borrowed(mesh))
}

/// Reconstruct every strictly separated component in one original STL, using
/// one shared workflow budget. All records must pass before an edit is made.
///
/// # Errors
/// Invalid or touching components, an individual Native/source proof refusal,
/// cancellation or budget exhaustion. No partial result is exposed.
pub fn reconstruct_certified_bodies(
    mesh: MeshInputRef<'_>,
    tolerance: f64,
) -> Result<Option<Vec<CertifiedMeshRecord>>> {
    let work = kernel::MeshWork::new();
    guarded("mesh::reconstruct_certified_bodies", |k| {
        let input = decode_reconstruction_input(k, &work, mesh)?;
        let Some(parts) = kernel::disjoint_component_meshes_with_work(k, &work, &input, tolerance)
            .map_err(geometry_error)?
        else {
            return Ok(
                reconstruct_input(k, &work, &input, tolerance, true)?.map(|solid| vec![solid])
            );
        };
        let mut records = Vec::new();
        for part in &parts {
            let Some(solid) = reconstruct_input(k, &work, part, tolerance, true)? else {
                return Err(refused(
                    "component reconstruction",
                    "an original component does not match a supported solid family",
                ));
            };
            records.push(solid);
        }
        work.check(k).map_err(geometry_error)?;
        Ok(Some(records))
    })
}

fn reconstruct_input(
    k: &mut solidcore::Kernel,
    work: &kernel::MeshWork,
    input: &kernel::MeshInput,
    tolerance: f64,
    allow_extra_families: bool,
) -> Result<Option<CertifiedMeshRecord>> {
    let result = (|| {
        let mut prepared = kernel::prepare_conversion_with_work(k, work, input, tolerance, &[])
            .map_err(geometry_error)?;
        let source = match kernel::certify_source_with_work(k, work, input, &prepared.weld)
            .map_err(core_error)?
        {
            kernel::SourceVerdict::Proven(source) => source,
            kernel::SourceVerdict::Undecided(reason) => {
                return Err(Error::Certificate(CertificateFailure(reason)));
            }
        };
        let chosen = kernel::choose_analytic_prism_from_source_with_work(
            k, work, &source, &prepared, tolerance,
        )
        .map_err(geometry_error)?;
        let radial = if allow_extra_families && chosen.is_none() {
            kernel::choose_radial_solid_from_source_with_work(
                k, work, &source, &prepared, tolerance,
            )
            .map_err(geometry_error)?
        } else {
            None
        };
        let bored = if allow_extra_families && chosen.is_none() && radial.is_none() {
            kernel::choose_bored_stock_from_source_with_work(k, work, &source, &prepared, tolerance)
                .map_err(geometry_error)?
        } else {
            None
        };
        let candidate = match (&chosen, &radial, &bored) {
            (Some(prism), _, _) => prism.build_native_candidate(k).map_err(geometry_error)?,
            (None, Some(band), _) => band.build_native_candidate(k).map_err(geometry_error)?,
            (None, None, Some(stock)) => stock.build_native_candidate(k).map_err(geometry_error)?,
            (None, None, None) if allow_extra_families => {
                let Some(plan) = kernel::choose_orthogonal_stock_from_source_with_work(
                    k, work, &source, &prepared,
                )
                .map_err(geometry_error)?
                else {
                    return Ok(None);
                };
                let body = kernel::build_faceted(k, &plan).map_err(geometry_error)?;
                prepared.provenance.faceted_source_patches = plan
                    .into_source_patch_claims_with_work(k, work)
                    .map_err(geometry_error)?;
                body
            }
            (None, None, None) => return Ok(None),
        };
        kernel::check_native_payload_with_work(k, work, &candidate).map_err(geometry_error)?;
        let mut candidate =
            crate::body::finish(k, candidate, crate::body::Expect::SOLID).map_err(core_error)??;
        work.check(k).map_err(geometry_error)?;
        // These are the same normal converters used by Body::to_record/from_record.
        // Export may finish UV trims and canonicalize angles: it precedes proof.
        let (record, _) =
            solidcore_convert::brep::to_record(k, &mut candidate).map_err(record_error)?;
        let (actual, _) =
            solidcore_convert::brep::to_kernel(k, &record, true).map_err(record_error)?;
        kernel::check_native_payload_with_work(k, work, &actual).map_err(geometry_error)?;
        let mut actual =
            crate::body::finish(k, actual, crate::body::Expect::SOLID).map_err(core_error)??;
        work.check(k).map_err(geometry_error)?;
        let verdict = match (&chosen, &radial, &bored) {
            (Some(prism), _, _) => prism.certify_final(k, &prepared, &mut actual),
            (None, Some(band), _) => band.certify_final(k, &mut actual),
            (None, None, Some(stock)) => stock.certify_final(k, &mut actual),
            (None, None, None) => kernel::certify_reconstruction_from_source_with_work(
                k,
                work,
                &source,
                &prepared,
                &mut actual,
                tolerance,
            ),
        }
        .map_err(core_error)?;
        let boundary_error_upper = match verdict {
            kernel::ReconstructionVerdict::Proven(proof) => proof.boundary_error_upper(),
            kernel::ReconstructionVerdict::Undecided(reason) => {
                return Err(Error::Certificate(CertificateFailure(reason)));
            }
        };
        // Never export `actual` after proof. The pre-proof canonical record is
        // immutable and is the exact output every cache-free consumer imports.
        Ok(Some(CertifiedMeshRecord {
            record,
            boundary_error_upper,
        }))
    })();
    // Original native/cancel/budget latches take precedence over a local refusal.
    work.check(k).map_err(geometry_error)?;
    result
}

/// Recognise one source region. Returned fitting metrics are descriptive, not an acceptance
/// proof. Application selection/placement has already mapped `point` to this mesh's frame.
///
/// # Errors
/// Structured native refusal, cancellation, or a caught internal failure.
pub fn recognize_region(
    mesh: &MeshInput,
    point: Vec3,
    kind: SurfaceKind,
    tolerance: f64,
) -> Result<MeshRegion> {
    recognize_region_borrowed(mesh.into(), point, kind, tolerance)
}

/// Recognise one region from borrowed ORIGINAL source arrays. No input is copied
/// before count/cancel admission; original triangle backing moves to the result.
///
/// # Errors
/// Native support/input/budget refusal, cancellation or a caught internal failure.
pub fn recognize_region_borrowed(
    mesh: MeshInputRef<'_>,
    point: Vec3,
    kind: SurfaceKind,
    tolerance: f64,
) -> Result<MeshRegion> {
    let work = kernel::MeshWork::new();
    let point = solidcore_convert::vec3(point);
    let kind = convert::kind(kind);
    admitted_source_with_work(
        &work,
        "mesh::recognize_region",
        source_counts(mesh),
        || convert::input_borrowed(mesh),
        |k, work, input| {
            let region =
                kernel::recognize_region_with_work(k, work, input, point, kind, tolerance)?;
            kernel::admit_region_handoff_with_work(k, work, std::slice::from_ref(&region))?;
            work.check(k)?;
            Ok(convert::record_region_owned(region))
        },
    )
}

/// Recognise every supported source region in the native deterministic order.
///
/// # Errors
/// Structured native refusal, cancellation, or a caught internal failure.
pub fn recognize_all(mesh: &MeshInput, tolerance: f64) -> Result<Vec<MeshRegion>> {
    recognize_all_borrowed(mesh.into(), tolerance)
}

/// Borrow original arrays and move native region IDs through a counted data-only
/// handoff. One SAME work ledger covers input and both declared return mappings.
///
/// # Errors
/// Native support/count/budget refusal, allocation failure, cancellation or internal failure.
pub fn recognize_all_borrowed(mesh: MeshInputRef<'_>, tolerance: f64) -> Result<Vec<MeshRegion>> {
    let work = kernel::MeshWork::new();
    admitted_source_with_work(
        &work,
        "mesh::recognize_all",
        source_counts(mesh),
        || convert::input_borrowed(mesh),
        |k, work, input| {
            let regions = kernel::recognize_all_with_work(k, work, input, tolerance)?;
            kernel::admit_region_handoff_with_work(k, work, &regions)?;
            let mut out = Vec::new();
            out.try_reserve_exact(regions.len())
                .map_err(|_| kernel::MeshError::Refused {
                    stage: "recognition record handoff",
                    detail: "return allocation refused".into(),
                })?;
            for region in regions {
                work.check(k)?;
                out.push(convert::record_region_owned(region));
            }
            work.check(k)?;
            Ok(out)
        },
    )
}

/// Native all-surface picks, retaining the existing largest-original-facet rule.
///
/// # Errors
/// Native refusal, cancellation, shared budget exhaustion or an internal failure.
pub fn picks_for_all(
    mesh: &MeshInput,
    tolerance: f64,
) -> Result<Vec<solidcore_record::mesh::MeshPick>> {
    picks_for_all_borrowed(mesh.into(), tolerance)
}

/// Borrow source arrays before constructing all-surface picks. Core owns ALL
/// centroid/area/noise calculations; this workflow copies only final fields.
///
/// # Errors
/// Native refusal, allocation/budget exhaustion, cancellation or an internal failure.
pub fn picks_for_all_borrowed(
    mesh: MeshInputRef<'_>,
    tolerance: f64,
) -> Result<Vec<solidcore_record::mesh::MeshPick>> {
    let work = kernel::MeshWork::new();
    admitted_source_with_work(
        &work,
        "mesh::picks_for_all",
        source_counts(mesh),
        || convert::input_borrowed(mesh),
        |k, work, input| {
            let picks = kernel::picks_for_all_with_work(k, work, input, tolerance)?;
            kernel::admit_pick_handoff_with_work(k, work, &picks)?;
            let mut out = Vec::new();
            out.try_reserve_exact(picks.len())
                .map_err(|_| kernel::MeshError::Refused {
                    stage: "pick record handoff",
                    detail: "return allocation refused".into(),
                })?;
            for pick in picks {
                work.check(k)?;
                out.push(convert::record_pick(&pick));
            }
            work.check(k)?;
            Ok(out)
        },
    )
}

/// A complete precomputed rigid alignment; app command parameters only copy these fields.
///
/// # Errors
/// Structured native refusal, cancellation or a caught internal failure.
pub fn align_to_axes(
    mesh: &MeshInput,
    options: &solidcore_record::mesh::AlignOptions,
) -> Result<solidcore_record::mesh::Alignment> {
    align_to_axes_borrowed(mesh.into(), options)
}

/// Align borrowed original arrays without an application-side geometry copy.
/// Source counts and cancellation are admitted to this command's one ledger
/// before the fieldwise converter copies either array. Geometry is computed by Core.
/// This source-copy admission does not qualify unrelated native workspace costs.
///
/// # Errors
/// Structured native input/budget refusal, cancellation or a caught internal failure.
pub fn align_to_axes_borrowed(
    mesh: MeshInputRef<'_>,
    options: &solidcore_record::mesh::AlignOptions,
) -> Result<solidcore_record::mesh::Alignment> {
    let work = kernel::MeshWork::new();
    admitted_source_with_work(
        &work,
        "mesh::align_to_axes",
        SourceCounts {
            purpose: kernel::InputPurpose::Recognition,
            vertices: mesh.positions.len(),
            triangles: mesh.triangles.len(),
        },
        || convert::input_borrowed(mesh),
        |k, work, input| {
            kernel::align_to_axes_with_work(k, work, input, options.tolerance, options.centred)
        },
    )
    .map(|alignment| convert::record_alignment(&alignment))
}

/// Place a source section plane at its requested level using the kernel's frame primitive.
/// No coordinates or normals are calculated in this workflow.
///
/// # Errors
/// Invalid plane/level, cancellation or a caught internal failure.
pub fn offset_plane(
    plane: &solidcore_record::Plane,
    offset: f64,
) -> Result<solidcore_record::Plane> {
    let frame = solidcore_convert::plane(plane);
    native("mesh::offset_plane", |k| {
        kernel::offset_plane(k, &frame, offset)
    })
    .map(|frame| solidcore_convert::record_plane(&frame))
}

/// Place a fitted sketch plane through a rigid occurrence without normalisation.
///
/// # Errors
/// Native non-rigid/undecided refusal, cancellation or caught internal failure.
pub fn transform_plane(
    plane: &solidcore_record::Plane,
    matrix: &[[f64; 4]; 4],
) -> Result<solidcore_record::Plane> {
    let frame = solidcore_convert::plane(plane);
    native("mesh::transform_plane", |k| {
        kernel::transform_frame(k, &frame, matrix)
    })
    .map(|frame| solidcore_convert::record_plane(&frame))
}

/// Precompute snapshot sketch entities through the Core's existing analytic arc primitives.
///
/// # Errors
/// Invalid/unsupported profile, budget refusal, cancellation or caught internal failure.
pub fn sketch_geometry(
    regions: &[solidcore_record::Region2],
    tolerance: f64,
) -> Result<solidcore_record::mesh::SketchDrawing> {
    let work = kernel::MeshWork::new();
    sketch_geometry_with_work(&work, regions, tolerance)
}

/// Borrowed record metadata admission before ANY Region2/holes/Seg2 copy. The
/// private materializer must copy these exact borrowed records through convert;
/// counts are DATA/resource admission only, never geometric proof or a bypass of
/// native validation. Cancellation/budget/Core errors keep their precedence.
pub(super) fn admitted_sketch_regions_with_work<T>(
    work: &kernel::MeshWork,
    call: &'static str,
    regions: &[solidcore_record::Region2],
    materialize: impl FnOnce() -> Vec<solidcore::prism::profile::Region2>,
    f: impl FnOnce(
        &mut solidcore::Kernel,
        &kernel::MeshWork,
        &[solidcore::prism::profile::Region2],
    ) -> kernel::Result<T>,
) -> Result<T> {
    native(call, |k| {
        let answer = (|| {
            kernel::admit_sketch_copy_with_work(
                k,
                work,
                kernel::SketchCopyPart::Regions,
                regions.len(),
            )?;
            let mut segments = 0usize;
            for region in regions {
                // Empty holes still contain a Loop2/Vec descriptor and must be paid.
                kernel::admit_sketch_copy_with_work(
                    k,
                    work,
                    kernel::SketchCopyPart::Holes,
                    region.holes.len(),
                )?;
                for lp in region.loops() {
                    segments = kernel::admit_sketch_copy_with_work(
                        k,
                        work,
                        kernel::SketchCopyPart::Segments { previous: segments },
                        lp.segs.len(),
                    )?;
                }
            }
            let input = materialize();
            f(k, work, &input)
        })();
        work.check(k)?;
        answer
    })
}
/// Precompute snapshot entities using the actual command's SAME work ledger.
/// Only record metadata/counts and field copies occur in Ops/convert; all curve
/// computation/validation stays in Core. This resource gate does not certify a
/// source profile, native lazy construction, export or whole reconstructed body.
///
/// # Errors
/// Native profile/count/budget refusal, original cancellation or internal failure.
pub(crate) fn sketch_geometry_with_work(
    work: &kernel::MeshWork,
    regions: &[solidcore_record::Region2],
    tolerance: f64,
) -> Result<solidcore_record::mesh::SketchDrawing> {
    admitted_sketch_regions_with_work(
        work,
        "mesh::sketch_geometry",
        regions,
        || regions.iter().map(solidcore_convert::region2).collect(),
        |k, work, profiles| {
            let drawing = kernel::sketch_geometry_with_work(k, work, profiles, tolerance)?;
            kernel::admit_sketch_copy_with_work(
                k,
                work,
                kernel::SketchCopyPart::Drawing,
                drawing.geometry.len(),
            )?;
            Ok(convert::record_sketch_drawing(&drawing))
        },
    )
}

/// A stable application-facing failure category; the native cause remains on `Error`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorClass {
    /// Invalid source arrays or topology.
    InvalidInput,
    /// Valid input outside the complete reconstruction proof.
    Unsupported,
    /// A declared input/work/cell/output budget was exhausted.
    LimitExceeded,
    /// The operation was cancelled.
    Cancelled,
    /// A native construction, canonicalization or internal failure.
    Failed,
}
impl Error {
    /// Classify without exposing Core types or changing the failure into success.
    #[must_use]
    pub fn class(&self) -> ErrorClass {
        if self.is_cancelled() {
            return ErrorClass::Cancelled;
        }
        match self {
            Self::Geometry(error) => match &error.0 {
                kernel::MeshError::InvalidInput { .. } => ErrorClass::InvalidInput,
                kernel::MeshError::InputLimit { .. } | kernel::MeshError::BudgetExceeded { .. } => {
                    ErrorClass::LimitExceeded
                }
                kernel::MeshError::Refused { .. } | kernel::MeshError::Undecided { .. } => {
                    ErrorClass::Unsupported
                }
                kernel::MeshError::Kernel(solidcore::SolidError::Unsupported { .. }) => {
                    ErrorClass::Unsupported
                }
                kernel::MeshError::Kernel(_) => ErrorClass::Failed,
            },
            Self::Certificate(error) => match &error.0 {
                kernel::ReconstructionRefusal::InvalidInput
                | kernel::ReconstructionRefusal::SourceTopology { .. } => ErrorClass::InvalidInput,
                kernel::ReconstructionRefusal::InputBudget { .. } => ErrorClass::LimitExceeded,
                kernel::ReconstructionRefusal::GeometryCorrespondence { .. } => {
                    ErrorClass::Unsupported
                }
                kernel::ReconstructionRefusal::SourceIdentity
                | kernel::ReconstructionRefusal::NativeSolidValidity => ErrorClass::Failed,
            },
            Self::Operation(_) => ErrorClass::Failed,
        }
    }
}
