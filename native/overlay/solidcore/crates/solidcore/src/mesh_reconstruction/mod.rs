//! Source-mesh recognition and reconstruction planning in the native geometry kernel.
//! Construction requests are candidates. No public planning function certifies a final body.
//! Full acceptance requires the independent bounded whole-domain certificate and topology
//! correspondence proof against the untouched raw indexed input.
mod alignment;
mod analytic;
mod deviation;
mod faceted;
mod frame;
pub mod milled;
mod native_payload;
mod numeric;
mod outline;
mod prepare;
mod primitive_certificate;
mod prismatic;
mod profile;
mod regions;
mod snap;
mod source;
mod tools;
mod types;
mod work;
pub use alignment::align_to_axes;
/// Frozen saved AnalyticV1 candidate generation; not the complete canonical proof.
pub use analytic::{
    reconstruct as reconstruct_analytic_v1,
    reconstruct_with_work as reconstruct_analytic_v1_with_work,
};
pub use deviation::{deviation_points, finish_deviation};
pub use faceted::{faceted_plan, FacetedFace, FacetedPlan, NativeEdge};
pub use native_payload::check_native_payload_with_work;
pub use outline::surface_outline;
pub use prepare::{prepare_conversion, prismatic_plans, PreparedMesh};
pub use prismatic::PrismaticPlan;
pub use regions::{picks_for_all, recognize_all, recognize_region};
pub use source::{admit_input_counts, admit_input_counts_with_work, InputPurpose};
pub use tools::{fit_tools, primitive_tool};
pub use types::{
    Deviation, FittedTool, MeshError, MeshInput, MeshPick, MeshRegion, Primitive, PrimitiveTool,
    PrismTool, ReconstructionProvenance, Result, SourcePatch, SurfaceKind, ToolGeometry, WeldClaim,
    WeldVertexClaim,
};

pub use milled::{
    fit_shadow_runs, milled_setups, section_outline, FittedShadowRuns, MilledSetup, ProfileNesting,
    SlabSections, SlabShadow,
};

pub use types::{primitive_measures, Alignment, PrimitiveMeasures};

pub use primitive_certificate::{certify_primitive_region, PrimitiveFitCertificate};

mod build_faceted;
mod build_tool;
mod certificate;
mod frame_output;
mod sketch_geometry;
pub use build_faceted::build_faceted;
pub use build_tool::build_tool;
pub use frame_output::{offset_plane, transform_frame};
pub use sketch_geometry::{
    admit_sketch_copy_with_work, sketch_geometry, sketch_geometry_with_work, SketchCopyPart,
    SketchDrawing, SketchGeometry,
};

pub use alignment::align_to_axes_with_work;
pub use deviation::{deviation_points_with_work, finish_deviation_with_work};
pub use faceted::faceted_plan_with_work;
pub use milled::{fit_shadow_runs_with_work, milled_setups_with_work, section_outline_with_work};
pub use outline::surface_outline_with_work;
pub use prepare::{prepare_conversion_with_work, prismatic_plans_with_work};
pub use primitive_certificate::certify_primitive_region_with_work;
pub use regions::{
    admit_pick_handoff_with_work, admit_region_handoff_with_work, picks_for_all_with_work,
    recognize_all_with_work, recognize_region_with_work,
};
pub use tools::fit_tools_with_work;
/// One opaque budget for the complete mesh command/workflow.
pub use work::MeshWork;

mod budgeted;
pub use budgeted::{
    can_merge_runs_with_work, check_nesting_intersection_with_work, filter_planar_result_with_work,
    filter_pocket_regions_with_work, keep_fresh_tool_with_work, nesting_intersections_with_work,
    order_tools_deepest_first_with_work, outside_stock_tool_with_work, pocket_tool_with_work,
    primitive_tool_with_work, same_shadow_with_work, seal_regions_with_work,
    shadow_differences_agree_with_work, single_section_regions_with_work,
    stock_rectangle_with_work, stock_tool_with_work,
};

pub use certificate::{
    certify_native_endpoint_prismatic_reconstruction_from_source_with_work,
    certify_native_prismatic_reconstruction_from_source_with_work,
    certify_prismatic_reconstruction_from_source_with_work, certify_reconstruction,
    certify_reconstruction_from_source_with_work, certify_reconstruction_with_work,
    certify_source_with_work, choose_analytic_prism_from_source_with_work,
    propose_prismatic_endpoints_with_work, ChosenAnalyticPrism, EndpointAlias,
    PrismaticConstructionClaim, PrismaticEndpointProposal, ProductCapClaim, ProductRimClaim,
    ReconstructionCertificate, ReconstructionRefusal, ReconstructionVerdict, SourceCertificate,
    SourceVerdict,
};

#[cfg(test)]
mod tests;

mod angular_link;
mod fitted_tool_certificate;
mod interval_trig;
pub use fitted_tool_certificate::{certify_fitted_tool_with_work, FittedToolCertificate};

pub use certificate::SourceTopologyRefusal;

mod actual_controls;
mod actual_roots;
mod cap_exit;
mod consumed_sketch;
mod convex_controls;
mod native_caps;
mod profile_chain;

/// Untrusted source/actual interval data, independently checked before acceptance.
pub use profile_chain::{GraphClaim as ProfileGraphClaim, SourceCursor as ProfileSourceCursor};

/// Complete finite stock recipe proof, distinct from one-way support fitting.
pub use certificate::{certify_finite_fitted_tool_with_work, FiniteFittedToolCertificate};
