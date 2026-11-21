//! Full exact-planar reconstruction proof and independent source preflight.
//! Curved/moved candidates remain typed Undecided until the product/CW theorem.
mod actual_ruling;
mod radial_frame;
// Value authority is consumed by the private complete-cylinder side adapter.
mod analytic_ruling;
mod apex;
mod bore_shoulder;
mod bored_stock_proposal;
mod bored_stock_source;
mod complete_product;
mod endpoint_proposal;
mod errors;
pub(crate) mod exact_geometry;
mod exact_planar;
mod faceted_witness;
mod fitted_recipe;
pub(crate) mod hulls;
mod layered_source;
mod native_bored_stock;
mod native_profile;
mod native_radial_topology;
pub(crate) mod open_face_complex;
mod planar_chart;
mod plane_trim_image;
mod product_cap;
mod product_driver;
mod product_profiles;
mod product_reference;
mod product_side_band;
mod radial_band;
mod radial_curve;
mod radial_proposal;
mod radial_solid_source;
mod radial_source;
mod radial_stack;
mod radial_stock;
mod reconstruction;
mod rectangular_trim;
mod rim_motion;
mod ruling_band;
mod sewn_curve;
mod source_cells;
mod source_index;
mod source_motion;
mod source_nesting;
mod source_prism;
mod source_topology;
pub(crate) mod source_view;
pub(crate) mod target_complex;
pub(crate) use apex::ordered_apex_link_with_work;
pub use endpoint_proposal::{EndpointAlias, PrismaticEndpointProposal};
pub use product_driver::{PrismaticConstructionClaim, ProductCapClaim, ProductRimClaim};
pub use reconstruction::{
    certify_native_endpoint_prismatic_reconstruction_from_source_with_work,
    certify_native_prismatic_reconstruction_from_source_with_work,
    certify_prismatic_reconstruction_from_source_with_work, certify_reconstruction,
    certify_reconstruction_from_source_with_work, certify_reconstruction_with_work,
    certify_source_with_work, choose_analytic_prism_from_source_with_work,
    choose_bored_stock_from_source_with_work, choose_orthogonal_stock_from_source_with_work,
    choose_radial_solid_from_source_with_work, propose_prismatic_endpoints_with_work,
    ChosenAnalyticPrism, ChosenBoredStock, ChosenRadialSolid, ReconstructionCertificate,
    ReconstructionRefusal, ReconstructionVerdict, SourceCertificate, SourceVerdict,
};

pub(crate) use exact_planar::affine_ends;
pub(crate) use product_profiles::exact_source_unit_complement;
pub(crate) use target_complex::TargetComplex;

pub use source_topology::SourceRefusal as SourceTopologyRefusal;

pub(crate) use hulls::{
    curve_cap_bound, curve_graph_bound, point_distance_upper, CurveCapBound, PointBox,
};

pub(crate) use apex::{inspect_vector_apex_link_with_work, ApexLink};

/// Complete finite stock recipe proof, distinct from one-way support fitting.
pub use fitted_recipe::{certify_finite_fitted_tool_with_work, FiniteFittedToolCertificate};
