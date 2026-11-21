//! Fieldwise snapshot of the SAME solved/checked sketch, before document write.
//! No native/application dependency or proof-status field is included.
use crate::prism::profile::{Region2, Seg2};
/// Supported actual solved curve topology, using dense indices of actual points.
#[derive(Clone, Debug, PartialEq)]
pub enum ConsumedSketchKind {
    /// One directed line between actual point identities.
    Line {
        /// First actual endpoint index.
        a: u32,
        /// Second actual endpoint index.
        b: u32,
    },
    /// Existing sketch's CCW a→b arc and actual centre identity.
    Arc {
        /// Actual centre index.
        c: u32,
        /// Actual CCW start endpoint index.
        a: u32,
        /// Actual CCW end endpoint index.
        b: u32,
    },
    /// Existing sketch's full circle and actual radius parameter.
    Circle {
        /// Actual centre index.
        c: u32,
        /// Actual solved radius parameter.
        radius: f64,
    },
}
/// Actual entity kind PLUS segments from the existing sketch consumer API.
#[derive(Clone, Debug, PartialEq)]
pub struct ConsumedSketchCurve {
    /// Actual final point identities and entity kind.
    pub kind: ConsumedSketchKind,
    /// Fieldwise copy of SAME solved `Sketch::segs(ci)`; not reconstructed DXF.
    /// For Arc, these carry the existing consumer's actual radius/start/sweep,
    /// which need not pass exactly through its independently rounded end point.
    pub segments: Vec<Seg2>,
}
/// Immutable authoritative callback snapshot. The caller must commit the SAME
/// solved sketch without mutation only after its geometry/source proof succeeds.
#[derive(Clone, Debug, PartialEq)]
pub struct ConsumedSketch {
    /// ALL actual solved points, including actual centres and any reused points.
    pub points: Vec<[f64; 2]>,
    /// ALL supported solved entities, never silently omit unrecognised kinds.
    pub curves: Vec<ConsumedSketchCurve>,
    /// Dense indices corresponding exactly to returned created stable curve IDs.
    pub created_curve_indices: Vec<u32>,
    /// Actual import/merge allowance, after the existing clamp policy.
    pub join_tolerance: f64,
    /// Actual SAME solved sketch `ProfileSearch` output, including final arrangements.
    pub profiles: Vec<ConsumedSketchProfile>,
    /// Actual consumer search state; incomplete results can never be accepted.
    pub profiles_incomplete: bool,
}

/// Actual downstream profile geometry and its source entity membership. Metadata
/// is retained, never trusted as the whole geometric/source certificate itself.
#[derive(Clone, Debug, PartialEq)]
pub struct ConsumedSketchProfile {
    /// Exact Region2 returned by the same consumer used by later extrusion.
    pub region: Region2,
    /// Actual outer boundary entity indices.
    pub outer_curves: Vec<u32>,
    /// Actual entity indices of each hole boundary.
    pub hole_curves: Vec<Vec<u32>>,
    /// Existing `Profile::whole_curve_boundaries` metadata, fieldwise copied.
    /// None indicates the consumer could not establish complete original IDs;
    /// Some is still not a native geometry acceptance flag.
    pub whole_curve_boundaries: Option<(Vec<u32>, Vec<Vec<u32>>)>,
}
