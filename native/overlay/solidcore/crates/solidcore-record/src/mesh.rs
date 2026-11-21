//! Mesh reconstruction as data: the original indexed triangles, user picks, recognised
//! analytic surfaces and the reports returned by the kernel. Geometry and acceptance proofs
//! are computed only in `solidcore::mesh_reconstruction`; these records carry no proof.
//!
//! Existing surface/region/deviation field names are retained for design and command replies.
use serde::{Deserialize, Serialize};

use crate::{Plane, Region2, Vec3};

/// Original source triangles in the definition body's coordinates, without display normals.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MeshInput {
    /// Original coordinates; conversion does not weld, transform, round or reorder them.
    pub positions: Vec<Vec3>,
    /// Original vertex indices; source triangle order is preserved.
    pub triangles: Vec<[u32; 3]>,
}

/// Borrowed original source data for a synchronous modelling call. This view does
/// not allocate, validate, weld or carry a proof. Ops admits and charges the source
/// to one command budget before the native conversion copies either array.
#[derive(Clone, Copy, Debug)]
pub struct MeshInputRef<'a> {
    /// The untouched original coordinates, in their source order.
    pub positions: &'a [Vec3],
    /// The untouched original triangle indices, in their source order.
    pub triangles: &'a [[u32; 3]],
}
impl<'a> From<&'a MeshInput> for MeshInputRef<'a> {
    fn from(input: &'a MeshInput) -> Self {
        Self {
            positions: &input.positions,
            triangles: &input.triangles,
        }
    }
}

/// The analytic surface requested by a pick.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SurfaceKind {
    /// Try the supported surface families in the kernel's documented order.
    #[default]
    Auto,
    /// A plane.
    Plane,
    /// A circular cylinder.
    Cylinder,
    /// A circular cone.
    Cone,
    /// A sphere.
    Sphere,
    /// A torus.
    Torus,
}

impl SurfaceKind {
    /// Parse the existing command spelling. This is textual data parsing, never surface inference.
    #[must_use]
    pub fn parse(text: &str) -> Option<Self> {
        Some(match text.trim().to_ascii_lowercase().as_str() {
            "auto" | "" => Self::Auto,
            "plane" => Self::Plane,
            "cylinder" => Self::Cylinder,
            "cone" => Self::Cone,
            "sphere" => Self::Sphere,
            "torus" => Self::Torus,
            _ => return None,
        })
    }
}

/// Parameters of an analytic surface, not a claim that any input lies on it.
#[derive(Clone, Copy, Debug, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Primitive {
    /// A plane through `point` with direction `normal`.
    Plane {
        /// A point on the plane.
        point: Vec3,
        /// The plane's normal.
        normal: Vec3,
    },
    /// A circular cylinder about the line through `point` in direction `axis`.
    Cylinder {
        /// A point on the axis.
        point: Vec3,
        /// The axis direction.
        axis: Vec3,
        /// Radius in model units.
        radius: f64,
    },
    /// A circular cone whose axis points from its apex into the cone.
    Cone {
        /// The cone's apex.
        apex: Vec3,
        /// The axis direction.
        axis: Vec3,
        /// Half angle in radians.
        half_angle: f64,
    },
    /// A sphere.
    Sphere {
        /// Centre of the sphere.
        center: Vec3,
        /// Radius in model units.
        radius: f64,
    },
    /// A torus about `axis`, with its generating circle at distance `major` from `center`.
    Torus {
        /// Centre of the torus.
        center: Vec3,
        /// The axis direction.
        axis: Vec3,
        /// Major radius in model units.
        major: f64,
        /// Generating circle radius in model units.
        minor: f64,
    },
}

impl Primitive {
    /// The stored variant's discriminator, with no evaluation or validation of its fields.
    #[must_use]
    pub fn kind(&self) -> SurfaceKind {
        match self {
            Self::Plane { .. } => SurfaceKind::Plane,
            Self::Cylinder { .. } => SurfaceKind::Cylinder,
            Self::Cone { .. } => SurfaceKind::Cone,
            Self::Sphere { .. } => SurfaceKind::Sphere,
            Self::Torus { .. } => SurfaceKind::Torus,
        }
    }
}

/// Display measurements computed by the kernel, separate from a surface's definition.
#[derive(Clone, Copy, Debug, Default, PartialEq, Serialize, Deserialize)]
pub struct PrimitiveMeasures {
    /// Cylinder diameter in model units, when applicable.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub diameter: Option<f64>,
    /// Cone's full included angle in degrees, when applicable.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub full_angle_degrees: Option<f64>,
}

/// A recognised connected region and its descriptive fitting metrics.
/// These metrics are not a whole-domain reconstruction acceptance certificate.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MeshRegion {
    /// Parameters of the fitted surface.
    pub surface: Primitive,
    /// Optional display data; old replies without it keep the generic surface label.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub measurements: Option<PrimitiveMeasures>,
    /// Original source triangle indices, in the kernel's returned order.
    pub triangles: Vec<u32>,
    /// Region area in square model units.
    pub area: f64,
    /// Largest reported fitting deviation in model units.
    pub max_deviation: f64,
    /// Root mean square reported fitting deviation in model units.
    pub rms_deviation: f64,
    /// A bore or pocket rather than a boss or ball; false for a plane.
    pub concave: bool,
}

/// One user pick, already mapped by the application to the definition body coordinates.
#[derive(Clone, Copy, Debug, PartialEq, Serialize, Deserialize)]
pub struct MeshPick {
    /// The selected point on the input mesh.
    pub point: Vec3,
    /// Requested surface family.
    pub kind: SurfaceKind,
}

/// Recognition parameters. Defaults and input validation belong to the caller and kernel.
#[derive(Clone, Copy, Debug, PartialEq, Serialize, Deserialize)]
pub struct RecognizeOptions {
    /// Maximum requested deviation in model units.
    pub tolerance: f64,
    /// Requested surface family for a single pick.
    pub kind: SurfaceKind,
}

/// Parameters of reconstructing one complete source mesh.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ReconstructionOptions {
    /// Maximum requested deviation in model units.
    pub tolerance: f64,
    /// Guided surface picks, in selection order.
    pub picks: Vec<MeshPick>,
    /// Recognise the entire source before reconstruction.
    pub all_surfaces: bool,
}

/// Parameters of making independent bodies or sheets from selected surface regions.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct FitOptions {
    /// Maximum requested deviation in model units.
    pub tolerance: f64,
    /// Guided surface picks, in selection order.
    pub picks: Vec<MeshPick>,
    /// Recognise the entire source instead of requiring explicit picks.
    pub all_surfaces: bool,
    /// Return sheets rather than solid feature bodies.
    pub surfaces: bool,
    /// Requested size rounding grid; zero keeps measured sizes.
    pub round: f64,
}

/// Parameters of outlining a selected surface in a sketch plane.
#[derive(Clone, Copy, Debug, PartialEq, Serialize, Deserialize)]
pub struct OutlineOptions {
    /// Maximum requested deviation in model units.
    pub tolerance: f64,
    /// Requested size rounding grid; zero keeps measured sizes.
    pub round: f64,
}

/// Parameters of aligning a mesh to the model axes.
#[derive(Clone, Copy, Debug, PartialEq, Serialize, Deserialize)]
pub struct AlignOptions {
    /// Maximum requested deviation in model units.
    pub tolerance: f64,
    /// Centre X/Y; otherwise put the minimum X/Y coordinates at the origin.
    pub centred: bool,
}

/// A plane and its fitted profile regions, expressed in that plane's coordinates.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct SurfaceOutline {
    /// Sketch plane in the input mesh's coordinate system.
    pub plane: Plane,
    /// Outer boundaries and holes, in returned order.
    pub regions: Vec<Region2>,
}

/// Precomputed drawing entity fields for a snapshot sketch.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum SketchGeometry {
    /// A line segment.
    Line {
        /// First endpoint.
        a: crate::Vec2,
        /// Second endpoint.
        b: crate::Vec2,
    },
    /// A counter-clockwise sketch arc with precomputed endpoints.
    Arc {
        /// Centre.
        center: crate::Vec2,
        /// First endpoint.
        a: crate::Vec2,
        /// Second endpoint.
        b: crate::Vec2,
    },
    /// A complete circle.
    Circle {
        /// Centre.
        center: crate::Vec2,
        /// Radius.
        radius: f64,
    },
}

/// Drawing entities and the Core's chosen endpoint-joining tolerance.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct SketchDrawing {
    /// Entities in source loop/segment order.
    pub geometry: Vec<SketchGeometry>,
    /// Endpoint-joining tolerance in model units.
    pub join_tolerance: f64,
}

/// A rigid alignment: rotate around the origin first, then translate.
#[derive(Clone, Copy, Debug, PartialEq, Serialize, Deserialize)]
pub struct Alignment {
    /// Translation after rotation.
    pub translation: Vec3,
    /// Rotation axis.
    pub axis: Vec3,
    /// Rotation angle in radians.
    pub angle: f64,
    /// The same rotation in degrees, computed by the kernel for command parameters.
    pub angle_degrees: f64,
    /// Whether to emit rotation parameters, using the Core's existing command threshold.
    pub rotate: bool,
}

/// A descriptive deviation report; never used as a reconstruction acceptance proof.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Deviation {
    /// Largest absolute distance reported.
    pub max: f64,
    /// Mean absolute distance reported.
    pub mean: f64,
    /// Root mean square distance reported.
    pub rms: f64,
    /// Reported share within the requested tolerance.
    pub within: f64,
    /// Number of vertices included by the report.
    pub vertices: usize,
    /// Farthest vertices: point and signed distance, farthest first.
    pub worst: Vec<(Vec3, f64)>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn existing_surface_names_and_fields_keep_their_serde_shape() {
        let surface = Primitive::Cone {
            apex: Vec3::new(1.0, 2.0, 3.0),
            axis: Vec3::new(0.0, 0.0, 1.0),
            half_angle: 0.25,
        };
        let wire =
            json!({"kind":"cone","apex":[1.0,2.0,3.0],"axis":[0.0,0.0,1.0],"half_angle":0.25});
        assert_eq!(serde_json::to_value(surface).unwrap(), wire);
        assert_eq!(serde_json::from_value::<Primitive>(wire).unwrap(), surface);
        assert_eq!(
            serde_json::to_value(SurfaceKind::Cylinder).unwrap(),
            json!("cylinder")
        );
        assert_eq!(surface.kind(), SurfaceKind::Cone);
        assert_eq!(
            SurfaceKind::parse("  CYLINDER  "),
            Some(SurfaceKind::Cylinder)
        );
        assert_eq!(SurfaceKind::parse("future_surface"), None);
    }

    #[test]
    fn mesh_record_is_an_indexed_source_not_a_display_mesh() {
        let wire =
            json!({"positions":[[0.0,0.0,0.0],[1.0,0.0,0.0],[0.0,1.0,0.0]],"triangles":[[2,0,1]]});
        let mesh: MeshInput = serde_json::from_value(wire.clone()).unwrap();
        assert_eq!(mesh.triangles, [[2, 0, 1]]);
        assert_eq!(serde_json::to_value(mesh).unwrap(), wire);
    }
}
