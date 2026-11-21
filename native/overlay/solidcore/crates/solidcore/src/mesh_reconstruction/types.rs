//! Native mesh reconstruction data. No record, application, or serialization dependency.
use super::numeric::Vec3Numeric;
use crate::eval::Frame;
use crate::math::Vec3;
use crate::prism::profile::Region2;

/// Source triangles in their original input order; indices are checked before work starts.
#[derive(Clone, Debug, PartialEq)]
pub struct MeshInput {
    /// Untouched original coordinates in input order.
    pub positions: Vec<[f64; 3]>,
    /// Original vertex triples in input order.
    pub triangles: Vec<[u32; 3]>,
}

#[derive(Clone, Copy, Debug, PartialEq)]
/// One source-space analytic selection.
pub struct MeshPick {
    /// Source-space selection point.
    pub point: [f64; 3],
    /// Requested analytic surface family.
    pub kind: SurfaceKind,
}

/// Native refusals are structured and preserve the original kernel error.
#[derive(Debug)]
pub enum MeshError {
    /// Malformed or unsupported input values.
    InvalidInput {
        /// The operation that refused the input or proof.
        stage: &'static str,
        /// The specific reason for refusal.
        detail: String,
    },
    /// The requested construction is not supported by the proven geometry.
    Refused {
        /// The operation that refused the input or proof.
        stage: &'static str,
        /// The specific reason for refusal.
        detail: String,
    },
    /// Source count exceeds its input admission limit before materialization.
    InputLimit {
        /// The operation that refused the input or proof.
        stage: &'static str,
        /// The actual input count.
        count: usize,
        /// The enforced count or work limit.
        limit: usize,
        /// The counted input entity.
        unit: &'static str,
    },
    /// The complete workflow exceeded a resource bound.
    BudgetExceeded {
        /// The operation that refused the input or proof.
        stage: &'static str,
        /// The enforced count or work limit.
        limit: usize,
    },
    /// Native failure, including cancellation and internal defects, preserved unchanged.
    Kernel(crate::SolidError),
    /// The required bounded proof was not established.
    Undecided {
        /// The operation that refused the input or proof.
        stage: &'static str,
        /// Work units consumed before the proof became undecided.
        work: usize,
    },
}
impl From<crate::SolidError> for MeshError {
    fn from(error: crate::SolidError) -> Self {
        Self::Kernel(error)
    }
}
/// A native mesh result that preserves input, resource, proof and kernel failures.
pub type Result<T> = core::result::Result<T, MeshError>;
pub(crate) fn invalid(message: &str) -> MeshError {
    MeshError::InvalidInput {
        stage: "mesh_reconstruction",
        detail: message.into(),
    }
}

/// The surface to recognise.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum SurfaceKind {
    /// Whichever of the others fits, simplest first.
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
    /// A ring: a fillet or round swept about an axis.
    Torus,
}

/// An analytic surface fitted to a region. Axes are unit vectors; a cone's axis points from
/// its apex into the cone.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Primitive {
    /// A plane.
    Plane {
        /// A point in model coordinates.
        point: Vec3,
        /// Oriented support normal.
        normal: Vec3,
    },
    /// A circular cylinder.
    Cylinder {
        /// A point in model coordinates.
        point: Vec3,
        /// Support axis direction.
        axis: Vec3,
        /// Radius in model units.
        radius: f64,
    },
    /// A circular cone.
    Cone {
        /// Cone apex in model coordinates.
        apex: Vec3,
        /// Support axis direction.
        axis: Vec3,
        /// Half angle in radians.
        half_angle: f64,
    },
    /// A sphere.
    Sphere {
        /// Centre in model coordinates.
        center: Vec3,
        /// Radius in model units.
        radius: f64,
    },
    /// The surface a circle of radius `minor` sweeps, its centre `major` from `center` in the
    /// plane across `axis`.
    Torus {
        /// Centre in model coordinates.
        center: Vec3,
        /// Support axis direction.
        axis: Vec3,
        /// Major radius in model units.
        major: f64,
        /// Generating-circle radius in model units.
        minor: f64,
    },
}

impl Primitive {
    /// Return the analytic surface family.
    pub fn kind(&self) -> SurfaceKind {
        match self {
            Primitive::Plane { .. } => SurfaceKind::Plane,
            Primitive::Cylinder { .. } => SurfaceKind::Cylinder,
            Primitive::Cone { .. } => SurfaceKind::Cone,
            Primitive::Sphere { .. } => SurfaceKind::Sphere,
            Primitive::Torus { .. } => SurfaceKind::Torus,
        }
    }

    /// Signed distance from the surface, positive on the side its [`Primitive::normal_at`] points to.
    pub fn signed_distance(&self, p: Vec3) -> f64 {
        match *self {
            Primitive::Plane { point, normal } => (p - point).dot(normal),
            Primitive::Cylinder {
                point,
                axis,
                radius,
            } => {
                let w = p - point;
                (w - axis * w.dot(axis)).len() - radius
            }
            Primitive::Cone {
                apex,
                axis,
                half_angle,
            } => {
                let w = p - apex;
                let h = w.dot(axis);
                let rho = (w - axis * h).len();
                rho * half_angle.cos() - h * half_angle.sin()
            }
            Primitive::Sphere { center, radius } => p.dist(center) - radius,
            Primitive::Torus {
                center,
                axis,
                major,
                minor,
            } => {
                let w = p - center;
                let h = w.dot(axis);
                let rho = (w - axis * h).len();
                (rho - major).hypot(h) - minor
            }
        }
    }

    /// The surface's unit normal near `p`, pointing away from its axis or centre.
    pub fn normal_at(&self, p: Vec3) -> Vec3 {
        match *self {
            Primitive::Plane { normal, .. } => normal,
            Primitive::Cylinder { point, axis, .. } => {
                let w = p - point;
                (w - axis * w.dot(axis))
                    .normalized()
                    .unwrap_or_else(|| axis.any_perp())
            }
            Primitive::Cone {
                apex,
                axis,
                half_angle,
            } => {
                let w = p - apex;
                let radial = (w - axis * w.dot(axis))
                    .normalized()
                    .unwrap_or_else(|| axis.any_perp());
                (radial * half_angle.cos() - axis * half_angle.sin())
                    .normalized()
                    .unwrap_or(radial)
            }
            Primitive::Sphere { center, .. } => (p - center).normalized().unwrap_or(Vec3::Z),
            Primitive::Torus {
                center,
                axis,
                major,
                ..
            } => {
                let w = p - center;
                let radial = (w - axis * w.dot(axis))
                    .normalized()
                    .unwrap_or_else(|| axis.any_perp());
                (p - (center + radial * major))
                    .normalized()
                    .unwrap_or(radial)
            }
        }
    }

    /// The nearest point on the surface.
    pub fn project(&self, p: Vec3) -> Vec3 {
        p - self.normal_at(p) * self.signed_distance(p)
    }
}

/// A recognised region of a mesh body.
#[derive(Clone, Debug, PartialEq)]
pub struct MeshRegion {
    /// Fitted analytic support; not a final-body acceptance proof.
    pub surface: Primitive,
    /// Derived dimensions for presentation.
    pub measurements: PrimitiveMeasures,
    /// The body's triangles (indices into its mesh) the surface covers.
    pub triangles: Vec<u32>,
    /// Sum of source triangle areas in squared model units.
    pub area: f64,
    /// Largest and root-mean-square distance of the region's vertices from the surface.
    pub max_deviation: f64,
    /// Root-mean-square descriptive vertex residual.
    pub rms_deviation: f64,
    /// The mesh lies on the surface's axis side: a bore or a spherical pocket, not a boss or a
    /// ball. Always false for a plane, whose normal points out of the material.
    pub concave: bool,
}

/// Diagnostic vertex distances, not a whole-surface reconstruction certificate.
#[derive(Clone, Debug, PartialEq)]
pub struct Deviation {
    /// Largest absolute reported distance.
    pub max: f64,
    /// Mean absolute reported distance.
    pub mean: f64,
    /// Root-mean-square reported distance.
    pub rms: f64,
    /// Fraction of reported vertices within the requested tolerance.
    pub within: f64,
    /// Number of reported source vertices.
    pub vertices: usize,
    /// Largest reported signed distances and their source positions.
    pub worst: Vec<(Vec3, f64)>,
}

/// Native extrusion data; modelling workflows execute it above the kernel.
#[derive(Clone, Debug)]
pub struct PrismTool {
    /// Local profile frame.
    pub frame: Frame,
    /// Planar material regions, including their holes.
    pub regions: Vec<Region2>,
    /// First axial coordinate in the profile frame.
    pub start: f64,
    /// Last axial coordinate in the profile frame.
    pub end: f64,
}
/// Source attribution retained across fitting. These are claims to verify, not certificates.
#[derive(Clone, Debug)]
pub struct SourcePatch {
    /// Fitted analytic support; not a final-body acceptance proof.
    pub surface: Primitive,
    /// Original indexed input triangle IDs, preserving attribution.
    pub source_triangles: Vec<u32>,
    /// Proposed directed boundary edges; the certificate rechecks incidence.
    pub oriented_rims: Vec<Vec<(u32, u32)>>,
    /// Whether source material lies on the support axis side.
    pub concave: bool,
}
#[derive(Clone, Debug, Default)]
/// Untrusted reconstruction correspondence claims; never an acceptance token.
pub struct ReconstructionProvenance {
    /// Original triangle-ID groups of the faceted candidate. Untrusted attribution:
    /// final face order, support, connectivity and complete rims must be re-verified.
    pub faceted_source_patches: Vec<Vec<u32>>,
    /// Proposed source support patches, independently verified before adoption.
    pub patches: Vec<SourcePatch>,
    /// Proposed cap loops indexed into the retained weld table.
    pub original_cap_loops: Vec<Vec<u32>>,
    /// Proposed immediate containing loops; None denotes an outer loop.
    pub cap_loop_parents: Vec<Option<usize>>,
}
#[derive(Clone, Debug)]
/// An analytic source feature and its proposed cutting extent.
pub struct PrimitiveTool {
    /// Fitted analytic support; not a final-body acceptance proof.
    pub surface: Primitive,
    /// Source support points used to choose tool extents.
    pub points: Vec<Vec3>,
    /// Whether source material lies on the support axis side.
    pub concave: bool,
    /// Original indexed input triangle IDs, preserving attribution.
    pub source_triangles: Vec<u32>,
}
#[derive(Clone, Debug, Default)]
pub(crate) struct Features {
    pub solids: Vec<PrimitiveTool>,
    pub patches: Vec<SourcePatch>,
}

impl MeshError {
    /// Whether the original native error is cancellation.
    pub fn is_cancelled(&self) -> bool {
        matches!(self,Self::Kernel(error) if error.is_cancelled())
    }
}
impl core::fmt::Display for MeshError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::InvalidInput { stage, detail } | Self::Refused { stage, detail } => {
                write!(f, "{stage}: {detail}")
            }
            Self::InputLimit {
                stage,
                count,
                limit,
                unit,
            } => write!(
                f,
                "{stage}: the mesh has {count} {unit}, more than the {limit} allowed"
            ),
            Self::BudgetExceeded { stage, limit } => {
                write!(f, "{stage}: work budget exceeded ({limit})")
            }
            Self::Kernel(error) => core::fmt::Display::fmt(error, f),
            Self::Undecided { stage, work } => write!(
                f,
                "{stage}: bounded proof undecided after {work} work units"
            ),
        }
    }
}
impl std::error::Error for MeshError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Kernel(error) => Some(error),
            _ => None,
        }
    }
}

/// A native construction request. Ops maps these to existing modelling calls, doing no math.
#[derive(Clone, Debug)]
pub enum ToolGeometry {
    /// A constant-section solid.
    Prism(PrismTool),
    /// A circular cylinder.
    Cylinder {
        /// Tool origin in model coordinates.
        origin: Vec3,
        /// Support axis direction.
        axis: Vec3,
        /// Radius in model units.
        radius: f64,
        /// Tool extent along its axis.
        length: f64,
    },
    /// A solid opening from one exact zero-radius pole along its axis.
    Cone {
        /// Exact tool pole in model coordinates.
        origin: Vec3,
        /// Direction from pole toward its circular base.
        axis: Vec3,
        /// Radius at the far base.
        radius: f64,
        /// Distance from pole to base along the axis.
        length: f64,
    },
    /// A sphere.
    Sphere {
        /// Centre in model coordinates.
        center: Vec3,
        /// Radius in model units.
        radius: f64,
    },
    /// A circular torus.
    Torus {
        /// Local profile frame.
        frame: Frame,
        /// Major radius in model units.
        major: f64,
        /// Generating-circle radius in model units.
        minor: f64,
    },
    /// A profile revolved about an in-plane axis.
    Revolve {
        /// Local profile frame.
        frame: Frame,
        /// Planar material regions, including their holes.
        regions: Vec<Region2>,
        /// Revolution origin in the profile plane.
        axis_origin: crate::math::Vec2,
        /// Revolution direction in the profile plane.
        axis_direction: crate::math::Vec2,
        /// Revolution sweep in radians.
        angle: f64,
    },
    /// Planar material regions as a sheet.
    PlanarSheet {
        /// Local profile frame.
        frame: Frame,
        /// Planar material regions, including their holes.
        regions: Vec<Region2>,
    },
    /// An exact circular wall extruded along its axis.
    CylindricalSheet {
        /// Local profile frame.
        frame: Frame,
        /// Ordered exact profile segments to extrude.
        chain: Vec<crate::prism::profile::Seg2>,
        /// First axial coordinate in the profile frame.
        start: f64,
        /// Last axial coordinate in the profile frame.
        end: f64,
    },
}
#[derive(Clone, Debug)]
/// A fitted tool candidate and its original source attribution.
pub struct FittedTool {
    /// Fitted analytic support; not a final-body acceptance proof.
    pub surface: Primitive,
    /// Native tool construction request.
    pub geometry: ToolGeometry,
    /// Original indexed input triangle IDs, preserving attribution.
    pub source_triangles: Vec<u32>,
    /// Whether source material lies on the support axis side.
    pub concave: bool,
}

/// A proposed alias class in the source weld. The certificate must verify its geometric
/// radius, unique oriented incidence, and absence of ambiguous sheet crossings.
#[derive(Clone, Debug)]
pub struct WeldVertexClaim {
    /// Proposed retained coordinate.
    pub position: [f64; 3],
    /// Original vertex IDs proposed as aliases of this coordinate.
    pub raw_vertices: Vec<u32>,
}
#[derive(Clone, Debug)]
/// Proposed source welding and triangle lineage, for independent verification.
pub struct WeldClaim {
    /// Proposed retained vertices and raw alias classes.
    pub vertices: Vec<WeldVertexClaim>,
    /// Candidate retained vertex triples.
    pub triangles: Vec<[u32; 3]>,
    /// Original triangle ID per candidate triangle; None marks synthetic geometry.
    pub original_triangles: Vec<Option<u32>>,
    /// Candidate welding allowance; this is not proof that the weld is harmless.
    pub tolerance: f64,
}

/// Geometric display quantities computed with the fitted primitive, not in presentation.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct PrimitiveMeasures {
    /// Full diameter in model units, when applicable.
    pub diameter: Option<f64>,
    /// Full included cone angle in degrees, when applicable.
    pub full_angle_degrees: Option<f64>,
}
/// Measured dimensions used by presentation; definition fields remain nonredundant.
pub fn primitive_measures(surface: &Primitive) -> PrimitiveMeasures {
    surface.measurements()
}
impl Primitive {
    /// Compute presentation dimensions from the analytic parameters.
    pub fn measurements(&self) -> PrimitiveMeasures {
        match *self {
            Self::Cylinder { radius, .. } | Self::Sphere { radius, .. } => PrimitiveMeasures {
                diameter: Some(2. * radius),
                full_angle_degrees: None,
            },
            Self::Cone { half_angle, .. } => PrimitiveMeasures {
                diameter: None,
                full_angle_degrees: Some(2. * half_angle.to_degrees()),
            },
            _ => PrimitiveMeasures::default(),
        }
    }
}
/// The rigid source alignment, with degrees precomputed for application move commands.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Alignment {
    /// Translation applied after the world-origin rotation.
    pub translation: Vec3,
    /// World-space rotation axis.
    pub axis: Vec3,
    /// Rotation in radians.
    pub angle: f64,
    /// The same rotation in degrees for command output.
    pub angle_degrees: f64,
    /// Whether the existing command rotation threshold is exceeded.
    pub rotate: bool,
}
