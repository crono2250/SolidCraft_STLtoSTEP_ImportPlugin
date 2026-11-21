//! Rigid placement of fitted frame data. This never normalises transformed axes or drops
//! scale/shear; non-rigid or undecided placements are typed refusals.
use crate::eval::Frame;
use crate::geom::certified::{dot, gamma, Bounded, Verdict};
use crate::kernel::Kernel;
use crate::math::{Transform, Vec3};
use crate::prism::profile;

use super::types::{invalid, MeshError, Result};

const OP: &str = "mesh_reconstruction::transform_frame";
const RIGID_TOLERANCE: f64 = 1e-10;

/// Transform a fitted frame through an existing application placement matrix without refitting
/// or normalising it. Matrices use the standard native/app row-vector basis storage.
///
/// # Errors
/// Nonfinite/non-affine data, scale/shear, undecided rigid bounds or cancellation.
pub fn transform_frame(k: &Kernel, frame: &Frame, matrix: &[[f64; 4]; 4]) -> Result<Frame> {
    k.check_cancelled(OP)?;
    if !matrix.iter().flatten().all(|value| value.is_finite())
        || !profile::frame_is_orthonormal(frame)
    {
        return Err(invalid(
            "a fitted plane and its placement must be finite and orthonormal",
        ));
    }
    if matrix[0][3] != 0.0 || matrix[1][3] != 0.0 || matrix[2][3] != 0.0 || matrix[3][3] != 1.0 {
        return Err(invalid("a fitted plane requires an affine placement"));
    }
    let transform = Transform { m: *matrix };
    let axes = [transform.x_axis(), transform.y_axis(), transform.z_axis()];
    for (i, a) in axes.iter().enumerate() {
        for (j, b) in axes.iter().enumerate().skip(i) {
            let expected: f64 = if i == j { 1.0 } else { 0.0 };
            let product = dot(*a, *b, 0.0, 0.0);
            let error = Bounded {
                value: (product.value - expected).abs(),
                bound: product.bound + gamma(1) * (product.value.abs() + expected.abs()),
            };
            match error.at_most(RIGID_TOLERANCE) {
                Verdict::Yes => {}
                Verdict::No => {
                    return Err(MeshError::Refused {
                        stage: OP,
                        detail: "scale or shear is not supported for a fitted sketch plane".into(),
                    })
                }
                Verdict::Undecided => {
                    return Err(MeshError::Undecided {
                        stage: OP,
                        work: 16,
                    })
                }
            }
        }
    }
    let vector = |values: [f64; 3]| Vec3::new(values[0], values[1], values[2]);
    let origin = transform.transform_point(vector(frame.origin));
    let x = transform.transform_vector(vector(frame.x_axis));
    let y = transform.transform_vector(vector(frame.y_axis));
    let placed = Frame {
        origin: [origin.x, origin.y, origin.z],
        x_axis: [x.x, x.y, x.z],
        y_axis: [y.x, y.y, y.z],
    };
    if !profile::frame_is_orthonormal(&placed) {
        return Err(MeshError::Refused {
            stage: OP,
            detail: "the placed plane is not orthonormal; axes were not normalised".into(),
        });
    }
    k.check_cancelled(OP)?;
    Ok(placed)
}

/// A section frame translated along its own normal by the requested level.
///
/// # Errors
/// Nonfinite data, nonorthonormal input or cancellation.
pub fn offset_plane(k: &Kernel, frame: &Frame, offset: f64) -> Result<Frame> {
    k.check_cancelled("mesh_reconstruction::offset_plane")?;
    if !offset.is_finite() || !profile::frame_is_orthonormal(frame) {
        return Err(invalid(
            "plane and offset must be finite with orthonormal axes",
        ));
    }
    let origin = profile::to_world(frame, crate::math::Vec2::ZERO, offset);
    Ok(Frame {
        origin: [origin.x, origin.y, origin.z],
        x_axis: frame.x_axis,
        y_axis: frame.y_axis,
    })
}
