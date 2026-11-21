//! Complete half-plane collar for a radial bore in convex prismatic stock.
//!
//! Every proposed stock edge must put every non-incident vertex strictly on its
//! interior side. This certifies one strictly convex closed outline. The
//! largest bore radius plus radial correction is attained at one of its
//! affine height endpoints. Subtract that allowance and the independent
//! wall movement bound from every support-line clearance. Positive margins
//! separate the whole moving bore from every moving stock side.
//!
//! Source/Native wall and cap matching are separate consumers. Angularly
//! complete cylindrical/countersunk bore patches come from SourceRadialStack.
//! Deviations: none. O(number of outline vertices squared), shared MeshWork.
use super::super::work::MeshWork;
use super::radial_stack::SourceRadialStack;
use crate::blend::fillet_section::interval::Ivl;
use crate::{Kernel, Result, SolidError};

const OP: &str = "mesh_reconstruction::certificate::radial_stock";
fn refusal(reason: &'static str) -> SolidError {
    SolidError::Unsupported {
        operation: OP,
        reason,
    }
}

fn difference(a: [f64; 2], b: [f64; 2]) -> [Ivl; 2] {
    let [x, y] = a.map(Ivl::from);
    let [u, v] = b.map(Ivl::from);
    [x - u, y - v]
}

fn cross([a, b]: [Ivl; 2], [u, v]: [Ivl; 2]) -> Ivl {
    a * v - b * u
}

struct ConvexStockCollar<'a> {
    _outline: &'a [[f64; 2]],
    minimum_clearance: f64,
}

fn convex_clearance_with_work<'a>(
    k: &Kernel,
    w: &MeshWork,
    outline: &'a [[f64; 2]],
    center: [f64; 2],
    maximum_radius: Ivl,
) -> Result<ConvexStockCollar<'a>> {
    w.spend_core(k, 32)?;
    if outline.len() < 3
        || !maximum_radius.is_finite()
        || maximum_radius.lo < 0.
        || center.iter().any(|v| !v.is_finite())
    {
        return Err(refusal("invalid convex stock collar input"));
    }
    let mut minimum_clearance = f64::INFINITY;
    let ends = outline.iter().copied().cycle().skip(1);
    for (i, (a, b)) in outline.iter().copied().zip(ends).enumerate() {
        w.spend_core(k, 48)?;
        let edge = difference(b, a);
        let [dx, dy] = edge;
        let length = (dx * dx + dy * dy).sqrt();
        if !length.is_finite() || !length.is_positive() {
            return Err(refusal("convex stock wall has a zero or unbounded edge"));
        }
        for (j, &point) in outline.iter().enumerate() {
            w.spend_core(k, 32)?;
            if j == i || (j == i + 1) || (i + 1 == outline.len() && j == 0) {
                continue;
            }
            let turn = cross(edge, difference(point, a));
            if !turn.is_finite() || !turn.is_positive() {
                return Err(refusal(
                    "stock profile is not a complete strictly convex CCW polygon",
                ));
            }
        }
        let signed = cross(edge, difference(center, a)) / length;
        let clearance = signed - maximum_radius;
        if !clearance.is_finite() || !clearance.is_positive() {
            return Err(refusal(
                "a moving radial bore can reach a convex stock wall",
            ));
        }
        minimum_clearance = minimum_clearance.min(clearance.lo);
    }
    Ok(ConvexStockCollar {
        _outline: outline,
        minimum_clearance,
    })
}

/// Returns a lower clearance in the common axial chart. The outer wall
/// allowance has to be independently proved in this same chart, covering its
/// entire movement. Its horizontal stock section must be constant in height.
pub(crate) fn prove_convex_stock_radial_collar_with_work(
    k: &Kernel,
    w: &MeshWork,
    outline: &[[f64; 2]],
    wall_movement_upper: f64,
    stack: &SourceRadialStack<'_, '_, '_, '_, '_>,
) -> Result<f64> {
    if !wall_movement_upper.is_finite() || wall_movement_upper < 0. {
        return Err(refusal("stock wall movement allowance is invalid"));
    }
    let first = stack
        .patches()
        .first()
        .ok_or_else(|| refusal("missing bore stack"))?;
    if !first.claim().concave {
        return Err(refusal("stock collar requires an inward radial wall"));
    }
    let mut maximum = 0_f64;
    for patch in stack.patches() {
        w.spend_core(k, 1)?;
        let [a, b] = patch.claim().law.radius;
        let envelope =
            Ivl::from(a.max(b)) + Ivl::from(patch.local_upper()) + Ivl::from(wall_movement_upper);
        if !envelope.is_finite() {
            return Err(refusal("bore radius envelope is not finite"));
        }
        maximum = maximum.max(envelope.hi);
    }
    let q = convex_clearance_with_work(k, w, outline, first.claim().center, Ivl::from(maximum))?;
    Ok(q.minimum_clearance)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn countersink_envelope_checks_entire_outer_stock_boundary() {
        let k = Kernel::default();
        let stock = [[0., 0.], [10., 0.], [10., 5.], [0., 5.]];
        for (center, radius, allowed) in [
            ([3., 2.5], 2.4, true),
            ([3., 2.5], 2.51, false),
            ([9., 3.], 1.01, false),
            ([-2., 2.5], 1., false),
        ] {
            let w = MeshWork::new();
            assert_eq!(
                convex_clearance_with_work(&k, &w, &stock, center, Ivl::from(radius)).is_ok(),
                allowed
            );
        }
    }

    #[test]
    fn concave_stock_cannot_claim_a_convex_collar() {
        let k = Kernel::default();
        let stock = [[0., 0.], [10., 0.], [10., 5.], [5., 1.], [0., 5.]];
        let w = MeshWork::new();
        assert!(convex_clearance_with_work(&k, &w, &stock, [2., 1.], Ivl::from(0.1)).is_err());
    }
}
