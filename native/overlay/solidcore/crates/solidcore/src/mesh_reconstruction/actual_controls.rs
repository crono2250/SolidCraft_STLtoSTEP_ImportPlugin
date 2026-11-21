//! Authoritative full control membership for immutable actual curve uses.
//! Projective control equality here never claims equality of rational curves.
use super::actual_roots::actual_used_roots;
use super::certificate::{affine_ends, exact_geometry as x};
use super::convex_controls::Control;
use super::profile_chain::ChainGraphCover;
use super::{MeshError, MeshWork};
use crate::curve::curve::{Curve, CurveKind};
use crate::Kernel;
const OP: &str = "mesh_reconstruction::actual_profile_controls";
type Result<T> = core::result::Result<T, MeshError>;
fn unsure(n: usize) -> MeshError {
    MeshError::Undecided { stage: OP, work: n }
}
pub(crate) struct ActualControlSpan<'a> {
    pub(crate) actual: &'a Curve,
    pub(crate) curve_use: usize,
    pub(crate) span: usize,
    pub(crate) native_interval: [f64; 2],
    pub(crate) controls: Vec<Control>,
}
/// Every control comes from the actual evaluated full native span, or from the
/// native Line's exact affine endpoint expression; no fitting/corner proxy.
pub(crate) fn actual_control_spans<'a>(
    k: &Kernel,
    work: &MeshWork,
    graph: &ChainGraphCover<'a>,
) -> Result<Vec<ActualControlSpan<'a>>> {
    work.check(k)?;
    let mut out = Vec::new();
    for (use_index, usage) in graph.uses.iter().enumerate() {
        let roots = actual_used_roots(k, work, usage.curve, usage.interval, usage.forward)?;
        work.reserve_output(k, roots.len())?;
        for (span, root) in roots.into_iter().enumerate() {
            let mut controls = Vec::new();
            if matches!(usage.curve.kind(), CurveKind::Line(_)) {
                let Some(mut ends) = affine_ends(usage.curve, usage.interval, false) else {
                    return Err(unsure(use_index));
                };
                if !usage.forward {
                    ends.reverse();
                }
                work.reserve_output(k, 2)?;
                for xyz in ends {
                    controls.push(Control {
                        xyz,
                        w: x::scalar(1.).ok_or_else(|| unsure(span))?,
                    });
                }
            } else {
                if root.piece.err != 0. {
                    return Err(unsure(span));
                }
                let [x, y, z, w] = &root.piece.h;
                let count = w.coefficients().len();
                if [x, y, z].iter().any(|p| p.coefficients().len() != count) {
                    return Err(unsure(span));
                }
                work.reserve_output(k, count)?;
                for (((&x, &y), &z), &w) in x
                    .coefficients()
                    .iter()
                    .zip(y.coefficients())
                    .zip(z.coefficients())
                    .zip(w.coefficients())
                {
                    work.spend(k, 1)?;
                    if !crate::geom::certified::above(w, 0.) {
                        return Err(unsure(span));
                    }
                    controls.push(Control {
                        xyz: x::point([x, y, z]).ok_or_else(|| unsure(span))?,
                        w: x::scalar(w).ok_or_else(|| unsure(span))?,
                    });
                }
            }
            out.push(ActualControlSpan {
                actual: usage.curve,
                curve_use: use_index,
                span,
                native_interval: root.native_interval,
                controls,
            });
        }
    }
    work.check(k)?;
    Ok(out)
}
