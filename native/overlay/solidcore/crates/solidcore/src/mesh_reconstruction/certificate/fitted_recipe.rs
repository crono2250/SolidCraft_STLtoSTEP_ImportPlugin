//! Complete finite rectangular-stock recipe and original-region finite membership.
//!
//! Initial proved recipe class: one CCW four-Line rectangle without holes, signed
//! permutation frame, finite increasing levels, exact finite lower origin/height.
//! It is an independently proved product domain, NEVER a MeshInput/SourceCertificate.
//! All actual cap/side/native CW/material geometry uses the SAME existing product
//! consumer. Other tool families/frames/holes remain pending, not a fallback.
use super::super::fitted_tool_certificate::{certify_fitted_tool_with_work, FittedToolCertificate};
use super::super::{
    FittedTool, MeshError, MeshInput, MeshWork, Primitive, PrismTool, ToolGeometry,
};
use super::endpoint_proposal::{build_endpoint_model, EndpointAlias, PrismaticEndpointProposal};
use super::exact_geometry as x;
use super::product_driver::prove_recipe_product_request_with_work;
use crate::blend::fillet_section::interval::Ivl;
use crate::prism::profile::Seg2;
use crate::{Brep, Kernel, Result, SolidError};
use std::collections::BTreeMap;
const OP: &str = "mesh_reconstruction::finite_rectangle_recipe";
fn refused(reason: &'static str) -> SolidError {
    SolidError::Unsupported {
        operation: OP,
        reason,
    }
}
fn arithmetic() -> SolidError {
    refused("finite recipe exact arithmetic could not be bounded")
}
fn invariant(reason: &'static str) -> SolidError {
    SolidError::port_invariant(OP, reason)
}
fn charged(k: &Kernel, work: &MeshWork, slots: usize) -> Result<()> {
    let steps = slots.checked_mul(16).ok_or_else(arithmetic)?;
    work.spend_core(k, steps)?;
    work.reserve_cells_core(k, slots)
}
// These are storage/work guards for EXISTING exact_geometry operations, not a
// second arithmetic implementation. add(m,n): m+nm+n(n+1)/2 coefficients and
// n+1 Vec headers; scale(m):3m²+2m coefficients,4m+1 headers (existing endpoint
// factory derivation). For subtraction, the conservative scale(n) to at most2n
// followed by add(m,2n) bounds the ACTUAL sub fold (same as add, scalar -c)
// with deliberate surplus. No cap or previously established charge is reduced.
fn add_slots(m: usize, n: usize) -> Result<usize> {
    let triangle = n
        .checked_add(1)
        .and_then(|a| n.checked_mul(a))
        .and_then(|a| a.checked_div(2))
        .ok_or_else(arithmetic)?;
    m.checked_add(m.checked_mul(n).ok_or_else(arithmetic)?)
        .and_then(|a| a.checked_add(triangle))
        .and_then(|a| a.checked_add(n))
        .and_then(|a| a.checked_add(1))
        .ok_or_else(arithmetic)
}
fn scale_slots(m: usize) -> Result<usize> {
    m.checked_mul(m)
        .and_then(|a| a.checked_mul(3))
        .and_then(|a| m.checked_mul(6).and_then(|b| a.checked_add(b)))
        .and_then(|a| a.checked_add(1))
        .ok_or_else(arithmetic)
}
fn subtract(k: &Kernel, work: &MeshWork, a: &x::E, b: &x::E) -> Result<x::E> {
    if a.is_empty() || b.is_empty() {
        return Err(arithmetic());
    }
    let doubled = b.len().checked_mul(2).ok_or_else(arithmetic)?;
    let slots = scale_slots(b.len())?
        .checked_add(add_slots(a.len(), doubled)?)
        .ok_or_else(arithmetic)?;
    charged(k, work, slots)?;
    x::sub(a, b).ok_or_else(arithmetic)
}
fn scale(k: &Kernel, work: &MeshWork, a: &x::E, b: f64) -> Result<x::E> {
    if a.is_empty() {
        return Err(arithmetic());
    }
    charged(k, work, scale_slots(a.len())?)?;
    x::scale(a, b).ok_or_else(arithmetic)
}
fn add(k: &Kernel, work: &MeshWork, a: &x::E, b: &x::E) -> Result<x::E> {
    if a.is_empty() || b.is_empty() {
        return Err(arithmetic());
    }
    charged(k, work, add_slots(a.len(), b.len())?)?;
    x::add(a, b).ok_or_else(arithmetic)
}
fn scalar(k: &Kernel, work: &MeshWork, value: f64) -> Result<x::E> {
    charged(k, work, 2)?;
    x::scalar(value).ok_or_else(arithmetic)
}
fn signed_axis(v: [f64; 3]) -> Option<(usize, f64)> {
    match v {
        [1., 0., 0.] => Some((0, 1.)),
        [-1., 0., 0.] => Some((0, -1.)),
        [0., 1., 0.] => Some((1, 1.)),
        [0., -1., 0.] => Some((1, -1.)),
        [0., 0., 1.] => Some((2, 1.)),
        [0., 0., -1.] => Some((2, -1.)),
        _ => None,
    }
}
fn line(segment: &Seg2) -> Result<(crate::math::Vec2, crate::math::Vec2)> {
    match segment {
        Seg2::Line { a, b } => Ok((*a, *b)),
        _ => Err(refused("recipe is not a four-Line rectangle")),
    }
}
/// Private constructor proves one exact filled rectangle × increasing interval.
/// Fixed complete corners have coherent closure and positive area, distinct
/// orthogonal signed-unit axes give an injective affine chart and nonzero D.
/// Its boundary is one embedded outward product with no holes/cavities/extra CW.
pub(crate) struct RectangularRecipe<'a> {
    tool: &'a PrismTool,
    points: Vec<x::P>,
    cap_levels: [x::E; 2],
    translation: x::P,
    normal: x::P,
    upper_to_lower: BTreeMap<u32, u32>,
    rims: Vec<Vec<u32>>,
    planar_axes: [usize; 2],
    normal_axis: usize,
    normal_hint: [f64; 3],
}
impl<'a> RectangularRecipe<'a> {
    pub(crate) fn new(k: &Kernel, work: &MeshWork, tool: &'a PrismTool) -> Result<Self> {
        work.spend_core(k, 128)?;
        let [region] = tool.regions.as_slice() else {
            return Err(refused("finite recipe needs exactly one region"));
        };
        if !region.holes.is_empty() {
            return Err(refused("rectangle recipe cannot contain holes"));
        }
        let [s0, s1, s2, s3] = region.outer.segs.as_slice() else {
            return Err(refused("finite recipe needs exactly four boundary lines"));
        };
        let (a0, b0) = line(s0)?;
        let (a1, b1) = line(s1)?;
        let (a2, b2) = line(s2)?;
        let (a3, b3) = line(s3)?;
        let finite = [a0, b0, a1, b1, a2, b2, a3, b3]
            .into_iter()
            .all(|p| p.x.is_finite() && p.y.is_finite());
        if !finite
            || a1 != b0
            || a2 != b1
            || a3 != b2
            || b3 != a0
            || b0.y != a0.y
            || b0.x <= a0.x
            || b1.x != b0.x
            || b1.y <= a0.y
            || b2.x != a0.x
            || b2.y != b1.y
            || a3.x != a0.x
            || a3.y != b1.y
            || !tool.start.is_finite()
            || !tool.end.is_finite()
            || tool.start >= tool.end
        {
            return Err(refused(
                "recipe rectangle is not a complete finite positive oriented domain",
            ));
        }
        let (u, _) = signed_axis(tool.frame.x_axis)
            .ok_or_else(|| refused("general recipe frame requires separate authority"))?;
        let (v, _) = signed_axis(tool.frame.y_axis)
            .ok_or_else(|| refused("general recipe frame requires separate authority"))?;
        if u == v {
            return Err(refused("recipe planar axes are dependent"));
        }
        let (_, _, _, n) = crate::prism::profile::axes(&tool.frame);
        let normal_hint = n.to_array();
        let (normal_axis, normal_sign) = signed_axis(normal_hint)
            .ok_or_else(|| invariant("signed-permutation normal changed"))?;
        let lower =
            crate::prism::profile::to_world(&tool.frame, crate::math::Vec2::ZERO, tool.start)
                .to_array();
        let h = tool.end - tool.start;
        if !h.is_finite() || h <= 0. || lower.iter().any(|v| !v.is_finite()) {
            return Err(refused("recipe origin/height is not finite"));
        }
        // Prove representability, never accept equality of rounded projections.
        for ((&o, &axis), &rounded) in tool.frame.origin.iter().zip(&normal_hint).zip(&lower) {
            let o = scalar(k, work, o)?;
            let n = scalar(k, work, axis)?;
            let start = scale(k, work, &n, tool.start)?;
            let exact = add(k, work, &o, &start)?;
            let rounded = scalar(k, work, rounded)?;
            if !x::zero(&subtract(k, work, &exact, &rounded)?) {
                return Err(refused(
                    "recipe lower origin needs a separate exact transport",
                ));
            }
        }
        let end = scalar(k, work, tool.end)?;
        let start = scalar(k, work, tool.start)?;
        let exact_h = subtract(k, work, &end, &start)?;
        let rounded_h = scalar(k, work, h)?;
        if !x::zero(&subtract(k, work, &exact_h, &rounded_h)?) {
            return Err(refused("recipe height needs a separate exact transport"));
        }
        // Eight recipe corners are construction geometry, not an original mesh.
        work.reserve_cells_core(k, 25)?;
        work.reserve_output_core(k, 8)?;
        let mut aliases = Vec::new();
        for translated in [false, true] {
            for p in [a0, b0, b1, b2] {
                work.spend_core(k, 1)?;
                aliases.push(EndpointAlias {
                    uv: p.to_array(),
                    translated,
                });
            }
        }
        let proposal = PrismaticEndpointProposal {
            origin: lower,
            a: tool.frame.x_axis,
            b: tool.frame.y_axis,
            translation_factor: h,
            aliases,
        };
        let model = build_endpoint_model(k, work, 8, &proposal)?;
        let low = model
            .points
            .first()
            .ok_or_else(|| invariant("exact recipe low corner missing"))?;
        let high = model
            .points
            .get(4)
            .ok_or_else(|| invariant("exact recipe high corner missing"))?;
        charged(k, work, 1)?;
        let mut translation = [Vec::new(), Vec::new(), Vec::new()];
        for ((out, high), low) in translation.iter_mut().zip(high).zip(low) {
            *out = subtract(k, work, high, low)?;
        }
        let low_level = scale(
            k,
            work,
            low.get(normal_axis)
                .ok_or_else(|| invariant("recipe normal coordinate missing"))?,
            normal_sign,
        )?;
        let high_level = scale(
            k,
            work,
            high.get(normal_axis)
                .ok_or_else(|| invariant("recipe normal coordinate missing"))?,
            normal_sign,
        )?;
        if x::sign(&subtract(k, work, &high_level, &low_level)?) != Some(1) {
            return Err(refused("exact recipe interval has no positive length"));
        }
        work.spend_core(k, 16)?;
        work.reserve_cells_core(k, 14)?; // four map entries, one rim/header+four IDs.
        work.reserve_output_core(k, 9)?;
        let mut partners = BTreeMap::new();
        for (high, low) in [(4, 0), (5, 1), (6, 2), (7, 3)] {
            partners.insert(high, low);
        }
        let rims = vec![vec![0, 1, 2, 3]];
        Ok(Self {
            tool,
            points: model.points,
            cap_levels: [low_level, high_level],
            translation,
            normal: model.normal,
            upper_to_lower: partners,
            rims,
            planar_axes: [u, v],
            normal_axis,
            normal_hint,
        })
    }
    pub(crate) fn points(&self) -> &[x::P] {
        &self.points
    }
    pub(crate) fn cap_levels(&self) -> &[x::E; 2] {
        &self.cap_levels
    }
    pub(crate) fn translation(&self) -> &x::P {
        &self.translation
    }
    pub(crate) fn cap_normal(&self) -> &x::P {
        &self.normal
    }
    pub(crate) fn partners(&self) -> &BTreeMap<u32, u32> {
        &self.upper_to_lower
    }
    pub(crate) fn rims(&self) -> &Vec<Vec<u32>> {
        &self.rims
    }
    pub(crate) fn normal_hint(&self) -> [f64; 3] {
        self.normal_hint
    }
    fn selected_finite_upper(
        &self,
        k: &Kernel,
        work: &MeshWork,
        source: &MeshInput,
        selected: &[u32],
    ) -> Result<f64> {
        let low = self
            .points
            .first()
            .ok_or_else(|| invariant("proved recipe low corner missing"))?;
        let opposite = self
            .points
            .get(2)
            .ok_or_else(|| invariant("proved recipe opposite corner missing"))?;
        let top = self
            .points
            .get(4)
            .and_then(|p| p.get(self.normal_axis))
            .ok_or_else(|| invariant("proved recipe top corner missing"))?;
        let mut upper = 0_f64;
        for &triangle in selected {
            work.spend_core(k, 1)?;
            let triangle = usize::try_from(triangle)
                .ok()
                .and_then(|i| source.triangles.get(i))
                .ok_or_else(|| invariant("validated selected triangle disappeared"))?;
            for &vertex in triangle {
                work.spend_core(k, 1)?;
                let point = usize::try_from(vertex)
                    .ok()
                    .and_then(|i| source.positions.get(i))
                    .ok_or_else(|| invariant("validated original vertex disappeared"))?;
                for axis in self.planar_axes {
                    let a = low
                        .get(axis)
                        .ok_or_else(|| invariant("proved planar coordinate missing"))?;
                    let b = opposite
                        .get(axis)
                        .ok_or_else(|| invariant("proved planar coordinate missing"))?;
                    let order = x::sign(&subtract(k, work, a, b)?).ok_or_else(arithmetic)?;
                    let (min, max) = if order < 0 { (a, b) } else { (b, a) };
                    let p = scalar(
                        k,
                        work,
                        *point
                            .get(axis)
                            .ok_or_else(|| invariant("validated source coordinate disappeared"))?,
                    )?;
                    if x::sign(&subtract(k, work, &p, min)?).is_none_or(|s| s < 0)
                        || x::sign(&subtract(k, work, max, &p)?).is_none_or(|s| s < 0)
                    {
                        return Err(refused(
                            "complete selected triangle leaves requested finite rectangle",
                        ));
                    }
                }
                let p = scalar(
                    k,
                    work,
                    *point.get(self.normal_axis).ok_or_else(|| {
                        invariant("validated source normal coordinate disappeared")
                    })?,
                )?;
                let delta = subtract(k, work, &p, top)?;
                let interval = x::interval(&delta).ok_or_else(arithmetic)?;
                upper = upper.max(interval.lo.abs().max(interval.hi.abs()));
            }
        }
        // Each projection coordinate and signed plane distance is affine on the
        // WHOLE source triangle. Corner inequalities imply convex filled-domain
        // membership and this uniform bound; no closest-point probes are used.
        Ok(upper)
    }
}
/// Complete finite recipe+selected-region result on the same final canonical body.
/// No Clone/serde/adoption boolean and no post-proof mutation is permitted.
pub struct FiniteFittedToolCertificate<'a> {
    support: FittedToolCertificate<'a>,
    selected_finite_upper: f64,
    recipe_boundary_upper: f64,
}
impl FiniteFittedToolCertificate<'_> {
    /// Uniform bound for EVERY complete selected original triangle to the finite
    /// actual requested tool, with its whole recipe/actual error added outward.
    #[must_use]
    pub fn selected_finite_upper(&self) -> f64 {
        self.selected_finite_upper
    }
    /// Bidirectional complete requested rectangle-product boundary/actual bound.
    #[must_use]
    pub fn recipe_boundary_upper(&self) -> f64 {
        self.recipe_boundary_upper
    }
    /// Same original data, selection/recipe and final actual B-rep kept borrowed.
    #[must_use]
    pub fn source(&self) -> (&MeshInput, &FittedTool, &Brep) {
        self.support.source()
    }
}
/// Prove a complete requested finite stock tool and ALL selected source triangles.
/// Initial closed class is an axis-frame single rectangular Prism; all other
/// recipes explicitly refuse pending their own complete domain theorem.
/// Native workspace/materialization/export admission is a separate required gate.
///
/// # Errors
/// Invalid/unsupported recipe, whole-domain/extent/CW/material refusal, native
/// errors/cancellation and cumulative shared budget exhaustion; no theorem retry.
pub fn certify_finite_fitted_tool_with_work<'a>(
    k: &mut Kernel,
    work: &MeshWork,
    source: &'a MeshInput,
    tool: &'a FittedTool,
    candidate: &'a mut Brep,
    tolerance: f64,
) -> super::super::Result<FiniteFittedToolCertificate<'a>> {
    work.check(k)?;
    super::super::regions::checked_tolerance(tolerance)?;
    if !matches!(tool.surface, Primitive::Plane { .. }) {
        return Err(MeshError::Refused {
            stage: OP,
            detail: "finite family is not proved by rectangle stock".into(),
        });
    }
    let ToolGeometry::Prism(prism) = &tool.geometry else {
        return Err(MeshError::Refused {
            stage: OP,
            detail: "finite tool requires a complete recipe authority".into(),
        });
    };
    let result = RectangularRecipe::new(k, work, prism);
    work.check(k)?;
    let recipe = result?;
    let standing = crate::topology::brep::validation::soundness(k, candidate);
    work.check(k)?;
    let standing = standing?;
    if !standing.manifold || !standing.sound() {
        return Err(MeshError::Refused {
            stage: OP,
            detail: "actual finite tool lacks native solid soundness".into(),
        });
    }
    let support = certify_fitted_tool_with_work(k, work, source, tool, candidate, tolerance)?;
    let body = support.source().2;
    let whole = prove_recipe_product_request_with_work(k, work, &recipe, body, tolerance);
    work.check(k)?;
    let whole = whole?;
    if !core::ptr::eq(whole.body(), body)
        || !core::ptr::eq(recipe.tool, prism)
        || support.actual_support().0 != whole.upper_cap()
    {
        return Err(MeshError::Refused {
            stage: OP,
            detail: "selected actual support is not the same finite upper cap".into(),
        });
    }
    let finite = recipe.selected_finite_upper(k, work, source, &tool.source_triangles);
    work.check(k)?;
    let finite = finite?;
    let selected_finite_upper = (Ivl::from(finite) + Ivl::from(whole.upper_bound())).hi;
    if !selected_finite_upper.is_finite() || selected_finite_upper > tolerance {
        return Err(MeshError::Refused {
            stage: OP,
            detail: "whole selected-to-finite bound exceeds unchanged tolerance".into(),
        });
    }
    work.check(k)?;
    let recipe_boundary_upper = whole.upper_bound();
    Ok(FiniteFittedToolCertificate {
        support,
        selected_finite_upper,
        recipe_boundary_upper,
    })
}
