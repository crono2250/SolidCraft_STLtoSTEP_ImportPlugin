//! Complete source-product cap rim to ACTUAL native cap-edge model binding.
//!
//! Draft construction binds EVERY source product rim and EVERY actual rim of ONE
//! selected native support patch through complete ChainGraphCover/NativeCaps. It
//! re-reads and restricts all actual curve roots, uses ONE exact projective join at
//! every virtual or real boundary, and projects the whole sewn model into the
//! original product cap plane. Acceptance requires full paired-span model errors
//! inside unchanged native edge tubes and real joins inside native vertex balls.
//! The whole family then consumes `RimMotion`'s all-level embedding/nesting proof.
//!
//! This certifies complete cap RIMS only. It does not authorize body adoption:
//! actual full cap face-domain/Plane-band coverage, all actual side surfaces and
//! full trim product, target-region/material correspondence, canonical candidate
//! identity and all standing validity remain mandatory. No partial loop subset,
//! root subset, index/order claim, endpoint overlap or corner residual is proof.
//! Deviations: none. No recursion; all loops charge ONE shared `MeshWork`.
use super::super::actual_roots::actual_used_roots;
use super::super::native_caps::{bind_native_caps, NativeCaps};
use super::super::profile_chain::ChainGraphCover;
use super::super::work::MeshWork;
use super::exact_geometry as x;
use super::hulls::{paired_curve_upper, point_distance_upper};
use super::product_reference::ProductReference;
use super::rim_motion::{
    prove_rim_motion_with_work, MotionEdge, RationalControl, RimMotionVerdict,
};
use super::sewn_curve::{
    enclose_controls_with_work, project_sew_curve_with_work, ProjectivePoint, SewnCurveVerdict,
};
use super::source_prism::SourcePrism;
use super::source_view::{copy_point_with_work, exact_at_with_work};
use super::target_complex::TargetComplex;
use crate::blend::fillet_section::interval::Ivl;
use crate::geom::tol::zone_tol3d;
use crate::query::distance_bound::Piece;
use crate::topology::edge;
use crate::{Kernel, Result, SolidError};
const OP: &str = "mesh_reconstruction::certificate::native_profile";
fn refused(reason: &'static str) -> SolidError {
    SolidError::Unsupported {
        operation: OP,
        reason,
    }
}
fn invariant(reason: &'static str) -> SolidError {
    SolidError::PortInvariant {
        operation: OP,
        reason,
    }
}
fn native<T>(
    k: &Kernel,
    work: &MeshWork,
    result: super::super::Result<T>,
    reason: &'static str,
) -> Result<T> {
    work.spend_core(k, 0)?;
    match result {
        Ok(v) => Ok(v),
        Err(super::super::MeshError::Kernel(e)) => Err(e),
        Err(
            super::super::MeshError::Undecided { .. } | super::super::MeshError::Refused { .. },
        ) => Err(refused(reason)),
        Err(_) => Err(invariant(
            "a certified native graph helper returned an unexpected non-kernel failure",
        )),
    }
}
use super::exact_geometry::interval;
fn point_box(p: &ProjectivePoint) -> Option<[Ivl; 3]> {
    let w = interval(&p.w)?;
    if !w.is_positive() {
        return None;
    }
    let [a, b, c] = p.xyz.each_ref().map(interval);
    Some([a? / w, b? / w, c? / w])
}
fn projected(p: &x::P, normal: &x::P, low: &x::E, direction: &x::P) -> Option<ProjectivePoint> {
    let w = x::dot(normal, direction)?;
    if x::sign(&w) != Some(1) {
        return None;
    }
    let offset = x::sub(&x::dot(normal, p)?, low)?;
    let mut out = Vec::new();
    for (p, d) in p.iter().zip(direction) {
        out.push(x::sub(&x::mul(&w, p)?, &x::mul(d, &offset)?)?);
    }
    let [Some(a), Some(b), Some(c)] = [out.first(), out.get(1), out.get(2)] else {
        return None;
    };
    Some(ProjectivePoint {
        xyz: [a.clone(), b.clone(), c.clone()],
        w,
    })
}
fn source_loop_matches(
    k: &Kernel,
    work: &MeshWork,
    positions: &std::collections::BTreeMap<u32, x::P>,
    rim: &[u32],
    points: &[x::P],
) -> Result<Option<(i32, usize)>> {
    work.spend_core(k, 0)?;
    if rim.len() != points.len() || rim.is_empty() {
        return Ok(None);
    }
    for offset in 0..rim.len() {
        for reverse in [false, true] {
            let mut good = true;
            for (i, p) in points.iter().enumerate() {
                let index = if reverse {
                    offset
                        .checked_add(rim.len())
                        .and_then(|a| a.checked_sub(i))
                        .and_then(|a| a.checked_rem(rim.len()))
                } else {
                    offset.checked_add(i).and_then(|a| a.checked_rem(rim.len()))
                };
                let q = index
                    .and_then(|i| rim.get(i))
                    .and_then(|i| positions.get(i));
                let Some(q) = q else {
                    good = false;
                    break;
                };
                for (a, b) in q.iter().zip(p) {
                    let count = a
                        .len()
                        .checked_add(b.len())
                        .ok_or_else(|| refused("source matching coefficient count overflow"))?;
                    work.spend_core(k, count)?;
                    work.reserve_cells_core(k, count)?;
                    if !x::sub(a, b).is_some_and(|v| x::zero(&v)) {
                        good = false;
                        break;
                    }
                }
                // One exact mismatch disproves THIS finite ordered-list candidate.
                // The same offset/direction order is retained; a successful match
                // still checks every coordinate. No geometric sample accepts.
                if !good {
                    break;
                }
            }
            if good {
                return Ok(Some((if reverse { -1 } else { 1 }, offset)));
            }
        }
    }
    Ok(None)
}
/// One immutable draft whose actual root restrictions and common joins can be
/// borrowed without self-referential tokens. All metadata is private/unmodifiable.
pub(crate) struct NativeProfileDraft<'a, 's, 'raw> {
    source: ProductReference<'a, 's, 'raw>,
    complex: &'a TargetComplex<'a>,
    patch: usize,
    graphs: &'a [ChainGraphCover<'a>],
    _caps: Vec<NativeCaps<'a>>,
    actual: Vec<Vec<Piece>>,
    joins: Vec<Vec<ProjectivePoint>>,
    axes: [usize; 2],
    lift_metric: f64,
    tolerance: f64,
    level: usize,
    source_senses: Vec<i32>,
    source_aliases: Vec<Vec<u32>>,
}
impl<'a, 's, 'raw> NativeProfileDraft<'a, 's, 'raw> {
    pub(crate) fn source(&self) -> &ProductReference<'a, 's, 'raw> {
        &self.source
    }
    pub(crate) fn complex(&self) -> &'a TargetComplex<'a> {
        self.complex
    }
    pub(crate) fn patch(&self) -> usize {
        self.patch
    }
    pub(crate) fn graphs(&self) -> &'a [ChainGraphCover<'a>] {
        self.graphs
    }
    /// Original source product cap end:0=low,1=high. This is not a tolerance flag.
    pub(crate) fn level(&self) -> usize {
        self.level
    }
    pub(crate) fn axes(&self) -> [usize; 2] {
        self.axes
    }
    /// +1/-1 relative to the original upper-outward (+normal) source rim.
    /// Consumers MUST bind the actual cap material orientation explicitly.
    pub(crate) fn source_aliases(&self) -> &[Vec<u32>] {
        &self.source_aliases
    }
    pub(crate) fn source_senses(&self) -> &[i32] {
        &self.source_senses
    }
}
/// A full native closed rim family, bound to untouched source product+actual `BRep`.
/// Private model controls remain alive and unmodified for the rest of the proof.
pub(crate) struct NativeProfile<'a, 'g, 's, 'raw> {
    draft: &'a NativeProfileDraft<'g, 's, 'raw>,
    model: Vec<Vec<MotionEdge>>,
    controls_3d: Vec<Vec<Vec<ProjectivePoint>>>,
    source_model_upper: f64,
    actual_model_upper: f64,
}
impl<'a, 'g, 's, 'raw> NativeProfile<'a, 'g, 's, 'raw> {
    pub(crate) fn draft(&self) -> &'a NativeProfileDraft<'g, 's, 'raw> {
        self.draft
    }
    pub(crate) fn model(&self) -> &[Vec<MotionEdge>] {
        &self.model
    }
    pub(crate) fn controls_3d(&self) -> &[Vec<Vec<ProjectivePoint>>] {
        &self.controls_3d
    }
    pub(crate) fn source_model_upper(&self) -> f64 {
        self.source_model_upper
    }
    pub(crate) fn actual_model_upper(&self) -> f64 {
        self.actual_model_upper
    }
}
/// Bind all rims of ONE actual patch to all original source product rims. The
/// selected graph references must be the exact complete vertices of the SAME
/// independently proved product origin, cyclically either orientation. Original
/// wrappers retain original aliases; recipe indices are never original source.
/// Final material proof compares the actual cap orientation.
pub(crate) fn native_reference_profile_draft_at_level_with_work<'a, 's, 'raw>(
    k: &Kernel,
    work: &MeshWork,
    source: ProductReference<'a, 's, 'raw>,
    complex: &'a TargetComplex<'a>,
    patch: usize,
    graphs: &'a [ChainGraphCover<'a>],
    axes: [usize; 2],
    tolerance: f64,
    level: usize,
) -> Result<NativeProfileDraft<'a, 's, 'raw>> {
    work.spend_core(k, 0)?;
    let [u, v] = axes;
    if u == v || u > 2 || v > 2 || !tolerance.is_finite() || tolerance <= 0. {
        return Err(refused("invalid profile frame/tolerance"));
    }
    let missing = (0..3)
        .find(|&a| a != u && a != v)
        .ok_or_else(|| invariant("a two-axis profile has no omitted axis"))?;
    if level > 1 {
        return Err(refused("source product cap end must be low or high"));
    }
    let normal = source.cap_normal();
    let low = source
        .cap_levels()
        .get(level)
        .ok_or_else(|| invariant("selected source product cap missing"))?;
    let omitted = normal
        .get(missing)
        .and_then(interval)
        .ok_or_else(|| refused("source cap normal cannot be enclosed"))?;
    if omitted.lo <= 0. && omitted.hi >= 0. {
        return Err(refused(
            "chosen profile axes cannot prove a nonsingular planar lift",
        ));
    }
    let normals = normal.each_ref().map(interval);
    let [Some(nx), Some(ny), Some(nz)] = normals else {
        return Err(refused("source plane metric is not bounded"));
    };
    let abs = |x: Ivl| Ivl::from(x.lo.abs().max(x.hi.abs()));
    let [nx, ny, nz] = [nx, ny, nz].map(abs);
    let denominator = Ivl::from(omitted.lo.abs().min(omitted.hi.abs()));
    let lift_metric = ((nx * nx + ny * ny + nz * nz).sqrt() / denominator).hi;
    if !lift_metric.is_finite() || lift_metric < 1. {
        return Err(refused("source planar lift metric cannot be bounded"));
    }
    let actual_patch = complex
        .patches
        .get(patch)
        .ok_or_else(|| refused("actual profile patch is absent"))?;
    if graphs.len() != actual_patch.rims.len()
        || graphs.len() != source.profile_rims().len()
        || graphs.is_empty()
    {
        return Err(refused("actual/source complete rim families differ"));
    }
    // Match only authoritative original raw aliases. The high cap uses the
    // already-proved one-to-one upper/lower boundary alias map, not new rounded
    // positions synthesized by adding the translation to low vertices.
    let mut upper = std::collections::BTreeMap::new();
    if level == 1 {
        for (&alias, &low_alias) in source.upper_to_lower() {
            work.spend_core(k, 1)?;
            work.reserve_cells_core(k, 1)?;
            if upper.insert(low_alias, alias).is_some() {
                return Err(invariant(
                    "proved source product upper aliases are not one-to-one",
                ));
            }
        }
    }
    let mut positions = std::collections::BTreeMap::new();
    for rim in source.profile_rims() {
        for &alias in rim {
            work.spend_core(k, 1)?;
            let selected = if level == 0 {
                alias
            } else {
                *upper
                    .get(&alias)
                    .ok_or_else(|| invariant("proved source upper boundary alias missing"))?
            };
            let position = source
                .position_with_work(k, work, selected)?
                .ok_or_else(|| invariant("proved exact-view cap position missing"))?;
            let position = copy_point_with_work(k, work, &position)?;
            work.reserve_cells_core(k, 1)?;
            positions.insert(alias, position);
        }
    }
    let mut matched = std::collections::BTreeSet::new();
    let mut caps = Vec::new();
    let mut source_senses = Vec::new();
    let mut source_aliases = Vec::new();
    let mut actual = Vec::new();
    let mut joins = Vec::new();
    for (rim, graph) in graphs.iter().enumerate() {
        work.spend_core(k, 1)?;
        let mut owner = None;
        for (i, candidate) in source.profile_rims().iter().enumerate() {
            work.spend_core(
                k,
                candidate
                    .len()
                    .checked_mul(graph.source.len())
                    .and_then(|v| v.checked_mul(2))
                    .ok_or_else(|| refused("source rim matching work overflow"))?,
            )?;
            if let Some((sense, offset)) =
                source_loop_matches(k, work, &positions, candidate, &graph.source)?
            {
                if owner.replace((i, sense, offset)).is_some() {
                    return Err(refused("source rim assignment is ambiguous"));
                }
            }
        }
        let (owner, sense, offset) = owner
            .ok_or_else(|| refused("graph source is not a complete untouched source cap rim"))?;
        if !matched.insert(owner) {
            return Err(refused("a complete source rim is duplicated"));
        }
        let candidate = source
            .profile_rims()
            .get(owner)
            .ok_or_else(|| invariant("matched exact source rim missing"))?;
        let mut aliases = Vec::new();
        for i in 0..graph.source.len() {
            work.spend_core(k, 1)?;
            let index = if sense < 0 {
                offset
                    .checked_add(candidate.len())
                    .and_then(|n| n.checked_sub(i))
                    .and_then(|n| n.checked_rem(candidate.len()))
            } else {
                offset
                    .checked_add(i)
                    .and_then(|n| n.checked_rem(candidate.len()))
            };
            let alias = index
                .and_then(|i| candidate.get(i))
                .copied()
                .ok_or_else(|| invariant("matched exact rim alias index missing"))?;
            let selected = if level == 0 {
                alias
            } else {
                *upper
                    .get(&alias)
                    .ok_or_else(|| invariant("matched upper alias missing"))?
            };
            work.reserve_output_core(k, 1)?;
            aliases.push(selected);
        }
        // NativeCaps binds every actual Curve pointer/use/domain/real vertex and
        // its actual endpoint balls. No caller geometry/order claim substitutes.
        let cap = native(
            k,
            work,
            bind_native_caps(k, work, complex, patch, rim, graph, tolerance),
            "native cap incidence/complete graph binding unresolved",
        )?;
        let mut roots = Vec::new();
        for usage in graph.uses {
            let row = native(
                k,
                work,
                actual_used_roots(k, work, usage.curve, usage.interval, usage.forward),
                "actual curve root extraction unresolved",
            )?;
            work.reserve_cells_core(k, 1)?;
            roots.push(row);
        }
        let mut row = Vec::new();
        let mut common = Vec::new();
        for cell in &graph.cells {
            work.spend_core(k, 1)?;
            let claim = &cell.claim;
            let root = roots
                .get(claim.curve)
                .and_then(|v| v.get(claim.span))
                .ok_or_else(|| invariant("certified graph actual root missing"))?;
            let [ta, tb] = claim.target_unit;
            let restricted = root.piece.restricted_u(ta, tb)?;
            let real_join = claim.span == 0 && ta == 0.;
            let point = if real_join {
                cap.caps
                    .get(claim.curve)
                    .map(|c| c.actual_vertex)
                    .ok_or_else(|| invariant("certified real native cap is absent"))?
            } else {
                let endpoint = cell
                    .endpoints
                    .first()
                    .ok_or_else(|| invariant("complete graph endpoint missing"))?;
                endpoint.map(|v| 0.5 * v.lo + 0.5 * v.hi)
            };
            let chosen = projected(
                &x::point(point).ok_or_else(|| refused("native join nonfinite"))?,
                normal,
                low,
                source.translation(),
            )
            .ok_or_else(|| refused("common planar join cannot be constructed exactly"))?;
            if real_join {
                let cap = cap
                    .caps
                    .get(claim.curve)
                    .ok_or_else(|| invariant("real native cap is absent"))?;
                let bound = point_distance_upper(
                    point_box(&chosen)
                        .ok_or_else(|| refused("exact common join cannot be enclosed"))?,
                    cap.actual_vertex.map(Ivl::from),
                )?;
                if bound > cap.native_radius || bound > tolerance {
                    return Err(refused(
                        "exact sewn real join leaves the unchanged actual native vertex ball",
                    ));
                }
            }
            work.reserve_cells_core(k, 2)?;
            row.push(restricted);
            common.push(chosen);
        }
        if row.len() < 3 {
            return Err(refused(
                "complete profile needs at least three virtual graph cells",
            ));
        }
        work.reserve_cells_core(k, 4)?;
        source_senses.push(sense);
        work.reserve_output_core(k, 1)?;
        source_aliases.push(aliases);
        caps.push(cap);
        actual.push(row);
        joins.push(common);
    }
    if matched.len() != source.profile_rims().len() {
        return Err(refused("some original source rim is unmatched"));
    }
    work.spend_core(k, 0)?;
    Ok(NativeProfileDraft {
        source,
        complex,
        patch,
        graphs,
        _caps: caps,
        actual,
        joins,
        axes,
        lift_metric,
        tolerance,
        level,
        source_senses,
        source_aliases,
    })
}
/// Original-source wrapper: retains the SAME exact source product origin.
pub(crate) fn native_profile_draft_at_level_with_work<'a, 's, 'raw>(
    k: &Kernel,
    work: &MeshWork,
    source: &'a SourcePrism<'s, 'raw>,
    complex: &'a TargetComplex<'a>,
    patch: usize,
    graphs: &'a [ChainGraphCover<'a>],
    axes: [usize; 2],
    tolerance: f64,
    level: usize,
) -> Result<NativeProfileDraft<'a, 's, 'raw>> {
    native_reference_profile_draft_at_level_with_work(
        k,
        work,
        ProductReference::original(source),
        complex,
        patch,
        graphs,
        axes,
        tolerance,
        level,
    )
}
/// Low-cap convenience. The two-cap product workflow uses the explicit proven
/// source end through `native_profile_draft_at_level_with_work`, sharing one budget.
pub(crate) fn native_profile_draft_with_work<'a, 's, 'raw>(
    k: &Kernel,
    work: &MeshWork,
    source: &'a SourcePrism<'s, 'raw>,
    complex: &'a TargetComplex<'a>,
    patch: usize,
    graphs: &'a [ChainGraphCover<'a>],
    axes: [usize; 2],
    tolerance: f64,
) -> Result<NativeProfileDraft<'a, 's, 'raw>> {
    native_profile_draft_at_level_with_work(
        k, work, source, complex, patch, graphs, axes, tolerance, 0,
    )
}
/// Consume ALL drafted actual roots+joins, then prove ONE complete closed family
/// motion. The result cannot outlive or mutate the actual/source draft.
pub(crate) fn prove_native_profile_model_with_work<'a, 'g, 's, 'raw>(
    k: &Kernel,
    work: &MeshWork,
    draft: &'a NativeProfileDraft<'g, 's, 'raw>,
    controls_3d: Vec<Vec<Vec<ProjectivePoint>>>,
) -> Result<NativeProfile<'a, 'g, 's, 'raw>> {
    work.spend_core(k, 0)?;
    let [u, v] = draft.axes;
    let low = draft
        .source
        .cap_levels()
        .get(draft.level)
        .ok_or_else(|| invariant("selected source product cap missing"))?;
    let actual_patch = draft
        .complex
        .patches
        .get(draft.patch)
        .ok_or_else(|| invariant("draft actual patch missing"))?;
    let mut model = Vec::new();
    if controls_3d.len() != draft.graphs.len() {
        return Err(refused("chosen common model rim family is incomplete"));
    }
    let mut actual_model_upper = 0.0_f64;
    for (rim, graph) in draft.graphs.iter().enumerate() {
        let actual = draft
            .actual
            .get(rim)
            .ok_or_else(|| invariant("draft actual roots missing"))?;
        let chosen = controls_3d
            .get(rim)
            .ok_or_else(|| invariant("chosen complete model rim missing"))?;
        if chosen.len() != graph.cells.len() {
            return Err(refused("chosen common model cell partition is incomplete"));
        }
        let target = actual_patch
            .rims
            .get(rim)
            .ok_or_else(|| invariant("draft actual rim missing"))?;
        let mut row = Vec::new();
        for (i, cell) in graph.cells.iter().enumerate() {
            work.spend_core(k, 1)?;
            let actual = actual
                .get(i)
                .ok_or_else(|| invariant("draft complete cell missing"))?;
            let chosen = chosen
                .get(i)
                .ok_or_else(|| invariant("chosen complete model cell missing"))?;
            for c in chosen {
                work.spend_core(k, 1)?;
                let residual = x::dot(draft.source.cap_normal(), &c.xyz)
                    .and_then(|v| x::sub(&v, &x::mul(low, &c.w)?));
                if x::sign(&c.w) != Some(1) || !residual.is_some_and(|v| x::zero(&v)) {
                    return Err(refused("chosen exact common model is not positive-weight planar on the original cap"));
                }
            }
            let enclosure = enclose_controls_with_work(k, work, chosen, actual)?
                .ok_or_else(|| refused("chosen common model coefficient enclosure unavailable"))?;
            let distance_upper = paired_curve_upper(actual, &enclosure, 0., 0.)?;
            let actual_use = target
                .get(cell.claim.curve)
                .ok_or_else(|| invariant("draft actual edge binding missing"))?;
            let radius = zone_tol3d(k, edge::tolerance(draft.complex.brep(), actual_use.edge)?);
            if !radius.is_finite() || distance_upper > radius || distance_upper > draft.tolerance {
                return Err(refused(
                    "a WHOLE projected sewn curve leaves its unchanged actual native edge tube",
                ));
            }
            actual_model_upper = actual_model_upper.max(distance_upper);
            // Provided common-model joins must independently fit the actual
            // real entity balls, not the draft's previously chosen steering join.
            let previous = i.checked_sub(1).and_then(|i| graph.cells.get(i));
            let next = i.checked_add(1).and_then(|i| graph.cells.get(i));
            let starts = previous.is_none_or(|c| c.claim.curve != cell.claim.curve);
            let ends = next.is_none_or(|c| c.claim.curve != cell.claim.curve);
            for (real, p, v) in [
                (starts, chosen.first(), actual_use.start),
                (ends, chosen.last(), actual_use.end),
            ] {
                if !real {
                    continue;
                }
                let p = p.ok_or_else(|| refused("chosen model real endpoint missing"))?;
                let actual_vertex = draft.complex.brep().vertex(v)?;
                let radius = zone_tol3d(k, actual_vertex.tolerance);
                let distance = point_distance_upper(
                    point_box(p).ok_or_else(|| {
                        refused("chosen exact model endpoint enclosure unavailable")
                    })?,
                    [
                        actual_vertex.point.x,
                        actual_vertex.point.y,
                        actual_vertex.point.z,
                    ]
                    .map(Ivl::from),
                )?;
                if !radius.is_finite()
                    || radius <= 0.
                    || distance > radius
                    || distance > draft.tolerance
                {
                    return Err(refused(
                        "chosen common model real join leaves unchanged native vertex ball",
                    ));
                }
                // Stored native vertex coordinates are part of the same data
                // correspondence, even if their permitted ball is larger than
                // the curve's endpoint enclosure. Include the proved distance
                // in the final source/model/stored bound, not just a ball check.
                actual_model_upper = actual_model_upper.max(distance);
            }

            let source_a = graph
                .source
                .get(cell.claim.source_edge)
                .ok_or_else(|| invariant("certified graph source edge missing"))?;
            let source_next = cell
                .claim
                .source_edge
                .checked_add(1)
                .ok_or_else(|| invariant("certified source edge index overflow"))?;
            let source_b = graph
                .source
                .get(source_next)
                .or_else(|| graph.source.first())
                .ok_or_else(|| invariant("certified graph next source corner missing"))?;
            let [a, b] = cell.claim.source_unit;
            let [a, b] = [
                exact_at_with_work(k, work, source_a, source_b, a)?,
                exact_at_with_work(k, work, source_a, source_b, b)?,
            ];
            let pick = |p: &x::P| -> Result<[x::E; 2]> {
                let a = p
                    .get(u)
                    .ok_or_else(|| invariant("chosen projection coordinate absent"))?;
                let b = p
                    .get(v)
                    .ok_or_else(|| invariant("chosen projection coordinate absent"))?;
                let count = a
                    .len()
                    .checked_add(b.len())
                    .ok_or_else(|| refused("projection copy count overflow"))?;
                work.spend_core(k, count)?;
                work.reserve_cells_core(k, count)?;
                Ok([a.clone(), b.clone()])
            };
            let [a, b] = [pick(&a)?, pick(&b)?];
            let mut controls = Vec::new();
            for c in chosen {
                work.spend_core(k, 1)?;
                let xy = pick(&c.xyz)?;
                work.reserve_cells_core(k, 1)?;
                controls.push(RationalControl {
                    xy,
                    weight: c.w.clone(),
                });
            }
            work.reserve_cells_core(k, 1)?;
            row.push(MotionEdge {
                source: [a, b],
                target: controls,
            });
        }
        work.reserve_cells_core(k, 1)?;
        model.push(row);
    }
    let distance = match prove_rim_motion_with_work(k, work, &model)? {
        RimMotionVerdict::Proven(p) => p.distance_upper(),
        RimMotionVerdict::Undecided(why) => return Err(refused(why)),
    };
    let source_model_upper = (Ivl::from(distance) * Ivl::from(draft.lift_metric)).hi;
    if !source_model_upper.is_finite()
        || (Ivl::from(source_model_upper) + Ivl::from(actual_model_upper)).hi > draft.tolerance
    {
        return Err(refused(
            "complete native/source rim correspondence exceeds the requested tolerance",
        ));
    }
    work.spend_core(k, 0)?;
    Ok(NativeProfile {
        draft,
        model,
        controls_3d,
        source_model_upper,
        actual_model_upper,
    })
}

/// Choose one exact planar sewn model, then use the SAME complete model checker
/// as translated upper/common-product models. No construction failure retry.
pub(crate) fn prove_native_profile_with_work<'a, 'g, 's, 'raw>(
    k: &Kernel,
    work: &MeshWork,
    draft: &'a NativeProfileDraft<'g, 's, 'raw>,
) -> Result<NativeProfile<'a, 'g, 's, 'raw>> {
    work.spend_core(k, 0)?;
    let low = draft
        .source
        .cap_levels()
        .get(draft.level)
        .ok_or_else(|| invariant("selected source product cap missing"))?;
    let mut controls = Vec::new();
    for (rim, actual) in draft.actual.iter().enumerate() {
        let joins = draft
            .joins
            .get(rim)
            .ok_or_else(|| invariant("draft common join family missing"))?;
        let mut row = Vec::new();
        for (i, actual) in actual.iter().enumerate() {
            work.spend_core(k, 1)?;
            let next = i
                .checked_add(1)
                .ok_or_else(|| invariant("draft source cell index overflow"))?;
            let a = joins
                .get(i)
                .ok_or_else(|| invariant("draft common join missing"))?;
            let b = joins
                .get(next)
                .or_else(|| joins.first())
                .ok_or_else(|| invariant("draft next common join missing"))?;
            let proof = match project_sew_curve_with_work(
                k,
                work,
                actual,
                [a, b],
                draft.source.cap_normal(),
                low,
                draft.source.translation(),
            )? {
                SewnCurveVerdict::Proven(p) => p,
                SewnCurveVerdict::Undecided(why) => return Err(refused(why)),
            };
            work.reserve_cells_core(k, proof.controls().len())?;
            let cell = proof
                .controls()
                .iter()
                .map(|c| ProjectivePoint {
                    xyz: c.xyz.clone(),
                    w: c.w.clone(),
                })
                .collect();
            work.reserve_cells_core(k, 1)?;
            row.push(cell);
        }
        work.reserve_cells_core(k, 1)?;
        controls.push(row);
    }
    prove_native_profile_model_with_work(k, work, draft, controls)
}

/// An explicit native-box counterexample, independent of primitive/drop-curve rounding.
/// Only one side-face trim changes; its actual edge, interval, incidence and zones do not.
#[cfg(test)]
pub(super) fn box_with_noniso_clamp_trim(k: &mut Kernel, work: &MeshWork) -> crate::topology::Brep {
    use super::target_complex::{target_complex_with_work, TargetCover, TargetPatchClaim};
    use crate::curve::curve::Curve;
    use crate::math::Point3;
    use crate::nurbs::b_spline_curve::BSplineCurve;
    use crate::nurbs::b_spline_surface_n_lib::p2::OrientType;
    use crate::nurbs::math::{CPoint, NOZ};
    use crate::surface::surface::SurfaceKind;
    use crate::topology::edgeuse::p1 as eu;

    let mut b =
        crate::primitive::api_primitives::create_box(k, Point3::new(0., 0., 0.), 20., 10., 5.)
            .unwrap();
    let (usage, owner, used, mut ends, axis, boundary, inward) = {
        let claims: Vec<_> = b
            .face_list()
            .iter()
            .map(|&f| TargetPatchClaim { faces: vec![f] })
            .collect();
        let complex = match target_complex_with_work(k, work, &b, &claims).unwrap() {
            TargetCover::Proven(p) => p,
            TargetCover::Undecided(why) => panic!("native-box fixture incidence: {why:?}"),
        };
        let cap = complex
            .patches
            .iter()
            .find(|p| {
                p.rims.len() == 1
                    && p.rims[0]
                        .iter()
                        .all(|u| b.vertex(u.start).unwrap().point.z == 0.)
            })
            .unwrap();
        let low = cap.rims[0][0];
        let usage = complex.edges[&low.edge]
            .iter()
            .find(|(_, u)| u.face != low.face)
            .unwrap()
            .1;
        let used = b.edge(usage.edge).unwrap().interval;
        let (trim, owner) = eu::uv_trim_curve(&b, usage.use_id).unwrap();
        let trim = trim.unwrap();
        let owner = owner.unwrap();
        assert_eq!(b.edgeuse(owner).unwrap().orientation, OrientType::Same);
        let exact = super::exact_planar::affine_ends(trim, used, true).unwrap();
        let a = trim.evaluate_point(k, used.min()).unwrap();
        let z = trim.evaluate_point(k, used.max()).unwrap();
        let ends = [[a.x, a.y, 0.], [z.x, z.y, 0.]];
        // Reading the existing endpoints must not substitute rounded samples for
        // this fixture's complete affine definition.
        assert!(x::equal_point(&exact[0], ends[0]));
        assert!(x::equal_point(&exact[1], ends[1]));
        let surface = b.face(usage.face).unwrap().surface.as_ref().unwrap();
        let SurfaceKind::Plane(plane) = surface.kind_with_nurb(k).unwrap() else {
            panic!("native-box side fixture is not a Plane");
        };
        assert!(!plane.is_out_of_bounds_enabled());
        let d = plane.step_uv_domain();
        let bounds = [(d.u_min(), d.u_max()), (d.v_min(), d.v_max())];
        let axis = if ends[0][0] == ends[1][0] {
            0
        } else {
            assert_eq!(ends[0][1], ends[1][1]);
            1
        };
        let boundary = ends[0][axis];
        let inward = if boundary == bounds[axis].0 {
            1.
        } else {
            assert_eq!(boundary, bounds[axis].1);
            -1.
        };
        // Canonical native-box planes have unit coordinate scale. Thus the
        // complete perturbed trim image stays within 2^-40 world units of the
        // original edge, without changing any native tolerance.
        let scale = plane.uv_scale();
        assert_eq!(if axis == 0 { scale.x } else { scale.y }, 1.);
        (usage, owner, used, ends, axis, boundary, inward)
    };
    let delta = 2.0_f64.powi(-40);
    ends[0][axis] = boundary - inward * delta;
    ends[1][axis] = boundary + inward * delta;
    // A genuine crossing, not the wholly-outside raw diagonal whose clamped
    // image is an exact ISO segment: the constant coordinate crosses halfway.
    let net = crate::nurbs::crv_basic::Curve::new(
        ends.iter()
            .map(|p| CPoint::new(p[0], p[1], NOZ, 1.))
            .collect(),
        1,
        vec![used.min(), used.min(), used.max(), used.max()],
    )
    .unwrap();
    eu::set_member_uv_trim_curve(
        &mut b,
        owner,
        Curve::from(BSplineCurve::from_nurb(net, 2, true)),
        None,
    )
    .unwrap();
    let (trim, stored_owner) = eu::uv_trim_curve(&b, usage.use_id).unwrap();
    assert_eq!(stored_owner, Some(owner));
    let exact = super::exact_planar::affine_ends(trim.unwrap(), used, true).unwrap();
    assert!(x::equal_point(&exact[0], ends[0]));
    assert!(x::equal_point(&exact[1], ends[1]));
    let surface = b.face(usage.face).unwrap().surface.as_ref().unwrap();
    let SurfaceKind::Plane(plane) = surface.kind_with_nurb(k).unwrap() else {
        unreachable!();
    };
    assert!(super::exact_planar::plane_trim_segment(plane, &exact).is_none());
    b
}

#[cfg(test)]
mod tests {
    use super::super::source_prism::prove_source_prism_with_work;
    use super::super::source_topology::{validate_source_weld_with_work, SourceTopology};
    use super::super::source_view::{exact_points_with_work, ExactSourceView};
    use super::super::target_complex::{target_complex_with_work, TargetCover, TargetPatchClaim};
    use super::*;
    use crate::kernel::KernelOptions;
    use crate::math::Point3;
    use crate::mesh_reconstruction::prepare::prepare_conversion_with_work;
    use crate::mesh_reconstruction::profile_chain::{chain_graph_cover, CurveUse, GraphClaim};
    use crate::mesh_reconstruction::types::MeshInput;
    use std::collections::BTreeSet;
    #[test]
    fn complete_actual_native_box_rim_model_is_bound_to_exact_original_source_product() {
        exercise_complete_box_product(false);
    }
    #[test]
    fn complete_actual_box_consumes_same_exact_endpoint_view_and_adds_motion_once() {
        exercise_complete_box_product(true);
    }
    fn exercise_complete_box_product(use_proven_motion: bool) {
        let mut k = Kernel::new(&KernelOptions::default());
        let work = MeshWork::new();
        let input = MeshInput {
            positions: vec![
                [0., 0., 0.],
                [20., 0., 0.],
                [20., 10., 0.],
                [0., 10., 0.],
                [0., 0., 5.],
                [20., 0., 5.],
                [20., 10., 5.],
                [0., 10., 5.],
            ],
            triangles: vec![
                [0, 2, 1],
                [0, 3, 2],
                [4, 5, 6],
                [4, 6, 7],
                [0, 1, 5],
                [0, 5, 4],
                [1, 2, 6],
                [1, 6, 5],
                [2, 3, 7],
                [2, 7, 6],
                [3, 0, 4],
                [3, 4, 7],
            ],
        };
        let prepared = prepare_conversion_with_work(&k, &work, &input, 0.05, &[]).unwrap();
        let source = match validate_source_weld_with_work(
            &k,
            &work,
            &input.positions,
            &input.triangles,
            &prepared.weld,
        )
        .unwrap()
        {
            SourceTopology::Proven(p) => p,
            SourceTopology::Undecided(e) => panic!("{e:?}"),
        };
        let normal = x::point([0., 0., 1.]).unwrap();
        let delta = if use_proven_motion {
            2.0_f64.powi(-60)
        } else {
            0.
        };
        let mut endpoints = Vec::new();
        for id in 0..source.alias_count() {
            let mut p = x::point(source.position(u32::try_from(id).unwrap()).unwrap()).unwrap();
            p[0] = x::add(&p[0], &x::scalar(delta).unwrap()).unwrap();
            endpoints.push(p);
        }
        let motion = if use_proven_motion {
            match super::super::source_motion::prove_source_motion_with_work(
                &k, &work, &source, &endpoints, 0.05,
            )
            .unwrap()
            {
                super::super::source_motion::SourceMotionVerdict::Proven(p) => Some(p),
                super::super::source_motion::SourceMotionVerdict::Undecided(why) => panic!("{why}"),
            }
        } else {
            None
        };
        let view = match &motion {
            Some(m) => ExactSourceView::motion(m),
            None => ExactSourceView::original(&source),
        };
        let prior = view.prior_motion_upper();
        let exact_ring = |kernel: &Kernel, points: &[[f64; 3]]| {
            let mut ring = exact_points_with_work(kernel, &work, points).unwrap();
            for p in &mut ring {
                p[0] = x::add(&p[0], &x::scalar(delta).unwrap()).unwrap();
            }
            ring
        };
        let source = prove_source_prism_with_work(&k, &work, view, &normal)
            .unwrap()
            .unwrap();
        let mut b = box_with_noniso_clamp_trim(&mut k, &work);
        let sound = crate::topology::brep::validation::soundness(&mut k, &mut b).unwrap();
        assert!(sound.sound());
        let claims: Vec<_> = b
            .face_list()
            .iter()
            .map(|&f| TargetPatchClaim { faces: vec![f] })
            .collect();
        let complex = match target_complex_with_work(&k, &work, &b, &claims).unwrap() {
            TargetCover::Proven(p) => p,
            TargetCover::Undecided(e) => panic!("{e:?}"),
        };
        let patch = complex
            .patches
            .iter()
            .position(|p| {
                p.rims.len() == 1
                    && p.rims[0]
                        .iter()
                        .all(|u| b.vertex(u.start).unwrap().point.z == 0.)
            })
            .unwrap();
        let rim = &complex.patches[patch].rims[0];
        let uses: Vec<_> = rim
            .iter()
            .map(|u| CurveUse {
                curve: b.edge(u.edge).unwrap().curve.as_ref().unwrap(),
                interval: b.edge(u.edge).unwrap().interval,
                forward: u.forward,
            })
            .collect();
        let points: Vec<_> = rim
            .iter()
            .map(|u| {
                let p = b.vertex(u.start).unwrap().point;
                [p.x, p.y, p.z]
            })
            .collect();
        let graph_claims: Vec<_> = (0..rim.len())
            .map(|i| GraphClaim {
                curve: i,
                span: 0,
                target_unit: [0., 1.],
                source_edge: i,
                source_unit: [0., 1.],
            })
            .collect();
        let graphs = vec![chain_graph_cover(
            &k,
            &work,
            &uses,
            exact_ring(&k, &points),
            &graph_claims,
            0.05,
        )
        .unwrap()];
        if use_proven_motion {
            let rounded = vec![chain_graph_cover(
                &k,
                &work,
                &uses,
                exact_points_with_work(&k, &work, &points).unwrap(),
                &graph_claims,
                0.05,
            )
            .unwrap()];
            assert!(
                native_profile_draft_with_work(
                    &k,
                    &work,
                    &source,
                    &complex,
                    patch,
                    &rounded,
                    [0, 1],
                    0.05
                )
                .is_err(),
                "rounded f64 source ring loses the nonzero exact motion"
            );
            let exact = graphs[0]
                .source
                .iter()
                .find(|p| crate::geom::expansion::to_f64(&p[0]) == 20.)
                .unwrap();
            assert!(!x::sub(&exact[0], &x::scalar(20.).unwrap()).is_some_and(|d| x::zero(&d)));
        }
        let draft = native_profile_draft_with_work(
            &k,
            &work,
            &source,
            &complex,
            patch,
            &graphs,
            [0, 1],
            0.05,
        )
        .unwrap();
        let proof = prove_native_profile_with_work(&k, &work, &draft).unwrap();
        assert!(core::ptr::eq(proof.draft(), &raw const draft));
        assert_eq!(proof.model().len(), 1);
        assert!(proof.source_model_upper().is_finite() && proof.source_model_upper() < 1e-9);
        assert!(proof.actual_model_upper().is_finite() && proof.actual_model_upper() < 1e-9);
        let clone_controls = || {
            proof
                .controls_3d()
                .iter()
                .map(|row| {
                    row.iter()
                        .map(|cell| {
                            cell.iter()
                                .map(|p| ProjectivePoint {
                                    xyz: p.xyz.clone(),
                                    w: p.w.clone(),
                                })
                                .collect()
                        })
                        .collect()
                })
                .collect()
        };
        let provided =
            prove_native_profile_model_with_work(&k, &work, &draft, clone_controls()).unwrap();
        assert!(provided.source_model_upper() < 1e-9 && provided.actual_model_upper() < 1e-9);
        let mut bad_controls: Vec<Vec<Vec<ProjectivePoint>>> = clone_controls();
        let control = &mut bad_controls[0][0][0];
        control.xyz[0] = x::add(&control.xyz[0], &x::scale(&control.w, 0.01).unwrap()).unwrap();
        assert!(prove_native_profile_model_with_work(&k, &work, &draft, bad_controls).is_err());
        let cap = super::super::product_cap::prove_product_cap_with_work(&k, &work, &proof, 0.05)
            .unwrap();
        assert_eq!(cap.face(), complex.patches[patch].faces[0]);
        assert!(cap.source_actual_upper().is_finite() && cap.source_actual_upper() < 1e-9);
        assert!(cap.model_band_upper() < 1e-9);

        // A source changed within fit tolerance is still NOT the untouched
        // original source rim. Complete raw binding must reject that substitution.
        let mut changed = points.clone();
        changed[0][0] += 1e-6;
        let changed_graphs = vec![chain_graph_cover(
            &k,
            &work,
            &uses,
            exact_ring(&k, &changed),
            &graph_claims,
            0.05,
        )
        .unwrap()];
        assert!(native_profile_draft_with_work(
            &k,
            &work,
            &source,
            &complex,
            patch,
            &changed_graphs,
            [0, 1],
            0.05
        )
        .is_err());
        let upper_patch = complex
            .patches
            .iter()
            .position(|p| {
                p.rims.len() == 1
                    && p.rims[0]
                        .iter()
                        .all(|u| b.vertex(u.start).unwrap().point.z == 5.)
            })
            .unwrap();
        let upper_rim = &complex.patches[upper_patch].rims[0];
        let upper_uses: Vec<_> = upper_rim
            .iter()
            .map(|u| CurveUse {
                curve: b.edge(u.edge).unwrap().curve.as_ref().unwrap(),
                interval: b.edge(u.edge).unwrap().interval,
                forward: u.forward,
            })
            .collect();
        let upper_points: Vec<_> = upper_rim
            .iter()
            .map(|u| {
                let p = b.vertex(u.start).unwrap().point;
                [p.x, p.y, p.z]
            })
            .collect();
        let upper_claims: Vec<_> = (0..upper_rim.len())
            .map(|i| GraphClaim {
                curve: i,
                span: 0,
                target_unit: [0., 1.],
                source_edge: i,
                source_unit: [0., 1.],
            })
            .collect();
        let upper_graphs = vec![chain_graph_cover(
            &k,
            &work,
            &upper_uses,
            exact_ring(&k, &upper_points),
            &upper_claims,
            0.05,
        )
        .unwrap()];
        let upper = native_profile_draft_at_level_with_work(
            &k,
            &work,
            &source,
            &complex,
            upper_patch,
            &upper_graphs,
            [0, 1],
            0.05,
            1,
        )
        .unwrap();
        let upper_proof = prove_native_profile_with_work(&k, &work, &upper).unwrap();
        assert_eq!(upper_proof.draft().level(), 1);
        assert!(upper_proof.source_model_upper() < 1e-9 && upper_proof.actual_model_upper() < 1e-9);
        let upper_cap =
            super::super::product_cap::prove_product_cap_with_work(&k, &work, &upper_proof, 0.05)
                .unwrap();
        assert!(
            upper_cap.source_actual_upper().is_finite() && upper_cap.source_actual_upper() < 1e-9
        );

        let product = super::super::product_profiles::prove_product_profiles_with_work(
            &k, &work, &proof, &upper,
        )
        .unwrap();
        assert!(core::ptr::eq(product.lower(), &raw const proof));
        let common_cap = super::super::product_cap::prove_product_cap_with_work(
            &k,
            &work,
            product.upper(),
            0.05,
        )
        .unwrap();
        assert!(
            common_cap.source_actual_upper().is_finite() && common_cap.source_actual_upper() < 1e-9
        );
        assert!(
            super::super::product_profiles::prove_product_profiles_with_work(
                &k, &work, &proof, &draft
            )
            .is_err()
        );
        // Steering from the ACTUAL cap/side edge incidence and full UV rectangle,
        // never a face index or a list of attempted parameter orientations.
        let mut sides = Vec::new();
        let mut strict_raw_refusals = 0;
        for (low_use, cap_use) in rim.iter().enumerate() {
            let pair = complex.edges.get(&cap_use.edge).unwrap();
            let side = pair.iter().find(|(_, u)| u.face != cap.face()).unwrap().1;
            let strict = super::super::rectangular_trim::prove_rectangular_trim_with_work(
                &k,
                &work,
                &b,
                side.face,
                side.faceuse,
            )
            .unwrap();
            if strict.is_none() {
                strict_raw_refusals += 1;
            }
            // This is explicitly a STEERING CLAIM, not an assertion that the
            // imperfect native pcurves themselves form an exact rectangle.
            let rectangle = super::super::rectangular_trim::rectangle_layout_claim_with_work(
                &k,
                &work,
                &b,
                side.face,
                side.faceuse,
            )
            .unwrap()
            .unwrap();
            let low = rectangle
                .edges
                .iter()
                .find(|e| e.edge == cap_use.edge)
                .unwrap();
            let ruling_is_u = x::sub(&low.ends[0][0], &low.ends[1][0]).is_some_and(|v| x::zero(&v));
            let (axis, maximum, profile_axis) = if ruling_is_u {
                (0, rectangle.domain[1], 1)
            } else {
                (1, rectangle.domain[3], 0)
            };
            let reverse_ruling = x::sub(&low.ends[0][axis], &x::scalar(maximum).unwrap())
                .is_some_and(|v| x::zero(&v));
            // The two actual void-boundary uses of the common edge run oppositely.
            let reverse_profile = x::sub(&low.ends[1][profile_axis], &low.ends[0][profile_axis])
                .and_then(|v| x::sign(&v))
                == Some(1);
            let cells = [super::super::product_side_band::BandCellClaim {
                root: 0,
                unit: [0., 1.],
            }];
            assert!(
                super::super::product_side_band::prove_product_side_band_with_work(
                    &k,
                    &work,
                    &product,
                    side.face,
                    side.faceuse,
                    ruling_is_u,
                    reverse_ruling,
                    0,
                    low_use,
                    !reverse_profile,
                    &cells,
                    0.05
                )
                .is_err()
            );
            sides.push(
                super::super::product_side_band::prove_product_side_band_with_work(
                    &k,
                    &work,
                    &product,
                    side.face,
                    side.faceuse,
                    ruling_is_u,
                    reverse_ruling,
                    0,
                    low_use,
                    reverse_profile,
                    &cells,
                    0.05,
                )
                .unwrap(),
            );
        }
        assert!(
            strict_raw_refusals > 0,
            "the same native-box nominal UV loop must remain unproved by the strict raw predicate"
        );
        assert!(sides
            .iter()
            .all(|side| side.model_orientation_numerator_lower().is_finite()
                && side.model_orientation_numerator_lower() > 0.));
        let whole = super::super::complete_product::complete_product_with_work(
            &k,
            &work,
            &product,
            &cap,
            &common_cap,
            &sides,
            0.05,
        )
        .unwrap();
        assert!(core::ptr::eq(whole.candidate(), &raw const b));
        assert!(whole.boundary_error_upper().is_finite() && whole.boundary_error_upper() < 1e-9);
        assert_eq!(
            whole.boundary_error_upper(),
            (Ivl::from(prior) + Ivl::from(whole.endpoint_boundary_error_upper())).hi
        );
        if use_proven_motion {
            assert!(prior > 0.);
        }

        // Exact same valid source/model/candidate and all successful subproofs do
        // not authorize adoption if ONE full actual side has not been consumed.
        assert!(super::super::complete_product::complete_product_with_work(
            &k,
            &work,
            &product,
            &cap,
            &common_cap,
            &sides[..sides.len() - 1],
            0.05
        )
        .is_err());
        // A high actual/source rim cannot be relabelled as the low original cap.
        assert!(native_profile_draft_with_work(
            &k,
            &work,
            &source,
            &complex,
            upper_patch,
            &upper_graphs,
            [0, 1],
            0.05
        )
        .is_err());
        // A native vertex may differ from both its exact source corner and its
        // stored curve endpoint while staying in its unchanged allowed ball.
        // Keep the original chosen model and actual curves: the REAL vertex gap
        // must be included in actual_model_upper, not merely tested then forgotten.
        let mut shifted = crate::topology::brep::p3::brep_copy(&mut k, &b).unwrap();
        let vertex = shifted
            .vertex_list()
            .iter()
            .copied()
            .find(|&v| shifted.vertex(v).unwrap().point.z == 0.)
            .unwrap();
        let original = shifted.vertex(vertex).unwrap().point;
        shifted.vertex_mut(vertex).unwrap().point.x += 1e-10;
        let delta = (shifted.vertex(vertex).unwrap().point.x - original.x).abs();
        assert!(delta > 0. && delta < zone_tol3d(&k, shifted.vertex(vertex).unwrap().tolerance));
        let shifted_claims: Vec<_> = shifted
            .face_list()
            .iter()
            .map(|&f| TargetPatchClaim { faces: vec![f] })
            .collect();
        let shifted_complex =
            match target_complex_with_work(&k, &work, &shifted, &shifted_claims).unwrap() {
                TargetCover::Proven(p) => p,
                TargetCover::Undecided(e) => panic!("{e:?}"),
            };
        let shifted_patch = shifted_complex
            .patches
            .iter()
            .position(|p| {
                p.rims.len() == 1
                    && p.rims[0]
                        .iter()
                        .all(|u| shifted.vertex(u.start).unwrap().point.z == 0.)
            })
            .unwrap();
        let shifted_rim = &shifted_complex.patches[shifted_patch].rims[0];
        let shifted_uses: Vec<_> = shifted_rim
            .iter()
            .map(|u| CurveUse {
                curve: shifted.edge(u.edge).unwrap().curve.as_ref().unwrap(),
                interval: shifted.edge(u.edge).unwrap().interval,
                forward: u.forward,
            })
            .collect();
        let shifted_source: Vec<_> = shifted_rim
            .iter()
            .map(|u| {
                let p = if u.start == vertex {
                    original
                } else {
                    shifted.vertex(u.start).unwrap().point
                };
                [p.x, p.y, p.z]
            })
            .collect();
        let shifted_graph_claims: Vec<_> = (0..shifted_rim.len())
            .map(|i| GraphClaim {
                curve: i,
                span: 0,
                target_unit: [0., 1.],
                source_edge: i,
                source_unit: [0., 1.],
            })
            .collect();
        let shifted_graphs = vec![chain_graph_cover(
            &k,
            &work,
            &shifted_uses,
            exact_ring(&k, &shifted_source),
            &shifted_graph_claims,
            0.05,
        )
        .unwrap()];
        let shifted_draft = native_profile_draft_with_work(
            &k,
            &work,
            &source,
            &shifted_complex,
            shifted_patch,
            &shifted_graphs,
            [0, 1],
            0.05,
        )
        .unwrap();
        let provided: Vec<Vec<Vec<ProjectivePoint>>> = vec![(0..shifted_source.len())
            .map(|i| {
                let a = shifted_source[i];
                let z = shifted_source[(i + 1) % shifted_source.len()];
                let old = (0..points.len())
                    .find(|&j| points[j] == a && points[(j + 1) % points.len()] == z)
                    .unwrap();
                proof.controls_3d()[0][old]
                    .iter()
                    .map(|p| ProjectivePoint {
                        xyz: p.xyz.clone(),
                        w: p.w.clone(),
                    })
                    .collect()
            })
            .collect()];
        let shifted_model =
            prove_native_profile_model_with_work(&k, &work, &shifted_draft, provided).unwrap();
        assert!(shifted_model.actual_model_upper() >= delta);
        assert!(shifted_model.actual_model_upper() < 1e-9);
        // Alter ONLY an actual native cap's UV definition, retaining all
        // original source arrays and actual3D edge curves/vertex coordinates.
        // Its0.01 UV bulge is inside the requested0.05 conversion scale, but
        // cannot acquire native tube/domain acceptance from the 3D-only rim.
        let mut bad = crate::topology::brep::p3::brep_copy(&mut k, &b).unwrap();
        // Native copy assigns its OWN ids. Recover the actual low-cap edge
        // through the copied body's verified complex; never reuse source ids.
        let setup_claims: Vec<_> = bad
            .face_list()
            .iter()
            .map(|&f| TargetPatchClaim { faces: vec![f] })
            .collect();
        let target = {
            let setup = match target_complex_with_work(&k, &work, &bad, &setup_claims).unwrap() {
                TargetCover::Proven(p) => p,
                TargetCover::Undecided(e) => panic!("{e:?}"),
            };
            let patch = setup
                .patches
                .iter()
                .find(|p| {
                    p.rims.len() == 1
                        && p.rims[0]
                            .iter()
                            .all(|u| bad.vertex(u.start).unwrap().point.z == 0.)
                })
                .unwrap();
            patch.rims[0][0]
        };
        let used = edge::interval(&bad, target.edge).unwrap();
        let (trim, _) = crate::topology::edgeuse::p1::uv_trim_curve(&bad, target.use_id).unwrap();
        let trim = trim.unwrap();
        let a = trim.evaluate_point(&k, used.min()).unwrap();
        let z = trim.evaluate_point(&k, used.max()).unwrap();
        let (mut mx, mut my) = ((a.x + z.x) * 0.5, (a.y + z.y) * 0.5);
        if (z.x - a.x).abs() >= (z.y - a.y).abs() {
            my += 0.01;
        } else {
            mx += 0.01;
        }
        let net = crate::nurbs::crv_basic::Curve::new(
            vec![
                crate::nurbs::math::CPoint::new(a.x, a.y, crate::nurbs::math::NOZ, 1.),
                crate::nurbs::math::CPoint::new(mx, my, crate::nurbs::math::NOZ, 1.),
                crate::nurbs::math::CPoint::new(z.x, z.y, crate::nurbs::math::NOZ, 1.),
            ],
            2,
            vec![
                used.min(),
                used.min(),
                used.min(),
                used.max(),
                used.max(),
                used.max(),
            ],
        )
        .unwrap();
        bad.edgeuse_mut(target.use_id).unwrap().uv_trim_curve =
            Some(crate::curve::curve::Curve::from(
                crate::nurbs::b_spline_curve::BSplineCurve::from_nurb(net, 2, true),
            ));
        let bad_claims: Vec<_> = bad
            .face_list()
            .iter()
            .map(|&f| TargetPatchClaim { faces: vec![f] })
            .collect();
        let bad_complex = match target_complex_with_work(&k, &work, &bad, &bad_claims).unwrap() {
            TargetCover::Proven(p) => p,
            TargetCover::Undecided(e) => panic!("{e:?}"),
        };
        let bad_patch = bad_complex
            .patches
            .iter()
            .position(|p| p.faces.contains(&target.face))
            .unwrap();
        let bad_rim = &bad_complex.patches[bad_patch].rims[0];
        let bad_uses: Vec<_> = bad_rim
            .iter()
            .map(|u| CurveUse {
                curve: bad.edge(u.edge).unwrap().curve.as_ref().unwrap(),
                interval: bad.edge(u.edge).unwrap().interval,
                forward: u.forward,
            })
            .collect();
        let bad_points: Vec<_> = bad_rim
            .iter()
            .map(|u| {
                let p = bad.vertex(u.start).unwrap().point;
                [p.x, p.y, p.z]
            })
            .collect();
        let bad_graph_claims: Vec<_> = (0..bad_rim.len())
            .map(|i| GraphClaim {
                curve: i,
                span: 0,
                target_unit: [0., 1.],
                source_edge: i,
                source_unit: [0., 1.],
            })
            .collect();
        let bad_graphs = vec![chain_graph_cover(
            &k,
            &work,
            &bad_uses,
            exact_ring(&k, &bad_points),
            &bad_graph_claims,
            0.05,
        )
        .unwrap()];
        let bad_draft = native_profile_draft_with_work(
            &k,
            &work,
            &source,
            &bad_complex,
            bad_patch,
            &bad_graphs,
            [0, 1],
            0.05,
        )
        .unwrap();
        let bad_profile = prove_native_profile_with_work(&k, &work, &bad_draft).unwrap();
        assert!(super::super::product_cap::prove_product_cap_with_work(
            &k,
            &work,
            &bad_profile,
            0.05
        )
        .is_err());
        work.check(&k).unwrap();
    }
    #[test]
    fn procedural_conic_prism_executes_complete_native_curved_cap_certificate() {
        exercise_complete_curved_product(false, false);
    }
    #[test]
    fn actual_periodic_cylinder_consumes_both_caps_seams_and_complete_common_model() {
        exercise_complete_curved_product(true, false);
    }
    #[test]
    fn phase_shifted_periodic_cylinder_consumes_interior_source_seams_and_all_native_faces() {
        exercise_complete_curved_product(true, true);
    }
    #[test]
    fn automatic_caps_preserve_subdivided_stock_and_independently_ordered_holes() {
        use crate::math::Point2;
        use crate::prism::profile::{Loop2, Region2, Seg2};
        let rectangle = |x: f64, y: f64, w: f64, h: f64| {
            let p = [
                Point2::new(x, y),
                Point2::new(x + w, y),
                Point2::new(x + w, y + h),
                Point2::new(x, y + h),
            ];
            Loop2 {
                segs: (0..4)
                    .map(|i| Seg2::Line {
                        a: p[i],
                        b: p[(i + 1) % 4],
                    })
                    .collect(),
            }
        };
        for holes in 0..=2 {
            let mut k = Kernel::new(&KernelOptions::default());
            let work = MeshWork::new();
            let frame = crate::eval::Frame {
                origin: [0., 0., 0.],
                x_axis: [1., 0., 0.],
                y_axis: [0., 1., 0.],
            };
            let region = Region2 {
                outer: rectangle(0., 0., 6., 3.),
                holes: (0..holes)
                    .map(|i| rectangle(1. + 3. * f64::from(i), 1., 1., 1.).reversed())
                    .collect(),
            };
            let mut body =
                crate::prism::extrude::extrude_region(&mut k, &frame, &region, 0., 2.).unwrap();
            if holes == 2 {
                let top = *body
                    .face_list()
                    .iter()
                    .find(|&&f| {
                        let face = body.face(f).unwrap();
                        face.loops.len() == 3
                            && face.loops.iter().all(|&lp| {
                                crate::topology::loopuse::loop_vertices(&body, lp)
                                    .unwrap()
                                    .iter()
                                    .all(|&v| body.vertex(v.unwrap()).unwrap().point.z == 2.)
                            })
                    })
                    .unwrap();
                // Change only the actual upper cap's hole enumeration. Outer
                // stays first, each owner/mate/edge use and geometry is unchanged.
                let uses: Vec<_> = body
                    .faceuses()
                    .iter()
                    .filter_map(|(id, u)| (u.face == Some(top)).then_some(id))
                    .collect();
                assert_eq!(uses.len(), 2);
                for id in uses {
                    body.faceuse_mut(id)
                        .unwrap()
                        .loopuses
                        .get_mut(1..)
                        .unwrap()
                        .reverse();
                }
                body.face_mut(top)
                    .unwrap()
                    .loops
                    .get_mut(1..)
                    .unwrap()
                    .reverse();
            }
            let mut input = MeshInput {
                positions: Vec::new(),
                triangles: Vec::new(),
            };
            for z in [0., 2.] {
                for y in 0..=3 {
                    for x in 0..=6 {
                        input.positions.push([f64::from(x), f64::from(y), z]);
                    }
                }
            }
            let occupied = |x: i32, y: i32| {
                (0..6).contains(&x)
                    && (0..3).contains(&y)
                    && !(y == 1 && ((holes >= 1 && x == 1) || (holes >= 2 && x == 4)))
            };
            let vertex = |x: i32, y: i32| u32::try_from(y * 7 + x).unwrap();
            for y in 0..3 {
                for x in 0..6 {
                    if !occupied(x, y) {
                        continue;
                    }
                    let a = vertex(x, y);
                    let b = vertex(x + 1, y);
                    let c = vertex(x + 1, y + 1);
                    let d = vertex(x, y + 1);
                    input.triangles.extend([
                        [a, c, b],
                        [a, d, c],
                        [a + 28, b + 28, c + 28],
                        [a + 28, c + 28, d + 28],
                    ]);
                    for (inside, u, v) in [
                        (occupied(x, y - 1), a, b),
                        (occupied(x + 1, y), b, c),
                        (occupied(x, y + 1), c, d),
                        (occupied(x - 1, y), d, a),
                    ] {
                        if !inside {
                            input
                                .triangles
                                .extend([[u, v, v + 28], [u, v + 28, u + 28]]);
                        }
                    }
                }
            }
            let prepared = prepare_conversion_with_work(&k, &work, &input, 0.05, &[]).unwrap();
            let source = match crate::mesh_reconstruction::certify_source_with_work(
                &k,
                &work,
                &input,
                &prepared.weld,
            )
            .unwrap()
            {
                crate::mesh_reconstruction::SourceVerdict::Proven(proof) => proof,
                crate::mesh_reconstruction::SourceVerdict::Undecided(why) => {
                    panic!("subdivided original stock refused: {why:?}")
                }
            };
            match crate::mesh_reconstruction::certify_native_prismatic_reconstruction_from_source_with_work(
                &mut k,&work,&source,&prepared,&mut body,[0.,0.,1.],None,0.05,
            ).unwrap() {
                crate::mesh_reconstruction::ReconstructionVerdict::Proven(proof)=>assert!(proof.boundary_error_upper()<0.05),
                crate::mesh_reconstruction::ReconstructionVerdict::Undecided(why)=>panic!("stock with {holes} holes refused: {why:?}"),
            }
            work.check(&k).unwrap();
        }
    }
    fn exercise_complete_curved_product(analytic_cylinder: bool, phase_shifted: bool) {
        use crate::math::Point2;
        use crate::mesh_reconstruction::profile_chain::{
            joint_cap_graph_proposals_with_work, CapProposalInput,
        };
        use crate::prism::profile::{Loop2, Region2, Seg2};
        let mut k = Kernel::new(&KernelOptions::default());
        let work = MeshWork::new();
        let frame = crate::eval::Frame {
            origin: [0., 0., 0.],
            x_axis: [1., 0., 0.],
            y_axis: [0., 1., 0.],
        };
        let w = core::f64::consts::FRAC_1_SQRT_2;
        let corners = [[1., 0.], [0., 1.], [-1., 0.], [0., -1.]];
        let apexes = [[1., 1.], [-1., 1.], [-1., -1.], [1., -1.]];
        // Four exact-construction conics share literal cardinal endpoints. This
        // is public procedural fixture geometry, not a user file or a fitted net.
        let segs = (0..4)
            .map(|i| {
                let a = corners[i];
                let b = corners[(i + 1) % 4];
                let c = apexes[i];
                Seg2::Conic {
                    a: Point2::new(a[0], a[1]),
                    apex: Point2::new(c[0], c[1]),
                    b: Point2::new(b[0], b[1]),
                    w,
                }
            })
            .collect();
        let region = Region2 {
            outer: Loop2 { segs },
            holes: Vec::new(),
        };
        let mut body = if analytic_cylinder {
            crate::primitive::api_primitives::create_cylinder(
                &mut k,
                Point3::new(0., 0., 0.),
                1.,
                5.,
            )
            .unwrap()
        } else {
            crate::prism::extrude::extrude_region(&mut k, &frame, &region, 0., 5.).unwrap()
        };
        let standing = crate::topology::brep::validation::soundness(&mut k, &mut body).unwrap();
        assert!(standing.sound());
        let claims: Vec<_> = body
            .face_list()
            .iter()
            .map(|&f| TargetPatchClaim { faces: vec![f] })
            .collect();
        let complex = match target_complex_with_work(&k, &work, &body, &claims).unwrap() {
            TargetCover::Proven(p) => p,
            TargetCover::Undecided(e) => panic!("{e:?}"),
        };
        let patch = complex
            .patches
            .iter()
            .position(|p| {
                p.rims.len() == 1
                    && p.rims[0]
                        .iter()
                        .all(|u| body.vertex(u.start).unwrap().point.z == 0.)
            })
            .unwrap();
        let rim = &complex.patches[patch].rims[0];
        let uses: Vec<_> = rim
            .iter()
            .map(|u| CurveUse {
                curve: body.edge(u.edge).unwrap().curve.as_ref().unwrap(),
                interval: body.edge(u.edge).unwrap().interval,
                forward: u.forward,
            })
            .collect();
        let mut points = Vec::new();
        for usage in &uses {
            let roots = crate::mesh_reconstruction::actual_roots::actual_roots(
                &k,
                &work,
                usage.curve,
                usage.forward,
            )
            .unwrap();
            for root in &roots {
                let [a, b] = root.native_interval;
                for j in 0..4 {
                    let ta = (f64::from(j) + if phase_shifted { 0.5 } else { 0. }) * 0.25;
                    // Sampling authors this generic STL fixture ONLY. The
                    // certificate later encloses every whole source/target cell.
                    let p = usage.curve.evaluate_point(&k, a + (b - a) * ta).unwrap();
                    points.push([p.x, p.y, p.z]);
                }
            }
        }
        assert!(points.len() >= 16);
        let mut source_loop = points.clone();
        let area: f64 = source_loop
            .iter()
            .zip(source_loop.iter().cycle().skip(1))
            .take(source_loop.len())
            .map(|(a, b)| a[0] * b[1] - a[1] * b[0])
            .sum();
        if area < 0. {
            source_loop.reverse();
        } // fixture winding, not acceptance
        let count = source_loop.len();
        let n = u32::try_from(count).unwrap();
        let mut input = MeshInput {
            positions: source_loop.clone(),
            triangles: Vec::new(),
        };
        input
            .positions
            .extend(source_loop.iter().map(|p| [p[0], p[1], 5.]));
        input.positions.extend([[0., 0., 0.], [0., 0., 5.]]);
        for i in 0..n {
            let next = (i + 1) % n;
            input.triangles.extend([
                [2 * n, next, i],
                [2 * n + 1, n + i, n + next],
                [i, next, n + next],
                [i, n + next, n + i],
            ]);
        }
        let prepared = prepare_conversion_with_work(&k, &work, &input, 0.05, &[]).unwrap();
        let source = match validate_source_weld_with_work(
            &k,
            &work,
            &input.positions,
            &input.triangles,
            &prepared.weld,
        )
        .unwrap()
        {
            SourceTopology::Proven(p) => p,
            SourceTopology::Undecided(e) => panic!("{e:?}"),
        };
        let normal = x::point([0., 0., 1.]).unwrap();
        let source =
            prove_source_prism_with_work(&k, &work, ExactSourceView::original(&source), &normal)
                .unwrap()
                .unwrap();
        // The complete common model must consume the other cap and every side.
        // Fixture evaluations below steer correspondence only; acceptance still
        // encloses every whole source/root cell and all unchanged native zones.
        let upper_patch = complex
            .patches
            .iter()
            .position(|p| {
                p.rims.len() == 1
                    && p.rims[0]
                        .iter()
                        .all(|u| body.vertex(u.start).unwrap().point.z == 5.)
            })
            .unwrap();
        let upper_rim = &complex.patches[upper_patch].rims[0];
        let upper_uses: Vec<_> = upper_rim
            .iter()
            .map(|u| CurveUse {
                curve: body.edge(u.edge).unwrap().curve.as_ref().unwrap(),
                interval: body.edge(u.edge).unwrap().interval,
                forward: u.forward,
            })
            .collect();
        let mut upper_points = Vec::new();
        let mut chosen = BTreeSet::new();
        for usage in &upper_uses {
            let roots =
                actual_used_roots(&k, &work, usage.curve, usage.interval, usage.forward).unwrap();
            for root in &roots {
                let [a, b] = root.native_interval;
                for j in 0..4 {
                    let ta = (f64::from(j) + if phase_shifted { 0.5 } else { 0. }) * 0.25;
                    let p = usage.curve.evaluate_point(&k, a + (b - a) * ta).unwrap();
                    // Choose an existing original alias; never introduce a newly
                    // rounded source coordinate into the proof.
                    let index = points
                        .iter()
                        .enumerate()
                        .min_by(|(_, a), (_, b)| {
                            let dist = |q: &&[f64; 3]| (q[0] - p.x).powi(2) + (q[1] - p.y).powi(2);
                            dist(a).total_cmp(&dist(b))
                        })
                        .unwrap()
                        .0;
                    assert!(chosen.insert(index));
                    let q = points[index];
                    upper_points.push([q[0], q[1], 5.]);
                }
            }
        }
        assert_eq!(chosen.len(), points.len());
        // Alias identity here comes from the original validated weld, not
        // nearest coordinates. The fixture picked only existing raw vertices.
        let aliases = |p: &[[f64; 3]]| -> Vec<u32> {
            p.iter()
                .map(|point| {
                    let mut found = prepared
                        .weld
                        .vertices
                        .iter()
                        .enumerate()
                        .filter(|(_, v)| v.position == *point);
                    let (index, _) = found.next().unwrap();
                    assert!(found.next().is_none());
                    u32::try_from(index).unwrap()
                })
                .collect()
        };
        let lower_aliases = aliases(&points);
        let upper_aliases = aliases(&upper_points);
        let [lower_claimed, upper_claimed] = joint_cap_graph_proposals_with_work(
            &k,
            &work,
            [
                CapProposalInput {
                    uses: &uses,
                    aliases: &lower_aliases,
                    points: &points,
                },
                CapProposalInput {
                    uses: &upper_uses,
                    aliases: &upper_aliases,
                    points: &upper_points,
                },
            ],
            &source.upper_to_lower,
            0.05,
        )
        .unwrap();
        let source_cursor = lower_claimed.source_cursor;
        let graph_claims = lower_claimed.cells;
        let upper_cursor = upper_claimed.source_cursor;
        let upper_claims = upper_claimed.cells;
        if phase_shifted {
            assert!(source_cursor.unit > 0. && source_cursor.unit < 1.);
            let seam = uses[0]
                .curve
                .evaluate_point(&k, uses[0].interval.min())
                .unwrap();
            assert!(points
                .iter()
                .all(|p| (Point3::new(p[0], p[1], p[2]) - seam).length() > 0.05));
        }
        let graphs = vec![
            crate::mesh_reconstruction::profile_chain::chain_graph_cover_from_cursor(
                &k,
                &work,
                &uses,
                exact_points_with_work(&k, &work, &points).unwrap(),
                &graph_claims,
                0.05,
                source_cursor,
            )
            .unwrap(),
        ];
        let draft = native_profile_draft_with_work(
            &k,
            &work,
            &source,
            &complex,
            patch,
            &graphs,
            [0, 1],
            0.05,
        )
        .unwrap();
        let model = prove_native_profile_with_work(&k, &work, &draft).unwrap();
        assert!(model.source_model_upper() > 0.001 && model.source_model_upper() < 0.05);
        let cap = super::super::product_cap::prove_product_cap_with_work(&k, &work, &model, 0.05)
            .unwrap();
        assert!(cap.source_actual_upper().is_finite() && cap.source_actual_upper() < 0.05);
        assert!(cap.model_band_upper() < 1e-7);

        let upper_graphs = vec![
            crate::mesh_reconstruction::profile_chain::chain_graph_cover_from_cursor(
                &k,
                &work,
                &upper_uses,
                exact_points_with_work(&k, &work, &upper_points).unwrap(),
                &upper_claims,
                0.05,
                upper_cursor,
            )
            .unwrap(),
        ];
        let upper = native_profile_draft_at_level_with_work(
            &k,
            &work,
            &source,
            &complex,
            upper_patch,
            &upper_graphs,
            [0, 1],
            0.05,
            1,
        )
        .unwrap();
        let product = super::super::product_profiles::prove_product_profiles_with_work(
            &k, &work, &model, &upper,
        )
        .unwrap();
        let upper_cap = super::super::product_cap::prove_product_cap_with_work(
            &k,
            &work,
            product.upper(),
            0.05,
        )
        .unwrap();
        let mut sides = Vec::new();
        for (low_use, cap_use) in rim.iter().enumerate() {
            let pair = complex.edges.get(&cap_use.edge).unwrap();
            let side = pair.iter().find(|(_, u)| u.face != cap.face()).unwrap().1;
            let rectangle = super::super::rectangular_trim::rectangle_layout_claim_with_work(
                &k,
                &work,
                &body,
                side.face,
                side.faceuse,
            )
            .unwrap()
            .unwrap();
            let low = rectangle
                .edges
                .iter()
                .find(|e| e.edge == cap_use.edge)
                .unwrap();
            let ruling_is_u = x::sub(&low.ends[0][0], &low.ends[1][0]).is_some_and(|v| x::zero(&v));
            let (axis, maximum, profile_axis) = if ruling_is_u {
                (0, rectangle.domain[1], 1)
            } else {
                (1, rectangle.domain[3], 0)
            };
            let reverse_ruling = x::sub(&low.ends[0][axis], &x::scalar(maximum).unwrap())
                .is_some_and(|v| x::zero(&v));
            let reverse_profile = x::sub(&low.ends[1][profile_axis], &low.ends[0][profile_axis])
                .and_then(|v| x::sign(&v))
                == Some(1);
            // Every side uses the SAME lower graph partition, including any
            // interior source-seam cuts. No separate uniform cut schedule.
            let cells: Vec<_> = graphs[0]
                .cells
                .iter()
                .filter(|cell| cell.claim.curve == low_use)
                .map(|cell| super::super::product_side_band::BandCellClaim {
                    root: cell.claim.span,
                    unit: cell.claim.target_unit,
                })
                .collect();
            sides.push(
                super::super::product_side_band::prove_product_side_band_with_work(
                    &k,
                    &work,
                    &product,
                    side.face,
                    side.faceuse,
                    ruling_is_u,
                    reverse_ruling,
                    0,
                    low_use,
                    reverse_profile,
                    &cells,
                    0.05,
                )
                .unwrap(),
            );
        }
        assert!(!sides.is_empty());
        if analytic_cylinder {
            assert_eq!(sides.len(), 1);
            assert_eq!(sides[0].rectangle().edges.len(), 4);
            let caps = sides[0].cap_edges();
            let generator_edges: BTreeSet<_> = sides[0]
                .rectangle()
                .edges
                .iter()
                .filter(|u| !caps.contains(&u.edge))
                .map(|u| u.edge)
                .collect();
            assert_eq!(
                generator_edges.len(),
                1,
                "periodic seam must bind both uses of the SAME generator"
            );
        }
        let whole = super::super::complete_product::complete_product_with_work(
            &k, &work, &product, &cap, &upper_cap, &sides, 0.05,
        )
        .unwrap();
        assert!(core::ptr::eq(whole.candidate(), &raw const body));
        assert!(whole.boundary_error_upper() > 0. && whole.boundary_error_upper() < 0.05);
        assert!(super::super::complete_product::complete_product_with_work(
            &k,
            &work,
            &product,
            &cap,
            &upper_cap,
            &sides[..sides.len() - 1],
            0.05
        )
        .is_err());
        // Exercise the REAL public source/final certificate entry with the
        // complete original alias data. It reuses one public source proof and
        // derives every side from the actual cap incidence; no scalar token bridge.
        let request = super::super::product_driver::PrismaticConstructionClaim {
            normal: [0., 0., 1.],
            lower: super::super::product_driver::ProductCapClaim {
                face: complex.patches[patch].faces[0],
                rims: vec![super::super::product_driver::ProductRimClaim {
                    aliases: draft.source_aliases()[0].clone(),
                    cursor: source_cursor,
                    cells: graph_claims.clone(),
                }],
            },
            upper: super::super::product_driver::ProductCapClaim {
                face: complex.patches[upper_patch].faces[0],
                rims: vec![super::super::product_driver::ProductRimClaim {
                    aliases: upper.source_aliases()[0].clone(),
                    cursor: upper_cursor,
                    cells: upper_claims.clone(),
                }],
            },
        };
        let public_work = MeshWork::new();
        let public_prepared =
            prepare_conversion_with_work(&k, &public_work, &input, 0.05, &[]).unwrap();
        let public_source = match crate::mesh_reconstruction::certify_source_with_work(
            &k,
            &public_work,
            &input,
            &public_prepared.weld,
        )
        .unwrap()
        {
            crate::mesh_reconstruction::SourceVerdict::Proven(proof) => proof,
            crate::mesh_reconstruction::SourceVerdict::Undecided(why) => panic!("{why:?}"),
        };
        match crate::mesh_reconstruction::certify_prismatic_reconstruction_from_source_with_work(
            &mut k,
            &public_work,
            &public_source,
            &public_prepared,
            &mut body,
            &request,
            0.05,
        )
        .unwrap()
        {
            crate::mesh_reconstruction::ReconstructionVerdict::Proven(proof) => {
                assert!(proof.boundary_error_upper() > 0. && proof.boundary_error_upper() < 0.05);
            }
            crate::mesh_reconstruction::ReconstructionVerdict::Undecided(why) => {
                panic!("complete public product declined: {why:?}")
            }
        }
        match crate::mesh_reconstruction::certify_native_prismatic_reconstruction_from_source_with_work(
            &mut k,&public_work,&public_source,&public_prepared,&mut body,[0.,0.,1.],
            Some([request.lower.face,request.upper.face]),0.05,
        ).unwrap() {
            crate::mesh_reconstruction::ReconstructionVerdict::Proven(proof)=>{
                assert!(proof.boundary_error_upper()>0. && proof.boundary_error_upper()<0.05);
            }
            crate::mesh_reconstruction::ReconstructionVerdict::Undecided(why)=>panic!("automatic native cap claims refused: {why:?}"),
        }
        assert!(matches!(crate::mesh_reconstruction::certify_native_prismatic_reconstruction_from_source_with_work(
            &mut k,&public_work,&public_source,&public_prepared,&mut body,[0.,0.,1.],
            Some([request.lower.face,request.lower.face]),0.05,
        ).unwrap(),crate::mesh_reconstruction::ReconstructionVerdict::Undecided(_)));
        match crate::mesh_reconstruction::certify_native_prismatic_reconstruction_from_source_with_work(
            &mut k,&public_work,&public_source,&public_prepared,&mut body,[0.,0.,1.],None,0.05,
        ).unwrap() {
            crate::mesh_reconstruction::ReconstructionVerdict::Proven(proof)=>{
                assert!(proof.boundary_error_upper()>0. && proof.boundary_error_upper()<0.05);
            }
            crate::mesh_reconstruction::ReconstructionVerdict::Undecided(why)=>panic!("automatic caps refused: {why:?}"),
        }
        let mut missing = request.clone();
        assert!(missing.lower.rims[0].cells.pop().is_some());
        assert!(matches!(
            crate::mesh_reconstruction::certify_prismatic_reconstruction_from_source_with_work(
                &mut k,
                &public_work,
                &public_source,
                &public_prepared,
                &mut body,
                &missing,
                0.05
            )
            .unwrap(),
            crate::mesh_reconstruction::ReconstructionVerdict::Undecided(_)
        ));
        let mut wrong_cap = request;
        core::mem::swap(&mut wrong_cap.lower.face, &mut wrong_cap.upper.face);
        assert!(matches!(
            crate::mesh_reconstruction::certify_prismatic_reconstruction_from_source_with_work(
                &mut k,
                &public_work,
                &public_source,
                &public_prepared,
                &mut body,
                &wrong_cap,
                0.05
            )
            .unwrap(),
            crate::mesh_reconstruction::ReconstructionVerdict::Undecided(_)
        ));
        public_work.check(&k).unwrap();
        work.check(&k).unwrap();
    }
    #[test]
    fn native_complex_keeps_disconnected_partition_and_duplicate_face_refusals() {
        use super::super::target_complex::TargetRefusal;
        let mut k = Kernel::new(&KernelOptions::default());
        let mut body = crate::primitive::api_primitives::create_box(
            &mut k,
            Point3::new(0., 0., 0.),
            5.,
            3.,
            2.,
        )
        .unwrap();
        assert!(
            crate::topology::brep::validation::soundness(&mut k, &mut body)
                .unwrap()
                .sound()
        );
        let faces = body.face_list().to_vec();
        let singletons: Vec<_> = faces
            .iter()
            .map(|&f| TargetPatchClaim { faces: vec![f] })
            .collect();
        let work = MeshWork::new();
        let native = match target_complex_with_work(&k, &work, &body, &singletons).unwrap() {
            TargetCover::Proven(p) => p,
            TargetCover::Undecided(why) => panic!("singleton native faces declined: {why:?}"),
        };
        // Derive two faces with no shared actual edge, without assuming face order.
        let mut opposite = None;
        for (i, &a) in faces.iter().enumerate() {
            for &z in faces.iter().skip(i + 1) {
                if native.edges.values().all(|[(_, x), (_, y)]| {
                    !((x.face == a && y.face == z) || (x.face == z && y.face == a))
                }) {
                    opposite = Some((a, z));
                    break;
                }
            }
            if opposite.is_some() {
                break;
            }
        }
        let (a, z) = opposite.expect("a box has opposite faces");
        let mut disconnected = vec![TargetPatchClaim { faces: vec![a, z] }];
        disconnected.extend(
            faces
                .iter()
                .filter(|&&f| f != a && f != z)
                .map(|&f| TargetPatchClaim { faces: vec![f] }),
        );
        assert!(matches!(
            target_complex_with_work(&k, &work, &body, &disconnected).unwrap(),
            TargetCover::Undecided(TargetRefusal::DisconnectedGroup { patch: 0 })
        ));
        let mut duplicated: Vec<_> = faces
            .iter()
            .map(|&f| TargetPatchClaim { faces: vec![f] })
            .collect();
        duplicated[0].faces.push(faces[1]);
        assert!(matches!(
            target_complex_with_work(&k, &work, &body, &duplicated).unwrap(),
            TargetCover::Undecided(TargetRefusal::InvalidFacePartition)
        ));
        let omitted: Vec<_> = faces
            .iter()
            .skip(1)
            .map(|&f| TargetPatchClaim { faces: vec![f] })
            .collect();
        assert!(matches!(
            target_complex_with_work(&k, &work, &body, &omitted).unwrap(),
            TargetCover::Undecided(TargetRefusal::InvalidFacePartition)
        ));
        assert_eq!(body.face_list(), faces);
    }
}

#[cfg(test)]
mod source_match_budget_tests {
    use super::*;
    use std::collections::BTreeMap;
    #[test]
    fn exact_source_loop_order_matches_after_long_rejected_prefix_with_same_budget() {
        let k = Kernel::default();
        let n = 128u32;
        let positions: BTreeMap<_, _> = (0..n)
            .map(|i| (i, x::point([f64::from(i), f64::from(i * i), 0.]).unwrap()))
            .collect();
        let rim: Vec<_> = (0..n).collect();
        let points: Vec<_> = (0..n).map(|i| positions[&(n - 1 - i)].clone()).collect();
        let work = MeshWork::new();
        work.reserve_cells_core(&k, 1_990_000).unwrap();
        assert_eq!(
            source_loop_matches(&k, &work, &positions, &rim, &points).unwrap(),
            Some((-1, 127))
        );
        // A nearby but foreign coordinate cannot be treated as an alias match.
        let mut changed = points;
        changed[64][0] = x::add(&changed[64][0], &x::scalar(0.5).unwrap()).unwrap();
        let work = MeshWork::new();
        work.reserve_cells_core(&k, 1_990_000).unwrap();
        assert!(source_loop_matches(&k, &work, &positions, &rim, &changed)
            .unwrap()
            .is_none());
    }
}
