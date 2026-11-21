//! Whole ordered source-edge/actual-curve parameter correspondence.
//! Graph coverage is necessary, not sufficient for an accepted closed rim.
//! Exact expansion coordinates are owned once; complete source-view/original-alias
//! binding is the consuming `NativeProfile` obligation. No f64 coordinate downgrade.
use super::actual_roots::actual_used_roots;
use super::certificate::exact_geometry as x;
use super::certificate::source_view::exact_at_with_work;
use super::certificate::{curve_graph_bound, PointBox};
use super::{MeshError, MeshWork};
use crate::blend::fillet_section::interval::Ivl;
use crate::curve::curve::Curve;
use crate::Kernel;
const OP: &str = "mesh_reconstruction::profile_chain";
type Result<T> = core::result::Result<T, MeshError>;
fn unsure(n: usize) -> MeshError {
    MeshError::Undecided { stage: OP, work: n }
}
/// Immutable actual curve, COMPLETE edge-use interval and topological orientation.
/// The native cap consumer binds all three to the same unchanged actual edge.
pub(crate) struct CurveUse<'a> {
    pub(crate) curve: &'a Curve,
    pub(crate) interval: crate::geom::extent1d::Extent1d,
    pub(crate) forward: bool,
}
/// Ordered correspondence claim; all intervals are interpreted as exact stored
/// f64 numbers. Claims are checked for complete, single coverage before proof.
#[derive(Clone, Debug)]
pub struct GraphClaim {
    /// Index of the actual ordered cap curve use.
    pub curve: usize,
    /// Index of its complete actual rational root.
    pub span: usize,
    /// Proposed increasing unit interval on that root.
    pub target_unit: [f64; 2],
    /// Index of the ORIGINAL source alias-ring edge.
    pub source_edge: usize,
    /// Proposed increasing unit interval on that original source edge.
    pub source_unit: [f64; 2],
}
/// One exact stored location on an ORIGINAL source edge. It is a subdivision
/// coordinate, not a fabricated source vertex or a new weld alias.
#[derive(Clone, Copy, Debug)]
pub struct SourceCursor {
    /// Index of the ORIGINAL source alias-ring edge.
    pub edge: usize,
    /// Exact stored unit parameter, in [0,1).
    pub unit: f64,
}

/// A proposed cap/root/cursor event on ONE original source rim. This is data,
/// never a proof. Ring identity prevents merging addresses from different holes.
pub(crate) struct SourceCutHint {
    pub(crate) ring: usize,
    pub(crate) at: SourceCursor,
}
/// Candidate-only shared source partition. Every original vertex is retained;
/// every hint keeps its own index even when several events share one cut. Later
/// joint target scheduling must reject collapsed distinct ordered root events.
pub(crate) struct SourceCutSchedule {
    ring: usize,
    cuts: Vec<SourceCursor>,
    hint_to_cut: Vec<usize>,
}
impl SourceCutSchedule {
    pub(crate) fn ring(&self) -> usize {
        self.ring
    }
    pub(crate) fn cuts(&self) -> &[SourceCursor] {
        &self.cuts
    }
    pub(crate) fn hint_cut(&self, hint: usize) -> Option<usize> {
        self.hint_to_cut.get(hint).copied()
    }
}
fn canonical_source_cut(source_edges: usize, at: SourceCursor) -> Result<SourceCursor> {
    const GRID: f64 = 9_007_199_254_740_992.;
    if source_edges < 3
        || at.edge >= source_edges
        || !at.unit.is_finite()
        || !(0.0..=1.0).contains(&at.unit)
    {
        return Err(unsure(0));
    }
    // An untrusted parameter proposal, NOT a geometric tolerance: 2^53 is the
    // exact integer-mantissa grid. Both n/2^53 and (2^53-n)/2^53 are representable.
    // Verify the exact complement using the SAME predicate as ProductProfiles.
    let unit = (at.unit * GRID).round() / GRID;
    if super::certificate::exact_source_unit_complement(unit).is_none() {
        return Err(unsure(0));
    }
    if unit == 1. {
        let next = at.edge.checked_add(1).ok_or_else(|| unsure(0))?;
        Ok(SourceCursor {
            edge: if next == source_edges { 0 } else { next },
            unit: 0.,
        })
    } else {
        Ok(SourceCursor {
            edge: at.edge,
            unit: if unit == 0. { 0. } else { unit },
        })
    }
}
/// Union both caps' root/entity/cursor events (and side-only cuts) in ONE source
/// address schedule before target parameters are proposed. No point coordinates
/// enter sorting or deduplication. This constructs only claims: complete graph,
/// model, native-zone and cross-cap proofs remain mandatory consumers.
pub(crate) fn joint_source_cuts_with_work(
    k: &Kernel,
    work: &MeshWork,
    ring: usize,
    source_edges: usize,
    hints: &[SourceCutHint],
) -> Result<SourceCutSchedule> {
    work.check(k)?;
    if source_edges < 3 {
        return Err(unsure(0));
    }
    let count = source_edges
        .checked_add(hints.len())
        .ok_or_else(|| unsure(source_edges))?;
    let cells = count.checked_mul(6).ok_or_else(|| unsure(count))?;
    work.reserve_cells(k, cells)?;
    work.reserve_output(k, count.checked_mul(3).ok_or_else(|| unsure(count))?)?;
    let bits = usize::try_from(count.ilog2())
        .map_err(|_| unsure(count))?
        .checked_add(1)
        .ok_or_else(|| unsure(count))?;
    // Bounded tuple-sort precharge; no allocation or geometric solve inside the
    // comparison. Original/hint admission occurs BEFORE any materialization.
    work.spend(
        k,
        count
            .checked_mul(bits)
            .and_then(|n| n.checked_mul(16))
            .ok_or_else(|| unsure(count))?,
    )?;
    let mut entries = Vec::new();
    entries
        .try_reserve_exact(count)
        .map_err(|_| MeshError::Refused {
            stage: "profile chain workspace",
            detail: "allocation refused".into(),
        })?;
    for edge in 0..source_edges {
        work.spend(k, 1)?;
        entries.push((SourceCursor { edge, unit: 0. }, None));
    }
    for (index, hint) in hints.iter().enumerate() {
        work.spend(k, 16)?;
        if hint.ring != ring {
            return Err(unsure(index));
        }
        entries.push((canonical_source_cut(source_edges, hint.at)?, Some(index)));
    }
    entries.sort_unstable_by(|(a, _), (b, _)| {
        a.edge.cmp(&b.edge).then_with(|| a.unit.total_cmp(&b.unit))
    });
    let mut cuts: Vec<SourceCursor> = Vec::new();
    cuts.try_reserve_exact(count)
        .map_err(|_| MeshError::Refused {
            stage: "profile chain workspace",
            detail: "allocation refused".into(),
        })?;
    let mut hint_to_cut = Vec::new();
    hint_to_cut
        .try_reserve_exact(hints.len())
        .map_err(|_| MeshError::Refused {
            stage: "profile chain workspace",
            detail: "allocation refused".into(),
        })?;
    for _ in 0..hints.len() {
        hint_to_cut.push(usize::MAX);
    }
    for (at, hint) in entries {
        work.spend(k, 1)?;
        if cuts
            .last()
            .is_none_or(|old| old.edge != at.edge || old.unit != at.unit)
        {
            cuts.push(at);
        }
        let index = cuts.len().checked_sub(1).ok_or_else(|| unsure(0))?;
        if let Some(hint) = hint {
            let slot = hint_to_cut.get_mut(hint).ok_or_else(|| unsure(hint))?;
            if *slot != usize::MAX {
                return Err(unsure(hint));
            }
            *slot = index;
        }
    }
    if hint_to_cut.contains(&usize::MAX) {
        return Err(unsure(hints.len()));
    }
    work.check(k)?;
    Ok(SourceCutSchedule {
        ring,
        cuts,
        hint_to_cut,
    })
}

#[derive(Clone, Copy)]
struct PartnerEdge {
    edge: usize,
    reversed: bool,
}
/// Candidate address correspondence only. Original alias pairs, never rounded
/// coordinates, determine the proposed opposite-cap edge and its direction.
/// NativeProfile/ProductProfiles must still bind and verify these claims.
pub(crate) struct RingPartnerMap {
    rings: [usize; 2],
    edges: Vec<PartnerEdge>,
    inverse: Vec<PartnerEdge>,
}
impl RingPartnerMap {
    pub(crate) fn rings(&self) -> [usize; 2] {
        self.rings
    }
    /// Maps a cut on `rings()[0]` to `rings()[1]`; this is the reverse direction
    /// of the supplied upper-to-lower alias table's name.
    pub(crate) fn map_cut_with_work(
        &self,
        k: &Kernel,
        work: &MeshWork,
        at: SourceCursor,
    ) -> Result<SourceCursor> {
        Self::map_with_work(&self.edges, k, work, at)
    }
    pub(crate) fn inverse_cut_with_work(
        &self,
        k: &Kernel,
        work: &MeshWork,
        at: SourceCursor,
    ) -> Result<SourceCursor> {
        Self::map_with_work(&self.inverse, k, work, at)
    }
    fn map_with_work(
        edges: &[PartnerEdge],
        k: &Kernel,
        work: &MeshWork,
        at: SourceCursor,
    ) -> Result<SourceCursor> {
        work.spend(k, 16)?;
        if !at.unit.is_finite() || !(0.0..=1.0).contains(&at.unit) {
            return Err(unsure(0));
        }
        let partner = edges.get(at.edge).ok_or_else(|| unsure(at.edge))?;
        let complement = super::certificate::exact_source_unit_complement(at.unit)
            .ok_or_else(|| unsure(at.edge))?;
        let unit = if partner.reversed {
            complement
        } else {
            at.unit
        };
        // Complement on the matched directed edge FIRST. Only then turn the
        // endpoint into its successor vertex in the target ring.
        let edge = if unit == 1. {
            let next = partner.edge.checked_add(1).ok_or_else(|| unsure(0))?;
            if next == edges.len() {
                0
            } else {
                next
            }
        } else {
            partner.edge
        };
        Ok(SourceCursor {
            edge,
            unit: if unit == 1. || unit == 0. { 0. } else { unit },
        })
    }
}
/// Builds one unique adjacency-preserving edge map from the claimed raw alias
/// partner table (normally the proven `SourcePrism` table). No geometric proof is
/// returned, and no alternative ordering is tried after a later proof refuses.
pub(crate) fn source_ring_partner_map_with_work(
    k: &Kernel,
    work: &MeshWork,
    rings: [usize; 2],
    lower: &[u32],
    upper: &[u32],
    upper_to_lower: &std::collections::BTreeMap<u32, u32>,
) -> Result<RingPartnerMap> {
    use std::collections::{BTreeMap, BTreeSet};
    work.check(k)?;
    let n = lower.len();
    if n < 3 || upper.len() != n {
        return Err(unsure(n));
    }
    work.reserve_cells(k, n.checked_mul(9).ok_or_else(|| unsure(n))?)?;
    work.reserve_output(k, n.checked_mul(6).ok_or_else(|| unsure(n))?)?;
    if upper_to_lower.len() < n {
        return Err(unsure(n));
    }
    let log = usize::try_from(n.ilog2())
        .map_err(|_| unsure(n))?
        .checked_add(1)
        .ok_or_else(|| unsure(n))?;
    let partner_log = usize::try_from(upper_to_lower.len().ilog2())
        .map_err(|_| unsure(n))?
        .checked_add(1)
        .ok_or_else(|| unsure(n))?;
    let log = log.checked_add(partner_log).ok_or_else(|| unsure(n))?;
    work.spend(
        k,
        n.checked_mul(log)
            .and_then(|v| v.checked_mul(16))
            .ok_or_else(|| unsure(n))?,
    )?;
    let mut seen = BTreeSet::new();
    let mut lookup = BTreeMap::new();
    for (index, &a) in lower.iter().enumerate() {
        work.spend(k, 1)?;
        if !seen.insert(a) {
            return Err(unsure(index));
        }
        let next = index.checked_add(1).ok_or_else(|| unsure(index))?;
        let b = *lower
            .get(if next == n { 0 } else { next })
            .ok_or_else(|| unsure(index))?;
        if a == b || lookup.insert((a, b), index).is_some() {
            return Err(unsure(index));
        }
    }
    let mut seen = BTreeSet::new();
    let mut output = Vec::new();
    output
        .try_reserve_exact(n)
        .map_err(|_| MeshError::Refused {
            stage: "profile chain workspace",
            detail: "allocation refused".into(),
        })?;
    for _ in 0..n {
        output.push(None);
    }
    let mut inverse = Vec::new();
    inverse
        .try_reserve_exact(n)
        .map_err(|_| MeshError::Refused {
            stage: "profile chain workspace",
            detail: "allocation refused".into(),
        })?;
    let mut reverse = None;
    let mut order = Vec::new();
    order.try_reserve_exact(n).map_err(|_| MeshError::Refused {
        stage: "profile chain workspace",
        detail: "allocation refused".into(),
    })?;
    for (index, &a) in upper.iter().enumerate() {
        work.spend(k, 1)?;
        if !seen.insert(a) {
            return Err(unsure(index));
        }
        let next = index.checked_add(1).ok_or_else(|| unsure(index))?;
        let b = upper
            .get(if next == n { 0 } else { next })
            .ok_or_else(|| unsure(index))?;
        let (&a, &b) = (
            upper_to_lower.get(&a).ok_or_else(|| unsure(index))?,
            upper_to_lower.get(b).ok_or_else(|| unsure(index))?,
        );
        let (target, reversed) = match (lookup.get(&(a, b)), lookup.get(&(b, a))) {
            (Some(&target), None) => (target, false),
            (None, Some(&target)) => (target, true),
            _ => return Err(unsure(index)),
        };
        if reverse.is_some_and(|old| old != reversed) {
            return Err(unsure(index));
        }
        reverse = Some(reversed);
        let slot = output.get_mut(target).ok_or_else(|| unsure(target))?;
        if slot
            .replace(PartnerEdge {
                edge: index,
                reversed,
            })
            .is_some()
        {
            return Err(unsure(index));
        }
        inverse.push(PartnerEdge {
            edge: target,
            reversed,
        });
        order.push(target);
    }
    // Explicit whole-cycle adjacency check, including its wrap edge. This is
    // exact alias indexing; nearest/world-coordinate equality cannot stand in.
    let reversed = reverse.ok_or_else(|| unsure(0))?;
    for (index, &a) in order.iter().enumerate() {
        work.spend(k, 1)?;
        let next = index.checked_add(1).ok_or_else(|| unsure(index))?;
        let b = *order
            .get(if next == n { 0 } else { next })
            .ok_or_else(|| unsure(index))?;
        let expected = if reversed {
            if a == 0 {
                n.checked_sub(1).ok_or_else(|| unsure(n))?
            } else {
                a.checked_sub(1).ok_or_else(|| unsure(a))?
            }
        } else {
            let next = a.checked_add(1).ok_or_else(|| unsure(a))?;
            if next == n {
                0
            } else {
                next
            }
        };
        if b != expected {
            return Err(unsure(index));
        }
    }
    let mut edges = Vec::new();
    edges.try_reserve_exact(n).map_err(|_| MeshError::Refused {
        stage: "profile chain workspace",
        detail: "allocation refused".into(),
    })?;
    for slot in output {
        edges.push(slot.ok_or_else(|| unsure(n))?);
    }
    work.check(k)?;
    Ok(RingPartnerMap {
        rings,
        edges,
        inverse,
    })
}

/// Candidate parameter location in the ordered actual curve/root inventory.
#[derive(Clone, Copy)]
pub(crate) struct TargetCursor {
    pub(crate) curve: usize,
    pub(crate) root: usize,
    pub(crate) unit: f64,
}
struct TargetKey {
    curve: usize,
    root: usize,
    flat: usize,
    unit: f64,
}
/// Still only claims: the real curve and original alias arrays are bound by
/// `chain_graph_cover_from_cursor` and all its native consumers afterwards.
pub(crate) struct CapGraphClaims {
    pub(crate) source_cursor: SourceCursor,
    pub(crate) cells: Vec<GraphClaim>,
}
/// Emit one complete ordered schedule, starting at the explicitly selected
/// native-zero source anchor, never at the sorted minimum. Candidate inputs must
/// include every original vertex and every target root break. Missing breaks,
/// collapsed parameters and skipped edges refuse, rather than selecting another
/// correspondence after a geometric proof fails.
pub(crate) fn cap_graph_claims_with_work(
    k: &Kernel,
    work: &MeshWork,
    source_edges: usize,
    source_cuts: &[SourceCursor],
    targets: &[TargetCursor],
    root_counts: &[usize],
    anchor: usize,
) -> Result<CapGraphClaims> {
    work.check(k)?;
    let count = source_cuts.len();
    if source_edges < 3
        || count < source_edges
        || targets.len() != count
        || anchor >= count
        || root_counts.is_empty()
    {
        return Err(unsure(count));
    }
    work.reserve_cells(k, count.checked_mul(8).ok_or_else(|| unsure(count))?)?;
    work.reserve_output(
        k,
        count
            .checked_mul(3)
            .and_then(|n| n.checked_add(root_counts.len()))
            .ok_or_else(|| unsure(count))?,
    )?;
    let bits = usize::try_from(count.ilog2())
        .map_err(|_| unsure(count))?
        .checked_add(1)
        .ok_or_else(|| unsure(count))?;
    work.spend(
        k,
        count
            .checked_mul(bits)
            .and_then(|n| n.checked_mul(16))
            .ok_or_else(|| unsure(count))?,
    )?;
    let mut offsets = Vec::new();
    offsets
        .try_reserve_exact(root_counts.len())
        .map_err(|_| MeshError::Refused {
            stage: "profile chain workspace",
            detail: "allocation refused".into(),
        })?;
    let mut total = 0usize;
    for &roots in root_counts {
        work.spend(k, 1)?;
        if roots == 0 {
            return Err(unsure(0));
        }
        offsets.push(total);
        total = total.checked_add(roots).ok_or_else(|| unsure(roots))?;
    }
    work.reserve_cells(k, total)?;
    let mut entries = Vec::new();
    entries
        .try_reserve_exact(count)
        .map_err(|_| MeshError::Refused {
            stage: "profile chain workspace",
            detail: "allocation refused".into(),
        })?;
    for (index, (&at, &target)) in source_cuts.iter().zip(targets).enumerate() {
        work.spend(k, 16)?;
        if at.edge >= source_edges
            || !at.unit.is_finite()
            || !(0.0..1.0).contains(&at.unit)
            || super::certificate::exact_source_unit_complement(at.unit).is_none()
            || !target.unit.is_finite()
            || !(0.0..=1.0).contains(&target.unit)
        {
            return Err(unsure(index));
        }
        let &roots = root_counts.get(target.curve).ok_or_else(|| unsure(index))?;
        if target.root >= roots {
            return Err(unsure(index));
        }
        let flat = offsets
            .get(target.curve)
            .and_then(|n| n.checked_add(target.root))
            .ok_or_else(|| unsure(index))?;
        let mut key = TargetKey {
            curve: target.curve,
            root: target.root,
            flat,
            unit: if target.unit == 0. { 0. } else { target.unit },
        };
        if key.unit == 1. {
            key.flat = key.flat.checked_add(1).ok_or_else(|| unsure(index))?;
            key.root = key.root.checked_add(1).ok_or_else(|| unsure(index))?;
            if key.root == roots {
                key.curve = key.curve.checked_add(1).ok_or_else(|| unsure(index))?;
                key.root = 0;
            }
            key.unit = 0.;
        }
        // The sole terminal sentinel is emitted below, never an interior cut.
        if key.flat >= total {
            return Err(unsure(index));
        }
        let at = SourceCursor {
            edge: at.edge,
            unit: if at.unit == 0. { 0. } else { at.unit },
        };
        entries.push((at, key, index));
    }
    entries.sort_unstable_by(|(a, _, _), (b, _, _)| {
        a.edge.cmp(&b.edge).then_with(|| a.unit.total_cmp(&b.unit))
    });
    if entries
        .iter()
        .zip(entries.iter().skip(1))
        .any(|((a, _, _), (b, _, _))| a.edge == b.edge && a.unit == b.unit)
        || entries.iter().filter(|(at, _, _)| at.unit == 0.).count() != source_edges
    {
        return Err(unsure(count));
    }
    let start = entries
        .iter()
        .position(|(_, _, index)| *index == anchor)
        .ok_or_else(|| unsure(anchor))?;
    entries.rotate_left(start);
    let (source_cursor, key, _) = entries.first().ok_or_else(|| unsure(0))?;
    if key.flat != 0 || key.unit != 0. {
        return Err(unsure(anchor));
    }
    let source_cursor = *source_cursor;
    let mut cells = Vec::new();
    cells
        .try_reserve_exact(count)
        .map_err(|_| MeshError::Refused {
            stage: "profile chain workspace",
            detail: "allocation refused".into(),
        })?;
    for (index, (at, key, _)) in entries.iter().enumerate() {
        work.spend(k, 16)?;
        let next = index.checked_add(1).ok_or_else(|| unsure(index))?;
        let (next_at, next_flat, next_unit) = if let Some((at, key, _)) = entries.get(next) {
            (at, key.flat, key.unit)
        } else {
            (&source_cursor, total, 0.)
        };
        let source_end = if next_at.edge == at.edge && next_at.unit > at.unit {
            next_at.unit
        } else {
            let following = at.edge.checked_add(1).ok_or_else(|| unsure(index))?;
            let following = if following == source_edges {
                0
            } else {
                following
            };
            if next_at.edge != following || next_at.unit != 0. {
                return Err(unsure(index));
            }
            1.
        };
        let target_end = if next_flat == key.flat && next_unit > key.unit {
            next_unit
        } else if key.flat.checked_add(1) == Some(next_flat) && next_unit == 0. {
            1.
        } else {
            return Err(unsure(index));
        };
        cells.push(GraphClaim {
            curve: key.curve,
            span: key.root,
            target_unit: [key.unit, target_end],
            source_edge: at.edge,
            source_unit: [at.unit, source_end],
        });
    }
    work.check(k)?;
    Ok(CapGraphClaims {
        source_cursor,
        cells,
    })
}
/// Numerical steering inventory only. No parameter, nearest point or bounding
/// box from this type is a certificate. Real graph/native/model proofs must bind
/// every proposed cell to the unchanged source aliases and actual curve uses.
/// Bernstein derivative differences and de Casteljau follow Piegl/Tiller sec6.1;
/// the rational jet uses the quotient rule on homogeneous coordinates.
type ProposalBox = ([f64; 3], [f64; 3]);
pub(crate) struct TargetProposals {
    roots: Vec<Vec<super::actual_roots::ActualRoot>>,
    boxes: Vec<Vec<ProposalBox>>,
}
fn proposal_polynomial_jet(coefficients: &[f64], unit: f64) -> Option<[f64; 3]> {
    if coefficients.is_empty() || coefficients.len() > 9 || !(0.0..=1.0).contains(&unit) {
        return None;
    }
    let casteljau = |values: &[f64]| -> Option<f64> {
        if values.is_empty() {
            return Some(0.);
        }
        let mut row = [0.; 9];
        for (slot, &value) in row.iter_mut().zip(values) {
            *slot = value;
        }
        for width in (1..values.len()).rev() {
            for index in 0..width {
                let a = *row.get(index)?;
                let b = *row.get(index.checked_add(1)?)?;
                *row.get_mut(index)? = (1. - unit) * a + unit * b;
            }
        }
        row.first().copied().filter(|v| v.is_finite())
    };
    let degree = coefficients.len().checked_sub(1)?;
    let mut first = [0.; 8];
    for (slot, pair) in first.iter_mut().zip(coefficients.windows(2)) {
        let [a, b] = pair else {
            return None;
        };
        *slot = f64::from(u32::try_from(degree).ok()?) * (b - a);
    }
    let first = first.get(..degree)?;
    let mut second = [0.; 7];
    for (slot, pair) in second.iter_mut().zip(first.windows(2)) {
        let [a, b] = pair else {
            return None;
        };
        *slot = f64::from(u32::try_from(degree.checked_sub(1)?).ok()?) * (b - a);
    }
    Some([
        casteljau(coefficients)?,
        casteljau(first)?,
        casteljau(second.get(..degree.saturating_sub(1))?)?,
    ])
}
fn proposal_curve_jet(
    root: &super::actual_roots::ActualRoot,
    unit: f64,
) -> Option<[crate::math::Vec3; 3]> {
    let [Some(x), Some(y), Some(z), Some(w)] = root
        .piece
        .h
        .each_ref()
        .map(|p| proposal_polynomial_jet(p.coefficients(), unit))
    else {
        return None;
    };
    if w[0] <= 0. || !w.into_iter().all(f64::is_finite) {
        return None;
    }
    let p = crate::math::Vec3::new(x[0], y[0], z[0]) / w[0];
    let d = (crate::math::Vec3::new(x[1], y[1], z[1]) - p * w[1]) / w[0];
    let dd = (crate::math::Vec3::new(x[2], y[2], z[2]) - p * w[2] - d * (2. * w[1])) / w[0];
    [p, d, dd]
        .iter()
        .flat_map(|v| v.to_array())
        .all(f64::is_finite)
        .then_some([p, d, dd])
}
impl TargetProposals {
    pub(crate) fn new_with_work(
        k: &Kernel,
        work: &MeshWork,
        uses: &[CurveUse<'_>],
    ) -> Result<Self> {
        work.check(k)?;
        if uses.is_empty() {
            return Err(unsure(0));
        }
        work.reserve_output(
            k,
            uses.len()
                .checked_mul(2)
                .ok_or_else(|| unsure(uses.len()))?,
        )?;
        let mut roots = Vec::new();
        roots
            .try_reserve_exact(uses.len())
            .map_err(|_| MeshError::Refused {
                stage: "profile chain workspace",
                detail: "allocation refused".into(),
            })?;
        let mut boxes = Vec::new();
        boxes
            .try_reserve_exact(uses.len())
            .map_err(|_| MeshError::Refused {
                stage: "profile chain workspace",
                detail: "allocation refused".into(),
            })?;
        for usage in uses {
            let pieces = actual_used_roots(k, work, usage.curve, usage.interval, usage.forward)?;
            work.reserve_output(k, pieces.len())?;
            let mut bounds = Vec::new();
            bounds
                .try_reserve_exact(pieces.len())
                .map_err(|_| MeshError::Refused {
                    stage: "profile chain workspace",
                    detail: "allocation refused".into(),
                })?;
            for root in &pieces {
                let count = root
                    .piece
                    .h
                    .first()
                    .ok_or_else(|| unsure(0))?
                    .coefficients()
                    .len();
                if !(2..=9).contains(&count)
                    || root
                        .piece
                        .h
                        .iter()
                        .any(|p| p.degrees() != (count - 1, 0) || p.coefficients().len() != count)
                {
                    return Err(unsure(count));
                }
                work.spend(k, count.checked_mul(64).ok_or_else(|| unsure(count))?)?;
                bounds.push(root.piece.widened_box()?);
            }
            roots.push(pieces);
            boxes.push(bounds);
        }
        work.check(k)?;
        Ok(Self { roots, boxes })
    }
    pub(crate) fn steering_jet_with_work(
        &self,
        k: &Kernel,
        work: &MeshWork,
    ) -> Result<[crate::math::Vec3; 3]> {
        self.jet_with_work(k, work, 0, 0, 0.5)
    }
    fn jet_with_work(
        &self,
        k: &Kernel,
        work: &MeshWork,
        curve: usize,
        root: usize,
        unit: f64,
    ) -> Result<[crate::math::Vec3; 3]> {
        let root = self
            .roots
            .get(curve)
            .and_then(|r| r.get(root))
            .ok_or_else(|| unsure(root))?;
        let n = root
            .piece
            .h
            .first()
            .ok_or_else(|| unsure(0))?
            .coefficients()
            .len();
        // Fixed stack arrays and a four-component jet; charge all differences,
        // three de Casteljau tables and quotient arithmetic BEFORE evaluation.
        work.spend(
            k,
            n.checked_mul(n)
                .and_then(|v| v.checked_mul(32))
                .ok_or_else(|| unsure(n))?,
        )?;
        proposal_curve_jet(root, unit).ok_or_else(|| unsure(n))
    }
    fn refine_with_work(
        &self,
        k: &Kernel,
        work: &MeshWork,
        at: TargetCursor,
        point: crate::math::Vec3,
        iterations: usize,
    ) -> Result<(TargetCursor, f64)> {
        let mut at = at;
        let [p, _, _] = self.jet_with_work(k, work, at.curve, at.root, at.unit)?;
        let mut distance = (p - point).dot(p - point);
        if !distance.is_finite() {
            return Err(unsure(0));
        }
        for _ in 0..iterations {
            let [p, d, dd] = self.jet_with_work(k, work, at.curve, at.root, at.unit)?;
            let delta = p - point;
            let slope = delta.dot(d);
            let curvature = d.dot(d) + delta.dot(dd);
            if !slope.is_finite() || !curvature.is_finite() {
                return Err(unsure(0));
            }
            if curvature <= 0. {
                break;
            }
            let step = slope / curvature;
            if !step.is_finite() {
                return Err(unsure(0));
            }
            let unit = (at.unit - step).clamp(0., 1.);
            if !unit.is_finite() {
                return Err(unsure(0));
            }
            if unit == at.unit {
                break;
            }
            let [p, _, _] = self.jet_with_work(k, work, at.curve, at.root, unit)?;
            let candidate = (p - point).dot(p - point);
            if !candidate.is_finite() {
                return Err(unsure(0));
            }
            if candidate >= distance {
                break;
            }
            at.unit = unit;
            distance = candidate;
        }
        Ok((at, distance))
    }
    fn on_root_with_work(
        &self,
        k: &Kernel,
        work: &MeshWork,
        curve: usize,
        root: usize,
        point: crate::math::Vec3,
    ) -> Result<TargetCursor> {
        work.check(k)?;
        if !point.to_array().into_iter().all(f64::is_finite) {
            return Err(unsure(root));
        }
        let mut seed: Option<(TargetCursor, f64)> = None;
        for unit in [0., 0.5, 1.] {
            let [p, _, _] = self.jet_with_work(k, work, curve, root, unit)?;
            let distance = (p - point).dot(p - point);
            if !distance.is_finite() {
                return Err(unsure(root));
            }
            if seed.is_none_or(|(_, old)| distance < old) {
                seed = Some((TargetCursor { curve, root, unit }, distance));
            }
        }
        let (seed, _) = seed.ok_or_else(|| unsure(root))?;
        Ok(self.refine_with_work(k, work, seed, point, 24)?.0)
    }
    /// One deterministic numerical proposal, not a closest-point assertion.
    /// Bounded seeds/Newton choose data once. If the later required geometric
    /// theorem refuses, no other seed, method or theorem is tried in response.
    pub(crate) fn propose_with_work(
        &self,
        k: &Kernel,
        work: &MeshWork,
        point: crate::math::Vec3,
    ) -> Result<TargetCursor> {
        const GRID: f64 = 9_007_199_254_740_992.;
        work.check(k)?;
        if !point.to_array().into_iter().all(f64::is_finite) {
            return Err(unsure(0));
        }
        let mut best: Option<(TargetCursor, f64)> = None;
        for (curve, roots) in self.roots.iter().enumerate() {
            for (root, _) in roots.iter().enumerate() {
                work.spend(k, 32)?;
                let &(low, high) = self
                    .boxes
                    .get(curve)
                    .and_then(|r| r.get(root))
                    .ok_or_else(|| unsure(root))?;
                let lower: f64 = point
                    .to_array()
                    .into_iter()
                    .zip(low.into_iter().zip(high))
                    .map(|(v, (a, b))| {
                        let gap = (a - v).max(0.).max(v - b);
                        gap * gap
                    })
                    .sum();
                // Data-only pruning: even an inaccurate numerical proposal can
                // only cause the independent complete graph proof to refuse.
                if best.is_some_and(|(_, old)| lower > old) {
                    continue;
                }
                let mut seed: Option<(TargetCursor, f64)> = None;
                for unit in [0., 0.5, 1.] {
                    let [p, _, _] = self.jet_with_work(k, work, curve, root, unit)?;
                    let distance = (p - point).dot(p - point);
                    if !distance.is_finite() {
                        return Err(unsure(root));
                    }
                    if seed.is_none_or(|(_, old)| distance < old) {
                        seed = Some((TargetCursor { curve, root, unit }, distance));
                    }
                }
                let (seed, _) = seed.ok_or_else(|| unsure(root))?;
                let candidate = self.refine_with_work(k, work, seed, point, 3)?;
                if best.is_none_or(|(_, old)| candidate.1 < old) {
                    best = Some(candidate);
                }
            }
        }
        let (best, _) = best.ok_or_else(|| unsure(0))?;
        let (mut best, _) = self.refine_with_work(k, work, best, point, 24)?;
        // Parameter-only integer grid, not an acceptance tolerance. Keeps
        // finite representable cuts; final graph/model proofs remain unchanged.
        best.unit = (best.unit * GRID).round() / GRID;
        if best.unit == 1. {
            best.root = best.root.checked_add(1).ok_or_else(|| unsure(0))?;
            let roots = self.roots.get(best.curve).ok_or_else(|| unsure(0))?;
            if best.root == roots.len() {
                best.root = 0;
                best.curve = best.curve.checked_add(1).ok_or_else(|| unsure(0))?;
            }
            if best.curve == self.roots.len() {
                best.curve = 0;
            }
            best.unit = 0.;
        }
        work.check(k)?;
        Ok(best)
    }
}

/// Original aliases/coordinates and immutable native uses, for steering only.
/// Acceptance rebinds all claims to the exact original view and SAME native body.
pub(crate) struct CapProposalInput<'a, 'curve> {
    pub(crate) uses: &'a [CurveUse<'curve>],
    pub(crate) aliases: &'a [u32],
    pub(crate) points: &'a [[f64; 3]],
}
fn proposal_point(points: &[[f64; 3]], at: SourceCursor) -> Result<crate::math::Vec3> {
    let a = points.get(at.edge).ok_or_else(|| unsure(at.edge))?;
    let next = at.edge.checked_add(1).ok_or_else(|| unsure(at.edge))?;
    let b = points
        .get(if next == points.len() { 0 } else { next })
        .ok_or_else(|| unsure(next))?;
    let [ax, ay, az] = *a;
    let [bx, by, bz] = *b;
    let [x, y, z] = [
        ax * (1. - at.unit) + bx * at.unit,
        ay * (1. - at.unit) + by * at.unit,
        az * (1. - at.unit) + bz * at.unit,
    ];
    if ![x, y, z].into_iter().all(f64::is_finite) {
        return Err(unsure(at.edge));
    }
    Ok(crate::math::Vec3::new(x, y, z))
}
/// Choose one address for a native root start. Vertex snapping uses ONLY the
/// caller's tolerance to steer data; it is never an alias identity or a proof.
fn root_source_cut(
    k: &Kernel,
    work: &MeshWork,
    points: &[[f64; 3]],
    point: crate::math::Vec3,
    tolerance: f64,
) -> Result<SourceCursor> {
    let mut vertex: Option<(usize, f64)> = None;
    let mut segment: Option<(SourceCursor, f64)> = None;
    for edge in 0..points.len() {
        work.spend(k, 128)?;
        let at = SourceCursor { edge, unit: 0. };
        let a = proposal_point(points, at)?;
        let b = proposal_point(points, SourceCursor { edge, unit: 1. })?;
        let distance = (point - a).length();
        let d = b - a;
        let square = d.dot(d);
        if !distance.is_finite() || !square.is_finite() || square <= 0. {
            return Err(unsure(edge));
        }
        if vertex.is_none_or(|(_, old)| distance < old) {
            vertex = Some((edge, distance));
        }
        let unit = (point - a).dot(d) / square;
        if !unit.is_finite() {
            return Err(unsure(edge));
        }
        let unit = unit.clamp(0., 1.);
        let gap = (a + d * unit - point).length();
        if !gap.is_finite() {
            return Err(unsure(edge));
        }
        if segment.is_none_or(|(_, old)| gap < old) {
            segment = Some((SourceCursor { edge, unit }, gap));
        }
    }
    let (edge, gap) = vertex.ok_or_else(|| unsure(0))?;
    let at = if gap <= tolerance {
        SourceCursor { edge, unit: 0. }
    } else {
        segment.ok_or_else(|| unsure(0))?.0
    };
    canonical_source_cut(points.len(), at)
}
/// Shared two-cap source schedule. Root events are proposed BEFORE any proof,
/// then fixed once. Every original vertex survives, and each cap's full root
/// cycle must appear exactly once. No alternate construction follows refusal.
pub(crate) fn joint_cap_graph_proposals_with_work(
    k: &Kernel,
    work: &MeshWork,
    input: [CapProposalInput<'_, '_>; 2],
    upper_to_lower: &std::collections::BTreeMap<u32, u32>,
    tolerance: f64,
) -> Result<[CapGraphClaims; 2]> {
    const GRID: f64 = 9_007_199_254_740_992.;
    work.check(k)?;
    let [lower, upper] = input;
    if !tolerance.is_finite()
        || tolerance <= 0.
        || lower.points.len() != lower.aliases.len()
        || upper.points.len() != upper.aliases.len()
    {
        return Err(unsure(0));
    }
    let partner = source_ring_partner_map_with_work(
        k,
        work,
        [0, 1],
        lower.aliases,
        upper.aliases,
        upper_to_lower,
    )?;
    let low = TargetProposals::new_with_work(k, work, lower.uses)?;
    let high = TargetProposals::new_with_work(k, work, upper.uses)?;
    let proposals = [&low, &high];
    let points = [lower.points, upper.points];
    let count = low
        .roots
        .iter()
        .chain(&high.roots)
        .try_fold(0usize, |n, r| n.checked_add(r.len()))
        .ok_or_else(|| unsure(0))?;
    work.reserve_cells(k, count.checked_mul(12).ok_or_else(|| unsure(count))?)?;
    work.reserve_output(k, count.checked_mul(8).ok_or_else(|| unsure(count))?)?;
    let mut hints = Vec::new();
    hints
        .try_reserve_exact(count)
        .map_err(|_| MeshError::Refused {
            stage: "profile chain workspace",
            detail: "allocation refused".into(),
        })?;
    let mut events = [Vec::new(), Vec::new()];
    let lower_event_count = low.roots.iter().map(Vec::len).sum::<usize>();
    for (cap, proposal) in proposals.iter().enumerate() {
        for (curve, roots) in proposal.roots.iter().enumerate() {
            for (root, _) in roots.iter().enumerate() {
                let [point, _, _] = proposal.jet_with_work(k, work, curve, root, 0.)?;
                let own = root_source_cut(
                    k,
                    work,
                    points.get(cap).copied().ok_or_else(|| unsure(cap))?,
                    point,
                    tolerance,
                )?;
                let mut at = if cap == 0 {
                    own
                } else {
                    partner.inverse_cut_with_work(k, work, own)?
                };
                if cap == 1 {
                    // Coalesce only across caps. Two distinct ordered roots of
                    // one cap can NEVER occupy a single source address.
                    let mut near: Option<(usize, f64)> = None;
                    for (index, hint) in hints.iter().take(lower_event_count).enumerate() {
                        work.spend(k, 64)?;
                        let hint: &SourceCutHint = hint;
                        if hint.at.edge != at.edge {
                            continue;
                        }
                        let distance = (proposal_point(lower.points, at)?
                            - proposal_point(lower.points, hint.at)?)
                        .length();
                        if !distance.is_finite() {
                            return Err(unsure(index));
                        }
                        if distance <= tolerance && near.is_none_or(|(_, old)| distance < old) {
                            near = Some((index, distance));
                        }
                    }
                    if let Some((index, _)) = near {
                        at = hints.get(index).ok_or_else(|| unsure(index))?.at;
                    }
                }
                let hint = hints.len();
                hints.push(SourceCutHint { ring: 0, at });
                events.get_mut(cap).ok_or_else(|| unsure(cap))?.push((
                    TargetCursor {
                        curve,
                        root,
                        unit: 0.,
                    },
                    hint,
                ));
            }
        }
    }
    let shared = joint_source_cuts_with_work(k, work, 0, lower.points.len(), &hints)?;
    let mut answers = Vec::new();
    work.reserve_output(k, 2)?;
    for (cap, proposal) in proposals.iter().enumerate() {
        let n = shared.cuts().len();
        work.reserve_cells(k, n.checked_mul(8).ok_or_else(|| unsure(n))?)?;
        work.reserve_output(k, n.checked_mul(5).ok_or_else(|| unsure(n))?)?;
        let mut cuts = Vec::new();
        cuts.try_reserve_exact(n).map_err(|_| MeshError::Refused {
            stage: "profile chain workspace",
            detail: "allocation refused".into(),
        })?;
        for (index, &cut) in shared.cuts().iter().enumerate() {
            cuts.push((
                if cap == 0 {
                    cut
                } else {
                    partner.map_cut_with_work(k, work, cut)?
                },
                index,
            ));
        }
        let bits = usize::try_from(n.ilog2())
            .map_err(|_| unsure(n))?
            .checked_add(1)
            .ok_or_else(|| unsure(n))?;
        work.spend(
            k,
            n.checked_mul(bits)
                .and_then(|v| v.checked_mul(16))
                .ok_or_else(|| unsure(n))?,
        )?;
        cuts.sort_unstable_by(|(a, _), (b, _)| {
            a.edge.cmp(&b.edge).then_with(|| a.unit.total_cmp(&b.unit))
        });
        let mut inverse = Vec::new();
        inverse
            .try_reserve_exact(n)
            .map_err(|_| MeshError::Refused {
                stage: "profile chain workspace",
                detail: "allocation refused".into(),
            })?;
        for _ in 0..n {
            inverse.push(usize::MAX);
        }
        for (index, (_, shared_index)) in cuts.iter().enumerate() {
            *inverse
                .get_mut(*shared_index)
                .ok_or_else(|| unsure(index))? = index;
        }
        let mut mandatory = Vec::new();
        let event = events.get(cap).ok_or_else(|| unsure(cap))?;
        work.reserve_output(k, event.len())?;
        for &(target, hint) in event {
            let shared_index = shared.hint_cut(hint).ok_or_else(|| unsure(hint))?;
            let index = *inverse
                .get(shared_index)
                .ok_or_else(|| unsure(shared_index))?;
            mandatory.push((index, target));
        }
        let &(anchor, _) = mandatory.first().ok_or_else(|| unsure(0))?;
        // Native inventory order is fixed; only one forward source traversal is
        // allowed. Missing, repeated or permuted mandatory events refuse.
        let mut previous = 0;
        for (j, &(index, _)) in mandatory.iter().enumerate() {
            let offset = if index >= anchor {
                index - anchor
            } else {
                n - (anchor - index)
            };
            if j > 0 && offset <= previous {
                return Err(unsure(index));
            }
            previous = offset;
        }
        let mut targets = Vec::new();
        targets
            .try_reserve_exact(n)
            .map_err(|_| MeshError::Refused {
                stage: "profile chain workspace",
                detail: "allocation refused".into(),
            })?;
        for _ in 0..n {
            targets.push(None);
        }
        for (j, &(start, target)) in mandatory.iter().enumerate() {
            *targets.get_mut(start).ok_or_else(|| unsure(start))? = Some(target);
            let next = j.checked_add(1).ok_or_else(|| unsure(j))?;
            let end = mandatory
                .get(next)
                .or_else(|| mandatory.first())
                .ok_or_else(|| unsure(next))?
                .0;
            let length = if end > start {
                end - start
            } else {
                n - (start - end)
            };
            let mut tick = 0.;
            for offset in 1..length {
                work.spend(k, 32)?;
                let added = start.checked_add(offset).ok_or_else(|| unsure(start))?;
                let index = if added >= n { added - n } else { added };
                let at = cuts.get(index).ok_or_else(|| unsure(index))?.0;
                let point =
                    proposal_point(points.get(cap).copied().ok_or_else(|| unsure(cap))?, at)?;
                let mut value =
                    proposal.on_root_with_work(k, work, target.curve, target.root, point)?;
                // Exact integer mantissa lattice; preserve the complete source
                // order even when numerical nearest parameters coincide.
                let remaining = u32::try_from(length - offset).map_err(|_| unsure(length))?;
                let minimum = tick + 1.;
                let maximum = GRID - f64::from(remaining);
                if minimum > maximum {
                    return Err(unsure(length));
                }
                tick = (value.unit * GRID).round().max(minimum).min(maximum);
                value.unit = tick / GRID;
                *targets.get_mut(index).ok_or_else(|| unsure(index))? = Some(value);
            }
        }
        let mut actual_cuts = Vec::new();
        actual_cuts
            .try_reserve_exact(n)
            .map_err(|_| MeshError::Refused {
                stage: "profile chain workspace",
                detail: "allocation refused".into(),
            })?;
        let mut actual_targets = Vec::new();
        actual_targets
            .try_reserve_exact(n)
            .map_err(|_| MeshError::Refused {
                stage: "profile chain workspace",
                detail: "allocation refused".into(),
            })?;
        for ((at, _), target) in cuts.into_iter().zip(targets) {
            actual_cuts.push(at);
            actual_targets.push(target.ok_or_else(|| unsure(n))?);
        }
        // This extra owned row is not one of the five n-entry arrays above.
        work.spend(k, proposal.roots.len())?;
        work.reserve_output(k, proposal.roots.len())?;
        let counts: Vec<_> = proposal.roots.iter().map(Vec::len).collect();
        answers.push(cap_graph_claims_with_work(
            k,
            work,
            points.get(cap).ok_or_else(|| unsure(cap))?.len(),
            &actual_cuts,
            &actual_targets,
            &counts,
            anchor,
        )?);
    }
    work.check(k)?;
    let mut answers = answers.into_iter();
    Ok([
        answers.next().ok_or_else(|| unsure(0))?,
        answers.next().ok_or_else(|| unsure(1))?,
    ])
}

pub(crate) struct GraphCell {
    pub(crate) claim: GraphClaim,
    pub(crate) actual_interval: [Ivl; 2],
    pub(crate) source: [PointBox; 2],
    pub(crate) endpoints: [PointBox; 2],
    pub(crate) distance_upper: f64,
}
/// Borrow-bound full coverage, with no claim that real entity joins are C0 or
/// that adjacent sectors/nonincident motion tubes preserve topology/nesting.
pub(crate) struct ChainGraphCover<'a> {
    pub(crate) uses: &'a [CurveUse<'a>],
    pub(crate) source: Vec<x::P>,
    pub(crate) cells: Vec<GraphCell>,
}
fn interval([a, b]: [f64; 2]) -> bool {
    a.is_finite() && b.is_finite() && 0. <= a && a < b && b <= 1.
}
fn enclose(p: &x::P) -> Result<PointBox> {
    let [a, b, c] = p.each_ref().map(x::interval);
    match (a, b, c) {
        (Some(a), Some(b), Some(c)) => Ok([a, b, c]),
        _ => Err(unsure(0)),
    }
}
/// Independently check complete source and target domain coverage, then certify
/// every whole rational interval. Steering claims cannot establish acceptance.
/// Adjacent cells on ONE root share an identical exact parameter, so their
/// virtual join has semantic curve identity; different native curves do not.
pub(crate) fn chain_graph_cover<'a>(
    k: &Kernel,
    work: &MeshWork,
    uses: &'a [CurveUse<'a>],
    source: Vec<x::P>,
    claims: &[GraphClaim],
    tolerance: f64,
) -> Result<ChainGraphCover<'a>> {
    chain_graph_cover_from_cursor(
        k,
        work,
        uses,
        source,
        claims,
        tolerance,
        SourceCursor { edge: 0, unit: 0. },
    )
}
/// Complete cyclic coverage starting inside one original source edge. Actual
/// native curves still start at their unchanged first root. The source cursor
/// traverses the tail, all other original edges, and the head exactly once.
/// Consumers retain the ORIGINAL alias ring and all exact source-unit cuts.
pub(crate) fn chain_graph_cover_from_cursor<'a>(
    k: &Kernel,
    work: &MeshWork,
    uses: &'a [CurveUse<'a>],
    source: Vec<x::P>,
    claims: &[GraphClaim],
    tolerance: f64,
    cursor: SourceCursor,
) -> Result<ChainGraphCover<'a>> {
    work.check(k)?;
    work.spend(k, source.len())?;
    let coefficient_count = source
        .iter()
        .flatten()
        .try_fold(0usize, |n, c| n.checked_add(c.len()))
        .ok_or_else(|| unsure(source.len()))?;
    work.spend(k, coefficient_count)?;
    if uses.is_empty()
        || source.len() < 3
        || cursor.edge >= source.len()
        || !cursor.unit.is_finite()
        || !(0.0..1.0).contains(&cursor.unit)
        || claims.is_empty()
        || !tolerance.is_finite()
        || tolerance <= 0.
        || source.iter().flatten().flatten().any(|x| !x.is_finite())
    {
        return Err(unsure(0));
    }
    work.spend(k, source.len())?;
    work.reserve_output(k, uses.len())?;
    let mut roots = Vec::new();
    for usage in uses {
        roots.push(actual_used_roots(
            k,
            work,
            usage.curve,
            usage.interval,
            usage.forward,
        )?);
    }
    let mut curve = 0usize;
    let mut span = 0usize;
    let mut target_end = 0.;
    let mut edge = cursor.edge;
    let mut source_end = cursor.unit;
    let mut completed_source_edges = 0usize;
    work.reserve_output(k, claims.len())?;
    let mut cells = Vec::new();
    for (index, claim) in claims.iter().enumerate() {
        work.spend(k, 1)?;
        if claim.curve != curve
            || claim.span != span
            || claim.source_edge != edge
            || claim.target_unit.first().copied() != Some(target_end)
            || claim.source_unit.first().copied() != Some(source_end)
            || !interval(claim.target_unit)
            || !interval(claim.source_unit)
        {
            return Err(unsure(index));
        }
        let Some(root) = roots.get(curve).and_then(|r| r.get(span)) else {
            return Err(unsure(index));
        };
        let Some(a) = source.get(edge) else {
            return Err(unsure(index));
        };
        let next = edge.checked_add(1).ok_or_else(|| unsure(index))?;
        let b = if next == source.len() {
            source.first()
        } else {
            source.get(next)
        }
        .ok_or_else(|| unsure(index))?;
        let [sa, sb] = claim.source_unit;
        let source_segment = [
            enclose(&exact_at_with_work(k, work, a, b, sa)?)?,
            enclose(&exact_at_with_work(k, work, a, b, sb)?)?,
        ];
        let [ta, tb] = claim.target_unit;
        work.reserve_cells(k, 1)?;
        let restricted = root.piece.restricted_u(ta, tb)?;
        let [u0, u1] = root.native_interval;
        let parameter = |t: f64| Ivl::from(u0) + (Ivl::from(u1) - Ivl::from(u0)) * Ivl::from(t);
        let bound = curve_graph_bound(&restricted, source_segment, 0.)?;
        if !(bound.distance_upper <= tolerance && bound.projection_numerator_lower > 0.) {
            return Err(unsure(index));
        }
        cells.push(GraphCell {
            claim: GraphClaim {
                curve,
                span,
                target_unit: claim.target_unit,
                source_edge: edge,
                source_unit: claim.source_unit,
            },
            actual_interval: [parameter(ta), parameter(tb)],
            source: source_segment,
            endpoints: bound.endpoints,
            distance_upper: bound.distance_upper,
        });
        target_end = tb;
        source_end = sb;
        if target_end == 1. {
            target_end = 0.;
            span = span.checked_add(1).ok_or_else(|| unsure(index))?;
            if roots.get(curve).is_some_and(|r| span == r.len()) {
                span = 0;
                curve = curve.checked_add(1).ok_or_else(|| unsure(index))?;
            }
        }
        if source_end == 1. {
            source_end = 0.;
            edge = edge.checked_add(1).ok_or_else(|| unsure(index))?;
            if edge == source.len() {
                edge = 0;
            }
            completed_source_edges = completed_source_edges
                .checked_add(1)
                .ok_or_else(|| unsure(index))?;
            if completed_source_edges > source.len() {
                return Err(unsure(index));
            }
        }
    }
    if curve != uses.len()
        || span != 0
        || target_end != 0.
        || completed_source_edges != source.len()
        || edge != cursor.edge
        || source_end != cursor.unit
    {
        return Err(unsure(claims.len()));
    }
    work.check(k)?;
    Ok(ChainGraphCover {
        uses,
        source,
        cells,
    })
}

#[cfg(test)]
mod tests {
    use super::super::certificate::source_view::exact_points_with_work;
    use super::*;
    use crate::nurbs::b_spline_curve::BSplineCurve;
    use crate::nurbs::crv_basic::Curve as Nurb;
    use crate::nurbs::math::CPoint;
    fn circle() -> Curve {
        let w = 0.5_f64.sqrt();
        let controls = [
            (1., 0., 1.),
            (w, w, w),
            (0., 1., 1.),
            (-w, w, w),
            (-1., 0., 1.),
            (-w, -w, w),
            (0., -1., 1.),
            (w, -w, w),
            (1., 0., 1.),
        ]
        .into_iter()
        .map(|(x, y, w)| CPoint::new(x, y, 0., w))
        .collect();
        Curve::from(BSplineCurve::from_nurb(
            Nurb::new(
                controls,
                2,
                vec![0., 0., 0., 0.25, 0.25, 0.5, 0.5, 0.75, 0.75, 1., 1., 1.],
            )
            .unwrap(),
            3,
            true,
        ))
    }
    fn claims(count: usize) -> Vec<GraphClaim> {
        let mut result = Vec::new();
        let mut edge = 0;
        let mut span = 0;
        let mut t = 0.;
        while edge < count && span < 4 {
            let edge_start = edge as f64 / count as f64;
            let edge_end = (edge + 1) as f64 / count as f64;
            let span_start = span as f64 / 4.;
            let span_end = (span + 1) as f64 / 4.;
            let next = edge_end.min(span_end);
            let a = if t == span_start {
                0.
            } else {
                (t - span_start) * 4.
            };
            let b = if next == span_end {
                1.
            } else {
                (next - span_start) * 4.
            };
            let c = if t == edge_start {
                0.
            } else {
                (t - edge_start) / (edge_end - edge_start)
            };
            let d = if next == edge_end {
                1.
            } else {
                (next - edge_start) / (edge_end - edge_start)
            };
            result.push(GraphClaim {
                curve: 0,
                span,
                target_unit: [a, b],
                source_edge: edge,
                source_unit: [c, d],
            });
            if next == edge_end {
                edge += 1;
            }
            if next == span_end {
                span += 1;
            }
            t = next;
        }
        result
    }
    #[test]
    fn joint_caps_use_independent_curve_partitions_and_refuse_duplicate_root_cycles() {
        use crate::geom::extent1d::Extent1d;
        let k = Kernel::default();
        let work = MeshWork::new();
        let curve = circle();
        // One complete lower use versus two reversed upper uses of the SAME
        // definition. Correspondence parameters are not supplied to the solver.
        let lower = [CurveUse {
            curve: &curve,
            interval: curve.natural_interval(),
            forward: true,
        }];
        let upper = [
            CurveUse {
                curve: &curve,
                interval: Extent1d::from_raw(0.5, 1.),
                forward: false,
            },
            CurveUse {
                curve: &curve,
                interval: Extent1d::from_raw(0., 0.5),
                forward: false,
            },
        ];
        let points: Vec<_> = (0..16)
            .map(|i| {
                // Independent procedural source fixture, not acceptance samples.
                let p = curve
                    .evaluate_point(&k, (f64::from(i) + 0.5) / 16.)
                    .unwrap();
                [p.x, p.y, p.z]
            })
            .collect();
        let upper_points: Vec<_> = points.iter().rev().copied().collect();
        let aliases: Vec<u32> = (0..16).collect();
        let upper_aliases: Vec<u32> = (100..116).rev().collect();
        let partners: std::collections::BTreeMap<_, _> = (0..16).map(|i| (100 + i, i)).collect();
        let input = || {
            [
                CapProposalInput {
                    uses: &lower,
                    aliases: &aliases,
                    points: &points,
                },
                CapProposalInput {
                    uses: &upper,
                    aliases: &upper_aliases,
                    points: &upper_points,
                },
            ]
        };
        let proposed =
            joint_cap_graph_proposals_with_work(&k, &work, input(), &partners, 0.05).unwrap();
        for ((claim, uses), points) in proposed
            .iter()
            .zip([lower.as_slice(), upper.as_slice()])
            .zip([points.as_slice(), upper_points.as_slice()])
        {
            assert!(claim.source_cursor.unit > 0. && claim.source_cursor.unit < 1.);
            let proof = chain_graph_cover_from_cursor(
                &k,
                &work,
                uses,
                exact_points_with_work(&k, &work, points).unwrap(),
                &claim.cells,
                0.05,
                claim.source_cursor,
            )
            .unwrap();
            assert!(proof.cells.iter().all(|cell| cell.distance_upper < 0.05));
            assert_eq!(proof.source.len(), 16);
            let membership = crate::mesh_reconstruction::actual_controls::actual_control_spans(
                &k, &work, &proof,
            )
            .unwrap();
            assert_eq!(membership.len(),4,"membership must refer to the used roots, not two repeated complete natural supports");
            for span in &membership {
                let used = proof.uses[span.curve_use].interval;
                assert!(span
                    .native_interval
                    .iter()
                    .all(|&u| used.min() <= u && u <= used.max()));
            }
        }
        assert!(proposed[1].cells.iter().any(|cell| cell.curve == 1));
        let partial = [CurveUse {
            curve: &curve,
            interval: Extent1d::from_raw(0.1, 0.5),
            forward: true,
        }];
        // A non-knot endpoint still needs its own authoritative restriction
        // proof. This change may not silently round that interval to a root.
        assert!(TargetProposals::new_with_work(&k, &work, &partial).is_err());
        // Duplicated ordered roots must refuse, never collapse into one cycle.
        let repeated = [
            CurveUse {
                curve: &curve,
                interval: curve.natural_interval(),
                forward: true,
            },
            CurveUse {
                curve: &curve,
                interval: curve.natural_interval(),
                forward: true,
            },
        ];
        assert!(joint_cap_graph_proposals_with_work(
            &k,
            &work,
            [
                CapProposalInput {
                    uses: &repeated,
                    aliases: &aliases,
                    points: &points
                },
                CapProposalInput {
                    uses: &upper,
                    aliases: &upper_aliases,
                    points: &upper_points
                },
            ],
            &partners,
            0.05
        )
        .is_err());
        assert!(joint_cap_graph_proposals_with_work(
            &k,
            &work,
            input(),
            &std::collections::BTreeMap::new(),
            0.05
        )
        .is_err());
        work.check(&k).unwrap();
        let exhausted = MeshWork::new();
        assert!(exhausted.reserve_cells(&k, usize::MAX).is_err());
        assert!(matches!(
            joint_cap_graph_proposals_with_work(&k, &exhausted, input(), &partners, f64::NAN),
            Err(MeshError::BudgetExceeded { .. })
        ));
    }
    #[test]
    fn nondyadic_source_edges_across_actual_rational_spans_have_full_graph_cover() {
        let k = Kernel::default();
        let curve = circle();
        let count = 21;
        let source = (0..count)
            .map(|i| {
                let p = curve.evaluate_point(&k, i as f64 / count as f64).unwrap();
                [p.x, p.y, p.z]
            })
            .collect::<Vec<_>>();
        let uses = [CurveUse {
            curve: &curve,
            interval: curve.natural_interval(),
            forward: true,
        }];
        let claims = claims(count);
        let proof = chain_graph_cover(
            &k,
            &MeshWork::new(),
            &uses,
            exact_points_with_work(&k, &MeshWork::new(), &source).unwrap(),
            &claims,
            0.03,
        )
        .unwrap();
        assert_eq!(proof.source.len(), count);
        assert!(proof.cells.iter().all(|cell| cell.distance_upper <= 0.03));
    }
    #[test]
    fn duplicate_or_missing_target_interval_refuses_even_when_source_vertices_fit() {
        let k = Kernel::default();
        let curve = circle();
        let count = 16;
        let source = (0..count)
            .map(|i| {
                let p = curve.evaluate_point(&k, i as f64 / count as f64).unwrap();
                [p.x, p.y, p.z]
            })
            .collect::<Vec<_>>();
        let uses = [CurveUse {
            curve: &curve,
            interval: curve.natural_interval(),
            forward: true,
        }];
        let mut claims = claims(count);
        let first = claims.first_mut().unwrap();
        first.target_unit = [0., 0.2];
        assert!(matches!(
            chain_graph_cover(
                &k,
                &MeshWork::new(),
                &uses,
                exact_points_with_work(&k, &MeshWork::new(), &source).unwrap(),
                &claims,
                0.03
            ),
            Err(MeshError::Undecided { .. })
        ));
    }
    #[test]
    fn closed_chain_uses_finite_edges_of_unbounded_canonical_lines() {
        use crate::curve::line::Line;
        use crate::geom::extent1d::Extent1d;
        use crate::math::Vec3;
        let k = Kernel::default();
        let work = MeshWork::new();
        // Each edge's real parameter is t in[2,5], not the infinite natural support.
        let curves = [
            (Vec3::new(-2., 0., 0.), Vec3::X),
            (Vec3::new(3., -2., 0.), Vec3::Y),
            (Vec3::new(5., 3., 0.), -Vec3::X),
            (Vec3::new(0., 5., 0.), -Vec3::Y),
        ]
        .map(|(p, v)| Curve::from(Line::create_canonical(p, v)));
        let used = Extent1d::from_raw(2., 5.);
        let mut uses: Vec<_> = curves
            .iter()
            .map(|curve| CurveUse {
                curve,
                interval: used,
                forward: true,
            })
            .collect();
        let source = [[0., 0., 0.], [3., 0., 0.], [3., 3., 0.], [0., 3., 0.]];
        let claims: Vec<_> = (0..4)
            .map(|i| GraphClaim {
                curve: i,
                span: 0,
                target_unit: [0., 1.],
                source_edge: i,
                source_unit: [0., 1.],
            })
            .collect();
        let graph = chain_graph_cover(
            &k,
            &work,
            &uses,
            exact_points_with_work(&k, &work, &source).unwrap(),
            &claims,
            1e-6,
        )
        .unwrap();
        assert_eq!(graph.cells.len(), 4);
        let membership =
            crate::mesh_reconstruction::actual_controls::actual_control_spans(&k, &work, &graph)
                .unwrap();
        assert_eq!(membership.len(), 4);
        assert!(membership
            .iter()
            .all(|span| span.native_interval == [2., 5.] && span.controls.len() == 2));

        assert!(graph.cells.iter().all(|c| c.distance_upper < 1e-10));
        assert!(graph
            .cells
            .iter()
            .all(|c| c.actual_interval[0].lo <= 2. && c.actual_interval[1].hi >= 5.));
        drop(graph);
        uses[0].interval = Extent1d::from_raw(2., 4.);
        assert!(
            chain_graph_cover(
                &k,
                &work,
                &uses,
                exact_points_with_work(&k, &work, &source).unwrap(),
                &claims,
                1e-6
            )
            .is_err(),
            "a shorter interval cannot cover the original full source edge"
        );
    }

    fn phase_shifted_claims() -> Vec<GraphClaim> {
        // Integer ticks encode the fixture's one complete cyclic schedule:
        // source vertices at odd ticks, rational roots at multiples of eight.
        let events: Vec<i32> = (0..=32)
            .filter(|t| *t == 0 || *t == 32 || t % 8 == 0 || t % 2 == 1)
            .collect();
        events
            .windows(2)
            .map(|v| {
                let (a, b) = (v[0], v[1]);
                let edge = ((a + 31) / 2) % 16;
                let start = if a == 0 { -1 } else { 1 + 2 * edge };
                let span = a / 8;
                GraphClaim {
                    curve: 0,
                    span: usize::try_from(span).unwrap(),
                    target_unit: [f64::from(a - span * 8) / 8., f64::from(b - span * 8) / 8.],
                    source_edge: usize::try_from(edge).unwrap(),
                    source_unit: [f64::from(a - start) / 2., f64::from(b - start) / 2.],
                }
            })
            .collect()
    }
    #[test]
    fn a_native_periodic_seam_can_correspond_to_an_interior_original_source_edge() {
        let k = Kernel::default();
        let work = MeshWork::new();
        let curve = circle();
        // These samples author the ORIGINAL procedural fixture only. Acceptance
        // below encloses every full source/target cell and retains every alias.
        let source: Vec<_> = (0..16)
            .map(|i| {
                let p = curve
                    .evaluate_point(&k, (f64::from(i) + 0.5) / 16.)
                    .unwrap();
                [p.x, p.y, p.z]
            })
            .collect();
        let unchanged = source.clone();
        let uses = [CurveUse {
            curve: &curve,
            interval: curve.natural_interval(),
            forward: true,
        }];
        let claims = phase_shifted_claims();
        // The native seam is farther than .05 from every original vertex;
        // moving the seam or inventing a source alias would change the problem.
        let seam = curve.evaluate_point(&k, 0.).unwrap();
        assert!(source
            .iter()
            .all(|p| crate::math::Vec3::new(p[0], p[1], p[2]).distance(seam) > 0.05));
        let proof = chain_graph_cover_from_cursor(
            &k,
            &work,
            &uses,
            exact_points_with_work(&k, &work, &source).unwrap(),
            &claims,
            0.05,
            SourceCursor {
                edge: 15,
                unit: 0.5,
            },
        )
        .unwrap();
        assert_eq!(proof.source.len(), 16);
        assert_eq!(proof.cells.len(), claims.len());
        assert!(proof.cells.iter().all(|cell| cell.distance_upper <= 0.05));
        assert_eq!(proof.cells.first().unwrap().claim.source_unit[0], 0.5);
        assert_eq!(proof.cells.last().unwrap().claim.source_unit[1], 0.5);
        assert_eq!(source, unchanged);
        assert!(chain_graph_cover(
            &k,
            &work,
            &uses,
            exact_points_with_work(&k, &work, &source).unwrap(),
            &claims,
            0.05
        )
        .is_err());
        work.check(&k).unwrap();
    }
    #[test]
    fn cyclic_source_coverage_cannot_hide_an_omitted_head_duplicate_or_invalid_cursor() {
        let k = Kernel::default();
        let work = MeshWork::new();
        let curve = circle();
        let source: Vec<_> = (0..16)
            .map(|i| {
                let p = curve
                    .evaluate_point(&k, (f64::from(i) + 0.5) / 16.)
                    .unwrap();
                [p.x, p.y, p.z]
            })
            .collect();
        let uses = [CurveUse {
            curve: &curve,
            interval: curve.natural_interval(),
            forward: true,
        }];
        let claims = phase_shifted_claims();
        for cursor in [
            SourceCursor { edge: 0, unit: 0. },
            SourceCursor { edge: 16, unit: 0. },
            SourceCursor { edge: 15, unit: 1. },
            SourceCursor {
                edge: 15,
                unit: -0.5,
            },
            SourceCursor {
                edge: 15,
                unit: f64::NAN,
            },
        ] {
            assert!(chain_graph_cover_from_cursor(
                &k,
                &work,
                &uses,
                exact_points_with_work(&k, &work, &source).unwrap(),
                &claims,
                0.05,
                cursor
            )
            .is_err());
        }
        assert!(chain_graph_cover_from_cursor(
            &k,
            &work,
            &uses,
            exact_points_with_work(&k, &work, &source).unwrap(),
            &claims[..claims.len() - 1],
            0.05,
            SourceCursor {
                edge: 15,
                unit: 0.5
            }
        )
        .is_err());
        let mut duplicate = phase_shifted_claims();
        duplicate.extend(phase_shifted_claims());
        assert!(chain_graph_cover_from_cursor(
            &k,
            &work,
            &uses,
            exact_points_with_work(&k, &work, &source).unwrap(),
            &duplicate,
            0.05,
            SourceCursor {
                edge: 15,
                unit: 0.5
            }
        )
        .is_err());
        work.check(&k).unwrap();
    }

    #[test]
    fn joint_cap_cut_schedule_retains_all_vertices_events_and_exact_reversal_complements() {
        let k = Kernel::default();
        let work = MeshWork::new();
        let hints = [
            SourceCutHint {
                ring: 7,
                at: SourceCursor { edge: 0, unit: 0.1 },
            },
            SourceCutHint {
                ring: 7,
                at: SourceCursor {
                    edge: 0,
                    unit: 1. / 3.,
                },
            },
            SourceCutHint {
                ring: 7,
                at: SourceCursor { edge: 0, unit: 0.1 },
            },
            SourceCutHint {
                ring: 7,
                at: SourceCursor { edge: 2, unit: 1. },
            },
            SourceCutHint {
                ring: 7,
                at: SourceCursor { edge: 3, unit: -0. },
            },
            SourceCutHint {
                ring: 7,
                at: SourceCursor { edge: 3, unit: 1. },
            },
        ];
        let schedule = joint_source_cuts_with_work(&k, &work, 7, 4, &hints).unwrap();
        assert_eq!(schedule.ring(), 7);
        assert_eq!(schedule.cuts().len(), 6);
        for edge in 0..4 {
            assert_eq!(
                schedule
                    .cuts()
                    .iter()
                    .filter(|c| c.edge == edge && c.unit == 0.)
                    .count(),
                1
            );
        }
        for cut in schedule.cuts() {
            assert!(cut.unit.is_finite() && (0.0..1.0).contains(&cut.unit));
            let reverse =
                super::super::certificate::exact_source_unit_complement(cut.unit).unwrap();
            assert_eq!(
                super::super::certificate::exact_source_unit_complement(reverse),
                Some(cut.unit)
            );
            if cut.unit == 0. {
                assert_eq!(cut.unit.to_bits(), 0);
            }
        }
        assert_eq!(schedule.hint_cut(0), schedule.hint_cut(2));
        assert_eq!(schedule.hint_cut(3), schedule.hint_cut(4));
        assert_eq!(schedule.hint_cut(5), Some(0));
        // A native-zero cursor is its explicit event, never the sorted minimum.
        assert_ne!(schedule.hint_cut(1), Some(0));
        assert!(schedule.hint_cut(hints.len()).is_none());
        work.check(&k).unwrap();
    }
    #[test]
    fn joint_cut_schedule_rejects_other_rings_and_invalid_hints_without_fabricating_aliases() {
        let k = Kernel::default();
        let work = MeshWork::new();
        for (ring, edge, unit) in [
            (1, 0, 0.5),
            (0, 4, 0.5),
            (0, 0, -0.1),
            (0, 0, 1.1),
            (0, 0, f64::NAN),
            (0, 0, f64::INFINITY),
        ] {
            let hints = [SourceCutHint {
                ring,
                at: SourceCursor { edge, unit },
            }];
            assert!(joint_source_cuts_with_work(&k, &work, 0, 4, &hints).is_err());
        }
        assert!(joint_source_cuts_with_work(&k, &work, 0, 2, &[]).is_err());
        let hints = [SourceCutHint {
            ring: 0,
            at: SourceCursor {
                edge: 1,
                unit: f64::from_bits(1),
            },
        }];
        let schedule = joint_source_cuts_with_work(&k, &work, 0, 4, &hints).unwrap();
        assert_eq!(schedule.cuts().len(), 4);
        // Rounding may collapse a candidate-only event, but it is still named.
        // The future target scheduler MUST refuse a needed zero-length root cell.
        assert_eq!(schedule.hint_cut(0), Some(1));
        work.check(&k).unwrap();
    }

    #[test]
    fn opposite_cap_cuts_follow_unique_original_alias_edges_before_endpoint_wrap() {
        let k = Kernel::default();
        let work = MeshWork::new();
        let lower = [10, 20, 30, 40];
        let mut partners =
            std::collections::BTreeMap::from([(100, 10), (200, 20), (300, 30), (400, 40)]);
        // Other source rims share the global partner table; its size exceeds n.
        for alias in 500..600 {
            partners.insert(alias, alias + 1000);
        }
        let same = source_ring_partner_map_with_work(
            &k,
            &work,
            [7, 9],
            &lower,
            &[300, 400, 100, 200],
            &partners,
        )
        .unwrap();
        assert_eq!(same.rings(), [7, 9]);
        let cut = same
            .map_cut_with_work(
                &k,
                &work,
                SourceCursor {
                    edge: 0,
                    unit: 0.25,
                },
            )
            .unwrap();
        assert_eq!((cut.edge, cut.unit), (2, 0.25));
        let opposite = source_ring_partner_map_with_work(
            &k,
            &work,
            [7, 9],
            &lower,
            &[300, 200, 100, 400],
            &partners,
        )
        .unwrap();
        let cut = opposite
            .map_cut_with_work(
                &k,
                &work,
                SourceCursor {
                    edge: 0,
                    unit: 0.25,
                },
            )
            .unwrap();
        assert_eq!((cut.edge, cut.unit), (1, 0.75));
        let vertex = opposite
            .map_cut_with_work(&k, &work, SourceCursor { edge: 0, unit: 0. })
            .unwrap();
        assert_eq!((vertex.edge, vertex.unit), (2, 0.));
        let endpoint = opposite
            .map_cut_with_work(&k, &work, SourceCursor { edge: 0, unit: 1. })
            .unwrap();
        assert_eq!((endpoint.edge, endpoint.unit), (1, 0.));
        let cut = opposite
            .map_cut_with_work(&k, &work, SourceCursor { edge: 3, unit: 0. })
            .unwrap();
        assert_eq!((cut.edge, cut.unit), (3, 0.));
        for map in [&same, &opposite] {
            for edge in 0..lower.len() {
                for unit in [0., 0.25, 0.5, 0.75, 1.] {
                    let original = SourceCursor { edge, unit };
                    let mapped = map.map_cut_with_work(&k, &work, original).unwrap();
                    let back = map.inverse_cut_with_work(&k, &work, mapped).unwrap();
                    let expected = canonical_source_cut(lower.len(), original).unwrap();
                    assert_eq!((back.edge, back.unit), (expected.edge, expected.unit));
                }
            }
        }
        work.check(&k).unwrap();
    }
    #[test]
    fn missing_ambiguous_or_noncyclic_partner_aliases_cannot_create_a_cut_map() {
        let k = Kernel::default();
        let work = MeshWork::new();
        let lower = [10, 20, 30, 40];
        let partners =
            std::collections::BTreeMap::from([(100, 10), (200, 20), (300, 30), (400, 40)]);
        for upper in [
            [100, 300, 200, 400],
            [100, 200, 300, 300],
            [100, 200, 300, 500],
        ] {
            assert!(source_ring_partner_map_with_work(
                &k,
                &work,
                [0, 0],
                &lower,
                &upper,
                &partners
            )
            .is_err());
        }
        assert!(source_ring_partner_map_with_work(
            &k,
            &work,
            [0, 0],
            &[10, 20, 30, 30],
            &[100, 200, 300, 400],
            &partners
        )
        .is_err());
        let map = source_ring_partner_map_with_work(
            &k,
            &work,
            [0, 0],
            &lower,
            &[100, 200, 300, 400],
            &partners,
        )
        .unwrap();
        for at in [
            SourceCursor { edge: 4, unit: 0.5 },
            SourceCursor { edge: 0, unit: 0.1 },
            SourceCursor {
                edge: 0,
                unit: f64::NAN,
            },
        ] {
            assert!(map.map_cut_with_work(&k, &work, at).is_err());
        }
        work.check(&k).unwrap();
    }

    fn phase_shifted_target_cursors(cuts: &[SourceCursor]) -> Vec<TargetCursor> {
        cuts.iter()
            .map(|at| {
                let mut tick = 1. + 2. * f64::from(u32::try_from(at.edge).unwrap()) + 2. * at.unit;
                if tick >= 32. {
                    tick -= 32.;
                }
                let root = (0..4).find(|&r| tick < f64::from((r + 1) * 8)).unwrap();
                TargetCursor {
                    curve: 0,
                    root: usize::try_from(root).unwrap(),
                    unit: (tick - f64::from(root * 8)) / 8.,
                }
            })
            .collect()
    }
    fn phase_shifted_joint_schedule(k: &Kernel, work: &MeshWork) -> SourceCutSchedule {
        let hints = [
            SourceCutHint {
                ring: 0,
                at: SourceCursor {
                    edge: 15,
                    unit: 0.5,
                },
            },
            SourceCutHint {
                ring: 0,
                at: SourceCursor { edge: 3, unit: 0.5 },
            },
            SourceCutHint {
                ring: 0,
                at: SourceCursor { edge: 7, unit: 0.5 },
            },
            SourceCutHint {
                ring: 0,
                at: SourceCursor {
                    edge: 11,
                    unit: 0.5,
                },
            },
            SourceCutHint {
                ring: 0,
                at: SourceCursor {
                    edge: 5,
                    unit: 0.25,
                },
            },
        ];
        joint_source_cuts_with_work(k, work, 0, 16, &hints).unwrap()
    }
    #[test]
    fn joint_source_schedule_emits_one_whole_native_curve_graph_from_its_explicit_seam_anchor() {
        let k = Kernel::default();
        let work = MeshWork::new();
        let curve = circle();
        let schedule = phase_shifted_joint_schedule(&k, &work);
        let targets = phase_shifted_target_cursors(schedule.cuts());
        let anchor = schedule.hint_cut(0).unwrap();
        assert_ne!(anchor, 0);
        let claims =
            cap_graph_claims_with_work(&k, &work, 16, schedule.cuts(), &targets, &[4], anchor)
                .unwrap();
        assert_eq!(
            (claims.source_cursor.edge, claims.source_cursor.unit),
            (15, 0.5)
        );
        assert_eq!(claims.cells.len(), 21);
        let points: Vec<_> = (0..16)
            .map(|i| {
                let p = curve
                    .evaluate_point(&k, (f64::from(i) + 0.5) / 16.)
                    .unwrap();
                [p.x, p.y, p.z]
            })
            .collect();
        let uses = [CurveUse {
            curve: &curve,
            interval: curve.natural_interval(),
            forward: true,
        }];
        let proof = chain_graph_cover_from_cursor(
            &k,
            &work,
            &uses,
            exact_points_with_work(&k, &work, &points).unwrap(),
            &claims.cells,
            0.05,
            claims.source_cursor,
        )
        .unwrap();
        assert_eq!(proof.source.len(), 16);
        assert_eq!(proof.cells.len(), 21);
        assert!(proof.cells.iter().all(|c| c.distance_upper <= 0.05));
        work.check(&k).unwrap();
    }
    #[test]
    fn target_schedule_cannot_skip_a_root_vertex_or_collapsed_correspondence() {
        let k = Kernel::default();
        let work = MeshWork::new();
        let schedule = phase_shifted_joint_schedule(&k, &work);
        let targets = phase_shifted_target_cursors(schedule.cuts());
        let anchor = schedule.hint_cut(0).unwrap();
        assert!(
            cap_graph_claims_with_work(&k, &work, 16, schedule.cuts(), &targets, &[4], 0).is_err()
        );
        for missing in [schedule.hint_cut(1).unwrap(), 0] {
            let cuts: Vec<_> = schedule
                .cuts()
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != missing)
                .map(|(_, p)| *p)
                .collect();
            let ts: Vec<_> = targets
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != missing)
                .map(|(_, p)| *p)
                .collect();
            let anchor = cuts
                .iter()
                .position(|c| c.edge == 15 && c.unit == 0.5)
                .unwrap();
            assert!(cap_graph_claims_with_work(&k, &work, 16, &cuts, &ts, &[4], anchor).is_err());
        }
        let mut collapsed = targets.clone();
        collapsed[0] = collapsed[1];
        assert!(cap_graph_claims_with_work(
            &k,
            &work,
            16,
            schedule.cuts(),
            &collapsed,
            &[4],
            anchor
        )
        .is_err());
        for roots in [[3], [5], [0]] {
            assert!(cap_graph_claims_with_work(
                &k,
                &work,
                16,
                schedule.cuts(),
                &targets,
                &roots,
                anchor
            )
            .is_err());
        }
        work.check(&k).unwrap();
    }
    #[test]
    fn target_proposals_keep_actual_root_parameters_separate_from_proof_authority() {
        let k = Kernel::default();
        let work = MeshWork::new();
        let curve = circle();
        for forward in [false, true] {
            let uses = [CurveUse {
                curve: &curve,
                interval: curve.natural_interval(),
                forward,
            }];
            let proposals = TargetProposals::new_with_work(&k, &work, &uses).unwrap();
            for t in [0., 0.03125, 0.2499, 0.375, 0.7499, 0.9999] {
                let point = curve.evaluate_point(&k, t).unwrap();
                let at = proposals.propose_with_work(&k, &work, point).unwrap();
                let root = &proposals.roots[at.curve][at.root];
                let [a, b] = root.native_interval;
                let actual = curve.evaluate_point(&k, a + (b - a) * at.unit).unwrap();
                assert!((actual - point).length() < 1e-9, "forward={forward}, t={t}");
            }
            assert!(proposals
                .propose_with_work(&k, &work, crate::math::Vec3::new(f64::NAN, 0., 0.))
                .is_err());
        }
        work.check(&k).unwrap();
    }
    #[test]
    fn proposal_jets_keep_linear_and_rational_circle_derivative_identities() {
        assert_eq!(
            proposal_polynomial_jet(&[2., 6.], 0.25).unwrap(),
            [3., 4., 0.]
        );
        let k = Kernel::default();
        let work = MeshWork::new();
        let curve = circle();
        let uses = [CurveUse {
            curve: &curve,
            interval: curve.natural_interval(),
            forward: true,
        }];
        let proposals = TargetProposals::new_with_work(&k, &work, &uses).unwrap();
        for root in &proposals.roots[0] {
            let [p, d, dd] = proposal_curve_jet(root, 0.375).unwrap();
            assert!((p.dot(p) - 1.).abs() < 1e-12);
            assert!(p.dot(d).abs() < 1e-12);
            assert!((p.dot(dd) + d.dot(d)).abs() < 1e-11);
        }
    }
    #[test]
    fn target_proposals_preserve_latched_work_failure_before_invalid_point_refusal() {
        let k = Kernel::default();
        let work = MeshWork::new();
        let curve = circle();
        let uses = [CurveUse {
            curve: &curve,
            interval: curve.natural_interval(),
            forward: true,
        }];
        let proposals = TargetProposals::new_with_work(&k, &work, &uses).unwrap();
        assert!(work.spend(&k, usize::MAX).is_err());
        assert!(matches!(
            proposals.propose_with_work(&k, &work, crate::math::Vec3::new(f64::NAN, 0., 0.)),
            Err(MeshError::BudgetExceeded { .. })
        ));
    }
}
