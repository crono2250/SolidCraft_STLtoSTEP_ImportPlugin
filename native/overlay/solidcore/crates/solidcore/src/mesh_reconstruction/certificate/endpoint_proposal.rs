//! Finite affine endpoint candidates on the ORIGINAL weld-alias inventory.
//!
//! These are geometric input, not proof flags or a moved MeshInput. Core builds
//! O+uA+vB (+h(A cross B)) with the existing exact expansion primitives. Motion,
//! complete source product, native cap/side/rim/material and final identity proof
//! remain mandatory. No arbitrary caller-supplied expansion is admitted.
//!
//! Deviations: no recursion; same MeshWork. All intermediate initialized logical
//! coefficient/vector slots are charged BEFORE the fixed expressions, not merely
//! their result length. Accounting follows geom::expansion::{grow,add,scale} and
//! certificate::exact_geometry::{mul,cross}; spare Vec capacity is not bytes.
use super::super::types::{MeshError, PrismTool};
use super::super::work::MeshWork;
use super::exact_geometry as x;
use super::source_topology::SourceManifold;
use crate::math::Vec3;
use crate::{Kernel, Result, SolidError};
use std::collections::{BTreeMap, BTreeSet};

const OP: &str = "mesh_reconstruction::certificate::endpoint_proposal";
/// Untrusted parameters for ONE unchanged original weld alias.
#[derive(Clone, Copy, Debug)]
pub struct EndpointAlias {
    /// Finite dyadic coefficients of the frame A and B (all stored f64 are dyadic).
    pub uv: [f64; 2],
    /// Geometric choice of the translated cap, NOT a certificate/status flag.
    pub translated: bool,
}
/// Candidate-only exact affine product coordinates in original weld-alias order.
/// Neither projected samples nor rounded endpoint coordinates certify this data.
#[derive(Clone, Debug)]
pub struct PrismaticEndpointProposal {
    /// Finite frame origin.
    pub origin: [f64; 3],
    /// Finite first in-plane vector.
    pub a: [f64; 3],
    /// Finite second in-plane vector, independently checked nonparallel to A.
    pub b: [f64; 3],
    /// Finite nonzero h; translation is constructed EXACTLY as h*(A cross B).
    pub translation_factor: f64,
    /// EXACTLY one row for every SAME original weld alias; no reindex/weld.
    pub aliases: Vec<EndpointAlias>,
}
pub(super) struct EndpointModel {
    pub(super) points: Vec<x::P>,
    pub(super) normal: x::P,
    pub(super) normal_hint: [f64; 3],
}
fn refused(reason: &'static str) -> SolidError {
    SolidError::Unsupported {
        operation: OP,
        reason,
    }
}
fn charge(k: &Kernel, work: &MeshWork, slots: usize) -> Result<()> {
    // Work accounting is in logical coefficient steps, not a floating-error or
    // CPU-cycle claim. Six TwoSum operations plus loop/update/finite scans fit
    // within sixteen units per allocated coefficient/vector slot in these fixed
    // expressions; product/range tests are charged by the same conservative guard.
    let steps = slots
        .checked_mul(16)
        .ok_or_else(|| refused("endpoint work count overflow"))?;
    work.spend_core(k, steps)?;
    work.reserve_cells_core(k, slots)
}
fn bounded(p: &x::P, terms: usize) -> Result<()> {
    if p.iter().any(|c| c.is_empty() || c.len() > terms) {
        return Err(SolidError::port_invariant(
            OP,
            "fixed native expansion term bound changed",
        ));
    }
    Ok(())
}
/// Build data only. These fixed term/allocation bounds use the ACTUAL native paths:
/// add(m,n) writes m+sum(j=1..n)(m+j) coefficients and has n+1 Vec headers;
/// scale(m) writes at most3m²+2m coefficients and has4m+1 headers. Native x::mul
/// of two one-term scalars additionally adds its2-term scale into an empty sum.
/// Hence x::cross(A,B) writes25 coefficients+21 headers/component (139 total
/// with its P slot); result<=4 terms. Scaling that by h writes56+17 per
/// component (220 total); result<=8 terms. Each endpoint coordinate uses two
/// scalar scales (10 slots each), add(1,2)=9, add(3,2)=15, and for upper points
/// add(5,8)=90. Including one P slot: lower133, upper403. The lower
/// precharge deliberately retains172 (39 surplus slots); no charge is reduced.
/// Frame scalar points
/// O,A,B cost3*(3 coefficients+3 Vec headers+1 P)=21. Exact-zero compaction
/// only lowers these bounds and never substitutes a rounded coordinate.
pub(super) fn build_endpoint_model(
    k: &Kernel,
    work: &MeshWork,
    alias_count: usize,
    proposal: &PrismaticEndpointProposal,
) -> Result<EndpointModel> {
    work.spend_core(k, 0)?;
    if proposal.aliases.len() != alias_count || alias_count == 0 {
        return Err(refused(
            "endpoint rows differ from original weld alias inventory",
        ));
    }
    work.spend_core(k, 10)?;
    if !proposal
        .origin
        .iter()
        .chain(&proposal.a)
        .chain(&proposal.b)
        .all(|v| v.is_finite())
        || !proposal.translation_factor.is_finite()
        || proposal.translation_factor == 0.
    {
        return Err(refused(
            "endpoint frame/factor is not finite and nondegenerate",
        ));
    }
    charge(k, work, 21)?;
    let o =
        x::point(proposal.origin).ok_or_else(|| refused("endpoint origin outside exact range"))?;
    let a = x::point(proposal.a).ok_or_else(|| refused("endpoint A outside exact range"))?;
    let b = x::point(proposal.b).ok_or_else(|| refused("endpoint B outside exact range"))?;
    charge(k, work, 139)?;
    let normal = x::cross(&a, &b)
        .ok_or_else(|| refused("endpoint frame cross outside exact arithmetic range"))?;
    bounded(&normal, 4)?;
    if normal.iter().all(x::zero) {
        return Err(refused("endpoint frame vectors are exactly dependent"));
    }
    charge(k, work, 220)?;
    let [nx, ny, nz] = &normal;
    let h = proposal.translation_factor;
    let d = [
        x::scale(nx, h).ok_or_else(|| refused("endpoint translation outside exact range"))?,
        x::scale(ny, h).ok_or_else(|| refused("endpoint translation outside exact range"))?,
        x::scale(nz, h).ok_or_else(|| refused("endpoint translation outside exact range"))?,
    ];
    bounded(&d, 8)?;
    work.spend_core(k, 12)?;
    let normal_hint = normal.each_ref().map(|c| crate::geom::expansion::to_f64(c));
    if !normal_hint.iter().all(|v| v.is_finite()) || normal_hint.iter().all(|v| *v == 0.) {
        return Err(refused(
            "endpoint normal has no finite numerical steering vector",
        ));
    }
    let mut points = Vec::new();
    for alias in &proposal.aliases {
        work.spend_core(k, 2)?;
        let [u, v] = alias.uv;
        if !u.is_finite() || !v.is_finite() {
            return Err(refused("endpoint alias coefficient is not finite"));
        }
        charge(k, work, if alias.translated { 403 } else { 172 })?;
        work.reserve_output_core(k, 1)?;
        let component = |o: &x::E, a: &x::E, b: &x::E, d: &x::E| -> Result<x::E> {
            let ua = x::scale(a, u).ok_or_else(|| refused("endpoint uA outside exact range"))?;
            let vb = x::scale(b, v).ok_or_else(|| refused("endpoint vB outside exact range"))?;
            let p = x::add(o, &ua)
                .and_then(|p| x::add(&p, &vb))
                .ok_or_else(|| refused("endpoint affine sum outside exact range"))?;
            if alias.translated {
                x::add(&p, d).ok_or_else(|| refused("endpoint translated sum outside exact range"))
            } else {
                Ok(p)
            }
        };
        let [ox, oy, oz] = &o;
        let [ax, ay, az] = &a;
        let [bx, by, bz] = &b;
        let [dx, dy, dz] = &d;
        let p = [
            component(ox, ax, bx, dx)?,
            component(oy, ay, by, dy)?,
            component(oz, az, bz, dz)?,
        ];
        bounded(&p, if alias.translated { 13 } else { 5 })?;
        points.push(p);
    }
    work.spend_core(k, 0)?;
    Ok(EndpointModel {
        points,
        normal,
        normal_hint,
    })
}

// This is a single candidate synthesis, not an acceptance theorem. Approximate
// projections and nearest scores choose data only; the existing exact endpoint
// factory, source motion, source product and complete actual product proof decide.

type CandidateResult<T> = super::super::types::Result<T>;
fn candidate_refused(reason: &'static str) -> MeshError {
    MeshError::Refused {
        stage: OP,
        detail: reason.into(),
    }
}
fn candidate_invariant(reason: &'static str) -> MeshError {
    SolidError::port_invariant(OP, reason).into()
}
fn row(rows: &[EndpointAlias], id: u32) -> CandidateResult<&EndpointAlias> {
    usize::try_from(id)
        .ok()
        .and_then(|i| rows.get(i))
        .ok_or_else(|| candidate_invariant("proved original alias missing from candidate rows"))
}
fn nearest_partner(
    k: &Kernel,
    work: &MeshWork,
    rows: &[EndpointAlias],
    id: u32,
    candidates: &BTreeSet<u32>,
) -> CandidateResult<u32> {
    let [u, v] = row(rows, id)?.uv;
    let mut best: Option<(u32, f64)> = None;
    let mut tied = false;
    for &other in candidates {
        work.spend(k, 64)?;
        let [a, b] = row(rows, other)?.uv;
        let du = u - a;
        let dv = v - b;
        let score = du * du + dv * dv;
        if !score.is_finite() {
            return Err(candidate_refused("endpoint partner score is nonfinite"));
        }
        match best {
            None => best = Some((other, score)),
            Some((_, old)) if score < old => {
                best = Some((other, score));
                tied = false;
            }
            Some((_, old)) if score == old => tied = true,
            _ => {}
        }
    }
    if tied {
        return Err(candidate_refused(
            "endpoint partner has tied projected candidates",
        ));
    }
    best.map(|(id, _)| id)
        .ok_or_else(|| candidate_refused("endpoint partner inventory is empty"))
}
/// Candidate-only mutual nearest bijection. The original rows are immutable for
/// the ENTIRE association; copying a chosen low coordinate into a high row is
/// deferred until every partner is selected. No rounded score proves equality.
pub(super) fn candidate_partners(
    k: &Kernel,
    work: &MeshWork,
    rows: &[EndpointAlias],
    lower: &BTreeSet<u32>,
    upper: &BTreeSet<u32>,
) -> CandidateResult<BTreeMap<u32, u32>> {
    work.check(k)?;
    let inventory = lower
        .len()
        .checked_add(upper.len())
        .ok_or_else(|| candidate_refused("endpoint boundary inventory count overflow"))?;
    work.spend(k, inventory)?;
    if lower.len() < 3 || lower.len() != upper.len() || !lower.is_disjoint(upper) {
        return Err(candidate_refused(
            "endpoint cap boundary inventories do not pair",
        ));
    }
    let mut upper_to_lower = BTreeMap::new();
    for &low in lower {
        let high = nearest_partner(k, work, rows, low, upper)?;
        if nearest_partner(k, work, rows, high, lower)? != low {
            return Err(candidate_refused(
                "endpoint partner association is not mutual",
            ));
        }
        work.spend(k, 1)?;
        if upper_to_lower.contains_key(&high) {
            return Err(candidate_refused("endpoint partner would be duplicated"));
        }
        work.reserve_cells(k, 2)?;
        work.reserve_output(k, 1)?;
        upper_to_lower.insert(high, low);
    }
    if upper_to_lower.len() != upper.len() {
        return Err(candidate_refused(
            "endpoint upper boundary is not completely paired",
        ));
    }
    Ok(upper_to_lower)
}
fn candidate_cap_boundaries(
    k: &Kernel,
    work: &MeshWork,
    source: &SourceManifold<'_>,
    rows: &[EndpointAlias],
) -> CandidateResult<[BTreeSet<u32>; 2]> {
    let mut caps: [BTreeMap<(u32, u32), (u8, i8)>; 2] = [BTreeMap::new(), BTreeMap::new()];
    for retained in &source.aliases {
        work.spend(k, 1)?; // Includes every explicitly regularized None entry.
        let Some([a, b, c]) = *retained else { continue };
        work.spend(k, 7)?;
        let cap = row(rows, a)?.translated;
        if row(rows, b)?.translated != cap || row(rows, c)?.translated != cap {
            continue;
        }
        let map = caps
            .get_mut(usize::from(cap))
            .ok_or_else(|| candidate_invariant("binary cap index changed"))?;
        for (a, b) in [(a, b), (b, c), (c, a)] {
            work.spend(k, 64)?;
            if a == b {
                return Err(candidate_refused(
                    "candidate cap has a collapsed alias edge",
                ));
            }
            let key = (a.min(b), a.max(b));
            let sense = if a < b { 1_i8 } else { -1_i8 };
            if let Some((count, balance)) = map.get_mut(&key) {
                *count = count
                    .checked_add(1)
                    .ok_or_else(|| candidate_refused("candidate cap edge count overflow"))?;
                *balance = balance
                    .checked_add(sense)
                    .ok_or_else(|| candidate_refused("candidate cap edge balance overflow"))?;
                if *count > 2 {
                    return Err(candidate_refused(
                        "candidate cap has repeated boundary incidence",
                    ));
                }
            } else {
                work.reserve_cells(k, 2)?;
                work.reserve_output(k, 1)?;
                map.insert(key, (1, sense));
            }
        }
    }
    let mut boundaries = [BTreeSet::new(), BTreeSet::new()];
    for (map, boundary) in caps.iter().zip(&mut boundaries) {
        for (&(a, b), &(count, balance)) in map {
            work.spend(k, 8)?;
            match (count, balance) {
                (2, 0) => {}
                (1, -1 | 1) => {
                    for id in [a, b] {
                        work.spend(k, 32)?;
                        if !boundary.contains(&id) {
                            work.reserve_cells(k, 1)?;
                            work.reserve_output(k, 1)?;
                            boundary.insert(id);
                        }
                    }
                }
                _ => {
                    return Err(candidate_refused(
                        "candidate cap edge incidence is inconsistent",
                    ))
                }
            }
        }
    }
    Ok(boundaries)
}
/// Choose ONE finite affine proposal in the SAME original proven alias inventory.
/// The chosen construction frame is numerical steering, not a source/target proof.
/// No candidate mesh indices, rewelding, synthetic fan, or caller status is read.
pub(super) fn propose_from_source(
    k: &Kernel,
    work: &MeshWork,
    source: &SourceManifold<'_>,
    tool: &PrismTool,
) -> CandidateResult<PrismaticEndpointProposal> {
    work.check(k)?;
    work.spend(k, 96)?;
    if !crate::prism::profile::frame_is_orthonormal(&tool.frame)
        || !tool.start.is_finite()
        || !tool.end.is_finite()
        || tool.start >= tool.end
    {
        return Err(candidate_refused(
            "endpoint construction frame or levels are invalid",
        ));
    }
    let (_, a, b, normal) = crate::prism::profile::axes(&tool.frame);
    let origin = crate::prism::profile::to_world(&tool.frame, crate::math::Vec2::ZERO, tool.start);
    let h = tool.end - tool.start;
    let separation = h * normal.dot(normal);
    if origin.to_array().iter().any(|v| !v.is_finite())
        || !h.is_finite()
        || h <= 0.
        || !separation.is_finite()
        || separation <= 0.
    {
        return Err(candidate_refused(
            "endpoint construction has no finite separated caps",
        ));
    }
    let count = source.alias_count();
    let mut rows = Vec::new();
    for index in 0..count {
        work.spend(k, 64)?;
        let id = u32::try_from(index)
            .map_err(|_| candidate_refused("endpoint original alias index overflow"))?;
        let point = source
            .position(id)
            .map(Vec3::from_array)
            .ok_or_else(|| candidate_invariant("proved original alias point missing"))?;
        let q = point - origin;
        let uv = [q.dot(a), q.dot(b)];
        let height = q.dot(normal);
        let lo = height.abs();
        let hi = (height - separation).abs();
        if uv.iter().any(|v| !v.is_finite()) || !lo.is_finite() || !hi.is_finite() {
            return Err(candidate_refused("endpoint projection is nonfinite"));
        }
        if lo == hi {
            return Err(candidate_refused(
                "endpoint alias is tied between cap levels",
            ));
        }
        work.reserve_cells(k, 3)?;
        work.reserve_output(k, 1)?;
        rows.push(EndpointAlias {
            uv,
            translated: hi < lo,
        });
    }
    let [lower, upper] = candidate_cap_boundaries(k, work, source, &rows)?;
    let partners = candidate_partners(k, work, &rows, &lower, &upper)?;
    let mut aliases = Vec::new();
    for (index, current) in rows.iter().enumerate() {
        work.spend(k, 32)?;
        let id = u32::try_from(index)
            .map_err(|_| candidate_refused("endpoint original alias index overflow"))?;
        // Cap-interior points deliberately need no opposite-cap vertex mate.
        // Boundary pairs instead receive EXACTLY THE SAME stored dyadic u,v.
        let uv = match partners.get(&id) {
            Some(&low) => row(&rows, low)?.uv,
            None => current.uv,
        };
        work.reserve_cells(k, 3)?;
        work.reserve_output(k, 1)?;
        aliases.push(EndpointAlias {
            uv,
            translated: current.translated,
        });
    }
    work.check(k)?;
    Ok(PrismaticEndpointProposal {
        origin: origin.to_array(),
        a: a.to_array(),
        b: b.to_array(),
        translation_factor: h,
        aliases,
    })
}
