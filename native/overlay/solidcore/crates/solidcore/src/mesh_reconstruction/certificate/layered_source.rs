//! Exact monotone two-slab source analysis, NEVER native-body acceptance.
//!
//! Initial class: one positive embedded retained source component, three exact
//! coordinate-axis levels, lower-outward cap and upper-outward floor/top chains.
//! Every other triangle belongs once to a COMPLETE oriented rectangular wall.
//! Exact footprint columns and complete cap/wall boundary chains are rechecked.
//! The compact planar chain with zero boundary is zero: its multiplicity is
//! locally constant off its finite edge set and zero outside compact support.
//! Hence C_low=C_floor+C_top with positive embedded planar chains, so floor/top
//! interiors are disjoint and partition low. No point classifications/samples.
//!
//! Same ExactSourceView, retained aliases and original triangle IDs are borrowed.
//! An endpoint view retains its SourceMotion/prior bound; no moved MeshInput or
//! SourceCertificate is made. Curved final S, native CW/material/regions, canonical
//! record, arbitrary frames/multi-direction machining remain separate obligations.
//! Deviations: none. Iterative, one MeshWork; existing native exact arithmetic/CW.
use super::super::work::MeshWork;
use super::exact_geometry as x;
use super::source_prism;
use super::source_view::{copy_point_with_work, ExactSourceView};
use crate::{Kernel, Result, SolidError};
use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};
const OP: &str = "mesh_reconstruction::certificate::layered_source";
fn refused(reason: &'static str) -> SolidError {
    SolidError::Unsupported {
        operation: OP,
        reason,
    }
}
fn overflow() -> SolidError {
    refused("layered source logical count overflow")
}
fn sum(a: usize, b: usize) -> Result<usize> {
    a.checked_add(b).ok_or_else(overflow)
}
fn product(a: usize, b: usize) -> Result<usize> {
    a.checked_mul(b).ok_or_else(overflow)
}
/// Candidate IDs only. Corners run bottom-a,b,top-b,a, with outward triangle sense.
#[derive(Clone, Debug)]
pub(crate) struct WallClaim {
    pub(crate) triangles: Vec<usize>,
    pub(crate) corners: [u32; 4],
    pub(crate) interval: [usize; 2],
}
#[derive(Clone, Debug)]
pub(crate) struct LayeredClaim {
    pub(crate) axis: usize,
    /// Three retained aliases whose coordinates specify the exact ordered levels.
    pub(crate) level_aliases: [u32; 3],
    /// SAME weld-alias inventory; None iff absent from the retained source complex.
    /// A Some value is a retained representative alias for that exact footprint.
    pub(crate) columns: Vec<Option<u32>>,
    /// Original triangle IDs of bottom, upward floor, upward top respectively.
    pub(crate) caps: [Vec<usize>; 3],
    pub(crate) walls: Vec<WallClaim>,
}
/// Source-only proof over immutable original ownership and exact coordinates.
/// No native candidate, cloneable flag or public adoption certificate is present.
pub(crate) struct LayeredSource<'v, 'raw, 'c> {
    view: ExactSourceView<'v, 'raw>,
    claim: &'c LayeredClaim,
}
impl<'v, 'raw> LayeredSource<'v, 'raw, '_> {
    pub(crate) fn view(&self) -> &ExactSourceView<'v, 'raw> {
        &self.view
    }
    pub(crate) fn claim(&self) -> &LayeredClaim {
        self.claim
    }
}
pub(crate) enum LayeredVerdict<'v, 'raw, 'c> {
    Proven(LayeredSource<'v, 'raw, 'c>),
    Undecided(&'static str),
}
struct Checks<'a> {
    k: &'a Kernel,
    work: &'a MeshWork,
}
impl Checks<'_> {
    fn charge(&self, slots: usize) -> Result<()> {
        self.work.spend_core(self.k, 0)?;
        self.work.spend_core(self.k, product(slots, 16)?)?;
        self.work.reserve_cells_core(self.k, slots)
    }
    fn sub(&self, a: &x::E, b: &x::E) -> Result<x::E> {
        self.charge(add_slots(a.len(), b.len())?)?;
        x::sub(a, b).ok_or_else(|| refused("exact source difference outside native range"))
    }
    fn equal(&self, a: &x::E, b: &x::E) -> Result<bool> {
        Ok(x::zero(&self.sub(a, b)?))
    }
    fn difference(&self, a: &x::P, b: &x::P) -> Result<x::P> {
        self.charge(difference_slots(
            a.each_ref().map(Vec::len),
            b.each_ref().map(Vec::len),
        )?)?;
        x::difference(a, b).ok_or_else(|| refused("source vector difference outside native range"))
    }
    fn dot(&self, a: &x::P, b: &x::P) -> Result<x::E> {
        self.charge(dot_slots(
            a.each_ref().map(Vec::len),
            b.each_ref().map(Vec::len),
        )?)?;
        x::dot(a, b).ok_or_else(|| refused("source dot outside native range"))
    }
    fn normal(&self, p: [&x::P; 3]) -> Result<x::P> {
        let [a, b, c] = p;
        let aa = a.each_ref().map(Vec::len);
        let bb = b.each_ref().map(Vec::len);
        let cc = c.each_ref().map(Vec::len);
        let ab = pair_sizes(aa, bb)?;
        let ac = pair_sizes(aa, cc)?;
        let slots = sum(
            sum(difference_slots(bb, aa)?, difference_slots(cc, aa)?)?,
            cross_slots(ab, ac)?,
        )?;
        self.charge(slots)?;
        source_prism::normal(p)
            .ok_or_else(|| refused("source triangle normal outside native range"))
    }
    fn boundary(&self, triangles: &[[u32; 3]]) -> Result<BTreeSet<(u32, u32)>> {
        let edges = product(triangles.len(), 3)?;
        // At most3T map entries (key2+record1+Vec header1),3T use-pairs2,
        // 3T result entries (pair2+record1):27T+two root headers. Keep30T+4.
        self.charge(sum(product(triangles.len(), 30)?, 4)?)?;
        // A tree search visits at most entry_count nodes. Each fixed u32-pair
        // comparison/loop is covered by16; no assumed library branching factor.
        self.work.spend_core(
            self.k,
            product(product(sum(edges, 1)?, sum(edges, 1)?)?, 16)?,
        )?;
        source_prism::boundary(self.k, self.work, triangles)?
            .ok_or_else(|| refused("source patch boundary incidence is not a complete chain"))
    }
}
// Native add/sub clones m and grow-writes m+j (j1..n), with n+1 headers.
fn add_slots(m: usize, n: usize) -> Result<usize> {
    let (m, n) = (m.max(1), n.max(1)); // also bound finite(empty) materializing exact zero.
    let tri = product(n, sum(n, 1)?)?
        .checked_div(2)
        .ok_or_else(overflow)?;
    sum(sum(sum(sum(m, product(m, n)?)?, tri)?, n)?, 1)
}
fn scale_slots(m: usize) -> Result<usize> {
    let m = m.max(1);
    sum(sum(product(product(m, m)?, 3)?, product(m, 6)?)?, 1)
}
// x::mul: each of n native scale(m) then add of at most2m into accumulated
// at most2mj. Includes initial sum header; exact-zero compaction only decreases.
fn mul_slots(m: usize, n: usize) -> Result<usize> {
    let (m, n) = (m.max(1), n.max(1));
    let t = product(m, 2)?;
    let pairs = product(n, n.saturating_sub(1))?
        .checked_div(2)
        .ok_or_else(overflow)?;
    let adds = sum(
        product(product(sum(t, 1)?, t)?, pairs)?,
        product(n, add_slots(0, t)?)?,
    )?;
    sum(sum(product(n, scale_slots(m)?)?, adds)?, 1)
}
fn mul_size(m: usize, n: usize) -> Result<usize> {
    product(product(m.max(1), n.max(1))?, 2)
}
fn pair_sizes(a: [usize; 3], b: [usize; 3]) -> Result<[usize; 3]> {
    let [a, b0, c] = a;
    let [d, e, f] = b;
    Ok([sum(a, d)?.max(1), sum(b0, e)?.max(1), sum(c, f)?.max(1)])
}
fn difference_slots(a: [usize; 3], b: [usize; 3]) -> Result<usize> {
    let [a, b0, c] = a;
    let [d, e, f] = b;
    sum(
        sum(sum(add_slots(a, d)?, add_slots(b0, e)?)?, add_slots(c, f)?)?,
        1,
    )
}
fn cross_slots(a: [usize; 3], b: [usize; 3]) -> Result<usize> {
    let [ax, ay, az] = a;
    let [bx, by, bz] = b;
    let mut slots = 1;
    for (a, b, c, d) in [(ay, bz, az, by), (az, bx, ax, bz), (ax, by, ay, bx)] {
        slots = sum(
            slots,
            sum(
                sum(mul_slots(a, b)?, mul_slots(c, d)?)?,
                add_slots(mul_size(a, b)?, mul_size(c, d)?)?,
            )?,
        )?;
    }
    Ok(slots)
}
fn dot_slots(a: [usize; 3], b: [usize; 3]) -> Result<usize> {
    let [ax, ay, az] = a;
    let [bx, by, bz] = b;
    let first = mul_size(ax, bx)?;
    let second = mul_size(ay, by)?;
    let third = mul_size(az, bz)?;
    sum(
        sum(
            sum(
                sum(mul_slots(ax, bx)?, mul_slots(ay, by)?)?,
                mul_slots(az, bz)?,
            )?,
            add_slots(first, second)?,
        )?,
        add_slots(sum(first, second)?, third)?,
    )
}
/// Storage safety ONLY: callers have already charged this buffer's complete
/// count in the SAME workflow ledger. This neither admits geometry nor grants
/// permission for later native/lazy workspace. A fresh Vec owns no old payload.
fn admitted_buffer<T>(k: &Kernel, work: &MeshWork, count: usize) -> Result<Vec<T>> {
    work.spend_core(k, 0)?;
    let mut buffer = Vec::new();
    buffer
        .try_reserve_exact(count)
        .map_err(|_| refused("layered source owned buffer allocation refused"))?;
    Ok(buffer)
}
fn point(points: &[Option<x::P>], id: u32) -> Result<&x::P> {
    usize::try_from(id)
        .ok()
        .and_then(|i| points.get(i))
        .and_then(Option::as_ref)
        .ok_or_else(|| refused("claim references an absent retained alias"))
}
fn column(claim: &LayeredClaim, id: u32) -> Result<u32> {
    usize::try_from(id)
        .ok()
        .and_then(|i| claim.columns.get(i))
        .copied()
        .flatten()
        .ok_or_else(|| refused("retained alias has no claimed footprint column"))
}
fn rows(
    check: &Checks<'_>,
    source: &super::source_topology::SourceManifold<'_>,
    ids: &[usize],
) -> Result<Vec<[u32; 3]>> {
    check.charge(sum(product(ids.len(), 4)?, 1)?)?;
    check
        .work
        .reserve_output_core(check.k, product(ids.len(), 3)?)?;
    let mut rows = admitted_buffer(check.k, check.work, ids.len())?;
    for &id in ids {
        check.work.spend_core(check.k, 1)?;
        let t = source
            .aliases
            .get(id)
            .copied()
            .flatten()
            .ok_or_else(|| refused("claim uses a missing or regularized-away triangle"))?;
        rows.push(t);
    }
    Ok(rows)
}
fn flow(
    check: &Checks<'_>,
    map: &mut BTreeMap<(u32, u32), [i32; 5]>,
    a: u32,
    b: u32,
    slot: usize,
) -> Result<()> {
    if a == b {
        return Err(refused("horizontal boundary collapses a footprint edge"));
    }
    check
        .work
        .spend_core(check.k, product(sum(map.len(), 1)?, 16)?)?;
    check.charge(8)?; // key pair2,value array5,map entry1 (also on existing entry).
    let (key, sign) = if a < b {
        ((a, b), 1i32)
    } else {
        ((b, a), -1i32)
    };
    let counts = map.entry(key).or_insert([0; 5]);
    let value = counts
        .get_mut(slot)
        .ok_or_else(|| SolidError::port_invariant(OP, "fixed flow slot missing"))?;
    *value = value.checked_add(sign).ok_or_else(overflow)?;
    Ok(())
}
fn analyze<'v, 'raw, 'c>(
    k: &Kernel,
    work: &MeshWork,
    view: ExactSourceView<'v, 'raw>,
    claim: &'c LayeredClaim,
) -> Result<LayeredSource<'v, 'raw, 'c>> {
    let check = Checks { k, work };
    work.spend_core(k, 0)?;
    let source = view.source();
    let a = view.alias_count();
    let t = source.aliases.len();
    // Each valid wall owns at least one distinct retained triangle. Reject junk
    // inventories in O(1) before their metadata walk; no valid class is removed.
    if claim.walls.len() > source.retained_count {
        return Err(refused(
            "wall claim inventory exceeds retained triangle ownership",
        ));
    }
    if claim.axis > 2
        || claim.columns.len() != a
        || claim.caps.iter().any(Vec::is_empty)
        || claim.walls.is_empty()
        || source.components.len() != 1
        || source.signed_volumes.len() != 1
        || !source
            .signed_volumes
            .first()
            .is_some_and(|v| v.is_finite() && v.is_positive())
    {
        return Err(refused("two-slab class needs one positive source component and three nonempty oriented cap chains"));
    }
    work.spend_core(k, sum(3, claim.walls.len())?)?;
    let refs = claim.caps.iter().try_fold(0usize, |n, v| {
        work.spend_core(k, 0)?;
        let next = sum(n, v.len())?;
        if next > source.retained_count {
            return Err(refused(
                "claimed triangle references exceed retained source count",
            ));
        }
        Ok(next)
    })?;
    let refs = claim.walls.iter().try_fold(refs, |n, v| {
        work.spend_core(k, 0)?; // per-wall work was already charged before the walk.
        let next = sum(n, v.triangles.len())?;
        if next > source.retained_count {
            return Err(refused(
                "claimed triangle references exceed retained source count",
            ));
        }
        Ok(next)
    })?;
    if refs != source.retained_count {
        return Err(refused(
            "original retained triangle ownership is incomplete or duplicated",
        ));
    }
    work.reserve_output_core(k, sum(sum(refs, product(claim.walls.len(), 4)?)?, a)?)?;
    // Eight A-sized logical slots: retained,points,level,three column-levels,
    // their row plus representatives; original ownership T. Keep eight headers.
    check.charge(sum(sum(product(a, 8)?, t)?, 8)?)?;
    let mut retained = admitted_buffer(k, work, a)?;
    retained.resize(a, false);
    let mut owned = admitted_buffer(k, work, t)?;
    owned.resize(t, false);
    let mut points: Vec<Option<x::P>> = admitted_buffer(k, work, a)?;
    points.resize_with(a, || None);
    let mut levels = admitted_buffer(k, work, a)?;
    levels.resize(a, None);
    let mut column_levels = admitted_buffer(k, work, a)?;
    column_levels.resize(a, [None; 3]);
    let mut representatives = admitted_buffer(k, work, a)?;
    for triangle in &source.aliases {
        work.spend_core(k, 1)?;
        if let Some(triangle) = triangle {
            for &id in triangle {
                let i = usize::try_from(id)
                    .map_err(|_| refused("alias index does not fit platform"))?;
                *retained.get_mut(i).ok_or_else(|| {
                    SolidError::port_invariant(OP, "proved alias outside inventory")
                })? = true;
            }
        }
    }
    for ids in claim
        .caps
        .iter()
        .map(Vec::as_slice)
        .chain(claim.walls.iter().map(|w| w.triangles.as_slice()))
    {
        for &id in ids {
            work.spend_core(k, 1)?;
            if source.aliases.get(id).is_none_or(Option::is_none) {
                return Err(refused("claim uses absent original triangle"));
            }
            let owner = owned
                .get_mut(id)
                .ok_or_else(|| refused("claimed triangle id outside source"))?;
            if *owner {
                return Err(refused("original triangle has multiple owners"));
            }
            *owner = true;
        }
    }
    for (original, owned) in source.aliases.iter().zip(&owned) {
        work.spend_core(k, 1)?;
        if original.is_some() != *owned {
            return Err(refused("unassigned retained original triangle"));
        }
    }
    for (i, used) in retained.iter().copied().enumerate() {
        work.spend_core(k, 1)?;
        if !used {
            if claim.columns.get(i).copied().flatten().is_some() {
                return Err(refused("unused alias cannot supply a source column"));
            }
            continue;
        }
        let id = u32::try_from(i).map_err(|_| refused("alias index exceeds native source id"))?;
        work.reserve_cells_core(k, 3)?; // existing view/copy helper charges point+coefficients; add Vec headers.
        let p = view
            .position_with_work(k, work, id)?
            .ok_or_else(|| SolidError::port_invariant(OP, "proved source view position missing"))?;
        let p = match p {
            Cow::Owned(p) => p,
            Cow::Borrowed(p) => copy_point_with_work(k, work, p)?,
        };
        *points
            .get_mut(i)
            .ok_or_else(|| SolidError::port_invariant(OP, "point-cache slot missing"))? = Some(p);
    }
    let [l0, l1, l2] = claim.level_aliases;
    let low = point(&points, l0)?
        .get(claim.axis)
        .ok_or_else(|| refused("level axis missing"))?;
    let mid = point(&points, l1)?
        .get(claim.axis)
        .ok_or_else(|| refused("level axis missing"))?;
    let high = point(&points, l2)?
        .get(claim.axis)
        .ok_or_else(|| refused("level axis missing"))?;
    if x::sign(&check.sub(mid, low)?) != Some(1) || x::sign(&check.sub(high, mid)?) != Some(1) {
        return Err(refused("source slab levels are not exact and increasing"));
    }
    let axes = match claim.axis {
        0 => [1, 2],
        1 => [2, 0],
        2 => [0, 1],
        _ => return Err(refused("invalid source axis")),
    };
    for (i, used) in retained.iter().copied().enumerate() {
        if !used {
            continue;
        }
        work.spend_core(k, 1)?;
        let alias = u32::try_from(i).map_err(|_| refused("source alias id overflow"))?;
        let p = point(&points, alias)?;
        let h = p
            .get(claim.axis)
            .ok_or_else(|| refused("source height missing"))?;
        let mut level = None;
        for (index, value) in [low, mid, high].into_iter().enumerate() {
            if check.equal(h, value)? {
                if level.replace(index).is_some() {
                    return Err(refused("source height matches ambiguous levels"));
                }
            }
        }
        let level = level.ok_or_else(|| {
            refused("a retained source vertex is not at one of the three exact levels")
        })?;
        *levels
            .get_mut(i)
            .ok_or_else(|| SolidError::port_invariant(OP, "level-cache slot missing"))? =
            Some(level);
        let rep = column(claim, alias)?;
        let q = point(&points, rep)?;
        if column(claim, rep)? != rep {
            return Err(refused("footprint representative is not self-owned"));
        }
        for axis in axes {
            if !check.equal(
                p.get(axis)
                    .ok_or_else(|| refused("footprint coordinate missing"))?,
                q.get(axis)
                    .ok_or_else(|| refused("footprint coordinate missing"))?,
            )? {
                return Err(refused("source column moves an exact footprint coordinate"));
            }
        }
        let rep_index = usize::try_from(rep).map_err(|_| refused("column id overflow"))?;
        let row = column_levels
            .get_mut(rep_index)
            .ok_or_else(|| refused("column id outside inventory"))?;
        let slot = row
            .get_mut(level)
            .ok_or_else(|| SolidError::port_invariant(OP, "fixed column level missing"))?;
        if slot.replace(alias).is_some() {
            return Err(refused(
                "two retained aliases share one exact column and level",
            ));
        }
        work.spend_core(k, representatives.len())?;
        if !representatives.contains(&rep) {
            representatives.push(rep);
        }
    }
    for (i, &a) in representatives.iter().enumerate() {
        for &b in representatives.iter().skip(i + 1) {
            work.spend_core(k, 1)?;
            let p = point(&points, a)?;
            let q = point(&points, b)?;
            let mut same = true;
            for axis in axes {
                same &= check.equal(
                    p.get(axis)
                        .ok_or_else(|| refused("footprint coordinate missing"))?,
                    q.get(axis)
                        .ok_or_else(|| refused("footprint coordinate missing"))?,
                )?;
            }
            if same {
                return Err(refused("distinct column IDs have the same exact footprint"));
            }
        }
    }
    let mut chains = BTreeMap::new();
    for (level, ids) in claim.caps.iter().enumerate() {
        let triangles = rows(&check, source, ids)?;
        for &[a, b, c] in &triangles {
            work.spend_core(k, 1)?;
            for id in [a, b, c] {
                let index = usize::try_from(id).map_err(|_| refused("cap alias index overflow"))?;
                if levels.get(index).copied().flatten() != Some(level) {
                    return Err(refused(
                        "horizontal cap owns a triangle at the wrong source level",
                    ));
                }
            }
            let n = check.normal([point(&points, a)?, point(&points, b)?, point(&points, c)?])?;
            let expected = if level == 0 { -1 } else { 1 };
            if n.get(claim.axis).and_then(x::sign) != Some(expected) {
                return Err(refused("horizontal cap orientation/regularity does not match the monotone pocket class"));
            }
        }
        for &(a, b) in &check.boundary(&triangles)? {
            flow(
                &check,
                &mut chains,
                column(claim, a)?,
                column(claim, b)?,
                level,
            )?;
        }
    }
    for wall in &claim.walls {
        work.spend_core(k, 1)?;
        let [lo, hi] = wall.interval;
        if lo >= hi || hi > 2 || wall.triangles.is_empty() {
            return Err(refused("wall interval is not a nonempty source slab run"));
        }
        let [a, b, c, d] = wall.corners;
        for (id, expected) in [(a, lo), (b, lo), (c, hi), (d, hi)] {
            let i = usize::try_from(id).map_err(|_| refused("wall corner index overflow"))?;
            if levels.get(i).copied().flatten() != Some(expected) {
                return Err(refused(
                    "wall corner is not at its declared exact source level",
                ));
            }
        }
        if column(claim, a)? != column(claim, d)?
            || column(claim, b)? != column(claim, c)?
            || column(claim, a)? == column(claim, b)?
        {
            return Err(refused(
                "wall is not a nondegenerate exact column rectangle",
            ));
        }
        let origin = point(&points, a)?;
        let n = check.normal([origin, point(&points, b)?, point(&points, d)?])?;
        if n.iter().all(x::zero) {
            return Err(refused("wall rectangle has zero area"));
        }
        let triangles = rows(&check, source, &wall.triangles)?;
        for &[a, b, c] in &triangles {
            work.spend_core(k, 1)?;
            let p = [point(&points, a)?, point(&points, b)?, point(&points, c)?];
            for p in p {
                if !x::zero(&check.dot(&n, &check.difference(p, origin)?)?) {
                    return Err(refused(
                        "a complete wall triangle leaves its rectangle plane",
                    ));
                }
            }
            let actual = check.normal(p)?;
            if x::sign(&check.dot(&actual, &n)?) != Some(1) {
                return Err(refused(
                    "a complete wall triangle reverses its outward rectangle chain",
                ));
            }
        }
        let boundary = check.boundary(&triangles)?;
        check.charge(8)?;
        if boundary.len() != 4
            || [(a, b), (b, c), (c, d), (d, a)]
                .iter()
                .any(|e| !boundary.contains(e))
        {
            return Err(refused(
                "complete wall triangle chain is not the exact rectangle boundary",
            ));
        }
        if lo == 0 {
            flow(&check, &mut chains, column(claim, a)?, column(claim, b)?, 3)?;
        }
        if hi == 2 {
            flow(&check, &mut chains, column(claim, a)?, column(claim, b)?, 4)?;
        }
    }
    for counts in chains.values() {
        work.spend_core(k, 1)?;
        let [bottom, floor, top, wall_low, wall_high] = *counts;
        if bottom.checked_add(floor).and_then(|v| v.checked_add(top)) != Some(0)
            || bottom.checked_neg() != Some(wall_low)
            || top != wall_high
        {
            return Err(refused(
                "complete slab profiles/floor/internal-cap cancellation differ",
            ));
        }
    }
    work.spend_core(k, 0)?;
    Ok(LayeredSource { view, claim })
}
pub(crate) fn analyze_layered_source_with_work<'v, 'raw, 'c>(
    k: &Kernel,
    work: &MeshWork,
    view: ExactSourceView<'v, 'raw>,
    claim: &'c LayeredClaim,
) -> Result<LayeredVerdict<'v, 'raw, 'c>> {
    work.spend_core(k, 0)?;
    let result = analyze(k, work, view, claim);
    work.spend_core(k, 0)?;
    match result {
        Ok(p) => Ok(LayeredVerdict::Proven(p)),
        Err(SolidError::Unsupported {
            operation: OP,
            reason,
        }) => Ok(LayeredVerdict::Undecided(reason)),
        Err(e) => Err(e),
    }
}
