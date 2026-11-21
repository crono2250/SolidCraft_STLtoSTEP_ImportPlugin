//! Bounded decomposition at existing planar shoulders. Each final part must pass the
//! straight-extrusion certificate; cutting never makes a faceted B-rep.
//!
//! Deviations: no upstream counterpart. Shoulder decomposition descends at most eight levels.

use std::collections::{BTreeMap, VecDeque};

use super::MeshWork;
use crate::kernel::Kernel;
use crate::math::Vec3;
use crate::{Brep, Result, SolidError};

use super::geometry::{normalize, MeshPlane};
use super::{extrusion, invalid, native, TriMesh, MAX_BOUNDARY, MAX_TRIANGLES};

const MAX_ATTEMPTS: usize = 24;
const MAX_DEPTH: usize = 8;
const MAX_COMPONENTS: usize = 32;
const MAX_FACES: usize = 256;

/// Start bounded shoulder decomposition with one shared cut budget and original-mesh circle hints.
pub(super) fn reconstruct(
    k: &mut Kernel,
    work: &MeshWork,
    mesh: &TriMesh,
    tolerance: f64,
) -> Result<Option<Brep>> {
    recover(
        k,
        work,
        mesh,
        mesh,
        tolerance,
        0,
        &mut 0,
        &mut BTreeMap::new(),
    )
}

/// Rank at most sixteen canonical face-normal directions by triangle area to bound the reconstruction search.
pub(super) fn axes(mesh: &TriMesh) -> Vec<(Vec3, f64)> {
    let mut out = BTreeMap::new();
    for &[a, b, c] in &mesh.triangles {
        let (Some(a), Some(b), Some(c)) = (
            mesh.positions.get(a as usize),
            mesh.positions.get(b as usize),
            mesh.positions.get(c as usize),
        ) else {
            continue;
        };
        let cross = (*b - *a).cross(*c - *a);
        let Some(mut n) = normalize(cross) else {
            continue;
        };
        if n.x < -1e-8 || (n.x.abs() <= 1e-8 && (n.y < -1e-8 || (n.y.abs() <= 1e-8 && n.z < 0.))) {
            n = -n;
        }
        let key = (
            (n.x * 1e7).round() as i64,
            (n.y * 1e7).round() as i64,
            (n.z * 1e7).round() as i64,
        );
        let e = out.entry(key).or_insert((n, 0.));
        e.1 += cross.length();
    }
    let mut out: Vec<_> = out.into_values().collect();
    out.sort_by(|a, b| b.1.total_cmp(&a.1));
    out.truncate(16);
    out
}

/// Try certified extrusions before splitting at existing shoulders, sharing cut, depth and recovered-face budgets.
fn recover(
    k: &mut Kernel,
    work: &MeshWork,
    mesh: &TriMesh,
    root: &TriMesh,
    tolerance: f64,
    depth: usize,
    attempts: &mut usize,
    models: &mut BTreeMap<(i64, i64, i64), Vec<super::curves::Circle>>,
) -> Result<Option<Brep>> {
    work.spend_core(k, 0)?;
    work.spend_core(k, mesh.triangles.len())?;
    if depth > MAX_DEPTH || *attempts >= MAX_ATTEMPTS {
        return Ok(None);
    }
    let candidates = axes(mesh);
    {
        for &(axis, _) in &candidates {
            work.spend_core(k, 1)?;
            let key = (
                (axis.x * 1e6).round() as i64,
                (axis.y * 1e6).round() as i64,
                (axis.z * 1e6).round() as i64,
            );
            let circles = models.entry(key).or_insert_with(|| {
                super::curves::hints(root, axis, tolerance, tolerance.min(1e-3) * 0.01)
            });
            let result = match super::curves::extrusion(k, work, mesh, axis, tolerance, circles)? {
                Some(body) => Some(body),
                None if depth > 0 => extrusion(k, work, mesh, axis, tolerance)?,
                None => None,
            };
            if let Some(body) = result {
                if body.face_list().len() <= MAX_FACES {
                    return Ok(Some(body));
                }
                return Ok(None);
            }
        }
    }
    let size = mesh.size();
    let epsilon = (size.max(1.) * 1e-7).min(tolerance * 0.01).max(1e-9);
    let mut cuts = Vec::new();
    let area = candidates.iter().map(|x| x.1).sum::<f64>();
    for &(axis, _) in candidates.iter().take(6) {
        let lo = mesh
            .positions
            .iter()
            .map(|p| p.dot(axis))
            .fold(f64::INFINITY, f64::min);
        let hi = mesh
            .positions
            .iter()
            .map(|p| p.dot(axis))
            .fold(f64::NEG_INFINITY, f64::max);
        let mut planes = Vec::new();
        for &[a, b, c] in &mesh.triangles {
            let (Some(a), Some(b), Some(c)) = (
                mesh.positions.get(a as usize),
                mesh.positions.get(b as usize),
                mesh.positions.get(c as usize),
            ) else {
                return Err(invalid("missing part vertex"));
            };
            let h = [a.dot(axis), b.dot(axis), c.dot(axis)];
            if h.iter().copied().fold(f64::NEG_INFINITY, f64::max)
                - h.iter().copied().fold(f64::INFINITY, f64::min)
                <= epsilon
            {
                let height = h.iter().sum::<f64>() / 3.;
                if height > lo + epsilon * 8. && height < hi - epsilon * 8. {
                    planes.push((height, (*b - *a).cross(*c - *a).length()));
                }
            }
        }
        planes.sort_by(|a, b| a.0.total_cmp(&b.0));
        let mut merged: Vec<(f64, f64)> = Vec::new();
        for (h, a) in planes {
            if let Some(last) = merged.last_mut().filter(|p| (p.0 - h).abs() <= epsilon) {
                last.1 += a;
            } else {
                merged.push((h, a));
            }
        }
        for (height, a) in merged {
            if a >= area * 1e-3 {
                cuts.push((a, axis, height));
            }
        }
    }
    cuts.sort_by(|a, b| b.0.total_cmp(&a.0));
    cuts.truncate(8);
    for (_, axis, height) in cuts {
        work.spend_core(k, mesh.triangles.len())?;
        if *attempts >= MAX_ATTEMPTS {
            break;
        }
        *attempts += 1;
        let Some(low) = half(k, work, mesh, axis, height, false, epsilon)? else {
            continue;
        };
        let Some(high) = half(k, work, mesh, axis, height, true, epsilon)? else {
            continue;
        };
        let Some(mut pieces) = components(k, work, &low)? else {
            continue;
        };
        let Some(other) = components(k, work, &high)? else {
            continue;
        };
        pieces.extend(other);
        if pieces.len() < 2 || pieces.len() > MAX_COMPONENTS {
            continue;
        }
        let original = mesh.volume();
        let split_volume: f64 = pieces.iter().map(TriMesh::volume).sum();
        if (split_volume - original).abs() > epsilon * size.powi(2) * 10. {
            continue;
        }
        let mut bodies = Vec::new();
        let mut faces = 0;
        for piece in &pieces {
            let Some(body) = recover(k, work, piece, root, tolerance, depth + 1, attempts, models)?
            else {
                bodies.clear();
                break;
            };
            faces += body.face_list().len();
            if faces > MAX_FACES {
                bodies.clear();
                break;
            }
            bodies.push(body);
        }
        if bodies.len() != pieces.len() {
            continue;
        }
        let mut result: Option<Brep> = None;
        for body in bodies {
            work.spend_core(k, 1)?;
            result = Some(match result {
                None => body,
                Some(previous) => native::union(k, previous, body)?,
            });
        }
        if let Some(mut body) = result {
            if !native::is_valid(k, &mut body)? {
                return Err(invalid("reconstructed parts did not form a valid solid"));
            }
            let volume = native::volume(k, &mut body)?;
            let bound = size.powi(2) * tolerance * 4.;
            if !volume.is_finite() || volume <= 0. || (volume - original).abs() > bound {
                return Err(invalid("reconstructed part volume differs from the source"));
            }
            return Ok(Some(body));
        }
    }
    Ok(None)
}

/// Original-source or earlier artificial-cap ownership CLAIM. This tag never
/// stands in for a SourceCertificate or proves that a floating fragment lies on it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum FacetOrigin {
    Original(u32),
    ArtificialCap { cut: u8, cell: u32, positive: bool },
}
/// A predeclared split event, chosen before any native construction/proof. The
/// plane/snap values are those the original clip algorithm actually consumes.
#[derive(Clone, Copy, Debug)]
pub(super) struct CutEvent {
    pub(super) cut: u8,
    pub(super) parent_cut: Option<u8>,
    pub(super) depth: usize,
    pub(super) axis: Vec3,
    pub(super) height: f64,
    pub(super) epsilon: f64,
}
#[derive(Clone, Copy, Debug)]
pub(super) enum InsertClaim {
    DroppedArea,
    WeldedCollapse { aliases: [u32; 3] },
    Kept { output: u32, aliases: [u32; 3] },
}
#[derive(Clone, Copy, Debug)]
pub(super) enum ParentDisposition {
    Coplanar,
    Clipped,
}
#[derive(Clone, Debug)]
pub(super) struct ParentRow {
    pub(super) parent: u32,
    pub(super) origin: FacetOrigin,
    pub(super) fragments: std::ops::Range<usize>,
    pub(super) disposition: ParentDisposition,
}
#[derive(Clone, Debug)]
pub(super) struct FragmentClaim {
    pub(super) parent: u32,
    pub(super) origin: FacetOrigin,
    /// Actual pre-weld clip vertices, in the exact original fan order. A later
    /// geometric verifier must enclose them against the parent triangle/cut.
    pub(super) pre_weld: [Vec3; 3],
    pub(super) inserted: InsertClaim,
}
#[derive(Clone, Debug)]
pub(super) struct BoundaryClaim {
    pub(super) vertex: u32,
    pub(super) uv: [f64; 2],
}
#[derive(Clone, Debug)]
pub(super) struct CapClaim {
    pub(super) cut: u8,
    pub(super) positive: bool,
    pub(super) output: u32,
    /// SAME CDT boundary indices before the existing positive-side reversal.
    pub(super) boundary_triangle: [u32; 3],
}
#[derive(Default)]
pub(super) struct HalfAncestry {
    pub(super) rows: Vec<ParentRow>,
    pub(super) fragments: Vec<FragmentClaim>,
    pub(super) boundary: Vec<BoundaryClaim>,
    pub(super) loops: Vec<std::ops::Range<usize>>,
    pub(super) caps: Vec<CapClaim>,
}
struct TraceRecorder<'a> {
    parents: &'a [FacetOrigin],
    event: CutEvent,
    positive: bool,
    data: HalfAncestry,
}
impl<'a> TraceRecorder<'a> {
    fn new(
        k: &Kernel,
        work: &MeshWork,
        parents: &'a [FacetOrigin],
        event: CutEvent,
        positive: bool,
    ) -> Result<Self> {
        work.spend_core(k, 0)?;
        // Row: parent1+origin4+range2+disposition1 =8 logical fields, plus5 Vec headers.
        work.reserve_cells_core(
            k,
            parents
                .len()
                .checked_mul(8)
                .and_then(|n| n.checked_add(15))
                .ok_or_else(|| invalid("ancestry storage overflow"))?,
        )?;
        let mut data = HalfAncestry::default();
        data.rows
            .try_reserve_exact(parents.len())
            .map_err(|_| invalid("cannot allocate parent ancestry"))?;
        Ok(Self {
            parents,
            event,
            positive,
            data,
        })
    }
    fn attempt(
        &mut self,
        k: &Kernel,
        work: &MeshWork,
        parent: usize,
        pre_weld: [Vec3; 3],
        inserted: InsertClaim,
    ) -> Result<()> {
        work.spend_core(k, 1)?;
        if self.data.fragments.len()
            >= MAX_TRIANGLES
                .checked_mul(2)
                .ok_or_else(|| invalid("fragment cap overflow"))?
        {
            return Err(invalid("fragment ancestry budget"));
        }
        if pre_weld
            .iter()
            .flat_map(|p| p.to_array())
            .any(|v| !v.is_finite())
        {
            return Err(invalid("nonfinite clip ancestry"));
        }
        let origin = *self
            .parents
            .get(parent)
            .ok_or_else(|| invalid("missing parent origin"))?;
        // 1parent +4origin +9coordinates +5inserted +Vec slot =20;32 is conservative.
        work.reserve_cells_core(k, 32)?;
        work.reserve_output_core(k, 1)?;
        self.data
            .fragments
            .try_reserve_exact(1)
            .map_err(|_| invalid("cannot allocate fragment ancestry"))?;
        self.data.fragments.push(FragmentClaim {
            parent: u32::try_from(parent).map_err(|_| invalid("parent index overflow"))?,
            origin,
            pre_weld,
            inserted,
        });
        Ok(())
    }
    fn row(
        &mut self,
        k: &Kernel,
        work: &MeshWork,
        parent: usize,
        start: usize,
        disposition: ParentDisposition,
    ) -> Result<()> {
        work.spend_core(k, 1)?;
        let origin = *self
            .parents
            .get(parent)
            .ok_or_else(|| invalid("missing parent origin"))?;
        if self.data.rows.len() != parent {
            return Err(invalid("duplicate or out-of-order parent row"));
        }
        self.data.rows.push(ParentRow {
            parent: u32::try_from(parent).map_err(|_| invalid("parent index overflow"))?,
            origin,
            fragments: start..self.data.fragments.len(),
            disposition,
        });
        Ok(())
    }
    fn boundary(
        &mut self,
        k: &Kernel,
        work: &MeshWork,
        ids: &[u32],
        points: &[[f64; 2]],
        loops: &[std::ops::Range<usize>],
    ) -> Result<()> {
        work.spend_core(k, 0)?;
        if ids.len() != points.len() || ids.len() > MAX_BOUNDARY || loops.len() > ids.len() {
            return Err(invalid("invalid cap ancestry sizes"));
        }
        let fields = ids
            .len()
            .checked_mul(3)
            .and_then(|n| loops.len().checked_mul(2).and_then(|m| n.checked_add(m)))
            .ok_or_else(|| invalid("cap ancestry count overflow"))?;
        work.reserve_cells_core(k, fields)?;
        work.reserve_output_core(k, ids.len())?;
        self.data
            .boundary
            .try_reserve_exact(ids.len())
            .map_err(|_| invalid("cannot allocate cap boundary ancestry"))?;
        self.data
            .loops
            .try_reserve_exact(loops.len())
            .map_err(|_| invalid("cannot allocate cap loop ancestry"))?;
        for (&vertex, &uv) in ids.iter().zip(points) {
            work.spend_core(k, 1)?;
            self.data.boundary.push(BoundaryClaim { vertex, uv });
        }
        for range in loops {
            work.spend_core(k, 1)?;
            self.data.loops.push(range.clone());
        }
        Ok(())
    }
    fn cap(
        &mut self,
        k: &Kernel,
        work: &MeshWork,
        output: usize,
        boundary_triangle: [u32; 3],
    ) -> Result<()> {
        work.spend_core(k, 1)?;
        if output >= MAX_TRIANGLES {
            return Err(invalid("cap output ancestry budget"));
        }
        work.reserve_cells_core(k, 8)?;
        work.reserve_output_core(k, 1)?;
        self.data
            .caps
            .try_reserve_exact(1)
            .map_err(|_| invalid("cannot allocate cap cell ancestry"))?;
        self.data.caps.push(CapClaim {
            cut: self.event.cut,
            positive: self.positive,
            output: u32::try_from(output).map_err(|_| invalid("cap output overflow"))?,
            boundary_triangle,
        });
        Ok(())
    }
}
pub(super) struct TracedHalf {
    pub(super) mesh: TriMesh,
    pub(super) ancestry: HalfAncestry,
}
/// Candidate-only source partition; no native body, acceptance bool or proof token.
/// It borrows the unchanged parent inventory. A later verifier still must prove
/// whole fragment domains, snap/weld displacements and opposite FILLED cap chains.
pub(super) struct SourcePartitionPlan<'a> {
    pub(super) parent: &'a TriMesh,
    work: &'a MeshWork,
    pub(super) origins: &'a [FacetOrigin],
    pub(super) event: CutEvent,
    pub(super) halves: [TracedHalf; 2],
    pub(super) component_counts: [usize; 2],
}

/// Original root identity only, borrowing the actual plan and the SAME source proof.
/// This is NOT a child-fragment/cap/union/native/material reconstruction certificate.
/// The workflow owner supplies one ledger from preflight onward; SourceCertificate
/// does not retroactively record the ledger used to create it.
pub(super) struct RootSourceBinding<'bound, 'plan, 'source, 'proof> {
    _source: &'bound super::super::SourceCertificate<'source, 'proof>,
    _plan: &'bound SourcePartitionPlan<'plan>,
    parent_to_alias: Vec<Option<u32>>,
}
impl RootSourceBinding<'_, '_, '_, '_> {
    pub(super) fn parent_aliases(&self) -> &[Option<u32>] {
        &self.parent_to_alias
    }
}

/// Prove a root candidate is the retained oriented alias quotient of THIS original
/// certificate. Never enumerate a compacted weld and assume those are raw IDs.
/// Exact coordinate equality here binds representations, not a zero-error demand on
/// the later analytic reconstruction. Whole tolerant geometry proof remains separate.
pub(super) fn bind_root_source_with_work<'bound, 'plan, 'source, 'proof>(
    k: &Kernel,
    work: &MeshWork,
    source: &'bound super::super::SourceCertificate<'source, 'proof>,
    plan: &'bound SourcePartitionPlan<'plan>,
) -> Result<RootSourceBinding<'bound, 'plan, 'source, 'proof>> {
    work.spend_core(k, 0)?;
    if !std::ptr::eq(work, plan.work) {
        return Err(invalid("root source binding ledger identity mismatch"));
    }
    if plan.event.depth != 0 || plan.event.parent_cut.is_some() {
        return Err(invalid("root source binding cannot certify a descendant"));
    }
    let parent = plan.parent;
    super::check_budget(&parent.positions, &parent.triangles)?;
    let view = source.original_view();
    if plan.origins.len() != parent.triangles.len()
        || parent.triangles.len() != view.retained_triangle_count()
    {
        return Err(invalid("root source retained triangle inventory mismatch"));
    }
    let p = parent.positions.len();
    let a = view.alias_count();
    let raw_count = view.raw_triangle_count();
    let cells = p
        .checked_mul(2)
        .and_then(|n| a.checked_mul(2).and_then(|m| n.checked_add(m)))
        .and_then(|n| n.checked_add(raw_count))
        .and_then(|n| n.checked_add(9))
        .ok_or_else(|| invalid("root source binding allocation count overflow"))?;
    work.reserve_cells_core(k, cells)?;
    work.reserve_output_core(k, p)?;
    let mut forward: Vec<Option<u32>> = Vec::new();
    let mut reverse: Vec<Option<u32>> = Vec::new();
    let mut seen = Vec::new();
    forward
        .try_reserve_exact(p)
        .map_err(|_| invalid("cannot allocate root vertex map"))?;
    reverse
        .try_reserve_exact(a)
        .map_err(|_| invalid("cannot allocate root alias map"))?;
    seen.try_reserve_exact(raw_count)
        .map_err(|_| invalid("cannot allocate raw facet coverage"))?;
    forward.resize(p, None);
    reverse.resize(a, None);
    seen.resize(raw_count, false);
    for (triangle, origin) in parent.triangles.iter().zip(plan.origins) {
        work.spend_core(k, 1)?;
        let FacetOrigin::Original(raw_id) = *origin else {
            return Err(invalid("artificial cap cannot be an original root facet"));
        };
        let Some(Some([aa, bb, cc])) = view.retained_raw_triangle(raw_id as usize) else {
            return Err(invalid(
                "root facet ID is not retained by this source certificate",
            ));
        };
        let used = seen
            .get_mut(raw_id as usize)
            .ok_or_else(|| invalid("root facet ID outside coverage inventory"))?;
        if *used {
            return Err(invalid("duplicate original root facet"));
        }
        *used = true;
        let mut matched = None;
        // The three cyclic representations of ONE oriented simplex; no fitting,
        // reversed winding, nearest-point rule or alternate geometry construction.
        for aliases in [[aa, bb, cc], [bb, cc, aa], [cc, aa, bb]] {
            let mut same = true;
            for (&vertex, alias) in triangle.iter().zip(aliases) {
                work.spend_core(k, 1)?;
                let point = parent
                    .positions
                    .get(vertex as usize)
                    .ok_or_else(|| invalid("root triangle vertex outside parent inventory"))?;
                let original = view
                    .source()
                    .position(alias)
                    .ok_or(SolidError::PortInvariant {
                        operation: "mesh_reconstruction::root_source_binding",
                        reason: "proven retained source alias lacks a position",
                    })?;
                for (v, expected) in point.to_array().into_iter().zip(original) {
                    work.spend_core(k, 1)?;
                    if v != expected {
                        same = false;
                    }
                }
            }
            if same {
                matched = Some(aliases);
                break;
            }
        }
        let aliases = matched
            .ok_or_else(|| invalid("root facet coordinates or orientation differ from source"))?;
        for (&vertex, alias) in triangle.iter().zip(aliases) {
            work.spend_core(k, 1)?;
            let target = forward
                .get_mut(vertex as usize)
                .ok_or_else(|| invalid("root vertex map index outside inventory"))?;
            if target.is_some_and(|old| old != alias) {
                return Err(invalid(
                    "root vertex is assigned to distinct source aliases",
                ));
            }
            *target = Some(alias);
            let back = reverse
                .get_mut(alias as usize)
                .ok_or(SolidError::PortInvariant {
                    operation: "mesh_reconstruction::root_source_binding",
                    reason: "proven source alias exceeds its declared inventory",
                })?;
            if back.is_some_and(|old| old != vertex) {
                return Err(invalid(
                    "one source alias was split into distinct parent vertices",
                ));
            }
            *back = Some(vertex);
        }
    }
    for (id, &used) in seen.iter().enumerate() {
        work.spend_core(k, 1)?;
        let retained = view
            .retained_raw_triangle(id)
            .ok_or(SolidError::PortInvariant {
                operation: "mesh_reconstruction::root_source_binding",
                reason: "proven original source inventory changed",
            })?
            .is_some();
        if retained != used {
            return Err(invalid("root source facet coverage is incomplete"));
        }
    }
    for (vertex, &alias) in forward.iter().enumerate() {
        work.spend_core(k, 1)?;
        let Some(alias) = alias else {
            return Err(invalid("unused parent vertex in root source binding"));
        };
        let vertex =
            u32::try_from(vertex).map_err(|_| invalid("root parent vertex index overflow"))?;
        if reverse.get(alias as usize) != Some(&Some(vertex)) {
            return Err(invalid("root alias correspondence is not bijective"));
        }
    }
    for (alias, &vertex) in reverse.iter().enumerate() {
        work.spend_core(k, 1)?;
        if let Some(vertex) = vertex {
            let alias =
                u32::try_from(alias).map_err(|_| invalid("root source alias index overflow"))?;
            if forward.get(vertex as usize) != Some(&Some(alias)) {
                return Err(invalid("root reverse correspondence is not bijective"));
            }
        }
    }
    Ok(RootSourceBinding {
        _source: source,
        _plan: plan,
        parent_to_alias: forward,
    })
}

/// Clip ONE already chosen event, before native construction. There is no axis,
/// plane or theorem retry here; None is only the inherited candidate clip refusal.
pub(super) fn propose_partition_at_with_work<'a>(
    k: &Kernel,
    work: &'a MeshWork,
    parent: &'a TriMesh,
    origins: &'a [FacetOrigin],
    event: CutEvent,
) -> Result<Option<SourcePartitionPlan<'a>>> {
    work.spend_core(k, 0)?;
    super::check_budget(&parent.positions, &parent.triangles)?;
    if origins.len() != parent.triangles.len()
        || event.cut as usize >= MAX_ATTEMPTS
        || event.depth > MAX_DEPTH
        || event.parent_cut.is_some_and(|id| id >= event.cut)
        || (event.depth == 0) != event.parent_cut.is_none()
        || !event.height.is_finite()
        || !(event.epsilon > 0. && event.epsilon.is_finite())
        || !(event.axis.length() > 0. && event.axis.length().is_finite())
    {
        return Err(invalid("invalid predeclared source partition"));
    }
    work.spend_core(k, origins.len())?;
    let mut original_ids = std::collections::BTreeSet::new();
    for origin in origins {
        work.spend_core(k, 1)?;
        match *origin {
            FacetOrigin::Original(id) => {
                if id as usize >= MAX_TRIANGLES {
                    return Err(invalid("original facet id exceeds source budget"));
                }
                if event.parent_cut.is_none() {
                    work.reserve_cells_core(k, 1)?;
                    if !original_ids.insert(id) {
                        return Err(invalid("duplicate root triangle ancestry"));
                    }
                }
            }
            FacetOrigin::ArtificialCap { cut, .. } => {
                if event.parent_cut.is_none_or(|parent| cut > parent) || cut >= event.cut {
                    return Err(invalid("unresolved parent-cut ancestry"));
                }
            }
        }
    }
    let mut low = TraceRecorder::new(k, work, origins, event, false)?;
    let Some(low_mesh) = clip_half(
        k,
        work,
        parent,
        event.axis,
        event.height,
        false,
        event.epsilon,
        Some(&mut low),
    )?
    else {
        return Ok(None);
    };
    let mut high = TraceRecorder::new(k, work, origins, event, true)?;
    let Some(high_mesh) = clip_half(
        k,
        work,
        parent,
        event.axis,
        event.height,
        true,
        event.epsilon,
        Some(&mut high),
    )?
    else {
        return Ok(None);
    };
    // The existing component splitter enforces32, and remains the ONE component
    // algorithm. Account its actual bounded potential copies before invoking it;
    // no new component meshes are published or treated as source certificates.
    let low_count = component_count_with_work(k, work, &low_mesh)?;
    let high_count = component_count_with_work(k, work, &high_mesh)?;
    let total = low_count
        .checked_add(high_count)
        .ok_or_else(|| invalid("part components count overflow"))?;
    if total > MAX_COMPONENTS {
        return Err(invalid("too many reconstructed components"));
    }
    let plan = SourcePartitionPlan {
        parent,
        work,
        origins,
        event,
        component_counts: [low_count, high_count],
        halves: [
            TracedHalf {
                mesh: low_mesh,
                ancestry: low.data,
            },
            TracedHalf {
                mesh: high_mesh,
                ancestry: high.data,
            },
        ],
    };
    check_partition_inventory_with_work(k, work, &plan)?;
    Ok(Some(plan))
}
/// STRUCTURAL inventory check only. It does not prove geometric partition,
/// ancestry truth, exact cap equivalence, topology/material or final BRep validity.
/// Returning () never authorizes adoption. All original/source claims remain untrusted.
pub(super) fn check_partition_inventory_with_work(
    k: &Kernel,
    work: &MeshWork,
    plan: &SourcePartitionPlan<'_>,
) -> Result<()> {
    work.spend_core(k, 0)?;
    if !std::ptr::eq(work, plan.work) {
        return Err(invalid("source partition ledger identity mismatch"));
    }
    if plan.origins.len() != plan.parent.triangles.len() {
        return Err(invalid("missing parent ancestry"));
    }
    for (side, half) in plan.halves.iter().enumerate() {
        work.spend_core(k, 0)?;
        let trace = &half.ancestry;
        if trace.rows.len() != plan.origins.len() || half.mesh.triangles.len() > MAX_TRIANGLES {
            return Err(invalid("missing parent inventory rows"));
        }
        work.reserve_cells_core(k, half.mesh.triangles.len())?;
        let mut covered = Vec::new();
        covered
            .try_reserve_exact(half.mesh.triangles.len())
            .map_err(|_| invalid("cannot allocate inventory coverage"))?;
        covered.resize(half.mesh.triangles.len(), false);
        let mut end = 0;
        for (parent, row) in trace.rows.iter().enumerate() {
            work.spend_core(k, 1)?;
            if row.parent as usize != parent
                || Some(&row.origin) != plan.origins.get(parent)
                || row.fragments.start != end
                || row.fragments.start > row.fragments.end
            {
                return Err(invalid("duplicate or inconsistent parent ancestry"));
            }
            let attempts = trace
                .fragments
                .get(row.fragments.clone())
                .ok_or_else(|| invalid("missing source fragments"))?;
            let limit = match row.disposition {
                ParentDisposition::Coplanar => 1,
                ParentDisposition::Clipped => 2,
            };
            if attempts.len() > limit {
                return Err(invalid("fragment fan exceeds one triangle half-space clip"));
            }
            for fragment in attempts {
                work.spend_core(k, 1)?;
                if fragment.parent != row.parent
                    || fragment.origin != row.origin
                    || fragment
                        .pre_weld
                        .iter()
                        .flat_map(|p| p.to_array())
                        .any(|v| !v.is_finite())
                {
                    return Err(invalid("invalid source fragment ancestry"));
                }
                match fragment.inserted {
                    InsertClaim::Kept { output, aliases } => {
                        let slot = covered
                            .get_mut(output as usize)
                            .ok_or_else(|| invalid("fragment output outside inventory"))?;
                        if *slot || half.mesh.triangles.get(output as usize) != Some(&aliases) {
                            return Err(invalid("duplicate or mismatched fragment ownership"));
                        }
                        if aliases
                            .iter()
                            .any(|&i| half.mesh.positions.get(i as usize).is_none())
                        {
                            return Err(invalid("missing fragment alias"));
                        }
                        *slot = true;
                    }
                    InsertClaim::WeldedCollapse { aliases } => {
                        if aliases
                            .iter()
                            .any(|&i| half.mesh.positions.get(i as usize).is_none())
                        {
                            return Err(invalid("missing collapsed alias"));
                        }
                    }
                    InsertClaim::DroppedArea => {}
                }
            }
            end = row.fragments.end;
        }
        if end != trace.fragments.len() {
            return Err(invalid("orphan source fragment"));
        }
        let mut boundary_end = 0;
        for ring in &trace.loops {
            work.spend_core(k, 1)?;
            if ring.start != boundary_end
                || ring.start > ring.end
                || ring.len() < 3
                || trace.boundary.get(ring.clone()).is_none()
            {
                return Err(invalid("missing cap loop boundary"));
            }
            boundary_end = ring.end;
        }
        if boundary_end != trace.boundary.len() {
            return Err(invalid("orphan cap boundary"));
        }
        for cap in &trace.caps {
            work.spend_core(k, 1)?;
            if cap.cut != plan.event.cut || cap.positive != (side == 1) {
                return Err(invalid("wrong artificial cap owner"));
            }
            let [a, b, c] = cap.boundary_triangle;
            let vertex = |i: u32| {
                trace
                    .boundary
                    .get(i as usize)
                    .map(|p| p.vertex)
                    .ok_or_else(|| invalid("cap index outside boundary"))
            };
            let (a, b, c) = (vertex(a)?, vertex(b)?, vertex(c)?);
            let expected = if cap.positive { [a, c, b] } else { [a, b, c] };
            let slot = covered
                .get_mut(cap.output as usize)
                .ok_or_else(|| invalid("cap output outside inventory"))?;
            if *slot || half.mesh.triangles.get(cap.output as usize) != Some(&expected) {
                return Err(invalid("duplicate or mismatched cap ownership"));
            }
            *slot = true;
        }
        for point in &trace.boundary {
            work.spend_core(k, 1)?;
            if point.uv.iter().any(|v| !v.is_finite())
                || half.mesh.positions.get(point.vertex as usize).is_none()
            {
                return Err(invalid("invalid cap alias correspondence"));
            }
        }
        if covered.iter().any(|yes| !yes) {
            return Err(invalid("unowned output triangle"));
        }
    }
    work.spend_core(k, 0)
}

/// Ordered child ownership data for a later predeclared cut. A cap cell index
/// is LOCAL TO THIS SIDE, not a claimed bijection to opposite-side CDT cells.
/// This remains untrusted ancestry data; no source/material proof is returned.
pub(super) fn child_origins_with_work(
    k: &Kernel,
    work: &MeshWork,
    plan: &SourcePartitionPlan<'_>,
    positive: bool,
) -> Result<Vec<FacetOrigin>> {
    check_partition_inventory_with_work(k, work, plan)?;
    let half = plan
        .halves
        .get(usize::from(positive))
        .ok_or_else(|| invalid("missing partition side"))?;
    let n = half.mesh.triangles.len();
    work.spend_core(k, n)?;
    work.reserve_cells_core(
        k,
        n.checked_mul(5)
            .and_then(|n| n.checked_add(3))
            .ok_or_else(|| invalid("child origin storage overflow"))?,
    )?;
    work.reserve_output_core(k, n)?;
    let mut owners = Vec::new();
    owners
        .try_reserve_exact(n)
        .map_err(|_| invalid("cannot allocate child ancestry"))?;
    owners.resize(n, None);
    for fragment in &half.ancestry.fragments {
        work.spend_core(k, 1)?;
        if let InsertClaim::Kept { output, .. } = fragment.inserted {
            let slot = owners
                .get_mut(output as usize)
                .ok_or_else(|| invalid("missing child fragment owner"))?;
            if slot.replace(fragment.origin).is_some() {
                return Err(invalid("duplicate child fragment owner"));
            }
        }
    }
    for (cell, cap) in half.ancestry.caps.iter().enumerate() {
        work.spend_core(k, 1)?;
        let slot = owners
            .get_mut(cap.output as usize)
            .ok_or_else(|| invalid("missing child cap owner"))?;
        let origin = FacetOrigin::ArtificialCap {
            cut: cap.cut,
            cell: u32::try_from(cell).map_err(|_| invalid("cap cell ordinal overflow"))?,
            positive,
        };
        if slot.replace(origin).is_some() {
            return Err(invalid("duplicate child cap owner"));
        }
    }
    // Separate output buffer is counted BEFORE collection; Option4+tag and owned4.
    work.reserve_cells_core(
        k,
        n.checked_mul(4)
            .ok_or_else(|| invalid("child owner output overflow"))?,
    )?;
    let mut result = Vec::new();
    result
        .try_reserve_exact(n)
        .map_err(|_| invalid("cannot allocate ordered child owners"))?;
    for owner in owners {
        work.spend_core(k, 1)?;
        result.push(owner.ok_or_else(|| invalid("unowned child triangle"))?);
    }
    Ok(result)
}

fn component_count_with_work(k: &Kernel, work: &MeshWork, mesh: &TriMesh) -> Result<usize> {
    work.spend_core(k, 0)?;
    // Across all component copies each input triangle is copied once and creates
    // at most3 component vertices. Coordinates9T + triangle indices3T + outer32
    // are bounded logical data-copy fields, not a whole allocator/memory theorem.
    work.reserve_cells_core(
        k,
        mesh.triangles
            .len()
            .checked_mul(12)
            .and_then(|n| n.checked_add(MAX_COMPONENTS))
            .ok_or_else(|| invalid("component copy count overflow"))?,
    )?;
    let result = components(k, work, mesh)?;
    work.spend_core(k, 0)?;
    result
        .map(|pieces| pieces.len())
        .ok_or_else(|| invalid("source partition components could not be inventoried"))
}

struct CutMesh {
    mesh: TriMesh,
    grid: BTreeMap<(i64, i64, i64), Vec<u32>>,
    epsilon: f64,
}
impl CutMesh {
    /// Reuse a cut vertex within epsilon across neighboring grid cells and report vertex-index overflow.
    fn point(&mut self, p: Vec3) -> Result<u32> {
        let e = self.epsilon;
        if !(e > 0. && e.is_finite()) {
            return Err(invalid("invalid part weld grid epsilon"));
        }
        let cell = |coordinate: f64| -> Result<i64> {
            let value = (coordinate / e).floor();
            // i64::MAX rounds up to 2^63 as f64. Strict bounds both reject
            // saturated casts and leave room for the neighboring grid cells.
            if !value.is_finite() || value <= i64::MIN as f64 || value >= i64::MAX as f64 {
                return Err(invalid("part weld grid coordinate exceeds its range"));
            }
            Ok(value as i64)
        };
        let key = (cell(p.x)?, cell(p.y)?, cell(p.z)?);
        for x in -1..=1 {
            for y in -1..=1 {
                for z in -1..=1 {
                    for &i in self
                        .grid
                        .get(&(
                            key.0
                                .checked_add(x)
                                .ok_or_else(|| invalid("part weld grid neighbor overflow"))?,
                            key.1
                                .checked_add(y)
                                .ok_or_else(|| invalid("part weld grid neighbor overflow"))?,
                            key.2
                                .checked_add(z)
                                .ok_or_else(|| invalid("part weld grid neighbor overflow"))?,
                        ))
                        .into_iter()
                        .flatten()
                    {
                        if self
                            .mesh
                            .positions
                            .get(i as usize)
                            .is_some_and(|q| q.distance(p) <= e)
                        {
                            return Ok(i);
                        }
                    }
                }
            }
        }
        let i =
            u32::try_from(self.mesh.positions.len()).map_err(|_| invalid("part vertex budget"))?;
        self.mesh.positions.push(p);
        self.grid.entry(key).or_default().push(i);
        Ok(i)
    }
    /// Weld a clipped triangle, discard degenerate corners and enforce the clipping triangle budget.
    fn triangle(&mut self, a: Vec3, b: Vec3, c: Vec3) -> Result<InsertClaim> {
        if (b - a).cross(c - a).length() <= self.epsilon.powi(2) {
            return Ok(InsertClaim::DroppedArea);
        }
        let (a, b, c) = (self.point(a)?, self.point(b)?, self.point(c)?);
        let inserted = if a != b && b != c && c != a {
            let output = u32::try_from(self.mesh.triangles.len())
                .map_err(|_| invalid("fragment index overflow"))?;
            self.mesh.triangles.push([a, b, c]);
            InsertClaim::Kept {
                output,
                aliases: [a, b, c],
            }
        } else {
            InsertClaim::WeldedCollapse { aliases: [a, b, c] }
        };
        if self.mesh.triangles.len() > MAX_TRIANGLES {
            return Err(invalid("part clipping exceeds its triangle budget"));
        }
        Ok(inserted)
    }
}

/// Clip to one half-space and cap its planar cut, refusing ambiguous, oversized or unclosed boundaries.
pub(super) fn half(
    k: &Kernel,
    work: &MeshWork,
    mesh: &TriMesh,
    axis: Vec3,
    height: f64,
    positive: bool,
    epsilon: f64,
) -> Result<Option<TriMesh>> {
    clip_half(k, work, mesh, axis, height, positive, epsilon, None)
}

/// The ONE original clipping/CDT body. The optional recorder observes numeric
/// results; it never chooses geometry, winding, deduplication or native fallback.
#[allow(clippy::too_many_arguments)]
fn clip_half(
    k: &Kernel,
    work: &MeshWork,
    mesh: &TriMesh,
    axis: Vec3,
    height: f64,
    positive: bool,
    epsilon: f64,
    mut trace: Option<&mut TraceRecorder<'_>>,
) -> Result<Option<TriMesh>> {
    let mut out = CutMesh {
        mesh: TriMesh::default(),
        grid: BTreeMap::new(),
        epsilon,
    };
    let sign = if positive { 1. } else { -1. };
    for (parent, t) in mesh.triangles.iter().enumerate() {
        work.spend_core(k, 1)?;
        let first = trace.as_ref().map_or(0, |t| t.data.fragments.len());
        let mut points = Vec::new();
        for &i in t {
            let Some(&p) = mesh.positions.get(i as usize) else {
                return Err(invalid("missing clipping vertex"));
            };
            let d = p.dot(axis) - height;
            points.push(if d.abs() <= epsilon { p - axis * d } else { p });
        }
        if points
            .iter()
            .all(|p| (p.dot(axis) - height).abs() <= epsilon)
        {
            let (Some(a), Some(b), Some(c)) = (points.first(), points.get(1), points.get(2)) else {
                return Ok(None);
            };
            if (*b - *a).cross(*c - *a).dot(axis) * sign < 0. {
                let inserted = out.triangle(*a, *b, *c)?;
                if let Some(trace) = trace.as_mut() {
                    trace.attempt(k, work, parent, [*a, *b, *c], inserted)?;
                }
            }
            if let Some(trace) = trace.as_mut() {
                trace.row(k, work, parent, first, ParentDisposition::Coplanar)?;
            }
            continue;
        }
        let mut polygon = Vec::new();
        for (a, b) in points.iter().zip(points.iter().cycle().skip(1)).take(3) {
            let da = (a.dot(axis) - height) * sign;
            let db = (b.dot(axis) - height) * sign;
            if da >= 0. {
                polygon.push(*a);
            }
            if (da > 0. && db < 0.) || (da < 0. && db > 0.) {
                let p = *a + (*b - *a) * (da / (da - db));
                polygon.push(p - axis * (p.dot(axis) - height));
            }
        }
        polygon.dedup_by(|a, b| a.distance(*b) <= epsilon);
        if polygon.len() > 2
            && polygon
                .first()
                .zip(polygon.last())
                .is_some_and(|(a, b)| a.distance(*b) <= epsilon)
        {
            polygon.pop();
        }
        if let Some(&a) = polygon.first() {
            for (&b, &c) in polygon.iter().skip(1).zip(polygon.iter().skip(2)) {
                let inserted = out.triangle(a, b, c)?;
                if let Some(trace) = trace.as_mut() {
                    trace.attempt(k, work, parent, [a, b, c], inserted)?;
                }
            }
        }
        if let Some(trace) = trace.as_mut() {
            trace.row(k, work, parent, first, ParentDisposition::Clipped)?;
        }
    }
    if out.mesh.triangles.is_empty() {
        return Ok(None);
    }
    let edges = edge_map(&out.mesh);
    let mut next = BTreeMap::new();
    for (&(a, b), uses) in &edges {
        if uses.len() == 2 {
            continue;
        }
        if uses.len() != 1 {
            return Ok(None);
        }
        let (Some(pa), Some(pb)) = (
            out.mesh.positions.get(a as usize),
            out.mesh.positions.get(b as usize),
        ) else {
            return Ok(None);
        };
        if (pa.dot(axis) - height).abs() > epsilon * 4.
            || (pb.dot(axis) - height).abs() > epsilon * 4.
        {
            return Ok(None);
        }
        let Some(&(u, v, _)) = uses.first() else {
            return Ok(None);
        };
        if next.insert(v, u).is_some() {
            return Ok(None);
        }
    }
    if next.len() > MAX_BOUNDARY {
        return Err(invalid("part cap exceeds its boundary budget"));
    }
    let Some(plane) = MeshPlane::from_normal(axis * height, axis) else {
        return Ok(None);
    };
    let mut boundary = Vec::new();
    let mut ids = Vec::new();
    let mut loops = Vec::new();
    while let Some((&start, _)) = next.first_key_value() {
        let from = boundary.len();
        let mut at = start;
        loop {
            let Some(to) = next.remove(&at) else {
                return Ok(None);
            };
            let Some(&p) = out.mesh.positions.get(at as usize) else {
                return Ok(None);
            };
            let p = plane.to_local(p);
            boundary.push([p.x, p.y]);
            ids.push(at);
            at = to;
            if at == start {
                break;
            }
        }
        if boundary.len() - from < 3 {
            return Ok(None);
        }
        loops.push(from..boundary.len());
    }
    if !boundary.is_empty() {
        if let Some(trace) = trace.as_mut() {
            trace.boundary(k, work, &ids, &boundary, &loops)?;
        }
        let Some(triangles) = super::cap::triangulate(&boundary, &loops) else {
            return Ok(None);
        };
        for [a, b, c] in triangles {
            work.spend_core(k, 1)?;
            if let Some(trace) = trace.as_mut() {
                trace.cap(k, work, out.mesh.triangles.len(), [a, b, c])?;
            }
            let (Some(&a), Some(&b), Some(&c)) = (
                ids.get(a as usize),
                ids.get(b as usize),
                ids.get(c as usize),
            ) else {
                return Ok(None);
            };
            out.mesh
                .triangles
                .push(if positive { [a, c, b] } else { [a, b, c] });
        }
    }
    if out.mesh.triangles.len() > MAX_TRIANGLES {
        return Err(invalid("part cap exceeds its triangle budget"));
    }
    if !closed(&out.mesh) {
        return Ok(None);
    }
    Ok(Some(out.mesh))
}

type EdgeUses = BTreeMap<(u32, u32), Vec<(u32, u32, usize)>>;
/// Index oriented edge uses and their owning triangles for closedness and component checks.
fn edge_map(mesh: &TriMesh) -> EdgeUses {
    let mut edges = EdgeUses::new();
    for (i, &[a, b, c]) in mesh.triangles.iter().enumerate() {
        for (a, b) in [(a, b), (b, c), (c, a)] {
            edges
                .entry((a.min(b), a.max(b)))
                .or_default()
                .push((a, b, i));
        }
    }
    edges
}
/// Repair the orientation of a welded mesh, as welding can join previously separate patches.
pub(super) fn orient(mesh: &mut TriMesh) {
    let edges = edge_map(mesh);
    let mut seen = vec![false; mesh.triangles.len()];
    for seed in 0..mesh.triangles.len() {
        let Some(slot @ false) = seen.get_mut(seed) else {
            continue;
        };
        *slot = true;
        let mut stack = vec![seed];
        while let Some(i) = stack.pop() {
            let Some(&[a, b, c]) = mesh.triangles.get(i) else {
                continue;
            };
            for (a, b) in [(a, b), (b, c), (c, a)] {
                let Some([(_, _, left), (_, _, right)]) =
                    edges.get(&(a.min(b), a.max(b))).map(Vec::as_slice)
                else {
                    continue;
                };
                let other = if *left == i { *right } else { *left };
                let Some(slot @ false) = seen.get_mut(other) else {
                    continue;
                };
                *slot = true;
                let Some(triangle) = mesh.triangles.get_mut(other) else {
                    continue;
                };
                let [x, y, z] = *triangle;
                if [(x, y), (y, z), (z, x)].contains(&(a, b)) {
                    *triangle = [x, z, y];
                }
                stack.push(other);
            }
        }
    }
    if mesh.volume() < 0. && closed(mesh) {
        for triangle in &mut mesh.triangles {
            let [a, b, c] = *triangle;
            *triangle = [a, c, b];
        }
    }
}

/// Require each mesh edge to have exactly two uses with opposite winding.
fn closed(mesh: &TriMesh) -> bool {
    edge_map(mesh)
        .values()
        .all(|v| matches!(v.as_slice(),[(a,b,_),(c,d,_)] if a==d && b==c))
}
/// Split edge-connected pieces with compact vertex indices, requiring two uses per edge and bounded component count.
fn components(k: &Kernel, work: &MeshWork, mesh: &TriMesh) -> Result<Option<Vec<TriMesh>>> {
    work.spend_core(k, mesh.triangles.len())?;
    let edges = edge_map(mesh);
    let mut neighbours = vec![Vec::new(); mesh.triangles.len()];
    for uses in edges.values() {
        let [(_, _, a), (_, _, b)] = uses.as_slice() else {
            return Ok(None);
        };
        let Some(n) = neighbours.get_mut(*a) else {
            return Ok(None);
        };
        n.push(*b);
        let Some(n) = neighbours.get_mut(*b) else {
            return Ok(None);
        };
        n.push(*a);
    }
    let mut seen = vec![false; mesh.triangles.len()];
    let mut out = Vec::new();
    for seed in 0..mesh.triangles.len() {
        if seen.get(seed).copied().unwrap_or(true) {
            continue;
        }
        if out.len() >= MAX_COMPONENTS {
            return Err(invalid("too many reconstructed components"));
        }
        let mut part = TriMesh::default();
        let mut remap = BTreeMap::new();
        let mut queue = VecDeque::from([seed]);
        while let Some(i) = queue.pop_front() {
            work.spend_core(k, 1)?;
            let Some(done) = seen.get_mut(i) else {
                return Ok(None);
            };
            if *done {
                continue;
            }
            *done = true;
            let Some(t) = mesh.triangles.get(i) else {
                return Ok(None);
            };
            let mut mapped = [0; 3];
            for (slot, &v) in mapped.iter_mut().zip(t) {
                let id = if let Some(&j) = remap.get(&v) {
                    j
                } else {
                    let Some(&p) = mesh.positions.get(v as usize) else {
                        return Ok(None);
                    };
                    let j = u32::try_from(part.positions.len())
                        .map_err(|_| invalid("component vertex budget"))?;
                    part.positions.push(p);
                    remap.insert(v, j);
                    j
                };
                *slot = id;
            }
            part.triangles.push(mapped);
            if let Some(next) = neighbours.get(i) {
                queue.extend(next.iter().copied());
            }
        }
        out.push(part);
    }
    Ok(Some(out))
}
