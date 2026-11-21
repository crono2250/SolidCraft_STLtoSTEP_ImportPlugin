//! Conversion preflight and source-only candidate input preparation.
use super::numeric::Vec3Numeric;
use super::source::{weld_with_work, SourceMesh};
use super::types::{invalid, MeshInput, MeshPick, PrimitiveTool, Result};
use crate::math::Vec3;
use std::collections::BTreeMap;
#[derive(Clone, Debug)]
/// Original source and separate construction-planning candidates.
pub struct PreparedMesh {
    /// Exact original arrays, preserved before welding or snapping.
    pub original: MeshInput,
    /// Welded/snapped planning input; never the final acceptance reference.
    pub candidate: MeshInput,
    /// Candidate extrusion directions in deterministic priority order.
    pub axes: Vec<Vec3>,
    /// Recognised primitive cutting-tool candidates.
    pub features: Vec<PrimitiveTool>,
    /// Untrusted source correspondence claims for independent verification.
    pub provenance: super::types::ReconstructionProvenance,
    /// Untrusted source alias and retained-triangle claims.
    pub weld: super::types::WeldClaim,
}
/// Standalone single-job convenience; multi-stage callers share one `MeshWork`.
pub fn prepare_conversion(
    k: &crate::Kernel,
    input: &MeshInput,
    tolerance: f64,
    picks: &[MeshPick],
) -> Result<PreparedMesh> {
    let work_budget = super::work::MeshWork::new();
    prepare_conversion_with_work(k, &work_budget, input, tolerance, picks)
}

/// Validate raw source and prepare separate construction candidates using the same complete-workflow budget.
pub fn prepare_conversion_with_work(
    k: &crate::Kernel,
    work_budget: &super::work::MeshWork,
    input: &MeshInput,
    tolerance: f64,
    picks: &[MeshPick],
) -> Result<PreparedMesh> {
    work_budget.check(k)?;
    let answer = (|| {
        super::regions::checked_tolerance(tolerance)?;
        super::source::admit_conversion(input)?;
        if picks.len() > 10_000 || picks.iter().any(|p| p.point.iter().any(|x| !x.is_finite())) {
            return Err(invalid("picks must be finite points, at most10000"));
        }
        work_budget.spend(
            k,
            input
                .positions
                .len()
                .saturating_add(input.triangles.len().saturating_mul(3)),
        )?;
        let checked = SourceMesh::checked(input)?;
        let original = weld_with_work(k, work_budget, &checked, tolerance)?;
        let native_picks: Vec<_> = picks
            .iter()
            .map(|p| (Vec3::from_array(p.point), p.kind))
            .collect();
        let (candidate, features) = if picks.is_empty() {
            (original.clone(), super::types::Features::default())
        } else {
            super::snap::snap_to_picks_with_work(
                k,
                work_budget,
                &original,
                tolerance,
                &native_picks,
            )?
        };
        work_budget.reserve_output(
            k,
            features
                .solids
                .iter()
                .fold(0usize, |n, f| n.saturating_add(f.source_triangles.len())),
        )?;
        let mesh = &candidate;
        k.check_cancelled("mesh_reconstruction::prepare")?;
        let mut edges: BTreeMap<(u32, u32), (usize, i32)> = BTreeMap::new();
        let mut axes: BTreeMap<(i64, i64, i64), (Vec3, f64)> = BTreeMap::new();
        for triangle in &mesh.triangles {
            let [a, b, c] = *triangle;
            let (Some(pa), Some(pb), Some(pc)) = (
                mesh.positions.get(a as usize),
                mesh.positions.get(b as usize),
                mesh.positions.get(c as usize),
            ) else {
                return Err(invalid("triangle refers to a missing vertex"));
            };
            let cross = (*pb - *pa).cross(*pc - *pa);
            for (a, b) in [(a, b), (b, c), (c, a)] {
                let entry = edges.entry((a.min(b), a.max(b))).or_default();
                entry.0 += 1;
                entry.1 += if a < b { 1 } else { -1 };
            }
            // A zero-area sliver (common in exported meshes) still closes the mesh, but has
            // no direction of its own.
            let Some(mut n) = cross.normalized() else {
                continue;
            };
            if n.x < -1e-8
                || (n.x.abs() <= 1e-8 && (n.y < -1e-8 || (n.y.abs() <= 1e-8 && n.z < 0.)))
            {
                n = -n;
            }
            let key = (
                (n.x * 1e7).round() as i64,
                (n.y * 1e7).round() as i64,
                (n.z * 1e7).round() as i64,
            );
            let entry = axes.entry(key).or_insert((n, 0.));
            entry.1 += cross.len();
        }
        if edges
            .values()
            .any(|&(count, balance)| count != 2 || balance != 0)
        {
            return Err(invalid(
                "mesh must be closed and consistently oriented, with two triangles per edge",
            ));
        }
        let mut axes: Vec<_> = axes.into_values().collect();
        axes.sort_by(|a, b| b.1.total_cmp(&a.1));

        Ok(PreparedMesh {
            original: input.clone(),
            candidate: candidate.input(),
            axes: axes.into_iter().take(16).map(|(axis, _)| axis).collect(),
            provenance: super::types::ReconstructionProvenance {
                faceted_source_patches: Vec::new(),
                patches: features.patches,
                original_cap_loops: Vec::new(),
                cap_loop_parents: Vec::new(),
            },
            weld: original.weld_claim(),
            features: features.solids,
        })
    })();
    work_budget.check(k)?;
    answer
}
/// Standalone single-job convenience; multi-stage callers share one `MeshWork`.
pub fn prismatic_plans(
    k: &crate::Kernel,
    prepared: &PreparedMesh,
    tolerance: f64,
) -> Result<Vec<super::prismatic::PrismaticPlan>> {
    let work_budget = super::work::MeshWork::new();
    prismatic_plans_with_work(k, &work_budget, prepared, tolerance)
}

/// Plan supported constant-section reconstructions without accepting a body using the same complete-workflow budget.
pub fn prismatic_plans_with_work(
    k: &crate::Kernel,
    work_budget: &super::work::MeshWork,
    prepared: &PreparedMesh,
    tolerance: f64,
) -> Result<Vec<super::prismatic::PrismaticPlan>> {
    work_budget.check(k)?;
    let answer = (|| {
        if !prepared.features.is_empty() {
            return Ok(Vec::new());
        }
        let mesh = SourceMesh::checked(&prepared.candidate)?;
        let mut plans = Vec::new();
        for axis in &prepared.axes {
            if let Some(plan) =
                super::prismatic::extrusion_with_work(k, work_budget, &mesh, *axis, tolerance)?
            {
                plans.push(plan);
            }
        }
        Ok(plans)
    })();
    work_budget.check(k)?;
    answer
}
