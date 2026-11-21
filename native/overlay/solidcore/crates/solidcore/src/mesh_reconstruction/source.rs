//! Validated source mesh data and bounded source-only welding.
use super::numeric::{Bounds3, Vec3Numeric};
use super::types::{invalid, MeshError, MeshInput, Result};
use crate::math::Vec3;
use std::collections::BTreeMap;
pub(crate) const MAX_TRIANGLES: usize = 200_000;
pub(crate) const MAX_POSITIONS: usize = 600_000;
pub(crate) const MAX_CONVERSION_TRIANGLES: usize = 50_000;
#[derive(Clone, Debug)]
pub(crate) struct SourceMesh {
    pub positions: Vec<Vec3>,
    pub triangles: Vec<[u32; 3]>,
    /// Original triangle ids; welding/removing zero-area faces must not renumber attribution.
    pub source_triangles: Vec<Option<u32>>,
    pub vertex_sources: Vec<Vec<u32>>,
    pub weld_tolerance: f64,
}
impl SourceMesh {
    pub fn checked(input: &MeshInput) -> Result<Self> {
        if input.triangles.len() > MAX_TRIANGLES {
            return Err(MeshError::BudgetExceeded {
                stage: "mesh source triangles",
                limit: MAX_TRIANGLES,
            });
        }
        if input.positions.len() > MAX_POSITIONS {
            return Err(MeshError::BudgetExceeded {
                stage: "mesh source positions",
                limit: MAX_POSITIONS,
            });
        }
        if input
            .positions
            .iter()
            .flatten()
            .any(|x| !x.is_finite() || x.abs() > 1e9)
        {
            return Err(invalid(
                "source coordinates must be finite and within the kernel coordinate budget",
            ));
        }
        if input
            .triangles
            .iter()
            .flatten()
            .any(|i| (*i as usize) >= input.positions.len())
        {
            return Err(invalid("source triangle refers to a missing vertex"));
        }
        Ok(Self {
            positions: input
                .positions
                .iter()
                .copied()
                .map(Vec3::from_array)
                .collect(),
            triangles: input.triangles.clone(),
            vertex_sources: (0..input.positions.len()).map(|i| vec![i as u32]).collect(),
            weld_tolerance: 0.,
            source_triangles: (0..input.triangles.len())
                .map(|i| {
                    u32::try_from(i)
                        .map(Some)
                        .map_err(|_| invalid("source index overflow"))
                })
                .collect::<Result<_>>()?,
        })
    }
    pub fn input(&self) -> MeshInput {
        MeshInput {
            positions: self.positions.iter().map(|p| p.to_array()).collect(),
            triangles: self.triangles.clone(),
        }
    }
}
/// Standalone single-job convenience; multi-stage callers share one `MeshWork`.
pub(crate) fn weld(k: &crate::Kernel, mesh: &SourceMesh, tolerance: f64) -> Result<SourceMesh> {
    let work_budget = super::work::MeshWork::new();
    weld_with_work(k, &work_budget, mesh, tolerance)
}

pub(crate) fn weld_with_work(
    k: &crate::Kernel,
    work_budget: &super::work::MeshWork,
    mesh: &SourceMesh,
    tolerance: f64,
) -> Result<SourceMesh> {
    work_budget.check(k)?;
    let answer = (|| {
        if mesh.triangles.len() > MAX_CONVERSION_TRIANGLES {
            return Err(MeshError::InputLimit {
                stage: "mesh_reconstruction::weld",
                count: mesh.triangles.len(),
                limit: MAX_CONVERSION_TRIANGLES,
                unit: "triangles",
            });
        }
        if mesh.positions.len() > MAX_CONVERSION_TRIANGLES * 3 {
            return Err(invalid(&format!(
                "the mesh has {} vertices, more than the {} conversion can take",
                mesh.positions.len(),
                MAX_CONVERSION_TRIANGLES * 3
            )));
        }
        let work = super::work::Work::with_budget(k, work_budget)?;
        let bounds = mesh.positions.iter().fold(Bounds3::new(), |mut b, p| {
            b.add_point(*p);
            b
        });
        let epsilon = (bounds.size().len().max(1.) * 1e-7)
            .min(tolerance * 0.01)
            .max(1e-9);
        if !epsilon.is_finite()
            || mesh.positions.iter().any(|p| {
                [p.x, p.y, p.z]
                    .iter()
                    .any(|v| !v.is_finite() || (v / epsilon).abs() > 1e15)
            })
        {
            return Err(invalid("mesh coordinates exceed the conversion budget"));
        }
        let key = |p: Vec3| {
            (
                (p.x / epsilon).floor() as i64,
                (p.y / epsilon).floor() as i64,
                (p.z / epsilon).floor() as i64,
            )
        };
        let mut grid = BTreeMap::<_, Vec<u32>>::new();
        let mut positions: Vec<Vec3> = Vec::new();
        let mut remap = Vec::new();
        let mut comparisons = 0usize;
        for &p in &mesh.positions {
            work.spend(1)?;
            let k = key(p);
            let mut found = None;
            for dx in -1..=1 {
                for dy in -1..=1 {
                    for dz in -1..=1 {
                        for &i in grid
                            .get(&(k.0 + dx, k.1 + dy, k.2 + dz))
                            .into_iter()
                            .flatten()
                        {
                            work.spend(1)?;
                            comparisons += 1;
                            if comparisons > 8_000_000 {
                                return Err(invalid("vertex welding exceeds its work budget"));
                            }
                            if positions
                                .get(i as usize)
                                .is_some_and(|q| q.dist(p) <= epsilon)
                            {
                                found = Some(i);
                                break;
                            }
                        }
                    }
                }
            }
            let i = if let Some(i) = found {
                i
            } else {
                let i = u32::try_from(positions.len()).map_err(|_| invalid("too many vertices"))?;
                positions.push(p);
                grid.entry(k).or_default().push(i);
                i
            };
            remap.push(i);
        }
        let mut aliases = vec![Vec::new(); positions.len()];
        let mut total_aliases = 0usize;
        for (old, new) in remap.iter().enumerate() {
            let source = mesh
                .vertex_sources
                .get(old)
                .ok_or_else(|| invalid("missing raw vertex aliases"))?;
            total_aliases = total_aliases.saturating_add(source.len());
            if total_aliases > MAX_POSITIONS {
                return Err(MeshError::BudgetExceeded {
                    stage: "weld source alias references",
                    limit: MAX_POSITIONS,
                });
            }
            aliases
                .get_mut(*new as usize)
                .ok_or_else(|| invalid("missing welded vertex aliases"))?
                .extend_from_slice(source);
        }
        let mut kept_aliases = Vec::new();
        // A triangle of no area (its corners on one line, or welded into one another) adds no
        // surface, so it is dropped rather than refused (#4561); the closed-manifold check that
        // follows still refuses a mesh that needed it to close. Only the vertices the kept triangles
        // use stay, so a dropped triangle's corner cannot widen the part's extent.
        let mut used: Vec<Option<u32>> = vec![None; positions.len()];
        let mut kept_positions: Vec<Vec3> = Vec::new();
        let mut triangles = Vec::new();
        let mut source_triangles = Vec::new();
        for (source_index, t) in mesh.triangles.iter().enumerate() {
            work.spend(1)?;
            let (Some(&a), Some(&b), Some(&c)) = (
                remap.get(t[0] as usize),
                remap.get(t[1] as usize),
                remap.get(t[2] as usize),
            ) else {
                return Err(invalid("missing triangle vertex"));
            };
            let (Some(&pa), Some(&pb), Some(&pc)) = (
                positions.get(a as usize),
                positions.get(b as usize),
                positions.get(c as usize),
            ) else {
                return Err(invalid("missing triangle vertex"));
            };
            if (pb - pa).cross(pc - pa).normalized().is_none() {
                continue;
            }
            let mut keep = |i: u32| -> Result<u32> {
                let slot = used
                    .get_mut(i as usize)
                    .ok_or_else(|| invalid("missing triangle vertex"))?;
                if let Some(k) = *slot {
                    return Ok(k);
                }
                let k = u32::try_from(kept_positions.len())
                    .map_err(|_| invalid("too many vertices"))?;
                kept_positions.push(
                    positions
                        .get(i as usize)
                        .copied()
                        .ok_or_else(|| invalid("missing triangle vertex"))?,
                );
                kept_aliases.push(
                    aliases
                        .get(i as usize)
                        .cloned()
                        .ok_or_else(|| invalid("missing kept vertex aliases"))?,
                );
                *slot = Some(k);
                Ok(k)
            };
            triangles.push([keep(a)?, keep(b)?, keep(c)?]);
            source_triangles.push(
                mesh.source_triangles
                    .get(source_index)
                    .copied()
                    .ok_or_else(|| invalid("missing source triangle attribution"))?,
            );
        }
        if triangles.is_empty() {
            return Err(invalid("the mesh has no triangle of any area"));
        }
        Ok(SourceMesh {
            positions: kept_positions,
            triangles,
            source_triangles,
            vertex_sources: kept_aliases,
            weld_tolerance: epsilon,
        })
    })();
    work_budget.check(k)?;
    answer
}

impl SourceMesh {
    pub fn weld_claim(&self) -> super::types::WeldClaim {
        super::types::WeldClaim {
            vertices: self
                .positions
                .iter()
                .zip(&self.vertex_sources)
                .map(|(p, ids)| super::types::WeldVertexClaim {
                    position: p.to_array(),
                    raw_vertices: ids.clone(),
                })
                .collect(),
            triangles: self.triangles.clone(),
            original_triangles: self.source_triangles.clone(),
            tolerance: self.weld_tolerance,
        }
    }
}

/// Source count policy used before copying application or record geometry arrays.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InputPurpose {
    /// Solid conversion, including the source-only weld and correspondence stages.
    Conversion,
    /// Recognition, fitting, alignment and outlines that use the same weld policy.
    Recognition,
    /// Direct deviation queries over raw indexed geometry, without conversion welding.
    Deviation,
}

/// Check source counts without inspecting or materializing any geometry arrays.
/// This is admission only; it does not prove valid indices, finite data or geometry.
///
/// # Errors
/// Returns the actual count, limit and entity unit when the selected policy is exceeded.
pub fn admit_input_counts(purpose: InputPurpose, vertices: usize, triangles: usize) -> Result<()> {
    let (stage, triangle_limit, vertex_limit) = match purpose {
        InputPurpose::Conversion => (
            "mesh conversion",
            MAX_CONVERSION_TRIANGLES,
            MAX_CONVERSION_TRIANGLES * 3,
        ),
        InputPurpose::Recognition => (
            "mesh recognition",
            MAX_CONVERSION_TRIANGLES,
            MAX_CONVERSION_TRIANGLES * 3,
        ),
        InputPurpose::Deviation => ("mesh deviation", MAX_TRIANGLES, MAX_POSITIONS),
    };
    for (count, limit, unit) in [
        (triangles, triangle_limit, "triangles"),
        (vertices, vertex_limit, "vertices"),
    ] {
        if count > limit {
            return Err(MeshError::InputLimit {
                stage,
                count,
                limit,
                unit,
            });
        }
    }
    Ok(())
}

/// Admit and charge source materialization to the same complete workflow budget.
/// Call this before copying record arrays into native arrays, not after the allocation.
///
/// # Errors
/// Input count, shared workflow work/cell exhaustion, or native cancellation.
pub fn admit_input_counts_with_work(
    k: &crate::Kernel,
    work: &super::MeshWork,
    purpose: InputPurpose,
    vertices: usize,
    triangles: usize,
) -> Result<()> {
    work.check(k)?;
    admit_input_counts(purpose, vertices, triangles)?;
    // Admission limits bound this sum by 800,000 even for usize::MAX inputs.
    let count = vertices.saturating_add(triangles);
    work.spend(k, count)?;
    work.reserve_cells(k, count)?;
    work.check(k)
}

pub(crate) fn admit_conversion(input: &MeshInput) -> Result<()> {
    admit_input_counts(
        InputPurpose::Conversion,
        input.positions.len(),
        input.triangles.len(),
    )
}
