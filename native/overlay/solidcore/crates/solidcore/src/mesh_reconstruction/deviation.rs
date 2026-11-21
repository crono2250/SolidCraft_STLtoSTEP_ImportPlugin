//! Diagnostic vertex-distance reduction. This is not the reconstruction acceptance proof.
use super::types::{invalid, Deviation, MeshError, MeshInput, Result};
use crate::math::Vec3;
const MAX_POINTS: usize = 20_000;
const MAX_FACE_POINT_QUERIES: usize = 2_000_000;
/// Retains the original diagnostic report's bounded vertex subset; the certificate uses all
/// source triangles and every trimmed output face independently of this report.
/// Standalone single-job convenience; multi-stage callers share one `MeshWork`.
pub fn deviation_points(
    k: &crate::Kernel,
    input: &MeshInput,
    tolerance: f64,
    faces: usize,
) -> Result<Vec<Vec3>> {
    let work_budget = super::work::MeshWork::new();
    deviation_points_with_work(k, &work_budget, input, tolerance, faces)
}

/// Select the bounded diagnostic vertex subset under the caller's complete-workflow budget.
/// This report preparation does not certify reconstruction acceptance.
pub fn deviation_points_with_work(
    k: &crate::Kernel,
    work_budget: &super::work::MeshWork,
    input: &MeshInput,
    tolerance: f64,
    faces: usize,
) -> Result<Vec<Vec3>> {
    work_budget.check(k)?;
    let answer = (|| {
        super::regions::checked_tolerance(tolerance)?;
        let mesh = super::source::SourceMesh::checked(input)?;
        let step = mesh.positions.len().div_ceil(MAX_POINTS).max(1);
        let points: Vec<_> = mesh.positions.iter().step_by(step).copied().collect();
        if points.is_empty() {
            return Err(invalid("the mesh has no vertices"));
        }
        if faces
            .checked_mul(points.len())
            .is_none_or(|n| n > MAX_FACE_POINT_QUERIES)
        {
            return Err(MeshError::BudgetExceeded {
                stage: "deviation exact face/vertex queries",
                limit: MAX_FACE_POINT_QUERIES,
            });
        }
        k.check_cancelled("mesh_reconstruction::deviation_points")?;
        Ok(points)
    })();
    work_budget.check(k)?;
    answer
}
/// Ops supplies exact trimmed-face query results and explicit point classifications. Unknown
/// distances/classifications refuse instead of silently ignoring a trimmed face.
/// Standalone single-job convenience; multi-stage callers share one `MeshWork`.
pub fn finish_deviation(
    k: &crate::Kernel,
    points: &[Vec3],
    faces: &[Vec<Option<f64>>],
    inside: &[Option<bool>],
    tolerance: f64,
) -> Result<Deviation> {
    let work_budget = super::work::MeshWork::new();
    finish_deviation_with_work(k, &work_budget, points, faces, inside, tolerance)
}

/// Reduce exact trimmed-face distances and classifications into a signed diagnostic report.
/// Unknown query results refuse; the caller retains the same budget across all queries.
pub fn finish_deviation_with_work(
    k: &crate::Kernel,
    work_budget: &super::work::MeshWork,
    points: &[Vec3],
    faces: &[Vec<Option<f64>>],
    inside: &[Option<bool>],
    tolerance: f64,
) -> Result<Deviation> {
    work_budget.check(k)?;
    let answer = (|| {
        super::regions::checked_tolerance(tolerance)?;
        if points.is_empty()
            || points.len() > MAX_POINTS
            || inside.len() != points.len()
            || faces.is_empty()
        {
            return Err(invalid("incomplete deviation inputs"));
        }
        if faces
            .len()
            .checked_mul(points.len())
            .is_none_or(|n| n > MAX_FACE_POINT_QUERIES)
        {
            return Err(MeshError::BudgetExceeded {
                stage: "deviation exact face/vertex queries",
                limit: MAX_FACE_POINT_QUERIES,
            });
        }
        let mut nearest = vec![f64::INFINITY; points.len()];
        for distances in faces {
            k.check_cancelled("mesh_reconstruction::deviation")?;
            if distances.len() != points.len() {
                return Err(invalid("incomplete trimmed-face distance results"));
            }
            for (best, distance) in nearest.iter_mut().zip(distances) {
                let d = distance
                    .filter(|d| d.is_finite() && *d >= 0.)
                    .ok_or_else(|| {
                        invalid("an exact trimmed-face distance could not be determined")
                    })?;
                *best = best.min(d);
            }
        }
        let mut all = Vec::new();
        for ((point, distance), inside) in points.iter().zip(nearest).zip(inside) {
            let inside = inside.ok_or(MeshError::Undecided {
                stage: "deviation point classification",
                work: all.len(),
            })?;
            all.push((
                *point,
                if inside && distance > tolerance * 0.01 {
                    -distance
                } else {
                    distance
                },
            ));
        }
        let n = all.len() as f64;
        let max = all.iter().map(|(_, d)| d.abs()).fold(0., f64::max);
        let mean = all.iter().map(|(_, d)| d.abs()).sum::<f64>() / n;
        let rms = (all.iter().map(|(_, d)| d * d).sum::<f64>() / n).sqrt();
        let within = all.iter().filter(|(_, d)| d.abs() <= tolerance).count() as f64 / n;
        if ![max, mean, rms, within].iter().all(|v| v.is_finite()) {
            return Err(invalid("deviation reduction is not finite"));
        }
        all.sort_by(|a, b| b.1.abs().total_cmp(&a.1.abs()));
        all.truncate(10);
        Ok(Deviation {
            max,
            mean,
            rms,
            within,
            vertices: points.len(),
            worst: all,
        })
    })();
    work_budget.check(k)?;
    answer
}
