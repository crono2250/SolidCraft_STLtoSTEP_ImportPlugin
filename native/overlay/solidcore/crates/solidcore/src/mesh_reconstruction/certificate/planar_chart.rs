//! Complete oriented embedded piecewise-affine UV charts, not samples (not upstream).
//! Every chosen f64 UV vertex defines an exact parameter point. All full triangles
//! have the requested strict orientation, and complete pairwise simplex-intersection
//! proofs exclude every undeclared crossing/overlap/touch. Thus the exact source
//! patch complex has an injective planar chart. Final native trim correspondence,
//! full Plane band bounds and material gluing are separate mandatory consumers.
//! Deviations: none. Iterative BVH, 50000 triangles, 1M pairs, shared `MeshWork`.
use super::super::work::MeshWork;
use super::exact_geometry as x;
use super::source_index::SourceIndex;
use super::source_topology::{simplex_only, vertex_cones_separated};
use crate::math::Point3;
use crate::{Kernel, Result};
use std::collections::BTreeSet;
pub(crate) struct PlanarChart<'a> {
    _positions: &'a [[f64; 3]],
    _triangles: &'a [[u32; 3]],
}
pub(crate) enum PlanarChartCover<'a> {
    Proven(PlanarChart<'a>),
    Undecided(&'static str),
}
pub(crate) fn planar_chart_with_work<'a>(
    k: &Kernel,
    work: &MeshWork,
    positions: &'a [[f64; 3]],
    triangles: &'a [[u32; 3]],
    sense: i32,
) -> Result<PlanarChartCover<'a>> {
    macro_rules! refuse {
        ($why:expr) => {
            return Ok(PlanarChartCover::Undecided($why))
        };
    }
    work.spend_core(k, 0)?;
    if triangles.is_empty() || triangles.len() > 50000 || ![-1, 1].contains(&sense) {
        refuse!("UV chart input counts/orientation are invalid");
    }
    let mut points = BTreeSet::new();
    for p in positions {
        work.spend_core(k, 1)?;
        if !p.iter().all(|c| c.is_finite()) || p[2] != 0. {
            refuse!("a UV chart point is not an exact finite planar coordinate");
        }
        let key = p.map(|c| if c == 0. { 0 } else { c.to_bits() });
        if !points.insert(key) {
            refuse!("distinct source vertices have coincident chosen UV coordinates");
        }
    }
    for i in 0..triangles.len() {
        work.spend_core(k, 1)?;
        let Some([a, b, c]) = x::raw_triangle(positions, triangles, i) else {
            refuse!("a chosen UV triangle is missing");
        };
        let orientation = x::point(a)
            .and_then(|a| {
                x::cross(
                    &x::difference(&x::point(b)?, &a)?,
                    &x::difference(&x::point(c)?, &a)?,
                )
            })
            .and_then(|n| x::sign(&n[2]));
        if orientation.is_none_or(|s| s * sense <= 0) {
            refuse!("a whole UV triangle degenerates or reverses");
        }
    }
    let first = positions.first().copied().unwrap_or([0.; 3]);
    let index = SourceIndex::new(
        k,
        work,
        positions,
        triangles,
        Point3::new(first[0], first[1], 0.),
    )?;
    let mut broad = 4_000_000usize;
    let mut pairs = 0usize;
    for i in 0..triangles.len() {
        work.spend_core(k, 1)?;
        let Some(candidates) = index.overlapping_later(k, work, i, &mut broad)? else {
            refuse!("UV chart broad-phase budget is exhausted");
        };
        for j in candidates {
            work.spend_core(k, 1)?;
            if pairs >= 1_000_000 {
                refuse!("UV chart pair-proof budget is exhausted");
            }
            pairs += 1;
            let (Some(&a), Some(&b)) = (triangles.get(i), triangles.get(j)) else {
                refuse!("a complete UV triangle pair is missing");
            };
            let common = a.iter().filter(|id| b.contains(id)).count();
            let separated = if common == 1 {
                work.spend_core(k, 256)?;
                let (Some(aa), Some(bb)) = (
                    x::raw_triangle(positions, triangles, i),
                    x::raw_triangle(positions, triangles, j),
                ) else {
                    refuse!("a UV chart pair is missing");
                };
                vertex_cones_separated(k, work, aa, a, bb, b)?
            } else {
                simplex_only(&index.triangle(i)?, a, &index.triangle(j)?, b)
            };
            if !separated {
                refuse!("complete UV cells meet beyond their common source simplex");
            }
        }
    }
    work.spend_core(k, 0)?;
    Ok(PlanarChartCover::Proven(PlanarChart {
        _positions: positions,
        _triangles: triangles,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::KernelOptions;
    #[test]
    fn whole_embedded_annulus_keeps_a_hole_without_point_classification() {
        let k = Kernel::new(&KernelOptions::default());
        let work = MeshWork::new();
        let p = vec![
            [0., 0., 0.],
            [4., 0., 0.],
            [4., 4., 0.],
            [0., 4., 0.],
            [1., 1., 0.],
            [3., 1., 0.],
            [3., 3., 0.],
            [1., 3., 0.],
        ];
        let t = vec![
            [0, 1, 5],
            [0, 5, 4],
            [1, 2, 6],
            [1, 6, 5],
            [2, 3, 7],
            [2, 7, 6],
            [3, 0, 4],
            [3, 4, 7],
        ];
        assert!(matches!(
            planar_chart_with_work(&k, &work, &p, &t, 1).unwrap(),
            PlanarChartCover::Proven(_)
        ));
    }
    #[test]
    fn positive_triangles_can_still_cross_between_their_corners() {
        let k = Kernel::new(&KernelOptions::default());
        let work = MeshWork::new();
        let p = vec![
            [0., 0., 0.],
            [2., 0., 0.],
            [1., 2., 0.],
            [0., 1., 0.],
            [1., -1., 0.],
            [2., 1., 0.],
        ];
        let t = vec![[0, 1, 2], [3, 4, 5]];
        assert!(matches!(
            planar_chart_with_work(&k, &work, &p, &t, 1).unwrap(),
            PlanarChartCover::Undecided(_)
        ));
    }
}
