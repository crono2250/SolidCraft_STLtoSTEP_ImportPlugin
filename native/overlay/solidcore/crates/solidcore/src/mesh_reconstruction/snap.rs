//! Candidate-only snapping and picked-feature extraction. Final certificate uses original input.
use super::numeric::Vec3Numeric;
use super::regions::Ctx;
use super::source::SourceMesh;
use super::types::{
    invalid, MeshRegion, Primitive, PrimitiveTool, Result, SourcePatch, SurfaceKind,
};
use crate::math::Vec3;
/// Standalone single-job convenience; multi-stage callers share one `MeshWork`.
pub(crate) fn snap_to_picks(
    k: &crate::Kernel,
    mesh: &SourceMesh,
    tolerance: f64,
    picks: &[(Vec3, SurfaceKind)],
) -> Result<(SourceMesh, super::types::Features)> {
    let work_budget = super::work::MeshWork::new();
    snap_to_picks_with_work(k, &work_budget, mesh, tolerance, picks)
}

pub(crate) fn snap_to_picks_with_work(
    k: &crate::Kernel,
    work_budget: &super::work::MeshWork,
    mesh: &SourceMesh,
    tolerance: f64,
    picks: &[(Vec3, SurfaceKind)],
) -> Result<(SourceMesh, super::types::Features)> {
    work_budget.check(k)?;
    let answer = (|| {
        let ctx = Ctx::new_with_work(mesh, k, work_budget)?;
        let n = ctx.triangles.len();
        let mut claimed = vec![false; n];
        let mut regions: Vec<MeshRegion> = Vec::new();
        for (i, (point, kind)) in picks.iter().enumerate() {
            let nearest = ctx.nearest(*point);
            ctx.work.check()?;
            let seed = nearest.ok_or_else(|| invalid("empty mesh"))?;
            if claimed.get(seed as usize).copied().unwrap_or(true) {
                // A second pick on a region already recognised.
                continue;
            }
            let grown = super::regions::grow(&ctx, seed, *kind, tolerance, &claimed);
            ctx.work.check()?;
            let region = grown.ok_or_else(|| {
                let what = match kind {
                    SurfaceKind::Auto => "no plane, cylinder, cone, sphere or torus",
                    SurfaceKind::Plane => "no plane",
                    SurfaceKind::Cylinder => "no cylinder",
                    SurfaceKind::Cone => "no cone",
                    SurfaceKind::Sphere => "no sphere",
                    SurfaceKind::Torus => "no torus",
                };
                invalid(&format!(
                    "pick {}: {what} fits the mesh there within {tolerance} mm",
                    i + 1
                ))
            })?;
            for t in &region.triangles {
                if let Some(c) = claimed.get_mut(*t as usize) {
                    *c = true;
                }
            }
            regions.push(region);
        }
        super::regions::regularize(&mut regions, tolerance);
        let mut on: Vec<Vec<usize>> = vec![Vec::new(); mesh.positions.len()];
        for (r, region) in regions.iter().enumerate() {
            for t in &region.triangles {
                for v in ctx.triangles.get(*t as usize).copied().unwrap_or([0, 0, 0]) {
                    if let Some(list) = on.get_mut(v as usize) {
                        if !list.contains(&r) {
                            list.push(r);
                        }
                    }
                }
            }
        }
        let mut positions = mesh.positions.clone();
        for (p, surfaces) in positions.iter_mut().zip(&on) {
            ctx.work
                .spend(surfaces.len().saturating_mul(12).saturating_add(1))?;
            // Cones and spheres are cut as solids of their own; their vertices need not move.
            if surfaces.is_empty()
                || surfaces.iter().any(|r| {
                    regions.get(*r).is_none_or(|g| {
                        matches!(g.surface, Primitive::Cone { .. } | Primitive::Sphere { .. })
                    })
                })
            {
                continue;
            }
            let start = *p;
            let mut q = start;
            // Alternating projections settle on the surfaces' common points.
            for _ in 0..12 {
                for r in surfaces {
                    if let Some(region) = regions.get(*r) {
                        q = region.surface.project(q);
                    }
                }
            }
            if q.is_finite() && q.dist(start) <= tolerance * 2. {
                *p = q;
            }
        }
        // A facet the moves would flatten keeps its corners where they were.
        for _ in 0..4 {
            let mut reverted = false;
            for t in &mesh.triangles {
                let [a, b, c] = t.map(|i| positions.get(i as usize).copied().unwrap_or(Vec3::ZERO));
                if (b - a).cross(c - a).len() <= 1e-12 * (1. + a.len2()) {
                    for i in t {
                        if let (Some(p), Some(o)) = (
                            positions.get_mut(*i as usize),
                            mesh.positions.get(*i as usize),
                        ) {
                            if *p != *o {
                                *p = *o;
                                reverted = true;
                            }
                        }
                    }
                }
            }
            if !reverted {
                break;
            }
        }
        // Cones and spheres leave the mesh: each region is replaced by a fan over its rim, which
        // fills a drill point up to its bore's floor and a dimple up to its face. What is left is
        // milled; the cones and spheres are cut from it afterwards.
        let mut triangles: Vec<[u32; 3]> = Vec::new();
        let mut source_triangles = Vec::new();
        let mut vertex_sources = mesh.vertex_sources.clone();
        let mut patches = Vec::new();
        for region in &regions {
            patches.push(SourcePatch {
                surface: region.surface,
                source_triangles: super::regions::source_triangle_ids(&ctx, &region.triangles)?,
                oriented_rims: patch_rims(&ctx, &region.triangles)?,
                concave: region.concave,
            });
        }
        let mut solids = Vec::new();
        let mut removed = vec![false; n];
        for region in &regions {
            if matches!(
                region.surface,
                Primitive::Cone { .. } | Primitive::Sphere { .. }
            ) {
                for t in &region.triangles {
                    if let Some(r) = removed.get_mut(*t as usize) {
                        *r = true;
                    }
                }
                solids.push(PrimitiveTool {
                    surface: region.surface,
                    points: super::regions::vertices(&ctx, &region.triangles),
                    concave: region.concave,
                    source_triangles: super::regions::source_triangle_ids(&ctx, &region.triangles)?,
                });
            }
        }
        let mut rim = std::collections::BTreeMap::<(u32, u32), i32>::new();
        for (t, tri) in mesh.triangles.iter().enumerate() {
            if !removed.get(t).copied().unwrap_or(false) {
                triangles.push(*tri);
                source_triangles.push(mesh.source_triangles.get(t).copied().flatten());
                continue;
            }
            let [a, b, c] = *tri;
            for (p, q) in [(a, b), (b, c), (c, a)] {
                *rim.entry((p, q)).or_default() += 1;
                *rim.entry((q, p)).or_default() -= 1;
            }
        }
        // Rim edges, in the removed triangles' direction: one fan per loop, around its centre.
        let mut next = std::collections::BTreeMap::<u32, u32>::new();
        for (&(p, q), &k) in &rim {
            if k > 0 && next.insert(p, q).is_some() {
                return Err(invalid(
                    "a picked cone or sphere touches itself at a vertex",
                ));
            }
        }
        while let Some((&start, _)) = next.first_key_value() {
            let mut ring = vec![start];
            let mut current = start;
            loop {
                let Some(to) = next.remove(&current) else {
                    return Err(invalid("the rim of a picked cone or sphere is not closed"));
                };
                if to == start {
                    break;
                }
                ring.push(to);
                current = to;
            }
            let centre = ring.iter().fold(Vec3::ZERO, |s, i| {
                s + positions.get(*i as usize).copied().unwrap_or(Vec3::ZERO)
            }) / ring.len().max(1) as f64;
            let c = u32::try_from(positions.len()).map_err(|_| invalid("too many vertices"))?;
            positions.push(centre);
            vertex_sources.push(Vec::new());
            for (k, a) in ring.iter().enumerate() {
                let b = ring.get((k + 1) % ring.len()).copied().unwrap_or(*a);
                triangles.push([*a, b, c]);
                source_triangles.push(None);
            }
        }
        Ok((
            SourceMesh {
                positions,
                triangles,
                source_triangles,
                vertex_sources,
                weld_tolerance: mesh.weld_tolerance,
            },
            super::types::Features { solids, patches },
        ))
    })();
    work_budget.check(k)?;
    answer
}

/// Rim edges index the welded vertex alias table, not raw arrays. The certificate receives
/// both this directed incidence and the alias classes and must verify their correspondence.
fn patch_rims(ctx: &Ctx<'_>, triangles: &[u32]) -> Result<Vec<Vec<(u32, u32)>>> {
    let mut uses = std::collections::BTreeMap::<(u32, u32), i32>::new();
    for triangle in triangles {
        let [a, b, c] = ctx
            .triangles
            .get(*triangle as usize)
            .copied()
            .ok_or_else(|| invalid("missing patch triangle"))?;
        for (a, b) in [(a, b), (b, c), (c, a)] {
            *uses.entry((a, b)).or_default() += 1;
            *uses.entry((b, a)).or_default() -= 1;
        }
    }
    let mut next = std::collections::BTreeMap::new();
    for ((a, b), count) in uses {
        if count > 0 && next.insert(a, b).is_some() {
            return Err(invalid("ambiguous patch rim incidence"));
        }
    }
    let mut rims = Vec::new();
    while let Some((&start, _)) = next.first_key_value() {
        let mut rim = Vec::new();
        let mut current = start;
        loop {
            let to = next
                .remove(&current)
                .ok_or_else(|| invalid("open patch rim"))?;
            rim.push((current, to));
            if to == start {
                break;
            }
            current = to;
        }
        rims.push(rim);
    }
    Ok(rims)
}
