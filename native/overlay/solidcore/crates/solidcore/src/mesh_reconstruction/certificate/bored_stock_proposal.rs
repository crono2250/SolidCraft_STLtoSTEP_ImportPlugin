//! Source-only choice of a rectangular blank with coaxial through-hole bands.
//!
//! The numerical circle fits choose a candidate. Original exact planar cells,
//! bore connectivity, complete annular bands, opposite shared rings, retained
//! walls and the canonical Native body all require their own proofs.
//! Deviations: none. Bounded original inventories and one shared MeshWork.

use super::super::numeric::Vec3Numeric;
use super::super::regions::fit_circle;
use super::super::types::{invalid, Result};
use super::super::work::{MeshWork, Work};
use super::radial_band::RadiusLaw;
use super::radial_frame::AxialEndpointProposal;
use super::radial_source::RadialPatchClaim;
use super::source_view::ExactSourceView;
use crate::math::Vec3;
use crate::Kernel;
use std::collections::{BTreeMap, BTreeSet};

pub(crate) struct BoredStockProposal {
    pub(crate) charts: [AxialEndpointProposal; 3],
    pub(crate) bounds: [[f64; 3]; 2],
    /// Lower X, upper X, lower Y, upper Y, lower Z, upper Z.
    pub(crate) planes: [Vec<usize>; 6],
    pub(crate) bores: Vec<AxialBore>,
}
type Cells = Vec<(usize, [u32; 3])>;

fn row(rows: &[[f64; 3]], alias: u32) -> Result<[f64; 3]> {
    rows.get(alias as usize)
        .copied()
        .ok_or_else(|| invalid("retained bore alias is absent"))
}

fn bore_components(k: &Kernel, work: &MeshWork, cells: &[(usize, [u32; 3])]) -> Result<Vec<Cells>> {
    let mut edges = BTreeMap::<[u32; 2], usize>::new();
    let mut graph = vec![Vec::new(); cells.len()];
    for (i, (_, [a, b, c])) in cells.iter().enumerate() {
        for (a, b) in [(*a, *b), (*b, *c), (*c, *a)] {
            work.spend(k, 4096)?;
            work.reserve_cells(k, 8)?;
            let key = [a.min(b), a.max(b)];
            if let Some(other) = edges.insert(key, i) {
                graph
                    .get_mut(i)
                    .ok_or_else(|| invalid("bore adjacency index missing"))?
                    .push(other);
                graph
                    .get_mut(other)
                    .ok_or_else(|| invalid("bore adjacency index missing"))?
                    .push(i);
            }
        }
    }
    let mut seen = vec![false; cells.len()];
    let mut output = Vec::new();
    for i in 0..cells.len() {
        if seen.get(i) == Some(&true) {
            continue;
        }
        work.reserve_cells(k, 2)?;
        let mut stack = vec![i];
        let mut component = Vec::new();
        while let Some(j) = stack.pop() {
            work.spend(k, 8)?;
            let visited = seen
                .get_mut(j)
                .ok_or_else(|| invalid("bore membership index missing"))?;
            if *visited {
                continue;
            }
            *visited = true;
            let cell = cells
                .get(j)
                .ok_or_else(|| invalid("bore cell index missing"))?;
            work.reserve_cells(k, 8)?;
            component.push(*cell);
            let neighbors = graph
                .get(j)
                .ok_or_else(|| invalid("bore adjacency missing"))?;
            stack.extend(neighbors);
        }
        output.push(component);
    }
    Ok(output)
}

pub(crate) struct BoreShoulder {
    pub(crate) after_band: usize,
    pub(crate) triangles: Vec<usize>,
}

pub(crate) struct AxialBore {
    pub(crate) axis: usize,
    pub(crate) bands: Vec<RadialPatchClaim>,
    pub(crate) shoulders: Vec<BoreShoulder>,
}

/// Fit independently at the two ends of each complete axial band. An
/// interior plane can have two radii only when it provides a real annular
/// source group. Exact ring association and the final body remain mandatory.
fn one_bore(
    k: &Kernel,
    w: &MeshWork,
    cells: &Cells,
    rows: &[[f64; 3]],
    axis: usize,
    height: [f64; 2],
    tolerance: f64,
) -> Result<Option<AxialBore>> {
    let mut levels = Vec::new();
    for (_, tri) in cells {
        for &id in tri {
            w.spend(k, 128)?;
            let [_, _, z] = row(rows, id)?;
            if !levels.contains(&z) {
                if levels.len() >= 16 {
                    return Ok(None);
                }
                w.reserve_cells(k, 1)?;
                levels.push(z);
            }
        }
    }
    levels.sort_by(f64::total_cmp);
    if levels.len() < 2 || levels.first() != Some(&height[0]) || levels.last() != Some(&height[1]) {
        return Ok(None);
    }
    let mut stripes = vec![Vec::new(); levels.len() - 1];
    let mut flats = vec![Vec::new(); levels.len()];
    let mut rims: Vec<[BTreeSet<u32>; 2]> = (0..levels.len() - 1)
        .map(|_| [BTreeSet::new(), BTreeSet::new()])
        .collect();
    for (id, tri) in cells {
        let [a, b, c] = *tri;
        let zs = [row(rows, a)?[2], row(rows, b)?[2], row(rows, c)?[2]];
        let lo = zs.into_iter().fold(f64::INFINITY, f64::min);
        let hi = zs.into_iter().fold(f64::NEG_INFINITY, f64::max);
        w.spend(k, 512)?;
        if lo == hi {
            let at = levels
                .iter()
                .position(|v| *v == lo)
                .ok_or_else(|| invalid("lost annular level"))?;
            if at == 0 || at + 1 == levels.len() {
                return Ok(None);
            }
            w.reserve_cells(k, 1)?;
            flats[at].push(*id);
        } else {
            let Some(at) = levels.windows(2).position(|p| p == [lo, hi]) else {
                return Ok(None);
            };
            w.reserve_cells(k, 8)?;
            w.spend(k, 4096)?;
            stripes[at].push(*id);
            for (v, z) in tri.iter().copied().zip(zs) {
                let [first, last] = &mut rims[at];
                if z == lo {
                    first.insert(v);
                } else if z == hi {
                    last.insert(v);
                }
            }
        }
    }
    if stripes.iter().any(Vec::is_empty) {
        return Ok(None);
    }
    let budget = Work::with_budget(k, w)?;
    let fit = |ids: &BTreeSet<u32>| -> Result<Option<(Vec3, f64)>> {
        if ids.len() < 5 {
            return Ok(None);
        }
        w.spend(k, ids.len().saturating_mul(128))?;
        w.reserve_cells(k, ids.len().saturating_mul(3))?;
        let points = ids
            .iter()
            .map(|id| row(rows, *id).map(|[x, y, _]| Vec3::new(x, y, 0.)))
            .collect::<Result<Vec<_>>>()?;
        let result = fit_circle(&points, Vec3::Z, &budget);
        budget.check()?;
        Ok(result.filter(|&(c, r)| r > tolerance && r.is_finite() && c.is_finite()))
    };
    let mut dimensions = Vec::new();
    for [a, b] in &rims {
        let (Some(a), Some(b)) = (fit(a)?, fit(b)?) else {
            return Ok(None);
        };
        dimensions.push([a, b]);
    }
    let total = (2 * dimensions.len()) as f64;
    let centre = dimensions
        .iter()
        .flatten()
        .fold(Vec3::ZERO, |p, (c, _)| p + *c / total);
    if !centre.is_finite()
        || dimensions
            .iter()
            .flatten()
            .any(|(c, _)| c.distance(centre) > tolerance)
    {
        return Ok(None);
    }
    // Using one precomputed radius for a contiguous constant run keeps its
    // joins bit-identical. A real shoulder always starts another radius run.
    let mut logical: Vec<f64> = Vec::new();
    let mut indices: Vec<[usize; 2]> = Vec::new();
    let mut shoulders = Vec::new();
    for (i, [(_, a), (_, b)]) in dimensions.into_iter().enumerate() {
        let join = i > 0 && flats[i].is_empty();
        if join && rims[i - 1][1] != rims[i][0] {
            return Ok(None);
        }
        let start = if join {
            let p = indices[i - 1][1];
            if (logical[p] - a).abs() > tolerance * 0.0001 {
                return Ok(None);
            }
            p
        } else {
            if i > 0 {
                let old = logical[indices[i - 1][1]];
                if (old - a).abs() <= tolerance || !rims[i - 1][1].is_disjoint(&rims[i][0]) {
                    return Ok(None);
                }
                shoulders.push(BoreShoulder {
                    after_band: i - 1,
                    triangles: core::mem::take(&mut flats[i]),
                });
            }
            logical.push(a);
            logical.len() - 1
        };
        let end = if (logical[start] - b).abs() <= tolerance * 0.0001 {
            start
        } else {
            logical.push(b);
            logical.len() - 1
        };
        indices.push([start, end]);
    }
    let bands = stripes
        .into_iter()
        .zip(levels.windows(2))
        .zip(indices)
        .map(|((triangles, levels), [a, b])| RadialPatchClaim {
            triangles,
            center: [centre.x, centre.y],
            concave: true,
            law: RadiusLaw {
                height: [levels[0], levels[1]],
                radius: [logical[a], logical[b]],
            },
        })
        .collect();
    Ok(Some(AxialBore {
        axis,
        bands,
        shoulders,
    }))
}

pub(super) fn axes_for(axis: usize) -> [usize; 3] {
    [(axis + 1) % 3, (axis + 2) % 3, axis]
}

/// Two finite axial bands on different cardinal directions have a common
/// perpendicular coordinate. Strictly disjoint complete projections onto
/// that coordinate keep their entire radial envelopes apart.
pub(super) fn perpendicular_bands_are_separate(
    [axis_a, axis_b]: [usize; 2],
    [a, b]: [&RadialPatchClaim; 2],
    [ea, eb]: [f64; 2],
) -> bool {
    use crate::blend::fillet_section::interval::Ivl;
    if axis_a == axis_b || axis_a > 2 || axis_b > 2 {
        return false;
    }
    let c = 3 - axis_a - axis_b;
    let [Some(ia), Some(ib)] =
        [axis_a, axis_b].map(|ax| axes_for(ax).into_iter().take(2).position(|x| x == c))
    else {
        return false;
    };
    let gap = Ivl::from(a.center[ia]) - Ivl::from(b.center[ib]);
    let gap_lower = if gap.lo > 0. {
        gap.lo
    } else if gap.hi < 0. {
        -gap.hi
    } else {
        0.
    };
    let envelope = Ivl::from(a.law.radius[0].max(a.law.radius[1]))
        + Ivl::from(b.law.radius[0].max(b.law.radius[1]))
        + Ivl::from(ea)
        + Ivl::from(eb);
    gap.is_finite() && envelope.is_finite() && gap_lower > envelope.hi
}

pub(crate) fn propose_rectangular_bored_stock_with_work(
    k: &Kernel,
    w: &MeshWork,
    source: &ExactSourceView<'_, '_>,
    tolerance: f64,
) -> Result<Option<BoredStockProposal>> {
    let mut rows = Vec::new();
    let mut bounds = [[f64::INFINITY; 3], [f64::NEG_INFINITY; 3]];
    for i in 0..source.alias_count() {
        w.spend(k, 16)?;
        w.reserve_cells(k, 3)?;
        let p = source
            .source()
            .position(u32::try_from(i).map_err(|_| invalid("bore alias overflow"))?)
            .ok_or_else(|| invalid("original retained bore alias missing"))?;
        for (j, value) in p.iter().copied().enumerate() {
            bounds[0][j] = bounds[0][j].min(value);
            bounds[1][j] = bounds[1][j].max(value);
        }
        rows.push(p);
    }
    let [lo, hi] = bounds;
    if lo.into_iter().zip(hi).any(|(a, b)| b - a <= 2. * tolerance) {
        return Ok(None);
    }
    let mut planes: [Vec<usize>; 6] = core::array::from_fn(|_| Vec::new());
    let mut inner = Vec::new();
    for (id, [a, b, c]) in source.triangles() {
        w.spend(k, 64)?;
        w.reserve_cells(k, 5)?;
        let points = [row(&rows, a)?, row(&rows, b)?, row(&rows, c)?];
        let plane = (0..6).find(|i| points.iter().all(|p| p[*i / 2] == bounds[*i % 2][*i / 2]));
        if let Some(i) = plane {
            planes[i].push(id);
        } else {
            inner.push((id, [a, b, c]));
        }
    }
    if inner.is_empty() || planes.iter().any(Vec::is_empty) {
        return Ok(None);
    }
    w.reserve_cells(k, inner.len().saturating_mul(5))?;
    let groups = bore_components(k, w, &inner)?;
    if groups.len() > 16 {
        return Ok(None);
    }
    let basis = [[1., 0., 0.], [0., 1., 0.], [0., 0., 1.]];
    let make_chart = |axis: usize| -> Result<AxialEndpointProposal> {
        let axes = axes_for(axis);
        w.reserve_cells(k, rows.len().saturating_mul(3))?;
        w.spend(k, rows.len().saturating_mul(4))?;
        Ok(AxialEndpointProposal {
            origin: [0.; 3],
            columns: axes.map(|j| basis[j]),
            rows: rows.iter().map(|p| axes.map(|j| p[j])).collect(),
        })
    };
    let charts = [make_chart(0)?, make_chart(1)?, make_chart(2)?];
    let mut bores = Vec::new();
    for group in &groups {
        let mut matched = None;
        for axis in [2, 0, 1] {
            if let Some(bore) = one_bore(
                k,
                w,
                group,
                &charts[axis].rows,
                axis,
                [lo[axis], hi[axis]],
                tolerance,
            )? {
                if matched.replace(bore).is_some() {
                    return Ok(None);
                }
            }
        }
        let Some(bore) = matched else {
            return Ok(None);
        };
        bores.push(bore);
    }
    if bores
        .iter()
        .all(|b| b.axis == bores[0].axis && b.bands.len() == 1)
    {
        return Ok(None);
    }
    w.check(k)?;
    Ok(Some(BoredStockProposal {
        charts,
        bounds,
        planes,
        bores,
    }))
}

/// Construct one fixed bordered blank. Each analytic bore band is sewn into
/// the SAME candidate as its adjacent band and the two planar cap annuli.
/// Native topology construction is not a geometry equivalence certificate.
impl BoredStockProposal {
    pub(crate) fn build_candidate(&self, k: &mut Kernel, w: &MeshWork) -> Result<crate::Brep> {
        use crate::curve::{curve::Curve, line::Line};
        use crate::error::EntityRef;
        use crate::geom::{axis2_placement::Axis2Placement, extent2d::Extent2d, tol::USE_DEFAULT};
        use crate::math::Vec2;
        use crate::nurbs::b_spline_surface::SurfParamType;
        use crate::nurbs::b_spline_surface_n_lib::p2::OrientType;
        use crate::query::brep::BrepIdentity;
        use crate::surface::{cone::Cone, plane::Plane, surface::Surface};
        use crate::topology::brep::{
            p2::{caller_cache_key, ArenaNotifyState},
            p3::new_brep,
            p5::{stitch_and_orient_with_identity, StitchAndOrientOptions},
            p7::{make_face_with_curves, FaceCurvesInput},
            p8::{create_face_from_surface, FaceBuildEnv},
        };
        use crate::topology::{Brep, FaceId};

        let [lo, hi] = self.bounds;
        let [u, v, h] = lo;
        let [a, b, t] = hi;
        let bottom = [[u, v, h], [a, v, h], [a, b, h], [u, b, h]].map(Vec3::from_array);
        let top = [[u, v, t], [a, v, t], [a, b, t], [u, b, t]].map(Vec3::from_array);
        let rect = |ring: [Vec3; 4]| -> Result<Vec<Curve>> {
            ring.into_iter()
                .zip(ring.into_iter().cycle().skip(1))
                .map(|(p, q)| Ok(Curve::from(Line::create_line_segment(3, p, q, None)?)))
                .collect()
        };
        let mut caps: [Vec<Curve>; 6] = core::array::from_fn(|_| Vec::new());

        let mut candidate = new_brep(k, USE_DEFAULT, USE_DEFAULT)?;
        let mut notify = ArenaNotifyState::new(&candidate);
        let mut env = notify.env(None);
        let this_face = |id: FaceId| crate::topology::loopuse::notify_ref(EntityRef::Face(id));
        let mut marks = crate::topology::topology_traverser::Marks::default();
        let mut band_faces = Vec::new();
        {
            let mut face_env = FaceBuildEnv {
                env: &mut env,
                marks: &mut marks,
                this_face: &this_face,
            };
            // Bind each face to the exact finite stock chart rather than
            // fitting a plane from rounded 3D curve observations.
            let planar = |k: &mut Kernel,
                          b: &mut Brep,
                          ring: [Vec3; 4],
                          holes: Vec<Curve>,
                          hole_sense: OrientType,
                          env: &mut FaceBuildEnv<'_, '_>|
             -> Result<()> {
                let [p0, p1, _, p3] = ring;
                let x = p1 - p0;
                let y = p3 - p0;
                let ux = x
                    .normalized()
                    .ok_or_else(|| invalid("stock plane lacks its first axis"))?;
                let vy = y
                    .normalized()
                    .ok_or_else(|| invalid("stock plane lacks its second axis"))?;
                let domain = Extent2d::from_bounds(0., 0., x.length(), y.length());
                let plane = Plane::new(p0, ux, vy, Vec2::new(1., 1.), &domain);
                let mut loops = vec![4];
                loops.extend(core::iter::repeat_n(1, holes.len()));
                let mut senses = vec![OrientType::Same; 4];
                senses.extend(core::iter::repeat_n(hole_sense, holes.len()));
                let curves = rect(ring)?.into_iter().chain(holes).map(Some).collect();
                let features = FaceCurvesInput {
                    loops,
                    curves_3d: Some(curves),
                    uv_curves: None,
                    orientations: senses,
                    loop_points: Vec::new(),
                };
                let region = b.infinite_region();
                let made = make_face_with_curves(
                    k,
                    b,
                    region,
                    features,
                    Surface::from(plane),
                    &domain,
                    OrientType::Same,
                    None,
                    env.this_face,
                    env.env,
                )?;
                if made.face.is_none() {
                    return Err(invalid(
                        "bounded stock chart did not make its complete planar face",
                    ));
                }
                Ok(())
            };
            let build_shoulder = |k: &mut Kernel,
                                  body: &mut Brep,
                                  rings: [(f64, Curve); 2],
                                  origin: Vec3,
                                  [x, y]: [Vec3; 2],
                                  env: &mut FaceBuildEnv<'_, '_>|
             -> Result<()> {
                let [(a, first), (b, second)] = rings;
                if !(a > 0. && b > 0. && a != b) {
                    return Err(invalid(
                        "a bore shoulder must have two distinct positive diameters",
                    ));
                }
                let (outer, inner, forward) = if a < b {
                    (second, first, true)
                } else {
                    (first, second, false)
                };
                let cover = 2. * a.max(b);
                let domain = Extent2d::from_bounds(-cover, -cover, cover, cover);
                let orientation = if forward { y } else { -y };
                let plane = Plane::new(origin, x, orientation, Vec2::new(1., 1.), &domain);
                let input = FaceCurvesInput {
                    loops: vec![1, 1],
                    curves_3d: Some(vec![Some(outer), Some(inner)]),
                    uv_curves: None,
                    orientations: if forward {
                        vec![OrientType::Same, OrientType::Opposite]
                    } else {
                        vec![OrientType::Opposite, OrientType::Same]
                    },
                    loop_points: Vec::new(),
                };
                let region = body.infinite_region();
                let made = make_face_with_curves(
                    k,
                    body,
                    region,
                    input,
                    Surface::from(plane),
                    &domain,
                    OrientType::Same,
                    None,
                    env.this_face,
                    env.env,
                )?;
                if made.face.is_none() {
                    return Err(invalid("bore shoulder made no planar annulus"));
                }
                Ok(())
            };
            for hole in &self.bores {
                let [x, y, z] = self.charts[hole.axis].columns.map(Vec3::from_array);
                let world = |[a, b, c]: [f64; 3]| a * x + b * y + c * z;
                let side = hole.axis * 2;
                let mut previous_step_rim = None;
                for (i, band) in hole.bands.iter().enumerate() {
                    w.spend(k, 1024)?;
                    w.reserve_cells(k, 256)?;
                    let [start, end] = band.law.height;
                    let [r, s] = band.law.radius;
                    let [cx, cy] = band.center;
                    let placement = Axis2Placement::new(world([cx, cy, start]), x, y);
                    let cone = if r == s {
                        let mut c = Cone::create_canonical_cylinder(k, &placement, r)?;
                        c.adjust_step_uv_domain(
                            k,
                            &Extent2d::from_bounds(0., 0., 360., end - start),
                        )?;
                        c
                    } else {
                        Cone::create_canonical(k, &placement, r, s, end - start, false, false)?
                    };
                    let uv = cone.rev().base().natural_uv_domain();
                    let rim = |k: &Kernel, level: f64| -> Result<Curve> {
                        Ok(cone
                            .create_iso_parametric_curve(k, SurfParamType::V, level, None, false)?
                            .curve)
                    };
                    if i == 0 {
                        caps[side].push(rim(k, uv.min().y)?);
                    }
                    if i + 1 == hole.bands.len() {
                        caps[side + 1].push(rim(k, uv.max().y)?);
                    }
                    if let Some(last) = previous_step_rim.take() {
                        build_shoulder(
                            k,
                            &mut candidate,
                            [last, (r, rim(k, uv.min().y)?)],
                            world([cx, cy, start]),
                            [x, y],
                            &mut face_env,
                        )?;
                    }
                    if hole.shoulders.iter().any(|p| p.after_band == i) {
                        previous_step_rim = Some((s, rim(k, uv.max().y)?));
                    }
                    let id = create_face_from_surface(
                        k,
                        &mut candidate,
                        Some(Surface::from(cone)),
                        &uv,
                        &mut face_env,
                    )?;
                    band_faces.push(id);
                }
                if previous_step_rim.is_some() {
                    return Err(invalid("bore shoulder was missing its next band"));
                }
            }
            for (i, ((b0, b1), (t0, t1))) in bottom
                .into_iter()
                .zip(bottom.into_iter().cycle().skip(1))
                .zip(top.into_iter().zip(top.into_iter().cycle().skip(1)))
                .enumerate()
            {
                let side = [2, 1, 3, 0][i];
                let sense = if side % 2 == 0 {
                    OrientType::Same
                } else {
                    OrientType::Opposite
                };
                planar(
                    k,
                    &mut candidate,
                    [b0, b1, t1, t0],
                    core::mem::take(&mut caps[side]),
                    sense,
                    &mut face_env,
                )?;
            }
            let [_, _, _, _, lo_holes, hi_holes] = caps;
            let [p0, p1, p2, p3] = bottom;
            planar(
                k,
                &mut candidate,
                [p0, p3, p2, p1],
                lo_holes,
                OrientType::Same,
                &mut face_env,
            )?;
            planar(
                k,
                &mut candidate,
                top,
                hi_holes,
                OrientType::Opposite,
                &mut face_env,
            )?;
        }
        let keys = |object| caller_cache_key(env.key_of, object);
        stitch_and_orient_with_identity(
            k,
            &mut candidate,
            &StitchAndOrientOptions::default(),
            Some(BrepIdentity {
                keys: &keys,
                ..BrepIdentity::default()
            }),
        )?;
        candidate.refresh_cached_topology();
        if !crate::topology::brep::p2::is_manifold_solid(&candidate)? {
            return Err(invalid(
                "axial bore stock was not sewn into one closed solid",
            ));
        }
        crate::topology::brep::p1::set_region_is_void_flags_for_nested_solids(k, &mut candidate)?;
        for face in band_faces {
            super::native_radial_topology::construct_exact_cone_seams_for_face(
                k,
                w,
                &mut candidate,
                face,
            )?;
        }
        w.check(k)?;
        Ok(candidate)
    }
}
