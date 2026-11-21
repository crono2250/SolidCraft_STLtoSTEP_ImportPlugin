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
    pub(crate) chart: AxialEndpointProposal,
    pub(crate) bounds: [[f64; 3]; 2],
    /// Lower X, upper X, lower Y, upper Y, lower Z, upper Z.
    pub(crate) planes: [Vec<usize>; 6],
    pub(crate) bores: Vec<Vec<RadialPatchClaim>>,
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

fn one_bore(
    k: &Kernel,
    w: &MeshWork,
    cells: &Cells,
    rows: &[[f64; 3]],
    height: [f64; 2],
    tolerance: f64,
) -> Result<Option<Vec<RadialPatchClaim>>> {
    let mut stations = Vec::<(f64, BTreeSet<u32>)>::new();
    for (_, aliases) in cells {
        for &alias in aliases {
            w.spend(k, 4096)?;
            w.reserve_cells(k, 4)?;
            let [_, _, z] = row(rows, alias)?;
            match stations.iter_mut().find(|(level, _)| *level == z) {
                Some((_, ring)) => {
                    ring.insert(alias);
                }
                None => {
                    if stations.len() == 16 {
                        return Ok(None);
                    }
                    stations.push((z, BTreeSet::from([alias])));
                }
            }
        }
    }
    stations.sort_by(|a, b| a.0.total_cmp(&b.0));
    if stations.len() < 2
        || stations.first().map(|s| s.0) != Some(height[0])
        || stations.last().map(|s| s.0) != Some(height[1])
    {
        return Ok(None);
    }
    let budget = Work::with_budget(k, w)?;
    let mut circles = Vec::new();
    for (z, ring) in &stations {
        if ring.len() < 5 {
            return Ok(None);
        }
        w.reserve_cells(k, ring.len().saturating_mul(3))?;
        let points = ring
            .iter()
            .map(|&a| row(rows, a).map(|[x, y, _]| Vec3::new(x, y, 0.)))
            .collect::<Result<Vec<_>>>()?;
        let Some((c, r)) = fit_circle(&points, Vec3::Z, &budget) else {
            budget.check()?;
            return Ok(None);
        };
        if r <= tolerance || !r.is_finite() || !c.x.is_finite() || !c.y.is_finite() {
            return Ok(None);
        }
        circles.push((*z, c, r));
    }
    let n = circles.len() as f64;
    let centre = circles.iter().fold(Vec3::ZERO, |p, (_, c, _)| p + *c / n);
    if circles
        .iter()
        .any(|(_, c, _)| c.distance(centre) > tolerance)
    {
        return Ok(None);
    }
    // Within one near-constant run, choose one exact cylinder radius.
    // The complete original band later proves its own error to this law.
    let mut rest = circles.as_mut_slice();
    while !rest.is_empty() {
        let (_, _, reference) = rest
            .first()
            .copied()
            .ok_or_else(|| invalid("bore radius missing"))?;
        let n = rest
            .iter()
            .take_while(|(_, _, r)| (*r - reference).abs() <= tolerance * 0.0001)
            .count();
        let (run, next) = rest.split_at_mut(n);
        let mean = run.iter().map(|(_, _, r)| *r / (n as f64)).sum::<f64>();
        for (_, _, r) in run {
            *r = mean;
        }
        rest = next;
    }
    let mut bands = Vec::new();
    for pair in circles.windows(2) {
        let [a, b] = pair else {
            return Err(invalid("missing adjacent bore stations"));
        };
        bands.push(RadialPatchClaim {
            triangles: Vec::new(),
            center: [centre.x, centre.y],
            law: RadiusLaw {
                height: [a.0, b.0],
                radius: [a.2, b.2],
            },
            concave: true,
        });
    }
    for (id, aliases) in cells {
        w.spend(k, 512)?;
        let [a, b, c] = *aliases;
        let zs = [row(rows, a)?[2], row(rows, b)?[2], row(rows, c)?[2]];
        let low = zs.into_iter().fold(f64::INFINITY, f64::min);
        let high = zs.into_iter().fold(f64::NEG_INFINITY, f64::max);
        let Some(band) = bands.iter_mut().find(|band| band.law.height == [low, high]) else {
            return Ok(None);
        };
        w.reserve_output(k, 1)?;
        band.triangles.push(*id);
    }
    if bands.iter().any(|band| band.triangles.is_empty()) {
        return Ok(None);
    }
    Ok(Some(bands))
}

pub(crate) fn propose_rectangular_bored_stock_with_work(
    k: &Kernel,
    w: &MeshWork,
    source: &ExactSourceView<'_, '_>,
    tolerance: f64,
) -> Result<Option<BoredStockProposal>> {
    for axes in [[0, 1, 2], [1, 2, 0], [2, 0, 1]] {
        let mut rows = Vec::new();
        let mut bounds = [[f64::INFINITY; 3], [f64::NEG_INFINITY; 3]];
        for i in 0..source.alias_count() {
            w.spend(k, 16)?;
            w.reserve_cells(k, 3)?;
            let p = source
                .source()
                .position(u32::try_from(i).map_err(|_| invalid("bore alias overflow"))?)
                .ok_or_else(|| invalid("original retained bore alias missing"))?;
            let projected = axes.map(|a| p[a]);
            for (j, v) in projected.iter().copied().enumerate() {
                bounds[0][j] = bounds[0][j].min(v);
                bounds[1][j] = bounds[1][j].max(v);
            }
            rows.push(projected);
        }
        let [lo, hi] = bounds;
        if lo.into_iter().zip(hi).any(|(a, b)| b - a <= 2. * tolerance) {
            continue;
        }
        let mut planes: [Vec<usize>; 6] = core::array::from_fn(|_| Vec::new());
        let mut inner = Vec::new();
        for (id, [a, b, c]) in source.triangles() {
            w.spend(k, 64)?;
            let points = [row(&rows, a)?, row(&rows, b)?, row(&rows, c)?];
            let plane = (0..6).find(|i| points.iter().all(|p| p[*i / 2] == bounds[*i % 2][*i / 2]));
            w.reserve_cells(k, 5)?;
            if let Some(i) = plane {
                planes[i].push(id);
            } else {
                inner.push((id, [a, b, c]));
            }
        }
        if inner.is_empty() || planes.iter().any(Vec::is_empty) {
            continue;
        }
        w.reserve_cells(k, inner.len().saturating_mul(5))?;
        let groups = bore_components(k, w, &inner)?;
        if groups.len() > 16 {
            continue;
        }
        let mut bores = Vec::new();
        for g in &groups {
            if let Some(bore) = one_bore(k, w, g, &rows, [lo[2], hi[2]], tolerance)? {
                bores.push(bore);
            } else {
                break;
            }
        }
        if bores.len() != groups.len() || bores.iter().all(|b| b.len() == 1) {
            continue;
        }
        let basis = [[1., 0., 0.], [0., 1., 0.], [0., 0., 1.]];
        return Ok(Some(BoredStockProposal {
            chart: AxialEndpointProposal {
                origin: [0.; 3],
                columns: axes.map(|i| basis[i]),
                rows,
            },
            bounds,
            planes,
            bores,
        }));
    }
    w.check(k)?;
    Ok(None)
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

        let [x, y, z] = self.chart.columns.map(Vec3::from_array);
        let origin = Vec3::from_array(self.chart.origin);
        let world = |[a, b, c]: [f64; 3]| origin + a * x + b * y + c * z;
        let [lo, hi] = self.bounds;
        let [u, v, h] = lo;
        let [a, b, t] = hi;
        let bottom = [[u, v, h], [a, v, h], [a, b, h], [u, b, h]].map(world);
        let top = [[u, v, t], [a, v, t], [a, b, t], [u, b, t]].map(world);
        let rect = |ring: [Vec3; 4]| -> Result<Vec<Curve>> {
            ring.into_iter()
                .zip(ring.into_iter().cycle().skip(1))
                .map(|(p, q)| Ok(Curve::from(Line::create_line_segment(3, p, q, None)?)))
                .collect()
        };
        let mut caps: [Vec<Curve>; 2] = [Vec::new(), Vec::new()];

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
            for ((b0, b1), (t0, t1)) in bottom
                .into_iter()
                .zip(bottom.into_iter().cycle().skip(1))
                .zip(top.into_iter().zip(top.into_iter().cycle().skip(1)))
            {
                planar(
                    k,
                    &mut candidate,
                    [b0, b1, t1, t0],
                    Vec::new(),
                    OrientType::Opposite,
                    &mut face_env,
                )?;
            }
            for hole in &self.bores {
                for (i, band) in hole.iter().enumerate() {
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
                    if i == 0 {
                        caps[0].push(
                            cone.create_iso_parametric_curve(
                                k,
                                SurfParamType::V,
                                uv.min().y,
                                None,
                                false,
                            )?
                            .curve,
                        );
                    }
                    if i + 1 == hole.len() {
                        caps[1].push(
                            cone.create_iso_parametric_curve(
                                k,
                                SurfParamType::V,
                                uv.max().y,
                                None,
                                false,
                            )?
                            .curve,
                        );
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
            }
            let [lo_holes, hi_holes] = caps;
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
