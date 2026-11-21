//! A complete tolerant-solid witness for triangulated planar native cells (not upstream).
//!
//! The exact embedded raw source is the common solid witness. Every actual native
//! vertex/edge/planar face is assigned bijectively to its oriented source patch cell.
//! Original corners fit the unchanged native balls; full affine edges fit tubes;
//! full barycentric source triangles fit bands of the actual Plane definition S.
//! One chosen exact piecewise-affine UV chart covers ALL source triangles and is
//! proved embedded. Actual UV line spans/joins fit the same native tubes/balls and
//! its complete oriented rims, including holes. No sampled gap accepts.
//!
//! Every source shell is independently classified with complete exact ray predicates;
//! its containment forest, cavity orientation and actual native region adjacency must
//! agree. Curved/moved-source cases remain outside this construction class.
//!
//! Deviations: none. No recursion; shared `MeshWork` and 50000 source triangle bound.
use super::super::work::MeshWork;
use super::exact_geometry as x;
use super::exact_planar::affine_ends;
use super::hulls::{point_distance_upper, PointBox};
use super::planar_chart::{planar_chart_with_work, PlanarChartCover};
use super::plane_trim_image::plane_trim_image_with_work;
use super::source_cells::{source_cells_with_work, SourceCellsCover};
use super::source_nesting::{source_nesting_with_work, SourceNestingCover};
use super::source_topology::SourceManifold;
use super::target_complex::{target_complex_with_work, TargetCover, TargetPatchClaim};
use crate::blend::fillet_section::interval::Ivl;
use crate::geom::extent2d::Extent2d;
use crate::kernel::Kernel;
use crate::mass::integrator::properties::region_material;
use crate::nurbs::b_spline_surface_n_lib::p2::OrientType;
use crate::surface::{plane::Plane, surface::SurfaceKind};
use crate::topology::{edgeuse::p1 as eu, Brep};
use crate::Result;
use std::collections::{BTreeMap, BTreeSet};

pub(crate) struct FacetedCellCertificate<'a, 'raw> {
    _source: &'a SourceManifold<'raw>,
    _candidate: &'a Brep,
    pub(crate) stored_boundary_error_upper: f64,
}
pub(crate) enum FacetedWitness<'a, 'raw> {
    Proven(FacetedCellCertificate<'a, 'raw>),
    Undecided(&'static str),
}
fn key(p: [f64; 3]) -> [u64; 3] {
    p.map(|c| if c == 0. { 0 } else { c.to_bits() })
}
fn raw_point(p: [f64; 3]) -> PointBox {
    p.map(Ivl::from)
}
fn enclosure(e: &x::E) -> Option<Ivl> {
    let mut a = Ivl::from(0.);
    for &v in e {
        a = a.add_ulp(Ivl::from(v));
    }
    a.is_finite().then_some(a)
}
fn affine_point(p: &x::P) -> Option<PointBox> {
    Some([enclosure(&p[0])?, enclosure(&p[1])?, enclosure(&p[2])?])
}
/// Homogeneous UV coordinates U,V,W, W>0. No rounded division defines a join.
fn uv_affine(p: &x::P) -> Option<x::P> {
    if !x::zero(&p[2]) {
        return None;
    }
    Some([p[0].clone(), p[1].clone(), x::scalar(1.)?])
}
fn uv_inside(p: &x::P, d: Extent2d) -> bool {
    if !d.is_bounded() || x::sign(&p[2]) != Some(1) {
        return false;
    }
    let [u, v, _] = p;
    [(u, d.u_min(), d.u_max()), (v, d.v_min(), d.v_max())]
        .into_iter()
        .all(|(coordinate, lo, hi)| {
            lo.is_finite()
                && hi.is_finite()
                && lo < hi
                && x::scale(&p[2], lo)
                    .and_then(|b| x::sub(coordinate, &b))
                    .and_then(|v| x::sign(&v))
                    .is_some_and(|s| s >= 0)
                && x::scale(&p[2], hi)
                    .and_then(|b| x::sub(&b, coordinate))
                    .and_then(|v| x::sign(&v))
                    .is_some_and(|s| s >= 0)
        })
}
fn plane_value_h(plane: &Plane, uv: &x::P) -> Option<PointBox> {
    let frame = plane.position();
    let origin = x::vec(frame.origin())?;
    let a = x::vec(frame.x_axis())?;
    let b = x::vec(frame.y_axis())?;
    let scale = plane.uv_scale();
    if !(scale.x > 0. && scale.y > 0. && scale.x.is_finite() && scale.y.is_finite()) {
        return None;
    }
    let [u, v, w] = uv;
    let denominator = enclosure(w)?;
    if !denominator.is_positive() {
        return None;
    }
    let u = x::scale(u, scale.x)?;
    let v = x::scale(v, scale.y)?;
    let mut result = Vec::new();
    for ((o, a), b) in origin.iter().zip(&a).zip(&b) {
        let value = x::add(&x::add(&x::mul(o, w)?, &x::mul(a, &u)?)?, &x::mul(b, &v)?)?;
        let value = enclosure(&value)? / denominator;
        if !value.is_finite() {
            return None;
        }
        result.push(value);
    }
    Some([*result.first()?, *result.get(1)?, *result.get(2)?])
}
fn tolerance(k: &Kernel, value: f64) -> Option<f64> {
    let radius = crate::geom::tol::zone_tol3d(k, value);
    (radius.is_finite() && radius > 0.).then_some(radius)
}
fn sense(value: OrientType) -> Option<i32> {
    match value {
        OrientType::Same => Some(1),
        OrientType::Opposite => Some(-1),
        OrientType::Unknown => None,
    }
}
fn source_orientation(raw: [[f64; 3]; 3], plane: &Plane, sense: i32) -> bool {
    let [a, b, c] = raw;
    let frame = plane.position();
    x::point(a)
        .and_then(|a| {
            x::cross(
                &x::difference(&x::point(b)?, &a)?,
                &x::difference(&x::point(c)?, &a)?,
            )
        })
        .and_then(|n| {
            x::dot(
                &n,
                &x::cross(&x::vec(frame.x_axis())?, &x::vec(frame.y_axis())?)?,
            )
        })
        .and_then(|n| x::sign(&n))
        .is_some_and(|s| s * sense > 0)
}

/// Validate untrusted original-id groups against the WHOLE canonical actual body.
/// Source itself is the common exact solid witness, not an ideal tool or old cache.
pub(crate) fn prove_faceted_witness_with_work<'a, 'raw>(
    k: &Kernel,
    work: &MeshWork,
    source: &'a SourceManifold<'raw>,
    claims: &[Vec<u32>],
    b: &'a Brep,
    user_tolerance: f64,
) -> Result<FacetedWitness<'a, 'raw>> {
    macro_rules! refuse {
        ($why:expr) => {
            return Ok(FacetedWitness::Undecided($why))
        };
    }
    work.spend_core(k, 0)?;
    if !(user_tolerance.is_finite() && user_tolerance > 0.) {
        refuse!("the requested tolerance is invalid");
    }
    let nesting = match source_nesting_with_work(k, work, source)? {
        SourceNestingCover::Proven(p) => p,
        SourceNestingCover::Undecided(why) => {
            refuse!(why);
        }
    };
    let mut triangle_component = BTreeMap::new();
    for (component, triangles) in source.components.iter().enumerate() {
        for &id in triangles {
            work.spend_core(k, 1)?;
            if triangle_component.insert(id, component).is_some() {
                refuse!("source shell components are not a triangle partition");
            }
        }
    }
    let source_cells = match source_cells_with_work(k, work, source, claims)? {
        SourceCellsCover::Proven(p) => p,
        SourceCellsCover::Undecided(why) => {
            refuse!(why);
        }
    };
    if b.face_list().len() != source_cells.patches.len() {
        refuse!("actual/source face-cell partition counts differ");
    }
    let Some(infinite) = b.infinite_region() else {
        refuse!("the actual native infinite region is missing");
    };
    if region_material(b, infinite)? {
        refuse!("the actual infinite region is material");
    }
    let mut shell_regions = BTreeMap::new();
    let mut boundary_vertices = BTreeSet::new();
    let mut boundary_edges = BTreeSet::new();
    let mut patch_keys = BTreeMap::new();
    for (i, patch) in source_cells.patches.iter().enumerate() {
        work.spend_core(k, 1)?;
        let key: Vec<_> = patch.boundary.iter().copied().collect();
        if patch_keys.insert(key, i).is_some() {
            refuse!("untrusted source patches have ambiguous oriented boundaries");
        }
        for &(a, z) in &patch.boundary {
            boundary_vertices.extend([a, z]);
            boundary_edges.insert((a.min(z), a.max(z)));
        }
    }
    let mut positions = BTreeMap::new();
    for &alias in &boundary_vertices {
        work.spend_core(k, 1)?;
        let Some(p) = source.position(alias) else {
            refuse!("a proved source alias is missing");
        };
        if positions.insert(key(p), alias).is_some() {
            refuse!("distinct boundary aliases have one exact position");
        }
    }
    if b.vertex_list().len() != boundary_vertices.len()
        || b.edge_list().len() != boundary_edges.len()
    {
        refuse!("native vertex/edge counts differ from the complete source patch complex");
    }
    let mut vertex_alias = BTreeMap::new();
    let mut aliases_used = BTreeSet::new();
    let mut error = 0.0f64;
    for &v in b.vertex_list() {
        work.spend_core(k, 1)?;
        let point = b.vertex(v)?.point;
        let raw = [point.x, point.y, point.z];
        // Numerical nearest distance steers a candidate only. No closest-point
        // value proves a fit: the exact source point must fit the actual ball,
        // and ALL edge/patch/native-region incidence must subsequently agree.
        let alias = if let Some(alias) = positions.get(&key(raw)).copied() {
            alias
        } else {
            let mut best = None;
            for &alias in &boundary_vertices {
                work.spend_core(k, 1)?;
                let Some(p) = source.position(alias) else {
                    refuse!("an authoritative source corner is missing");
                };
                let d = [p[0] - raw[0], p[1] - raw[1], p[2] - raw[2]];
                let score = d[0] * d[0] + d[1] * d[1] + d[2] * d[2];
                if score.is_finite()
                    && best.is_none_or(|(distance, old)| {
                        score < distance || (score == distance && alias < old)
                    })
                {
                    best = Some((score, alias));
                }
            }
            let Some((_, alias)) = best else {
                refuse!("no finite source-corner assignment could be chosen");
            };
            alias
        };
        if !aliases_used.insert(alias) {
            refuse!("native vertices do not map injectively to source aliases");
        }
        let Some(radius) = tolerance(k, b.vertex(v)?.tolerance) else {
            refuse!("a native vertex ball is invalid");
        };
        let Some(p) = source.position(alias) else {
            refuse!("a source vertex assignment is missing");
        };
        let d = point_distance_upper(raw_point(p), raw_point(raw))?;
        if d > radius || d > user_tolerance {
            refuse!("an original source corner does not fit its unchanged native vertex ball");
        }
        error = error.max(d);
        vertex_alias.insert(v, alias);
    }
    if aliases_used != boundary_vertices {
        refuse!("a source boundary corner is absent from the actual complex");
    }
    let face_claims: Vec<_> = b
        .face_list()
        .iter()
        .map(|&f| TargetPatchClaim { faces: vec![f] })
        .collect();
    work.reserve_cells_core(k, face_claims.len())?;
    let target = match target_complex_with_work(k, work, b, &face_claims)? {
        TargetCover::Proven(p) => p,
        TargetCover::Undecided(_) => {
            refuse!("actual material boundary incidence is not certified");
        }
    };
    let mut patches_used = BTreeSet::new();
    let mut edges_used = BTreeMap::new();
    for actual in &target.patches {
        work.spend_core(k, 1)?;
        let [face] = actual.faces.as_slice() else {
            refuse!("an actual native face assignment is ambiguous");
        };
        let mut actual_boundary = BTreeSet::new();
        let mut use_info = BTreeMap::new();
        let mut faceuse = None;
        for rim in &actual.rims {
            for u in rim {
                work.spend_core(k, 1)?;
                let (Some(&a), Some(&z)) = (vertex_alias.get(&u.start), vertex_alias.get(&u.end))
                else {
                    refuse!("an actual native trim corner is unassigned");
                };
                if !actual_boundary.insert((a, z)) || use_info.insert(u.use_id, *u).is_some() {
                    refuse!("an actual native trim side is duplicated");
                }
                if faceuse.is_some_and(|fu| fu != u.faceuse) {
                    refuse!("one face has inconsistent material sides");
                }
                faceuse = Some(u.faceuse);
            }
        }
        let key: Vec<_> = actual_boundary.iter().copied().collect();
        let Some(&patch_id) = patch_keys.get(&key) else {
            refuse!("the actual oriented native boundary is not a complete source patch boundary");
        };
        if !patches_used.insert(patch_id) {
            refuse!("a source patch maps to more than one actual face");
        }
        let Some(patch) = source_cells.patches.get(patch_id) else {
            refuse!("an assigned original source cell is missing");
        };
        let Some(fu) = faceuse else {
            refuse!("an actual face has no complete boundary");
        };
        let Some(mate) = b.faceuse(fu)?.mate else {
            refuse!("an actual material face side has no mate");
        };
        let (Some(void_region), Some(material_region)) =
            (eu::faceuse_region(b, fu)?, eu::faceuse_region(b, mate)?)
        else {
            refuse!("an actual patch has no complete native region pair");
        };
        if region_material(b, void_region)? || !region_material(b, material_region)? {
            refuse!("an actual patch has inconsistent void/material labels");
        }
        let Some(&first_id) = patch.triangles.first() else {
            refuse!("a source patch has no retained triangle");
        };
        let Some(&component) = triangle_component.get(&first_id) else {
            refuse!("a source patch has no shell component");
        };
        for id in &patch.triangles {
            work.spend_core(k, 1)?;
            if triangle_component.get(id) != Some(&component) {
                refuse!("one planar patch spans distinct source shells");
            }
        }
        let pair = (void_region, material_region);
        if let Some(previous) = shell_regions.insert(component, pair) {
            if previous != pair {
                refuse!("one source shell maps to inconsistent actual native region pairs");
            }
        }
        let Some(face_sense) = sense(b.faceuse(fu)?.orientation) else {
            refuse!("an actual face has unknown orientation");
        };
        let Some(surface) = &b.face(*face)?.surface else {
            refuse!("an actual face has no surface definition");
        };
        if surface.has_kept_definition()
            || surface.procedural_blend().is_some()
            || surface.procedural_sweep().is_some()
        {
            refuse!("a kept/procedural definition cannot be replaced by a Plane label");
        }
        let SurfaceKind::Plane(plane) = surface.kind_with_nurb(k)? else {
            refuse!("an actual face is not an analytic Plane");
        };
        let Some(face_radius) = tolerance(k, b.face(*face)?.tolerance) else {
            refuse!("an actual face band is invalid");
        };
        let plane_domain = plane.step_uv_domain();
        let face_domain = b.face(*face)?.uv_domain;
        let lo = [
            plane_domain.u_min().max(face_domain.u_min()),
            plane_domain.v_min().max(face_domain.v_min()),
        ];
        let hi = [
            plane_domain.u_max().min(face_domain.u_max()),
            plane_domain.v_max().min(face_domain.v_max()),
        ];
        if !lo.iter().chain(&hi).all(|v| v.is_finite()) || lo[0] >= hi[0] || lo[1] >= hi[1] {
            refuse!("actual Plane/face domains have no bounded overlap");
        }
        let mut uv_positions = Vec::new();
        let mut alias_local = BTreeMap::new();
        let mut face_points = BTreeMap::new();
        for &alias in &patch.vertices {
            work.spend_core(k, 1)?;
            work.reserve_cells_core(k, 1)?;
            let Some(p) = source.position(alias) else {
                refuse!("an original source patch point is absent");
            };
            // Numerical projection chooses parameters ONLY. Every final full triangle
            // and its same-parameter distance are independently certified below.
            let guess =
                plane.project_point_to_uv_domain(crate::math::Point3::new(p[0], p[1], p[2]));
            if !guess.x.is_finite() || !guess.y.is_finite() {
                refuse!("the actual Plane could not choose finite chart parameters");
            }
            let uv = [
                guess.x.max(lo[0]).min(hi[0]),
                guess.y.max(lo[1]).min(hi[1]),
                0.,
            ];
            let Some(h) = x::point(uv).and_then(|p| uv_affine(&p)) else {
                refuse!("a chosen exact UV point is invalid");
            };
            if !uv_inside(&h, plane_domain) || !uv_inside(&h, face_domain) {
                refuse!("a chosen UV point leaves the actual definition domain");
            }
            let Some(q) = plane_value_h(plane, &h) else {
                refuse!("an actual Plane witness point is not enclosed");
            };
            let d = point_distance_upper(raw_point(p), q)?;
            if d > face_radius || d > user_tolerance {
                refuse!("a whole source cell cannot fit the unchanged actual Plane band");
            }
            error = error.max(d);
            let Ok(index) = u32::try_from(uv_positions.len()) else {
                refuse!("a chosen UV index does not fit u32");
            };
            alias_local.insert(alias, index);
            uv_positions.push(uv);
            face_points.insert(alias, q);
        }
        let mut uv_triangles = Vec::new();
        for &id in &patch.triangles {
            work.spend_core(k, 1)?;
            let Some(&Some(aliases)) = source.aliases.get(id) else {
                refuse!("an assigned original source triangle is missing");
            };
            let Some(raw) = source.original_triangle(id) else {
                refuse!("an authoritative raw source triangle is missing");
            };
            if !source_orientation(raw, plane, face_sense) {
                refuse!("source and actual face material orientations differ");
            }
            let mut t = [0u32; 3];
            for (slot, alias) in t.iter_mut().zip(aliases) {
                let Some(&local) = alias_local.get(&alias) else {
                    refuse!("a chosen source-cell chart vertex is missing");
                };
                *slot = local;
            }
            uv_triangles.push(t);
        }
        match planar_chart_with_work(k, work, &uv_positions, &uv_triangles, face_sense)? {
            PlanarChartCover::Proven(_) => {}
            PlanarChartCover::Undecided(why) => {
                refuse!(why);
            }
        }
        // Since this full chart is embedded, its oriented 2-chain and recovered rims
        // establish hole nesting/degree. The actual outer-first native loop order
        // must agree; a signed area is used only to orient these PROVEN simple loops.
        let native_loops = &b.faceuse(fu)?.loopuses;
        if native_loops.len() != patch.rims.len() {
            refuse!("actual/source complete loop families differ");
        }
        for (loop_index, &lu) in native_loops.iter().enumerate() {
            work.spend_core(k, 1)?;
            let list = crate::topology::loopuse::edgeuses(b, lu, None, None)?;
            let mut area = vec![0.0];
            for id in list {
                work.spend_core(k, 1)?;
                let Some(u) = use_info.get(&id) else {
                    refuse!("an actual loop use is outside its certified face boundary");
                };
                let (Some(&a), Some(&z)) = (vertex_alias.get(&u.start), vertex_alias.get(&u.end))
                else {
                    refuse!("an actual loop corner is unassigned");
                };
                let (Some(&ia), Some(&iz)) = (alias_local.get(&a), alias_local.get(&z)) else {
                    refuse!("a loop has no whole-cell chart");
                };
                let (Ok(ia), Ok(iz)) = (usize::try_from(ia), usize::try_from(iz)) else {
                    refuse!("a UV corner index does not fit this host");
                };
                let (Some(a), Some(z)) = (uv_positions.get(ia), uv_positions.get(iz)) else {
                    refuse!("an actual loop corner chart point is missing");
                };
                let Some(cross) = x::scalar(a[0])
                    .and_then(|a| x::scale(&a, z[1]))
                    .and_then(|az| {
                        x::scalar(a[1])
                            .and_then(|a| x::scale(&a, z[0]))
                            .and_then(|za| x::sub(&az, &za))
                    })
                else {
                    refuse!("a proven loop orientation is out of arithmetic range");
                };
                let Some(sum) = x::add(&area, &cross) else {
                    refuse!("a complete loop orientation is out of arithmetic range");
                };
                area = sum;
            }
            let expected = if loop_index == 0 {
                face_sense
            } else {
                -face_sense
            };
            if x::sign(&area) != Some(expected) {
                refuse!(
                    "actual outer/hole loop order differs from the complete embedded source chart"
                );
            }
        }
        for u in use_info.values() {
            work.spend_core(k, 1)?;
            let (Some(&a), Some(&z)) = (vertex_alias.get(&u.start), vertex_alias.get(&u.end))
            else {
                refuse!("an actual edge is unassigned");
            };
            let pair = (a.min(z), a.max(z));
            if let Some(previous) = edges_used.insert(u.edge, pair) {
                if previous != pair {
                    refuse!("actual edge uses disagree on source incidence");
                }
            }
            let edge = b.edge(u.edge)?;
            let Some(edge_radius) = tolerance(k, edge.tolerance) else {
                refuse!("an actual edge tube is invalid");
            };
            let Some(curve) = &edge.curve else {
                refuse!("an actual edge curve definition is missing");
            };
            let Some(mut line) = affine_ends(curve, edge.interval, false) else {
                refuse!("an actual boundary edge is not a complete affine Line definition");
            };
            let (Some(trim), _) = eu::uv_trim_curve(b, u.use_id)? else {
                refuse!("an actual native UV trim is missing");
            };
            let Some(mut uv) = affine_ends(trim, edge.interval, true) else {
                refuse!("an actual UV boundary is not a complete affine segment");
            };
            if !u.forward {
                line.swap(0, 1);
                uv.swap(0, 1);
            }
            let trim_image = plane_trim_image_with_work(k, work, plane, &uv)?;
            for (index, alias, vertex_id) in [(0usize, a, u.start), (1usize, z, u.end)] {
                work.spend_core(k, 1)?;
                let Some(p) = source.position(alias) else {
                    refuse!("an original source edge endpoint is missing");
                };
                let Some(q) = face_points.get(&alias).copied() else {
                    refuse!("an actual face chart endpoint is missing");
                };
                let Some(c) = line.get(index).and_then(affine_point) else {
                    refuse!("an actual analytic Line endpoint is not enclosed");
                };
                let knot = if index == 0 {
                    trim_image.knots.first()
                } else {
                    trim_image.knots.last()
                };
                let Some(knot) = knot else {
                    refuse!("a complete actual UV image endpoint is missing");
                };
                let t = knot.point;
                let vertex = b.vertex(vertex_id)?;
                let native = raw_point([vertex.point.x, vertex.point.y, vertex.point.z]);
                let Some(vertex_radius) = tolerance(k, vertex.tolerance) else {
                    refuse!("an actual corner ball is invalid");
                };
                for endpoint in [q, t] {
                    let d = point_distance_upper(endpoint, native)?;
                    if d > vertex_radius || d > user_tolerance {
                        refuse!("a complete UV join cannot fit its unchanged native vertex ball");
                    }
                    error = error.max(d);
                }
                // Both full source/model edges and the native 3D Line are affine.
                // Full UV image formula changes are checked independently below.
                for (left, right) in [(raw_point(p), c), (q, c)] {
                    let d = point_distance_upper(left, right)?;
                    if d > edge_radius || d > user_tolerance {
                        refuse!("a whole source/UV edge cannot fit its unchanged native tube");
                    }
                    error = error.max(d);
                }
            }
            // S(clamp(UV(t))) is affine on EACH exact breakpoint cell. Check
            // source/model correspondences at ALL formula changes; convex norms
            // cover every point between them. Original endpoints alone can miss
            // the interior corner of a non-ISO clamped trim.
            let (Some(pa), Some(pz)) = (source.position(a), source.position(z)) else {
                refuse!("an original full edge endpoint is missing");
            };
            let (Some(qa), Some(qz)) = (face_points.get(&a), face_points.get(&z)) else {
                refuse!("a full chart edge endpoint is missing");
            };
            let at = |[ax, ay, az]: PointBox, [bx, by, bz]: PointBox, t: Ivl| -> PointBox {
                [ax + (bx - ax) * t, ay + (by - ay) * t, az + (bz - az) * t]
            };
            for knot in &trim_image.knots {
                work.spend_core(k, 1)?;
                for witness in [
                    at(raw_point(pa), raw_point(pz), knot.parameter),
                    at(*qa, *qz, knot.parameter),
                ] {
                    let d = point_distance_upper(witness, knot.point)?;
                    if d > edge_radius || d > user_tolerance {
                        refuse!("a complete piecewise actual UV image escapes its unchanged tube/correspondence bound");
                    }
                    error = error.max(d);
                }
            }
        }
    }
    let assigned: BTreeSet<_> = edges_used.values().copied().collect();
    if patches_used.len() != source_cells.patches.len()
        || edges_used.len() != boundary_edges.len()
        || assigned != boundary_edges
    {
        refuse!("actual/source oriented patch cells are not a complete bijection");
    }
    // Match the ACTUAL native region tree to the independently proved source
    // containment forest. Negative cavity shells remain valid; no component/genus
    // count or aggregate volume substitutes for these exact incidence relations.
    let mut interiors = Vec::new();
    let mut exteriors = Vec::new();
    let mut assigned_regions = BTreeSet::new();
    assigned_regions.insert(infinite);
    for (component, &outward) in nesting.outward.iter().enumerate() {
        work.spend_core(k, 1)?;
        let Some(&(void_region, material_region)) = shell_regions.get(&component) else {
            refuse!("an original source shell is absent from the final native region boundary");
        };
        let (inside, outside) = if outward {
            (material_region, void_region)
        } else {
            (void_region, material_region)
        };
        if !assigned_regions.insert(inside) {
            refuse!("distinct source shell interiors are not distinct native regions");
        }
        interiors.push(inside);
        exteriors.push(outside);
    }
    for (component, parent) in nesting.parents.iter().enumerate() {
        work.spend_core(k, 1)?;
        let expected = match parent {
            Some(parent) => *interiors
                .get(*parent)
                .ok_or(crate::SolidError::PortInvariant {
                    operation: "mesh_reconstruction::certificate::faceted_witness",
                    reason: "a proved shell parent is missing",
                })?,
            None => infinite,
        };
        if exteriors.get(component).copied() != Some(expected) {
            refuse!("actual native region nesting differs from exact original material nesting");
        }
    }
    let actual_regions: BTreeSet<_> = crate::topology::brep::p1::regions(b, None)?
        .into_iter()
        .collect();
    if actual_regions != assigned_regions {
        refuse!("some actual native region has no original source-material cell");
    }
    work.spend_core(k, 0)?;
    Ok(FacetedWitness::Proven(FacetedCellCertificate {
        _source: source,
        _candidate: b,
        stored_boundary_error_upper: error,
    }))
}

#[cfg(test)]
mod tests {
    use super::super::super::{
        build_faceted::build_faceted, faceted::faceted_plan_with_work,
        prepare::prepare_conversion_with_work, types::MeshInput,
    };
    use super::super::source_topology::{validate_source_weld_with_work, SourceTopology};
    use super::*;
    use crate::kernel::KernelOptions;
    fn rotated_box() -> MeshInput {
        let p = vec![
            [0., 0., 0.],
            [20., 0., 0.],
            [20., 10., 0.],
            [0., 10., 0.],
            [0., 0., 5.],
            [20., 0., 5.],
            [20., 10., 5.],
            [0., 10., 5.],
        ];
        MeshInput {
            positions: p
                .into_iter()
                .map(|[x, y, z]| [7. + 0.6 * x - 0.8 * y, -3. + 0.8 * x + 0.6 * y, 2. + z])
                .collect(),
            triangles: vec![
                [0, 2, 1],
                [0, 3, 2],
                [4, 5, 6],
                [4, 6, 7],
                [0, 1, 5],
                [0, 5, 4],
                [1, 2, 6],
                [1, 6, 5],
                [2, 3, 7],
                [2, 7, 6],
                [3, 0, 4],
                [3, 4, 7],
            ],
        }
    }
    // The public final entry performs this same authoritative preparation before
    // borrowing the candidate for proof. Raw face construction defers UV trims.
    fn finished_faceted(k: &mut Kernel, plan: &super::super::super::faceted::FacetedPlan) -> Brep {
        let mut b = build_faceted(k, plan).unwrap();
        let standing = crate::topology::brep::validation::soundness(k, &mut b).unwrap();
        assert!(standing.manifold && standing.sound());
        b
    }
    #[test]
    fn normalized_faceted_planes_keep_a_complete_rotated_source_witness() {
        let mut k = Kernel::new(&KernelOptions::default());
        let work = MeshWork::new();
        let input = rotated_box();
        let prepared = prepare_conversion_with_work(&k, &work, &input, 0.05, &[]).unwrap();
        let source = match validate_source_weld_with_work(
            &k,
            &work,
            &input.positions,
            &input.triangles,
            &prepared.weld,
        )
        .unwrap()
        {
            SourceTopology::Proven(p) => p,
            SourceTopology::Undecided(why) => panic!("source preflight: {why:?}"),
        };
        let plan = faceted_plan_with_work(&k, &work, &input, 0.05).unwrap();
        assert_eq!(plan.faces.len(), 6);
        let claims: Vec<_> = plan
            .faces
            .iter()
            .map(|p| p.source_triangles.clone())
            .collect();
        let b = finished_faceted(&mut k, &plan);
        match prove_faceted_witness_with_work(&k, &work, &source, &claims, &b, 0.05).unwrap() {
            FacetedWitness::Proven(p) => assert!(p.stored_boundary_error_upper < 0.05),
            FacetedWitness::Undecided(why) => panic!("complete actual faceted witness: {why}"),
        }
    }
    #[test]
    fn source_group_claims_and_changed_actual_vertices_cannot_authorize_adoption() {
        let mut k = Kernel::new(&KernelOptions::default());
        let work = MeshWork::new();
        let input = rotated_box();
        let prepared = prepare_conversion_with_work(&k, &work, &input, 0.05, &[]).unwrap();
        let source = match validate_source_weld_with_work(
            &k,
            &work,
            &input.positions,
            &input.triangles,
            &prepared.weld,
        )
        .unwrap()
        {
            SourceTopology::Proven(p) => p,
            SourceTopology::Undecided(why) => panic!("source preflight: {why:?}"),
        };
        let plan = faceted_plan_with_work(&k, &work, &input, 0.05).unwrap();
        let mut claims: Vec<_> = plan
            .faces
            .iter()
            .map(|p| p.source_triangles.clone())
            .collect();
        let mut b = finished_faceted(&mut k, &plan);
        let duplicate = claims[0][0];
        claims[0].push(duplicate);
        assert!(matches!(
            prove_faceted_witness_with_work(&k, &work, &source, &claims, &b, 0.05).unwrap(),
            FacetedWitness::Undecided(_)
        ));
        claims[0].pop();
        let id = b.vertex_list()[0];
        b.vertex_mut(id).unwrap().point.x += 0.1;
        assert!(matches!(
            prove_faceted_witness_with_work(&k, &work, &source, &claims, &b, 0.05).unwrap(),
            FacetedWitness::Undecided(_)
        ));
    }
    #[test]
    fn full_public_entry_uses_the_faceted_family_and_keeps_the_proved_bound() {
        let mut k = Kernel::new(&KernelOptions::default());
        let work = MeshWork::new();
        let input = rotated_box();
        let mut prepared = prepare_conversion_with_work(&k, &work, &input, 0.05, &[]).unwrap();
        let plan = faceted_plan_with_work(&k, &work, &input, 0.05).unwrap();
        prepared.provenance.faceted_source_patches = plan
            .faces
            .iter()
            .map(|p| p.source_triangles.clone())
            .collect();
        let source = match super::super::reconstruction::certify_source_with_work(
            &k,
            &work,
            &input,
            &prepared.weld,
        )
        .unwrap()
        {
            super::super::reconstruction::SourceVerdict::Proven(p) => p,
            super::super::reconstruction::SourceVerdict::Undecided(why) => {
                panic!("source preflight: {why:?}")
            }
        };
        let mut b = build_faceted(&mut k, &plan).unwrap();
        match super::super::reconstruction::certify_reconstruction_from_source_with_work(
            &mut k, &work, &source, &prepared, &mut b, 0.05,
        )
        .unwrap()
        {
            super::super::reconstruction::ReconstructionVerdict::Proven(p) => {
                assert!(p.boundary_error_upper().is_finite());
                assert!(p.boundary_error_upper() > 0.0);
                assert!(p.boundary_error_upper() <= 0.05);
            }
            super::super::reconstruction::ReconstructionVerdict::Undecided(why) => {
                panic!("complete actual faceted certificate: {why:?}")
            }
        }
    }
    #[test]
    fn full_final_faceted_cavity_binds_actual_native_region_nesting() {
        let mut k = Kernel::new(&KernelOptions::default());
        let work = MeshWork::new();
        let mut input = rotated_box();
        let base = input.triangles.clone();
        let outer = input.positions.clone();
        let center = [9., 8., 4.5];
        input.positions.extend(
            outer
                .into_iter()
                .map(|p| core::array::from_fn(|i| 0.5 * (p[i] + center[i]))),
        );
        input.triangles.extend(base.into_iter().map(|mut t| {
            t.swap(1, 2);
            t.map(|v| v + 8)
        }));
        let mut prepared = prepare_conversion_with_work(&k, &work, &input, 0.05, &[]).unwrap();
        let plan = faceted_plan_with_work(&k, &work, &input, 0.05).unwrap();
        assert_eq!(plan.faces.len(), 12);
        prepared.provenance.faceted_source_patches = plan
            .faces
            .iter()
            .map(|p| p.source_triangles.clone())
            .collect();
        let source = match super::super::reconstruction::certify_source_with_work(
            &k,
            &work,
            &input,
            &prepared.weld,
        )
        .unwrap()
        {
            super::super::reconstruction::SourceVerdict::Proven(p) => p,
            super::super::reconstruction::SourceVerdict::Undecided(why) => {
                panic!("source cavity preflight: {why:?}")
            }
        };
        let mut b = build_faceted(&mut k, &plan).unwrap();
        match super::super::reconstruction::certify_reconstruction_from_source_with_work(
            &mut k, &work, &source, &prepared, &mut b, 0.05,
        )
        .unwrap()
        {
            super::super::reconstruction::ReconstructionVerdict::Proven(p) => {
                assert!(p.boundary_error_upper() <= 0.05);
            }
            super::super::reconstruction::ReconstructionVerdict::Undecided(why) => {
                panic!("complete final native cavity certificate: {why:?}")
            }
        }
    }
    #[test]
    fn a_rounded_actual_vertex_is_proved_in_its_ball_not_assumed_equal() {
        let mut k = Kernel::new(&KernelOptions::default());
        let work = MeshWork::new();
        let input = rotated_box();
        let prepared = prepare_conversion_with_work(&k, &work, &input, 0.05, &[]).unwrap();
        let source = match validate_source_weld_with_work(
            &k,
            &work,
            &input.positions,
            &input.triangles,
            &prepared.weld,
        )
        .unwrap()
        {
            SourceTopology::Proven(p) => p,
            SourceTopology::Undecided(why) => panic!("source: {why:?}"),
        };
        let plan = faceted_plan_with_work(&k, &work, &input, 0.05).unwrap();
        let claims: Vec<_> = plan
            .faces
            .iter()
            .map(|p| p.source_triangles.clone())
            .collect();
        let mut b = finished_faceted(&mut k, &plan);
        let v = b.vertex_list()[0];
        let old = b.vertex(v).unwrap().point.x;
        b.vertex_mut(v).unwrap().point.x += 1e-12;
        let delta = (b.vertex(v).unwrap().point.x - old).abs();
        assert!(delta > 0.);
        match prove_faceted_witness_with_work(&k, &work, &source, &claims, &b, 0.05).unwrap() {
            FacetedWitness::Proven(p) => assert!(p.stored_boundary_error_upper >= delta),
            FacetedWitness::Undecided(why) => panic!("actual rounded corner witness: {why}"),
        }
    }
}
