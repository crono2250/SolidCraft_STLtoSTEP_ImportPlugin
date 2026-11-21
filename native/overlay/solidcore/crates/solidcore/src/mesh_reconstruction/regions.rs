//! Native surface fitting and bounded source-mesh region growing.
//! Vertex residuals here choose candidates; they are not the final whole-domain certificate.
use super::numeric::{Bounds3, Vec3Numeric};
use super::source::{SourceMesh, MAX_POSITIONS, MAX_TRIANGLES};
use super::types::{invalid, MeshError, MeshInput, MeshRegion, Primitive, Result, SurfaceKind};
use crate::math::Vec3;
use std::collections::VecDeque;
const MAX_REGIONS: usize = 2000;
const SMOOTH_FOLD: f64 = 30.;
const FACET_TILT: f64 = 25.;
/// A welded mesh with what region growing asks of it.
pub(crate) struct Ctx<'a> {
    pub(crate) work: super::work::Work<'a>,
    pub(crate) source_triangles: Vec<Option<u32>>,
    pub(crate) positions: Vec<Vec3>,
    pub(crate) triangles: Vec<[u32; 3]>,
    pub(crate) normals: Vec<Vec3>,
    pub(crate) areas: Vec<f64>,
    pub(crate) neighbours: Vec<Vec<u32>>,
}

impl<'a> Ctx<'a> {
    pub(crate) fn new(mesh: &SourceMesh, k: &'a crate::Kernel) -> Result<Ctx<'a>> {
        Self::from_work(mesh, super::work::Work::new(k)?)
    }
    pub(crate) fn new_with_work(
        mesh: &SourceMesh,
        k: &'a crate::Kernel,
        work_budget: &'a super::work::MeshWork,
    ) -> Result<Ctx<'a>> {
        work_budget.check(k)?;
        let answer = (|| Self::from_work(mesh, super::work::Work::with_budget(k, work_budget)?))();
        work_budget.check(k)?;
        answer
    }
    fn from_work(mesh: &SourceMesh, work: super::work::Work<'a>) -> Result<Ctx<'a>> {
        if mesh.triangles.len() > MAX_TRIANGLES {
            return Err(invalid(&format!(
                "the mesh has {} triangles, more than the {MAX_TRIANGLES} recognition can take",
                mesh.triangles.len()
            )));
        }
        if mesh.positions.len() > MAX_POSITIONS {
            return Err(MeshError::BudgetExceeded {
                stage: "recognition positions",
                limit: MAX_POSITIONS,
            });
        }
        let mut normals = Vec::new();
        let mut areas = Vec::new();
        let mut sides = std::collections::BTreeMap::<(u32, u32), Vec<u32>>::new();
        for (i, t) in mesh.triangles.iter().enumerate() {
            work.spend(1)?;
            let [a, b, c] = *t;
            let (Some(pa), Some(pb), Some(pc)) = (
                mesh.positions.get(a as usize),
                mesh.positions.get(b as usize),
                mesh.positions.get(c as usize),
            ) else {
                return Err(invalid("triangle refers to a missing vertex"));
            };
            let cross = (*pb - *pa).cross(*pc - *pa);
            normals.push(cross.normalized().unwrap_or(Vec3::ZERO));
            areas.push(cross.len() * 0.5);
            let i = u32::try_from(i).map_err(|_| invalid("too many triangles"))?;
            for (p, q) in [(a, b), (b, c), (c, a)] {
                sides.entry((p.min(q), p.max(q))).or_default().push(i);
            }
        }
        let mut neighbours = vec![Vec::new(); mesh.triangles.len()];
        for tris in sides.values() {
            if tris.len() > 2 {
                return Err(invalid("source edge has more than two incident triangles"));
            }
            for &t in tris {
                for &u in tris {
                    if t != u {
                        if let Some(n) = neighbours.get_mut(t as usize) {
                            n.push(u);
                        }
                    }
                }
            }
        }
        Ok(Ctx {
            work,
            source_triangles: mesh.source_triangles.clone(),
            positions: mesh.positions.clone(),
            triangles: mesh.triangles.clone(),
            normals,
            areas,
            neighbours,
        })
    }

    pub(crate) fn corners(&self, t: u32) -> [Vec3; 3] {
        let [a, b, c] = self.triangles.get(t as usize).copied().unwrap_or([0, 0, 0]);
        let p = |i: u32| {
            self.positions
                .get(i as usize)
                .copied()
                .unwrap_or(Vec3::ZERO)
        };
        [p(a), p(b), p(c)]
    }

    fn normal(&self, t: u32) -> Vec3 {
        self.normals.get(t as usize).copied().unwrap_or(Vec3::ZERO)
    }

    fn area(&self, t: u32) -> f64 {
        self.areas.get(t as usize).copied().unwrap_or(0.)
    }

    fn centroid(&self, t: u32) -> Vec3 {
        let [a, b, c] = self.corners(t);
        (a + b + c) / 3.
    }

    fn neighbours(&self, t: u32) -> &[u32] {
        self.neighbours
            .get(t as usize)
            .map_or(&[][..], Vec::as_slice)
    }

    /// Does triangle `t` lie on `s`: corners within `tol` and facing along its normal?
    fn on(&self, t: u32, s: &Primitive, tol: f64) -> bool {
        let n = self.normal(t);
        // A sliver's normal is noise: only its corners count.
        let sliver = self.area(t) <= tol * tol * 4.;
        self.corners(t)
            .iter()
            .all(|p| s.signed_distance(*p).abs() <= tol)
            && (sliver
                || (n.len() > 0.5
                    && s.normal_at(self.centroid(t)).dot(n).abs() >= FACET_TILT.to_radians().cos()))
    }

    /// The triangle nearest `p`.
    pub(crate) fn nearest(&self, p: Vec3) -> Option<u32> {
        let mut best: Option<(u32, f64)> = None;
        for t in 0..self.triangles.len() {
            let t = u32::try_from(t).ok()?;
            if self.area(t) <= 0. {
                continue;
            }
            let [a, b, c] = self.corners(t);
            if !self.work.try_spend(1) {
                return None;
            }
            let d = closest_on_triangle(p, a, b, c).dist(p);
            if best.is_none_or(|(_, bd)| d < bd) {
                best = Some((t, d));
            }
        }
        best.map(|(t, _)| t)
    }
}

/// The point of triangle `abc` nearest `p`.
fn closest_on_triangle(p: Vec3, a: Vec3, b: Vec3, c: Vec3) -> Vec3 {
    let (ab, ac, ap) = (b - a, c - a, p - a);
    let (d1, d2) = (ab.dot(ap), ac.dot(ap));
    if d1 <= 0. && d2 <= 0. {
        return a;
    }
    let bp = p - b;
    let (d3, d4) = (ab.dot(bp), ac.dot(bp));
    if d3 >= 0. && d4 <= d3 {
        return b;
    }
    let vc = d1 * d4 - d3 * d2;
    if vc <= 0. && d1 >= 0. && d3 <= 0. {
        return a + ab * (d1 / (d1 - d3));
    }
    let cp = p - c;
    let (d5, d6) = (ab.dot(cp), ac.dot(cp));
    if d6 >= 0. && d5 <= d6 {
        return c;
    }
    let vb = d5 * d2 - d1 * d6;
    if vb <= 0. && d2 >= 0. && d6 <= 0. {
        return a + ac * (d2 / (d2 - d6));
    }
    let va = d3 * d6 - d5 * d4;
    if va <= 0. && (d4 - d3) >= 0. && (d5 - d6) >= 0. {
        return b + (c - b) * ((d4 - d3) / ((d4 - d3) + (d5 - d6)));
    }
    let denom = va + vb + vc;
    if denom.abs() <= f64::MIN_POSITIVE {
        return a;
    }
    a + ab * (vb / denom) + ac * (vc / denom)
}

type M3 = [[f64; 3]; 3];

fn outer(m: &mut M3, v: Vec3, w: f64) {
    let a = [v.x, v.y, v.z];
    for (i, row) in m.iter_mut().enumerate() {
        for (j, cell) in row.iter_mut().enumerate() {
            *cell += w * a.get(i).copied().unwrap_or(0.) * a.get(j).copied().unwrap_or(0.);
        }
    }
}

/// Fitting reuses the native bounded matrix engines with its explicit numeric policy.
/// Singular/nonconvergent candidates return None. Every actual kernel error is latched and
/// propagated by the existing public Work boundary, including cancelled/internal failures.
fn eigen(ctx: &Ctx<'_>, m: M3) -> Option<[(f64, Vec3); 3]> {
    let mut matrix = ctx.work.core(crate::geom::matrix::Matrix::from_row_major(
        3,
        3,
        m.into_iter().flatten().collect(),
    ))?;
    let result = ctx.work.core(matrix.eigen_system_jacobi_strict(1e-15))??;
    let read = |i: usize| -> Option<(f64, Vec3)> {
        let Some(value) = result.values.get(i).copied() else {
            ctx.work
                .invariant("native eigensolver returned wrong eigenvalue count");
            return None;
        };
        let v = Vec3::new(
            ctx.work.core(result.vectors.at(0, i))?,
            ctx.work.core(result.vectors.at(1, i))?,
            ctx.work.core(result.vectors.at(2, i))?,
        )
        .normalized()?;
        Some((value, v))
    };
    Some([read(0)?, read(1)?, read(2)?])
}
fn solve<const N: usize>(
    a: [[f64; N]; N],
    b: [f64; N],
    work: &super::work::Work<'_>,
) -> Option<[f64; N]> {
    let matrix = work.core(crate::geom::matrix::Matrix::from_row_major(
        N,
        N,
        a.into_iter().flatten().collect(),
    ))?;
    let result = work.core(matrix.solve_linear_system_strict(&b, 1e-14))??;
    if let Ok(values) = <[f64; N]>::try_from(result.x) {
        Some(values)
    } else {
        work.invariant("native linear solver returned wrong solution count");
        None
    }
}

pub(crate) fn vertices(ctx: &Ctx<'_>, tris: &[u32]) -> Vec<Vec3> {
    let mut seen = std::collections::BTreeSet::new();
    let mut out = Vec::new();
    for &t in tris {
        for i in ctx.triangles.get(t as usize).copied().unwrap_or([0, 0, 0]) {
            if seen.insert(i) {
                if let Some(p) = ctx.positions.get(i as usize) {
                    out.push(*p);
                }
            }
        }
    }
    out
}

fn fit_plane(ctx: &Ctx<'_>, tris: &[u32]) -> Option<Primitive> {
    let pts = vertices(ctx, tris);
    if pts.len() < 3 {
        return None;
    }
    let c = pts.iter().fold(Vec3::ZERO, |s, p| s + *p) / pts.len() as f64;
    let mut m: M3 = [[0.; 3]; 3];
    for p in &pts {
        outer(&mut m, *p - c, 1.);
    }
    let normal = eigen(ctx, m)?.first()?.1;
    let facing = tris
        .iter()
        .fold(Vec3::ZERO, |s, t| s + ctx.normal(*t) * ctx.area(*t));
    let normal = if facing.dot(normal) < 0. {
        -normal
    } else {
        normal
    };
    Some(Primitive::Plane { point: c, normal })
}

/// A cylinder's axis: the lines where neighbouring facets meet run along it.
fn ruling_axis(ctx: &Ctx<'_>, tris: &[u32]) -> Option<Vec3> {
    let inside: std::collections::BTreeSet<u32> = tris.iter().copied().collect();
    let mut m: M3 = [[0.; 3]; 3];
    let mut any = false;
    for &t in tris {
        for &u in ctx.neighbours(t) {
            if u > t && inside.contains(&u) {
                let c = ctx.normal(t).cross(ctx.normal(u));
                if c.len() > 1e-4 {
                    if let Some(d) = c.normalized() {
                        outer(&mut m, d, ctx.area(t).min(ctx.area(u)));
                        any = true;
                    }
                }
            }
        }
    }
    if !any {
        return None;
    }
    eigen(ctx, m)?.get(2).map(|e| e.1)
}

/// A circle through points projected along `axis`: (centre, radius).
pub(super) fn fit_circle(
    pts: &[Vec3],
    axis: Vec3,
    work: &super::work::Work<'_>,
) -> Option<(Vec3, f64)> {
    let u = axis.any_perp().normalized()?;
    let v = axis.cross(u);
    let origin = pts.iter().fold(Vec3::ZERO, |s, p| s + *p) / pts.len().max(1) as f64;
    // Kﾃ･sa: xﾂｲ + yﾂｲ + D x + E y + F = 0, least squares.
    let mut a = [[0.; 3]; 3];
    let mut b = [0.; 3];
    for p in pts {
        let w = *p - origin;
        let (x, y) = (w.dot(u), w.dot(v));
        let row = [x, y, 1.];
        let rhs = -(x * x + y * y);
        for (i, ri) in row.iter().enumerate() {
            for (j, rj) in row.iter().enumerate() {
                if let Some(c) = a.get_mut(i).and_then(|r: &mut [f64; 3]| r.get_mut(j)) {
                    *c += ri * rj;
                }
            }
            if let Some(c) = b.get_mut(i) {
                *c += ri * rhs;
            }
        }
    }
    let [d, e, f] = solve(a, b, work)?;
    let (cx, cy) = (-d / 2., -e / 2.);
    let r2 = cx * cx + cy * cy - f;
    (r2 > 0.).then(|| (origin + u * cx + v * cy, r2.sqrt()))
}

fn fit_cylinder(ctx: &Ctx<'_>, tris: &[u32]) -> Option<Primitive> {
    let axis = ruling_axis(ctx, tris)?;
    let pts = vertices(ctx, tris);
    if pts.len() < 4 {
        return None;
    }
    let (point, radius) = fit_circle(&pts, axis, &ctx.work)?;
    Some(Primitive::Cylinder {
        point,
        axis,
        radius,
    })
}

fn fit_sphere(ctx: &Ctx<'_>, tris: &[u32]) -> Option<Primitive> {
    let pts = vertices(ctx, tris);
    if pts.len() < 5 {
        return None;
    }
    let origin = pts.iter().fold(Vec3::ZERO, |s, p| s + *p) / pts.len() as f64;
    let mut a = [[0.; 4]; 4];
    let mut b = [0.; 4];
    for p in &pts {
        let w = *p - origin;
        let row = [w.x, w.y, w.z, 1.];
        let rhs = -w.len2();
        for (i, ri) in row.iter().enumerate() {
            for (j, rj) in row.iter().enumerate() {
                if let Some(c) = a.get_mut(i).and_then(|r: &mut [f64; 4]| r.get_mut(j)) {
                    *c += ri * rj;
                }
            }
            if let Some(c) = b.get_mut(i) {
                *c += ri * rhs;
            }
        }
    }
    let [d, e, f, g] = solve(a, b, &ctx.work)?;
    let c = Vec3::new(-d / 2., -e / 2., -f / 2.);
    let r2 = c.len2() - g;
    (r2 > 0.).then(|| Primitive::Sphere {
        center: origin + c,
        radius: r2.sqrt(),
    })
}

fn fit_cone(ctx: &Ctx<'_>, tris: &[u32]) -> Option<Primitive> {
    // The normals of a cone lie on a circle of the unit sphere around its axis.
    let total: f64 = tris.iter().map(|t| ctx.area(*t)).sum();
    if !crate::geom::certified::above(total, 0.) {
        return None;
    }
    let mean = tris
        .iter()
        .fold(Vec3::ZERO, |s, t| s + ctx.normal(*t) * ctx.area(*t))
        / total;
    let mut m: M3 = [[0.; 3]; 3];
    for &t in tris {
        outer(&mut m, ctx.normal(t) - mean, ctx.area(t));
    }
    let axis = eigen(ctx, m)?.first()?.1;
    // Every facet's plane passes through the apex: least squares over nﾂｷ(x - p) = 0.
    let mut a: M3 = [[0.; 3]; 3];
    let mut b = Vec3::ZERO;
    for &t in tris {
        let n = ctx.normal(t);
        let w = ctx.area(t);
        outer(&mut a, n, w);
        b += n * (n.dot(ctx.centroid(t)) * w);
    }
    let [x, y, z] = solve(a, [b.x, b.y, b.z], &ctx.work)?;
    let apex = Vec3::new(x, y, z);
    cone_from_axis_and_pole(apex, axis, &vertices(ctx, tris))
}

/// One cone regression rule for either a solved apex or an intrinsic complete source pole.
fn cone_from_axis_and_pole(apex: Vec3, axis: Vec3, pts: &[Vec3]) -> Option<Primitive> {
    let mean_h: f64 =
        pts.iter().map(|p| (*p - apex).dot(axis)).sum::<f64>() / pts.len().max(1) as f64;
    let axis = if mean_h < 0. { -axis } else { axis };
    // Regress rho = tan(angle) * h. Averaging each vertex's atan2(rho, h)
    // gives the apex an arbitrary angle from its floating-point roundoff; a shared pole
    // must instead contribute zero support. This also weights a vertex by its distance
    // from the apex, where it actually constrains the cone's opening.
    let (hr, hh) = pts.iter().fold((0., 0.), |(hr, hh), p| {
        let w = *p - apex;
        let h = w.dot(axis);
        let rho = (w - axis * h).len();
        (hr + h * rho, hh + h * h)
    });
    let half_angle = hr.atan2(hh);
    // Nearly a cylinder or a plane: those fit better as what they are.
    if !(0.5f64.to_radians()..=89.5f64.to_radians()).contains(&half_angle) {
        return None;
    }
    Some(Primitive::Cone {
        apex,
        axis,
        half_angle,
    })
}

/// One proposed original pole from the fitted inward axis BEFORE construction.
/// The unique lowest vertex only steers the candidate. The SAME full-source
/// incidence inspection decides whether it is a complete star; extra regular
/// triangles need not contain the pole. No epsilon point identity is used.
enum SourcePoleEvent {
    Ordinary,
    Fixed(Vec3),
}
fn complete_source_pole(ctx: &Ctx<'_>, triangles: &[u32], axis: Vec3) -> Option<SourcePoleEvent> {
    if !axis.to_array().into_iter().all(f64::is_finite)
        || !axis.len2().is_finite()
        || axis.len2() <= 0.
    {
        return None;
    }
    let &first = triangles.first()?;
    let reference = ctx.corners(first).first().copied()?;
    let mut lowest: Option<(Vec3, f64)> = None;
    let mut unique = false;
    for &id in triangles {
        if !ctx.work.try_spend(4) {
            return None;
        }
        for point in ctx.corners(id) {
            let height = (point - reference).dot(axis);
            if !height.is_finite() {
                return None;
            }
            match lowest {
                None => {
                    lowest = Some((point, height));
                    unique = true;
                }
                Some((_, old)) if height < old => {
                    lowest = Some((point, height));
                    unique = true;
                }
                Some((old, h)) if height == h && point != old => unique = false,
                _ => {}
            }
        }
    }
    let Some((pole, _)) = lowest.filter(|_| unique) else {
        return Some(SourcePoleEvent::Ordinary);
    };
    let fact = ctx
        .work
        .core(super::certificate::inspect_vector_apex_link_with_work(
            ctx.work.kernel(),
            ctx.work.budget(),
            &ctx.positions,
            &ctx.triangles,
            triangles,
            pole,
        ))?;
    Some(match fact {
        super::certificate::ApexLink::Complete(_) => SourcePoleEvent::Fixed(pole),
        super::certificate::ApexLink::Absent | super::certificate::ApexLink::Incomplete(_) => {
            SourcePoleEvent::Ordinary
        }
    })
}

/// Keep a complete source pole rather than letting least squares move the
/// singularity. This selects a candidate BEFORE acceptance; the raw-star,
/// angular-degree and whole-triangle proof independently decides acceptance.
fn anchor_complete_source_pole(
    ctx: &Ctx<'_>,
    triangles: &[u32],
    surface: Primitive,
) -> Option<Primitive> {
    let Primitive::Cone { axis, .. } = surface else {
        return Some(surface);
    };
    match complete_source_pole(ctx, triangles, axis)? {
        SourcePoleEvent::Fixed(pole) => {
            cone_from_axis_and_pole(pole, axis, &vertices(ctx, triangles))
        }
        SourcePoleEvent::Ordinary => Some(surface),
    }
}

/// Declare fixed-pole events BEFORE axis regularization and grid rounding.
/// A complete source pole constrains construction; ordinary pole-free frusta
/// retain their rounding rule. No failed certificate triggers an unrounded retry.
pub(crate) fn regularize_picked_regions(
    ctx: &Ctx<'_>,
    regions: &mut [MeshRegion],
    grid: f64,
    tolerance: f64,
) -> Result<()> {
    ctx.work.spend(regions.len())?;
    ctx.work
        .budget()
        .reserve_output(ctx.work.kernel(), regions.len())?;
    let mut poles = Vec::new();
    poles
        .try_reserve_exact(regions.len())
        .map_err(|_| MeshError::Refused {
            stage: "picked-region workspace",
            detail: "allocation refused".into(),
        })?;
    for region in regions.iter() {
        let pole = if let Primitive::Cone { axis, .. } = region.surface {
            let proposed = complete_source_pole(ctx, &region.triangles, axis);
            ctx.work.check()?;
            match proposed.ok_or_else(|| invalid("a fixed cone pole could not be selected"))? {
                SourcePoleEvent::Fixed(pole) => Some(pole),
                SourcePoleEvent::Ordinary => None,
            }
        } else {
            None
        };
        poles.push(pole);
    }
    regularize(regions, tolerance);
    for (region, &pole) in regions.iter_mut().zip(&poles) {
        if let (Primitive::Cone { axis, .. }, Some(pole)) = (region.surface, pole) {
            ctx.work.spend(region.triangles.len().saturating_mul(4))?;
            region.surface = cone_from_axis_and_pole(pole, axis, &vertices(ctx, &region.triangles))
                .ok_or_else(|| invalid("a fixed cone pole has no valid opening"))?;
            region.measurements = region.surface.measurements();
        }
    }
    round_sizes_with_poles(regions, grid, tolerance, &poles);
    ctx.work.check()
}

/// A torus: the spine circle is where the facets' normal lines meet it, `minor` in from the
/// surface. Search `minor` (either side) for the offset points that lie best on one circle,
/// then refine everything on the vertices.
fn fit_torus(ctx: &Ctx<'_>, tris: &[u32]) -> Option<Primitive> {
    if tris.len() < 24 {
        return None;
    }
    if !ctx.work.try_spend(tris.len().min(800).saturating_mul(240)) {
        return None;
    }
    let samples: Vec<(Vec3, Vec3)> = tris
        .iter()
        .step_by(tris.len().div_ceil(800).max(1))
        .map(|t| (ctx.centroid(*t), ctx.normal(*t)))
        .collect();
    let mut bounds = Bounds3::new();
    for (p, _) in &samples {
        bounds.add_point(*p);
    }
    let extent = bounds.size().len().max(1e-6);
    // The spine through points offset by `r` along their normals: (circle, residual).
    let spine = |r: f64| -> Option<(Vec3, Vec3, f64, f64)> {
        let q: Vec<Vec3> = samples.iter().map(|(p, n)| *p - *n * r).collect();
        let c = q.iter().fold(Vec3::ZERO, |s, p| s + *p) / q.len() as f64;
        let mut m: M3 = [[0.; 3]; 3];
        for p in &q {
            outer(&mut m, *p - c, 1.);
        }
        let axis = eigen(ctx, m)?.first()?.1;
        let (center, radius) = fit_circle(&q, axis, &ctx.work)?;
        let residual: f64 = q
            .iter()
            .map(|p| {
                let w = *p - center;
                let h = w.dot(axis);
                ((w - axis * h).len() - radius).powi(2) + h * h
            })
            .sum::<f64>()
            / q.len() as f64;
        Some((center, axis, radius, residual))
    };
    let mut best: Option<(f64, (Vec3, Vec3, f64, f64))> = None;
    for k in 1..=120 {
        let r = extent * 1e-3 * (2000f64).powf(f64::from(k) / 120.);
        for r in [r, -r] {
            if let Some(f) = spine(r) {
                if best.as_ref().is_none_or(|(_, b)| f.3 < b.3) {
                    best = Some((r, f));
                }
            }
        }
    }
    let (r, (center, axis, major, _)) = best?;
    let minor = r.abs();
    if !crate::geom::certified::above(major, minor * 1.0001)
        || !crate::geom::certified::above(minor, 0.)
    {
        return None;
    }
    Some(Primitive::Torus {
        center,
        axis,
        major,
        minor,
    })
}

fn fit(ctx: &Ctx<'_>, kind: SurfaceKind, tris: &[u32]) -> Option<Primitive> {
    if !ctx.work.try_spend(tris.len().saturating_add(1)) {
        return None;
    }
    let first = match kind {
        SurfaceKind::Plane | SurfaceKind::Auto => fit_plane(ctx, tris),
        SurfaceKind::Cylinder => fit_cylinder(ctx, tris),
        SurfaceKind::Cone => fit_cone(ctx, tris),
        SurfaceKind::Sphere => fit_sphere(ctx, tris),
        SurfaceKind::Torus => fit_torus(ctx, tris),
    }?;
    Some(refine(first, &vertices(ctx, tris), &ctx.work))
}

/// The surface's parameters as a vector (and back): what least squares adjusts.
fn params(s: &Primitive) -> [f64; 8] {
    match *s {
        Primitive::Plane { point, normal } => [
            point.x, point.y, point.z, normal.x, normal.y, normal.z, 0., 0.,
        ],
        Primitive::Cylinder {
            point,
            axis,
            radius,
        } => [
            point.x, point.y, point.z, axis.x, axis.y, axis.z, radius, 0.,
        ],
        Primitive::Cone {
            apex,
            axis,
            half_angle,
        } => [
            apex.x, apex.y, apex.z, axis.x, axis.y, axis.z, half_angle, 0.,
        ],
        Primitive::Sphere { center, radius } => {
            [center.x, center.y, center.z, radius, 0., 0., 0., 0.]
        }
        Primitive::Torus {
            center,
            axis,
            major,
            minor,
        } => [
            center.x, center.y, center.z, axis.x, axis.y, axis.z, major, minor,
        ],
    }
}

fn with_params(s: &Primitive, p: &[f64; 8]) -> Option<Primitive> {
    let [x, y, z, a, b, c, d, e] = *p;
    let point = Vec3::new(x, y, z);
    let dir = || Vec3::new(a, b, c).normalized();
    let out = match s {
        Primitive::Plane { .. } => Primitive::Plane {
            point,
            normal: dir()?,
        },
        Primitive::Cylinder { .. } => Primitive::Cylinder {
            point,
            axis: dir()?,
            radius: d,
        },
        Primitive::Cone { .. } => Primitive::Cone {
            apex: point,
            axis: dir()?,
            half_angle: d,
        },
        Primitive::Sphere { .. } => Primitive::Sphere {
            center: point,
            radius: a,
        },
        Primitive::Torus { .. } => Primitive::Torus {
            center: point,
            axis: dir()?,
            major: d,
            minor: e,
        },
    };
    params(&out).iter().all(|v| v.is_finite()).then_some(out)
}

/// Least squares on the vertices' distances (Levenberg-Marquardt): the facet-based first fit
/// of a coarse mesh is off by a fraction of a degree; this brings it onto the vertices.
fn refine(s: Primitive, pts: &[Vec3], work: &super::work::Work<'_>) -> Primitive {
    if matches!(s, Primitive::Plane { .. }) || pts.len() < 6 {
        return s;
    }
    // A torus adjusts all eight parameters; the other surfaces the first seven. Normalised
    // axes and unused parameters have null directions, regularised in the normal equations.
    if matches!(s, Primitive::Torus { .. }) {
        refine_n::<8>(s, pts, work)
    } else {
        refine_n::<7>(s, pts, work)
    }
}

fn refine_n<const N: usize>(s: Primitive, pts: &[Vec3], work: &super::work::Work<'_>) -> Primitive {
    let step = pts.len().div_ceil(1500).max(1);
    let sample: Vec<Vec3> = pts.iter().step_by(step).copied().collect();
    let cost = |s: &Primitive| {
        sample
            .iter()
            .map(|p| s.signed_distance(*p).powi(2))
            .sum::<f64>()
    };
    let mut best = s;
    let mut best_cost = cost(&s);
    let mut lambda = 1e-3;
    for _ in 0..30 {
        if !work.try_spend(sample.len().saturating_mul(N * N + N + 12)) {
            break;
        }
        let all = params(&best);
        let mut p0 = [0.; N];
        for (v, a) in p0.iter_mut().zip(all) {
            *v = a;
        }
        let full = |q: &[f64; N]| {
            let mut out = all;
            for (o, v) in out.iter_mut().zip(q) {
                *o = *v;
            }
            out
        };
        let scale = p0.iter().take(3).map(|v| v.abs()).fold(1f64, f64::max);
        let mut jt_j = [[0.; N]; N];
        let mut jt_r = [0.; N];
        let mut columns: Vec<Vec<f64>> = Vec::new();
        for k in 0..N {
            let h = if k < 3 { 1e-7 * scale } else { 1e-7 };
            let mut q = p0;
            if let Some(v) = q.get_mut(k) {
                *v += h;
            }
            let col: Vec<f64> = match with_params(&best, &full(&q)) {
                Some(t) => sample
                    .iter()
                    .map(|p| (t.signed_distance(*p) - best.signed_distance(*p)) / h)
                    .collect(),
                None => vec![0.; sample.len()],
            };
            columns.push(col);
        }
        let residual: Vec<f64> = sample.iter().map(|p| best.signed_distance(*p)).collect();
        for i in 0..N {
            for j in 0..N {
                let (Some(ci), Some(cj)) = (columns.get(i), columns.get(j)) else {
                    continue;
                };
                if let Some(c) = jt_j.get_mut(i).and_then(|r| r.get_mut(j)) {
                    *c = ci.iter().zip(cj).map(|(a, b)| a * b).sum();
                }
            }
            if let (Some(ci), Some(c)) = (columns.get(i), jt_r.get_mut(i)) {
                *c = -ci.iter().zip(&residual).map(|(a, b)| a * b).sum::<f64>();
            }
        }
        let mut improved = false;
        for _ in 0..8 {
            let mut a = jt_j;
            for (i, row) in a.iter_mut().enumerate() {
                if let Some(d) = row.get_mut(i) {
                    // Above solve's absolute pivot floor even for a null derivative (an
                    // axis's redundant length, or a sphere's unused parameters). Otherwise
                    // a perfectly axis-aligned first fit disables refinement altogether.
                    *d += lambda * (*d).max(1e-12) + 1e-12;
                }
            }
            let Some(delta) = solve(a, jt_r, work) else {
                break;
            };
            let mut q = p0;
            for (v, d) in q.iter_mut().zip(delta) {
                *v += d;
            }
            if let Some(t) = with_params(&best, &full(&q)) {
                let c = cost(&t);
                if c < best_cost {
                    best = t;
                    best_cost = c;
                    lambda = (lambda * 0.3).max(1e-12);
                    improved = true;
                    break;
                }
            }
            lambda *= 10.;
        }
        if !improved || best_cost < 1e-24 {
            break;
        }
    }
    best
}

/// Largest distance of the triangles' corners from `s`, or infinity when a facet faces away.
fn deviation(ctx: &Ctx<'_>, s: &Primitive, tris: &[u32], tol: f64) -> f64 {
    let mut worst = 0f64;
    for &t in tris {
        if !ctx.work.try_spend(1) {
            return f64::INFINITY;
        }
        if !ctx.on(t, s, f64::INFINITY) {
            return f64::INFINITY;
        }
        for p in ctx.corners(t) {
            worst = worst.max(s.signed_distance(p).abs());
        }
        if worst > tol * 1e3 {
            return worst;
        }
    }
    worst
}

/// The seed and its smooth neighbourhood (folds under [`SMOOTH_FOLD`]), nearest first.
fn neighbourhood(ctx: &Ctx<'_>, seed: u32, free: &dyn Fn(u32) -> bool, limit: usize) -> Vec<u32> {
    let mut near = vec![seed];
    let mut seen = std::collections::BTreeSet::from([seed]);
    let mut k = 0;
    while let Some(&t) = near.get(k) {
        if near.len() >= limit {
            break;
        }
        k += 1;
        for &u in ctx.neighbours(t) {
            if free(u)
                && ctx.normal(t).dot(ctx.normal(u)) >= SMOOTH_FOLD.to_radians().cos()
                && seen.insert(u)
            {
                near.push(u);
            }
        }
    }
    near.truncate(limit);
    near
}

/// Grow a region from `seed` over triangles not yet `claimed`.
///
/// The kind is chosen on the seed's smooth neighbourhood: the simplest kind that fits the
/// largest part of it (so a cone is not taken for a narrow cylinder, nor a bore for a strip of
/// planes). The region then grows over every neighbour on that surface, refitting as it grows.
pub(crate) fn grow(
    ctx: &Ctx<'_>,
    seed: u32,
    want: SurfaceKind,
    tol: f64,
    claimed: &[bool],
) -> Option<MeshRegion> {
    let n = ctx.triangles.len();
    let free = |t: u32| !claimed.get(t as usize).copied().unwrap_or(true);
    if !free(seed) {
        return None;
    }
    let kinds: &[SurfaceKind] = match want {
        SurfaceKind::Auto => &[
            SurfaceKind::Plane,
            SurfaceKind::Cylinder,
            SurfaceKind::Cone,
            SurfaceKind::Sphere,
            SurfaceKind::Torus,
        ],
        SurfaceKind::Plane => &[SurfaceKind::Plane],
        SurfaceKind::Cylinder => &[SurfaceKind::Cylinder],
        SurfaceKind::Cone => &[SurfaceKind::Cone],
        SurfaceKind::Sphere => &[SurfaceKind::Sphere],
        SurfaceKind::Torus => &[SurfaceKind::Torus],
    };
    // Adaptive tessellation may put the first 96 facets in a tiny azimuthal strip of a
    // toroidal fillet, where only its minor circle is observable. Start with broader bounded
    // support, then shrink geometrically below as before when it crosses another surface.
    // Every candidate must still fit every vertex and facet in the selected neighbourhood.
    let near = neighbourhood(ctx, seed, &free, 384);
    let mut start: Option<(Primitive, usize)> = None;
    let mut size = near.len();
    while start.is_none() && size >= 1 {
        let part = near.get(..size)?;
        for kind in kinds {
            if let Some(s) = fit(ctx, *kind, part).filter(|s| deviation(ctx, s, part, tol) <= tol) {
                start = Some((s, size));
                break;
            }
        }
        size = if size > 4 { size * 3 / 4 } else { size - 1 };
    }
    let (mut surface, size) = match start {
        Some(s) => s,
        // A lone facet of a fine mesh is a plane of its own.
        None if kinds.contains(&SurfaceKind::Plane) => {
            let [a, ..] = ctx.corners(seed);
            (
                Primitive::Plane {
                    point: a,
                    normal: ctx.normal(seed),
                },
                1,
            )
        }
        None => return None,
    };
    let mut in_patch = vec![false; n];
    let mut patch: Vec<u32> = near.get(..size)?.to_vec();
    for &t in &patch {
        if let Some(p) = in_patch.get_mut(t as usize) {
            *p = true;
        }
    }
    let mut fitted_at = patch.len();
    for _ in 0..64 {
        let mut queue: VecDeque<u32> = patch.iter().copied().collect();
        let mut added = 0usize;
        while let Some(t) = queue.pop_front() {
            if !ctx.work.try_spend(1) {
                return None;
            }
            for &u in ctx.neighbours(t) {
                if !free(u)
                    || in_patch.get(u as usize).copied().unwrap_or(true)
                    || !ctx.on(u, &surface, tol)
                {
                    continue;
                }
                if let Some(p) = in_patch.get_mut(u as usize) {
                    *p = true;
                }
                patch.push(u);
                queue.push_back(u);
                added += 1;
                // Follow the surface: refit as the region doubles.
                if patch.len() >= fitted_at * 2 {
                    if let Some(s) = fit(ctx, surface.kind(), &patch)
                        .filter(|s| deviation(ctx, s, &patch, tol) <= tol)
                    {
                        surface = s;
                        fitted_at = patch.len();
                    }
                }
            }
        }
        let refit =
            fit(ctx, surface.kind(), &patch).filter(|s| deviation(ctx, s, &patch, tol) <= tol);
        match refit {
            Some(s) if s != surface && added > 0 => {
                surface = s;
                fitted_at = patch.len();
                continue;
            }
            Some(s) => surface = s,
            None => {}
        }
        // Stopped: does a richer kind fit the region with its smooth neighbours (a fillet that
        // looked like a cylinder over its first few facets is a torus all round)?
        // A plane stops where its flat face ends; only curved regions move on.
        if want != SurfaceKind::Auto || surface.kind() == SurfaceKind::Plane {
            break;
        }
        let mut ring: Vec<u32> = Vec::new();
        for &t in &patch {
            for &u in ctx.neighbours(t) {
                if free(u)
                    && !in_patch.get(u as usize).copied().unwrap_or(true)
                    && ctx.normal(t).dot(ctx.normal(u)) >= SMOOTH_FOLD.to_radians().cos()
                {
                    ring.push(u);
                }
            }
        }
        ring.sort_unstable();
        ring.dedup();
        if ring.is_empty() {
            break;
        }
        let rank = |k: SurfaceKind| kinds.iter().position(|x| *x == k).unwrap_or(0);
        let mut grown = patch.clone();
        grown.extend_from_slice(&ring);
        let richer = kinds
            .iter()
            .skip(rank(surface.kind()) + 1)
            .find_map(|k| fit(ctx, *k, &grown).filter(|s| deviation(ctx, s, &grown, tol) <= tol));
        let Some(s) = richer else { break };
        surface = s;
        for u in &ring {
            if let Some(p) = in_patch.get_mut(*u as usize) {
                *p = true;
            }
        }
        patch = grown;
        fitted_at = patch.len();
    }
    surface = anchor_complete_source_pole(ctx, &patch, surface)?;
    let pts = vertices(ctx, &patch);
    let (mut worst, mut sum) = (0f64, 0f64);
    for p in &pts {
        let d = surface.signed_distance(*p);
        worst = worst.max(d.abs());
        sum += d * d;
    }
    let rms = (sum / pts.len().max(1) as f64).sqrt();
    let concave = if let Primitive::Plane { .. } = surface {
        false
    } else {
        let facing: f64 = patch
            .iter()
            .map(|t| ctx.normal(*t).dot(surface.normal_at(ctx.centroid(*t))) * ctx.area(*t))
            .sum();
        facing < 0.
    };
    let area = patch.iter().map(|t| ctx.area(*t)).sum();
    patch.sort_unstable();
    Some(MeshRegion {
        surface,
        measurements: surface.measurements(),
        triangles: patch,
        area,
        max_deviation: worst,
        rms_deviation: rms,
        concave,
    })
}

/// Design intent over measurement noise: directions (plane normals, axes) within half a degree
/// of each other become one, those within half a degree of a model axis or of square to a
/// larger one become exactly that, and parallel planes within the tolerance become one plane.
pub(crate) fn regularize(regions: &mut [MeshRegion], tolerance: f64) {
    let close = 0.5f64.to_radians();
    let direction = |s: &Primitive| match *s {
        Primitive::Plane { normal, .. } => Some(normal),
        Primitive::Cylinder { axis, .. }
        | Primitive::Cone { axis, .. }
        | Primitive::Torus { axis, .. } => Some(axis),
        Primitive::Sphere { .. } => None,
    };
    // Directions by the area behind them, largest first.
    let mut order: Vec<usize> = (0..regions.len()).collect();
    order.sort_by(|a, b| {
        regions
            .get(*b)
            .map_or(0., |r| r.area)
            .total_cmp(&regions.get(*a).map_or(0., |r| r.area))
    });
    let mut kept: Vec<Vec3> = Vec::new();
    for &i in &order {
        let Some(d) = regions.get(i).and_then(|r| direction(&r.surface)) else {
            continue;
        };
        let mut e = kept
            .iter()
            .copied()
            .find(|k| k.dot(d).abs() >= close.cos())
            .map(|k| if k.dot(d) < 0. { -k } else { k });
        if e.is_none() {
            let mut c = [Vec3::X, Vec3::Y, Vec3::Z]
                .into_iter()
                .find(|a| a.dot(d).abs() >= close.cos())
                .map_or(d, |a| if a.dot(d) < 0. { -a } else { a });
            // Square to a larger direction when nearly so.
            for k in &kept {
                if k.dot(c).abs() <= close.sin() {
                    if let Some(sq) = (c - *k * k.dot(c)).normalized() {
                        c = sq;
                    }
                }
            }
            kept.push(c);
            e = Some(c);
        }
        let Some(e) = e else { continue };
        if let Some(r) = regions.get_mut(i) {
            r.surface = match r.surface {
                Primitive::Plane { point, .. } => Primitive::Plane { point, normal: e },
                Primitive::Cylinder { point, radius, .. } => Primitive::Cylinder {
                    point,
                    axis: e,
                    radius,
                },
                Primitive::Cone {
                    apex, half_angle, ..
                } => Primitive::Cone {
                    apex,
                    axis: e,
                    half_angle,
                },
                Primitive::Torus {
                    center,
                    major,
                    minor,
                    ..
                } => Primitive::Torus {
                    center,
                    axis: e,
                    major,
                    minor,
                },
                other @ Primitive::Sphere { .. } => other,
            };
        }
    }
    // Coplanar planes: one offset, weighted by area.
    let n = regions.len();
    for i in 0..n {
        let Some(Primitive::Plane {
            point: pi,
            normal: ni,
        }) = regions.get(i).map(|r| r.surface)
        else {
            continue;
        };
        let mut members = vec![i];
        for j in i + 1..n {
            if let Some(Primitive::Plane {
                point: pj,
                normal: nj,
            }) = regions.get(j).map(|r| r.surface)
            {
                if nj.dot(ni).abs() >= 1. - 1e-12 && (pj - pi).dot(ni).abs() <= tolerance {
                    members.push(j);
                }
            }
        }
        if members.len() < 2 {
            continue;
        }
        let (mut sum, mut weight) = (0., 0.);
        for m in &members {
            if let Some(r) = regions.get(*m) {
                if let Primitive::Plane { point, .. } = r.surface {
                    sum += (point - pi).dot(ni) * r.area;
                    weight += r.area;
                }
            }
        }
        let offset = if weight > 0. { sum / weight } else { 0. };
        for m in &members {
            if let Some(r) = regions.get_mut(*m) {
                if let Primitive::Plane { point, normal } = r.surface {
                    let along = (point - pi).dot(ni);
                    r.surface = Primitive::Plane {
                        point: point + ni * (offset - along),
                        normal,
                    };
                }
            }
        }
    }
}

pub(crate) fn picked_regions(
    ctx: &Ctx<'_>,
    picks: &[(Vec3, SurfaceKind)],
    tolerance: f64,
) -> Result<Vec<MeshRegion>> {
    let mut claimed = vec![false; ctx.triangles.len()];
    let mut regions: Vec<MeshRegion> = Vec::new();
    for (i, (point, kind)) in picks.iter().enumerate() {
        let nearest = ctx.nearest(*point);
        ctx.work.check()?;
        let seed = nearest.ok_or_else(|| invalid("empty mesh"))?;
        if claimed.get(seed as usize).copied().unwrap_or(true) {
            continue;
        }
        let grown = grow(ctx, seed, *kind, tolerance, &claimed);
        ctx.work.check()?;
        let region = grown.ok_or_else(|| {
            invalid(&format!(
                "pick {}: no surface of that kind fits the mesh there within {tolerance} mm",
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
    Ok(regions)
}

/// Sizes rounded to `grid` mm where that moves them by no more than `tolerance`: radii and
/// minor radii, the offsets of planes square to a model axis, and the positions of axes along
/// a model axis. Design intent: 7.98 measured is 8.00 drawn.
pub(crate) fn round_sizes(regions: &mut [MeshRegion], grid: f64, tolerance: f64) {
    round_sizes_with_poles(regions, grid, tolerance, &[]);
}
fn round_sizes_with_poles(
    regions: &mut [MeshRegion],
    grid: f64,
    tolerance: f64,
    poles: &[Option<Vec3>],
) {
    if !(grid > 0. && grid.is_finite()) {
        return;
    }
    let round = |v: f64| {
        let r = (v / grid).round() * grid;
        if (r - v).abs() <= tolerance {
            r
        } else {
            v
        }
    };
    let on_axis = |d: Vec3| {
        [Vec3::X, Vec3::Y, Vec3::Z]
            .into_iter()
            .any(|a| d.dot(a).abs() > 1. - 1e-12)
    };
    // Points across an axis-aligned direction: their coordinates across it rounded.
    let across = |p: Vec3, d: Vec3| {
        let keep = |c: f64, k: f64| if k.abs() > 1. - 1e-12 { c } else { round(c) };
        if on_axis(d) {
            Vec3::new(keep(p.x, d.x), keep(p.y, d.y), keep(p.z, d.z))
        } else {
            p
        }
    };
    for (index, r) in regions.iter_mut().enumerate() {
        r.surface = match r.surface {
            Primitive::Plane { point, normal } if on_axis(normal) => {
                let along = point.dot(normal);
                Primitive::Plane {
                    point: point + normal * (round(along) - along),
                    normal,
                }
            }
            Primitive::Cylinder {
                point,
                axis,
                radius,
            } => Primitive::Cylinder {
                point: across(point, axis),
                axis,
                radius: round(radius),
            },
            Primitive::Cone {
                apex,
                axis,
                half_angle,
            } => Primitive::Cone {
                apex: match poles.get(index).copied().flatten() {
                    Some(pole) => pole,
                    None => across(apex, axis),
                },
                axis,
                half_angle,
            },
            Primitive::Sphere { center, radius } => Primitive::Sphere {
                center,
                radius: round(radius),
            },
            Primitive::Torus {
                center,
                axis,
                major,
                minor,
            } => Primitive::Torus {
                center: across(center, axis),
                axis,
                major: round(major),
                minor: round(minor),
            },
            other @ Primitive::Plane { .. } => other,
        };
        r.measurements = r.surface.measurements();
    }
}

pub(crate) fn checked_tolerance(tolerance: f64) -> Result<()> {
    if !tolerance.is_finite() || !(1e-6..=1.).contains(&tolerance) {
        return Err(invalid("tolerance must be between 0.000001 and 1 mm"));
    }
    Ok(())
}
pub(crate) fn context<'a>(
    k: &'a crate::Kernel,
    input: &MeshInput,
    tolerance: f64,
) -> Result<Ctx<'a>> {
    super::source::admit_conversion(input)?;
    let mesh = SourceMesh::checked(input)?;
    // Recognition historically shares conversion welding, including its 50k triangle gate.
    let welded = super::source::weld(k, &mesh, tolerance)?;
    Ctx::new(&welded, k)
}
pub(crate) fn context_with_work<'a>(
    k: &'a crate::Kernel,
    work_budget: &'a super::work::MeshWork,
    input: &MeshInput,
    tolerance: f64,
) -> Result<Ctx<'a>> {
    work_budget.check(k)?;
    let answer = (|| {
        work_budget.spend(
            k,
            input
                .positions
                .len()
                .saturating_add(input.triangles.len().saturating_mul(3)),
        )?;
        super::source::admit_conversion(input)?;
        let mesh = SourceMesh::checked(input)?;
        // Recognition historically shares conversion welding, including its 50k triangle gate.
        let welded = super::source::weld_with_work(k, work_budget, &mesh, tolerance)?;
        Ctx::new_with_work(&welded, k, work_budget)
    })();
    work_budget.check(k)?;
    answer
}
/// The region around `point` that one surface of `kind` fits within `tolerance` mm.
/// Standalone single-job convenience; multi-stage callers share one `MeshWork`.
pub fn recognize_region(
    k: &crate::Kernel,
    input: &MeshInput,
    point: Vec3,
    kind: SurfaceKind,
    tolerance: f64,
) -> Result<MeshRegion> {
    let work_budget = super::work::MeshWork::new();
    recognize_region_with_work(k, &work_budget, input, point, kind, tolerance)
}

/// Grow a candidate analytic region from the nearest triangle under one workflow budget.
/// Construction acceptance requires an independent complete-region certificate.
pub fn recognize_region_with_work(
    k: &crate::Kernel,
    work_budget: &super::work::MeshWork,
    input: &MeshInput,
    point: Vec3,
    kind: SurfaceKind,
    tolerance: f64,
) -> Result<MeshRegion> {
    work_budget.check(k)?;
    let answer = (|| {
        checked_tolerance(tolerance)?;
        if !point.is_finite() {
            return Err(invalid("the point must be finite"));
        }
        let ctx = context_with_work(k, work_budget, input, tolerance)?;
        let nearest = ctx.nearest(point);
        ctx.work.check()?;
        let seed = nearest.ok_or_else(|| invalid("empty mesh"))?;
        let claimed = vec![false; ctx.triangles.len()];
        let grown = grow(&ctx, seed, kind, tolerance, &claimed);
        ctx.work.check()?;
        let mut region = grown.ok_or_else(|| {
            let what = match kind {
                SurfaceKind::Auto => "no plane, cylinder, cone, sphere or torus",
                SurfaceKind::Plane => "no plane",
                SurfaceKind::Cylinder => "no cylinder",
                SurfaceKind::Cone => "no cone",
                SurfaceKind::Sphere => "no sphere",
                SurfaceKind::Torus => "no torus",
            };
            invalid(&format!(
                "{what} fits the mesh around that point within {tolerance} mm"
            ))
        })?;
        region.triangles = source_triangle_ids(&ctx, &region.triangles)?;
        let _proof = super::primitive_certificate::certify_primitive_region_with_work(
            k,
            work_budget,
            input,
            &region.surface,
            &region.triangles,
            region.concave,
            tolerance,
        )?;

        Ok(region)
    })();
    work_budget.check(k)?;
    answer
}

/// The whole mesh as regions, largest triangles first; triangles no surface fits stay out.
/// Standalone single-job convenience; multi-stage callers share one `MeshWork`.
pub fn recognize_all(
    k: &crate::Kernel,
    input: &MeshInput,
    tolerance: f64,
) -> Result<Vec<MeshRegion>> {
    let work_budget = super::work::MeshWork::new();
    recognize_all_with_work(k, &work_budget, input, tolerance)
}

/// Partition candidate analytic regions largest-first under one workflow budget.
/// Triangles not covered by a recognized region remain unclaimed.
pub fn recognize_all_with_work(
    k: &crate::Kernel,
    work_budget: &super::work::MeshWork,
    input: &MeshInput,
    tolerance: f64,
) -> Result<Vec<MeshRegion>> {
    work_budget.check(k)?;
    let answer = (|| {
        checked_tolerance(tolerance)?;
        let ctx = context_with_work(k, work_budget, input, tolerance)?;
        let n = ctx.triangles.len();
        let mut order: Vec<u32> = (0..n).filter_map(|t| u32::try_from(t).ok()).collect();
        order.sort_by(|a, b| ctx.area(*b).total_cmp(&ctx.area(*a)));
        let mut claimed = vec![false; n];
        let mut out = Vec::new();
        let mut output_references = 0usize;
        for seed in order {
            if claimed.get(seed as usize).copied().unwrap_or(true) || ctx.area(seed) <= 0. {
                continue;
            }
            let grown = grow(&ctx, seed, SurfaceKind::Auto, tolerance, &claimed);
            ctx.work.check()?;
            match grown {
                Some(region) => {
                    for t in &region.triangles {
                        if let Some(c) = claimed.get_mut(*t as usize) {
                            *c = true;
                        }
                    }
                    output_references = output_references.saturating_add(region.triangles.len());
                    if output_references > MAX_TRIANGLES {
                        return Err(MeshError::BudgetExceeded {
                            stage: "recognition output references",
                            limit: MAX_TRIANGLES,
                        });
                    }
                    let mut region = region;
                    region.triangles = source_triangle_ids(&ctx, &region.triangles)?;
                    let _proof = super::primitive_certificate::certify_primitive_region_with_work(
                        k,
                        work_budget,
                        input,
                        &region.surface,
                        &region.triangles,
                        region.concave,
                        tolerance,
                    )?;

                    out.push(region);
                    if out.len() >= MAX_REGIONS {
                        return Err(invalid(&format!(
                            "more than {MAX_REGIONS} regions; pick the surfaces one by one"
                        )));
                    }
                }
                None => {
                    if let Some(c) = claimed.get_mut(seed as usize) {
                        *c = true;
                    }
                }
            }
        }
        Ok(out)
    })();
    work_budget.check(k)?;
    answer
}

/// Map a recognised candidate patch back to original source triangle ids.
pub(crate) fn source_triangle_ids(ctx: &Ctx<'_>, triangles: &[u32]) -> Result<Vec<u32>> {
    let mut ids = Vec::new();
    for t in triangles {
        let id = ctx
            .source_triangles
            .get(*t as usize)
            .copied()
            .flatten()
            .ok_or_else(|| invalid("synthetic triangles cannot be source attribution"))?;
        ids.push(id);
    }
    Ok(ids)
}

/// Standalone single-job convenience; multi-stage callers share one `MeshWork`.
pub fn picks_for_all(
    k: &crate::Kernel,
    input: &MeshInput,
    tolerance: f64,
) -> Result<Vec<super::types::MeshPick>> {
    let work_budget = super::work::MeshWork::new();
    picks_for_all_with_work(k, &work_budget, input, tolerance)
}

/// Read the untouched triangle identified by a recognised region. Picking a point
/// needs its corners, not a new adjacency graph containing dropped zero-area faces.
fn original_triangle_corners(mesh: &SourceMesh, triangle: u32) -> Result<[Vec3; 3]> {
    let [a, b, c] = mesh
        .triangles
        .get(triangle as usize)
        .copied()
        .ok_or_else(|| invalid("missing original selection triangle"))?;
    let corner = |index: u32| {
        mesh.positions
            .get(index as usize)
            .copied()
            .ok_or_else(|| invalid("missing original selection vertex"))
    };
    Ok([corner(a)?, corner(b)?, corner(c)?])
}

/// Choose deterministic selection points for the recognised source regions using the same complete-workflow budget.
pub fn picks_for_all_with_work(
    k: &crate::Kernel,
    work_budget: &super::work::MeshWork,
    input: &MeshInput,
    tolerance: f64,
) -> Result<Vec<super::types::MeshPick>> {
    work_budget.check(k)?;
    let answer = (|| {
        let regions = recognize_all_with_work(k, work_budget, input, tolerance)?;
        work_budget.spend(
            k,
            input
                .positions
                .len()
                .saturating_add(input.triangles.len().saturating_mul(3)),
        )?;
        let raw = SourceMesh::checked(input)?;
        let total: f64 = regions.iter().map(|r| r.area).sum();
        let mut picks = Vec::new();
        for region in regions {
            work_budget.check(k)?;
            if region.triangles.len() <= 3 && region.area <= total * 0.005 {
                continue;
            }
            let mut largest: Option<(u32, f64)> = None;
            for &triangle in &region.triangles {
                work_budget.spend(k, 1)?;
                let [a, b, c] = original_triangle_corners(&raw, triangle)?;
                let area = (b - a).cross(c - a).len() * 0.5;
                if !area.is_finite() || area <= 0. {
                    return Err(invalid(
                        "recognised selection triangle needs finite positive area",
                    ));
                }
                // Iterator::max_by selects the last equal value; keep that order.
                if largest.is_none_or(|(_, previous)| !area.total_cmp(&previous).is_lt()) {
                    largest = Some((triangle, area));
                }
            }
            let (triangle, _) = largest.ok_or_else(|| invalid("empty recognised region"))?;
            work_budget.spend(k, 1)?;
            let [a, b, c] = original_triangle_corners(&raw, triangle)?;
            picks.push(super::types::MeshPick {
                point: ((a + b + c) / 3.).to_array(),
                kind: SurfaceKind::Auto,
            });
        }
        Ok(picks)
    })();
    work_budget.check(k)?;
    answer
}

/// Admit the two existing field-only return containers: native -> record and
/// record -> application. Triangle backing moves unchanged; it is NEVER cloned.
/// Each record slot has at most 21 inline scalar/header units: Primitive tag+8
/// scalars, optional measures tag+2*(tag+scalar), triangle Vec header3, metrics3
/// and concave1. The application slot has at most16 (no optional measures).
/// Two outer slots plus both inline payloads give39 per region; two Vec headers6.
/// This is logical return-storage admission, NOT native workspace/serialization.
///
/// # Errors
/// Existing region cap, checked metadata overflow, same-work exhaustion or cancellation.
pub fn admit_region_handoff_with_work(
    k: &crate::Kernel,
    work: &super::MeshWork,
    regions: &[MeshRegion],
) -> Result<()> {
    work.check(k)?;
    let answer = (|| {
        if regions.len() >= MAX_REGIONS {
            return Err(invalid(
                "recognition handoff reaches the existing region limit",
            ));
        }
        work.spend(k, regions.len())?;
        let mut references = regions
            .len()
            .checked_mul(2)
            .ok_or_else(|| invalid("region handoff count overflow"))?;
        for region in regions {
            work.check(k)?;
            references = references
                .checked_add(region.triangles.len())
                .ok_or_else(|| invalid("region handoff reference overflow"))?;
        }
        let slots = regions
            .len()
            .checked_mul(39)
            .and_then(|n| n.checked_add(6))
            .ok_or_else(|| invalid("region handoff storage overflow"))?;
        work.spend(k, slots)?;
        work.reserve_cells(k, slots)?;
        work.reserve_output(k, references)
    })();
    work.check(k)?;
    answer
}

/// Admit native picks -> record picks -> the existing application's tuple list.
/// Each side holds point3+kind1; two outer slots give10 units per pick, with6
/// units for the two Vec headers. No coordinate is computed by this admission.
/// This does not permit any additional clone, serializer or native allocation.
///
/// # Errors
/// Existing region/pick cap, checked overflow, shared work exhaustion or cancellation.
pub fn admit_pick_handoff_with_work(
    k: &crate::Kernel,
    work: &super::MeshWork,
    picks: &[super::types::MeshPick],
) -> Result<()> {
    work.check(k)?;
    let answer = (|| {
        if picks.len() >= MAX_REGIONS {
            return Err(invalid("pick handoff reaches the existing region limit"));
        }
        let slots = picks
            .len()
            .checked_mul(10)
            .and_then(|n| n.checked_add(6))
            .ok_or_else(|| invalid("pick handoff storage overflow"))?;
        let references = picks
            .len()
            .checked_mul(2)
            .ok_or_else(|| invalid("pick handoff reference overflow"))?;
        work.spend(k, slots)?;
        work.reserve_cells(k, slots)?;
        work.reserve_output(k, references)
    })();
    work.check(k)?;
    answer
}
