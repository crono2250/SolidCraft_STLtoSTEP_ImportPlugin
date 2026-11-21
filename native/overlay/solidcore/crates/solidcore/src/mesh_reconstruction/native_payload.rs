//! Bounded inspection of currently retained native mesh-result payloads.
//!
//! This is a storage preflight, NOT a geometry certificate or permission for later
//! lazy generation, cache filling, soundness, cloning, or record export. Callers
//! must hold the exclusive native owner/no-active-evaluator discipline throughout.
//! Original AND made surface kinds, raw revolution children, full NURB backing and
//! inactive topology slots are inspected. Shared backing is charged per occurrence.
//!
//! Deviations: no geometry evaluation, recursion, heap work queue, or pointer dedup.
//! Geometry ownership depth is at most the existing 32. The fixed DFS stack has
//! three pending siblings per depth plus one current entry: one boundary-slice
//! remainder, alternate kind, and alternate revolution child. Boundary slices are
//! drained one element at a time, so their length never causes eager fanout.
//! Curve caches use scoped nonblocking locks. Completed surface caches use one
//! nonnestable loan and a second fixed stack with the same ledger and absolute depth.
use super::types::Result;
use super::work::MeshWork;
use crate::curve::curve::{Curve, CurveKind};
use crate::nurbs::b_spline_curve::BSplineCurve;
use crate::nurbs::b_spline_surface::BSplineSurface;
use crate::nurbs::{crv_basic, srf_basic};
use crate::surface::surf_of_revolution::SurfOfRevolution;
use crate::surface::surface::p2::{NestedGeometry, SurfaceKind, MAX_GEOMETRY_NESTING};
use crate::{Brep, Kernel, SolidError};

const OP: &str = "mesh_reconstruction::native_payload";
const MAX_FACES: usize = 8192;
const MAX_USES: usize = 262_144;
const STACK_SLOTS: usize = 3 * (MAX_GEOMETRY_NESTING + 1) + 1;

fn unsupported(reason: &'static str) -> SolidError {
    SolidError::Unsupported {
        operation: OP,
        reason,
    }
}
fn invalid(reason: &'static str) -> SolidError {
    SolidError::invalid_input(OP, reason)
}
fn charge(k: &Kernel, work: &MeshWork, count: usize) -> crate::Result<()> {
    // Owner-defined logical slots, including explicitly reported retained capacity;
    // not byte estimates or permission for future allocations.
    // This runs BEFORE every owner container traversal.
    work.spend_core(k, count)?;
    work.reserve_cells_core(k, count)
}
fn next_depth(depth: usize) -> crate::Result<usize> {
    depth
        .checked_add(1)
        .ok_or_else(|| invalid("geometry depth overflow"))
}
#[derive(Clone, Copy)]
enum Item<'a> {
    Root(NestedGeometry<'a>),
    Curve(&'a CurveKind),
    Surface(&'a SurfaceKind),
    Boundary(&'a [Option<Curve>]),
}
#[derive(Clone, Copy)]
struct Entry<'a> {
    item: Item<'a>,
    depth: usize,
}
struct Walk<'a, 'k> {
    k: &'k Kernel,
    work: &'k MeshWork,
    stack: [Option<Entry<'a>>; STACK_SLOTS],
    len: usize,
    allow_trim_cache: bool,
}
impl<'a, 'k> Walk<'a, 'k> {
    fn new(k: &'k Kernel, work: &'k MeshWork) -> crate::Result<Self> {
        charge(k, work, STACK_SLOTS)?;
        Ok(Self {
            k,
            work,
            stack: [None; STACK_SLOTS],
            len: 0,
            allow_trim_cache: true,
        })
    }
    fn push(&mut self, item: Item<'a>, depth: usize) -> crate::Result<()> {
        self.work.spend_core(self.k, 1)?;
        if depth > MAX_GEOMETRY_NESTING {
            return Err(unsupported("owned geometry exceeds MAX_GEOMETRY_NESTING"));
        }
        let slot = self
            .stack
            .get_mut(self.len)
            .ok_or_else(|| unsupported("bounded geometry work stack is full"))?;
        *slot = Some(Entry { item, depth });
        self.len = self
            .len
            .checked_add(1)
            .ok_or_else(|| invalid("work stack index overflow"))?;
        Ok(())
    }
    fn root(&mut self, root: NestedGeometry<'a>) -> crate::Result<()> {
        if self.len != 0 {
            return Err(SolidError::port_invariant(
                OP,
                "root traversal did not drain",
            ));
        }
        self.push(Item::Root(root), 0)?;
        self.drain()
    }
    fn drain(&mut self) -> crate::Result<()> {
        while let Some(index) = self.len.checked_sub(1) {
            self.work.spend_core(self.k, 1)?;
            self.len = index;
            let Entry { item, depth } = self
                .stack
                .get_mut(index)
                .and_then(Option::take)
                .ok_or_else(|| SolidError::port_invariant(OP, "empty pending geometry slot"))?;
            let k = self.k;
            let work = self.work;
            match item {
                Item::Root(NestedGeometry::Curve(curve)) => curve.visit_stored_payload(
                    &mut |n| charge(k, work, n),
                    &mut |kind| self.push(Item::Curve(kind), depth),
                    &mut |cache| cache_payload(k, work, cache),
                )?,
                Item::Root(NestedGeometry::Surface(surface)) => {
                    // The owner invokes these callbacks synchronously, boundary first.
                    // A checked local borrow lets both callbacks append to the SAME
                    // fixed stack without cloning, queuing elsewhere, or panicking.
                    let allow_trim_cache = self.allow_trim_cache;
                    let pending = std::cell::RefCell::new(&mut *self);
                    surface.visit_stored_payload_with_cache(
                        &mut |n| charge(k, work, n),
                        &mut |kind| {
                            pending
                                .try_borrow_mut()
                                .map_err(|_| {
                                    SolidError::port_invariant(OP, "reentrant surface kind visitor")
                                })?
                                .push(Item::Surface(kind), depth)
                        },
                        &mut |curves| {
                            pending
                                .try_borrow_mut()
                                .map_err(|_| {
                                    SolidError::port_invariant(
                                        OP,
                                        "reentrant surface boundary visitor",
                                    )
                                })?
                                .push(Item::Boundary(curves), depth)
                        },
                        &mut |cache| {
                            if !allow_trim_cache {
                                return Err(unsupported(
                                    "nested retained surface-cache loan is not qualified",
                                ));
                            }
                            surface_cache_payload(k, work, cache, next_depth(depth)?)
                        },
                    )?;
                }
                Item::Root(NestedGeometry::Volume(_)) => {
                    return Err(unsupported("volume-map retained payload is not qualified"));
                }
                Item::Curve(kind) => self.curve(kind, depth)?,
                Item::Surface(kind) => self.surface(kind, depth)?,
                Item::Boundary(curves) => {
                    if let Some((first, rest)) = curves.split_first() {
                        if !rest.is_empty() {
                            self.push(Item::Boundary(rest), depth)?;
                        }
                        if let Some(curve) = first {
                            self.push(
                                Item::Root(NestedGeometry::Curve(curve)),
                                next_depth(depth)?,
                            )?;
                        }
                    }
                }
            }
        }
        Ok(())
    }
    fn curve(&mut self, kind: &'a CurveKind, depth: usize) -> crate::Result<()> {
        if let CurveKind::Iso(c) = kind {
            self.push(
                Item::Root(NestedGeometry::Surface(c.surface())),
                next_depth(depth)?,
            )
        } else {
            simple_curve_kind(self.k, self.work, kind)
        }
    }
    fn revolution(&mut self, rev: &'a SurfOfRevolution, depth: usize) -> crate::Result<()> {
        surface_base(self.k, self.work, rev.base())?;
        let k = self.k;
        let work = self.work;
        rev.visit_stored_curve_children(&mut |n| charge(k, work, n), &mut |curve| {
            self.push(Item::Root(NestedGeometry::Curve(curve)), next_depth(depth)?)
        })
    }
    fn surface(&mut self, kind: &'a SurfaceKind, depth: usize) -> crate::Result<()> {
        match kind {
            SurfaceKind::BSpline(s) => surface_base(self.k, self.work, s),
            SurfaceKind::Plane(s) => surface_base(self.k, self.work, s.base()),
            SurfaceKind::Cone(s) => self.revolution(s.rev(), depth),
            SurfaceKind::Sphere(s) => self.revolution(s.base(), depth),
            SurfaceKind::Torus(s) => self.revolution(s.base(), depth),
            SurfaceKind::SurfOfRevolution(s) => self.revolution(s, depth),
            SurfaceKind::SurfOfExtrusion(s) => {
                surface_base(self.k, self.work, s.base())?;
                if let Some(curve) = s.gen_curve() {
                    charge(self.k, self.work, 1)?;
                    self.push(Item::Root(NestedGeometry::Curve(curve)), next_depth(depth)?)?;
                }
                Ok(())
            }
            SurfaceKind::CurveBounded(_)
            | SurfaceKind::Step(_)
            | SurfaceKind::OffsetSurface(_)
            | SurfaceKind::SrfInVolume(_)
            | SurfaceKind::ProceduralBlend(_)
            | SurfaceKind::BallPatch(_) => Err(unsupported(
                "surface owner family retained payload is not qualified",
            )),
        }
    }
}
// One dispatch for ordinary simple kinds AND lock-held cache children.
fn simple_curve_kind(k: &Kernel, work: &MeshWork, kind: &CurveKind) -> crate::Result<()> {
    work.spend_core(k, 1)?;
    match kind {
        CurveKind::BSpline(c) => curve_base(k, work, c),
        CurveKind::Line(c) => curve_base(k, work, c.base()),
        CurveKind::Ellipse(c) => curve_base(k, work, c.base()),
        CurveKind::Hyperbola(c) => curve_base(k, work, c.base()),
        CurveKind::Parabola(c) => curve_base(k, work, c.base()),
        CurveKind::Hermite(_) | CurveKind::Conic(_) => Ok(()), // Fixed inline fields.
        CurveKind::Iso(_)
        | CurveKind::Projected(_)
        | CurveKind::Offset(_)
        | CurveKind::Composite(_)
        | CurveKind::CrvOnSurf(_)
        | CurveKind::CrvInVolume(_)
        | CurveKind::TangentField(_) => Err(unsupported(
            "simple cached curve family retained payload is not qualified",
        )),
    }
}
fn cache_payload(
    k: &Kernel,
    work: &MeshWork,
    cache: &crate::curve::curve_cache::CurveCache<()>,
) -> crate::Result<()> {
    work.spend_core(k, 1)?;
    cache.visit_stored_payload(&mut |n| charge(k, work, n), &mut |curve| {
        curve.visit_stored_simple_payload(&mut |n| charge(k, work, n), &mut |kind| {
            simple_curve_kind(k, work, kind)
        })
    })
}

// The cache lock lends roots only during this callback. Each scoped geometry
// stack drains synchronously. Its surface-cache policy forbids another loan:
// borrowed references cannot escape and owned cache traversal cannot recurse.
fn surface_cache_payload(
    k: &Kernel,
    work: &MeshWork,
    cache: &crate::surface::trim_srf_cache::TrimSrfCache<crate::EntityRef>,
    depth: usize,
) -> crate::Result<()> {
    use crate::surface::surface_cache::p1::StoredCacheGeometry;
    work.spend_core(k, 1)?;
    if depth > MAX_GEOMETRY_NESTING {
        return Err(unsupported(
            "owned cache geometry exceeds MAX_GEOMETRY_NESTING",
        ));
    }
    cache.visit_stored_payload(
        &mut |n| charge(k, work, n),
        &mut |geometry| match geometry {
            StoredCacheGeometry::CurveBase(curve) => curve_base(k, work, curve),
            StoredCacheGeometry::SurfaceNurb(surface) => surface_nurb(k, work, surface),
            StoredCacheGeometry::Curve(curve) => {
                let mut loan = Walk::new(k, work)?;
                loan.allow_trim_cache = false;
                loan.push(Item::Root(NestedGeometry::Curve(curve)), depth)?;
                loan.drain()
            }
            StoredCacheGeometry::Surface(surface) => {
                let mut loan = Walk::new(k, work)?;
                loan.allow_trim_cache = false;
                loan.push(Item::Root(NestedGeometry::Surface(surface)), depth)?;
                loan.drain()
            }
        },
    )
}

// Checked declared sizes prevent tiny backing with huge degree/index from
// admitting later native loops. No knot validity/evaluation is claimed here.
fn axis(n: usize, degree: usize, last_knot: usize) -> crate::Result<(usize, usize, usize)> {
    let points = n
        .checked_add(1)
        .ok_or_else(|| invalid("control index overflow"))?;
    let order = degree
        .checked_add(1)
        .ok_or_else(|| invalid("degree overflow"))?;
    let knots = last_knot
        .checked_add(1)
        .ok_or_else(|| invalid("knot index overflow"))?;
    let expected = n
        .checked_add(order)
        .ok_or_else(|| invalid("active knot relation overflow"))?;
    if degree > n || last_knot != expected {
        return Err(invalid("inconsistent declared NURB indices and degree"));
    }
    Ok((points, order, knots))
}
fn curve_nurb(k: &Kernel, work: &MeshWork, n: &crv_basic::Curve) -> crate::Result<()> {
    work.spend_core(k, 1)?;
    let (points, order, knots) = axis(n.n(), n.degree(), n.m())?;
    n.visit_stored_payload(&mut |count| charge(k, work, count))?;
    charge(k, work, points)?;
    charge(k, work, order)?;
    charge(k, work, knots)?;
    if n.cpts().len() != points || n.knots().len() != knots {
        return Err(invalid(
            "active curve backing is smaller than declared dimensions",
        ));
    }
    Ok(())
}
fn surface_nurb(k: &Kernel, work: &MeshWork, n: &srf_basic::Surface) -> crate::Result<()> {
    work.spend_core(k, 1)?;
    let (rows, u_order, u_knots) = axis(n.n(), n.p(), n.r())?;
    let (cols, v_order, v_knots) = axis(n.m(), n.q(), n.s())?;
    let points = rows
        .checked_mul(cols)
        .ok_or_else(|| invalid("active net size overflow"))?;
    let basis = u_order
        .checked_mul(v_order)
        .ok_or_else(|| invalid("active basis size overflow"))?;
    n.visit_stored_payload(&mut |count| charge(k, work, count))?;
    charge(k, work, points)?;
    charge(k, work, basis)?;
    charge(k, work, u_knots)?;
    charge(k, work, v_knots)?;
    if n.u_knots().len() != u_knots || n.v_knots().len() != v_knots {
        return Err(invalid(
            "active surface knots are smaller than declared dimensions",
        ));
    }
    for i in 0..rows {
        work.spend_core(k, 1)?;
        if n.row(i)?.len() != cols {
            return Err(invalid(
                "active surface row is smaller than declared dimensions",
            ));
        }
    }
    Ok(())
}
fn curve_base(k: &Kernel, work: &MeshWork, base: &BSplineCurve) -> crate::Result<()> {
    work.spend_core(k, 1)?;
    if !matches!(base.dim(), 2 | 3) {
        return Err(unsupported(
            "only native 2D/3D curve payload dimensions are qualified",
        ));
    }
    if let Some(nurb) = base.gw_nurb() {
        curve_nurb(k, work, nurb)?;
    }
    // Missing NURB retains no backing; no permission to generate it later.
    Ok(())
}
fn surface_base(k: &Kernel, work: &MeshWork, base: &BSplineSurface) -> crate::Result<()> {
    work.spend_core(k, 1)?;
    if let Some(nurb) = base.gw_nurb() {
        surface_nurb(k, work, nurb)?;
    }
    Ok(())
}
fn inspect(k: &Kernel, work: &MeshWork, body: &Brep) -> crate::Result<()> {
    work.spend_core(k, 1)?;
    if body.faces().slot_count() > MAX_FACES {
        return Err(unsupported("native retained face slots exceed 8192"));
    }
    for count in [
        body.edges().slot_count(),
        body.edgeuses().slot_count(),
        body.faceuses().slot_count(),
        body.loopuses().slot_count(),
        body.loops().slot_count(),
    ] {
        work.spend_core(k, 1)?;
        if count > MAX_USES {
            return Err(unsupported(
                "native retained edge/use/loop slots exceed 262144",
            ));
        }
    }
    let mut walk = Walk::new(k, work)?;
    body.visit_stored_payload(&mut |n| charge(k, work, n), &mut |root| walk.root(root))
}
/// Inspect all currently retained payload of a native mesh candidate with the SAME
/// complete-command budget. Nothing is cloned, evaluated, or materialized.
///
/// Returns no adoption token. Later lazy representation/cache generation and
/// record/export allocation need separate qualified admission. The owner must
/// remain exclusive throughout inspection; shared lazy cells can otherwise change.
///
/// # Errors
///
/// Preserves cancellation and original native errors. Latched shared-budget
/// exhaustion remains typed even when an owner also refuses. Refuses unqualified
/// owner families, kept definitions, busy caches, nested/populated child memos,
/// owned surface trim caches, opaque attributes or
/// diagnostics, excessive nesting, and inconsistent declared active dimensions.
pub fn check_native_payload_with_work(k: &Kernel, work: &MeshWork, body: &Brep) -> Result<()> {
    work.check(k)?;
    let answer = inspect(k, work, body);
    work.check(k)?;
    answer.map_err(Into::into)
}

#[cfg(test)]
mod tests {
    use super::super::MeshError;
    use super::*;
    use crate::curve::curve::Curve;
    use crate::curve::iso_curve::IsoCurve;
    use crate::math::Vec3;
    use crate::nurbs::b_spline_surface::SurfParamType;
    use crate::nurbs::math::CPoint;
    use crate::surface::plane::Plane;
    use crate::surface::surf_of_extrusion::SurfOfExtrusion;
    use crate::surface::surface::Surface;

    fn backed_curve(size: usize) -> Curve {
        let raw = crv_basic::Curve::with_indices(
            vec![CPoint::default(); size],
            1,
            1,
            vec![0.0, 0.0, 1.0, 1.0],
            3,
        )
        .unwrap();
        let mut base = BSplineCurve::new(3);
        base.nurb = Some(raw); // Preserve full backing; no compacting constructor.
        Curve::from(base)
    }
    fn with_curve(curve: Curve) -> Brep {
        let mut body = Brep::new();
        let a = body.add_vertex(Vec3::ZERO).unwrap();
        let z = body.add_vertex(Vec3::Z).unwrap();
        let edge = body.add_edge(a, z).unwrap();
        body.edge_mut(edge).unwrap().curve = Some(curve);
        body
    }
    fn with_surface(surface: Surface) -> Brep {
        let mut body = Brep::new();
        let shell = body.add_shell().unwrap();
        let face = body.add_face(shell).unwrap();
        body.face_mut(face).unwrap().surface = Some(surface);
        body
    }
    fn budget_left(k: &Kernel, left: usize) -> MeshWork {
        let work = MeshWork::new();
        work.reserve_cells(k, 2_000_000 - left).unwrap();
        work
    }
    #[test]
    fn retained_curve_tail_exhausts_before_any_native_evaluation() {
        let k = Kernel::default();
        let body = with_curve(backed_curve(2048));
        let work = budget_left(&k, 512);
        assert!(matches!(
            check_native_payload_with_work(&k, &work, &body),
            Err(MeshError::BudgetExceeded {
                stage: "complete mesh workflow certificate cells",
                ..
            })
        ));
        let curve = body
            .edges()
            .iter()
            .next()
            .unwrap()
            .1
            .curve
            .as_ref()
            .unwrap();
        let CurveKind::BSpline(base) = curve.kind() else {
            panic!("spline")
        };
        assert_eq!(base.gw_nurb().unwrap().storage(), (2048, 4));
    }
    #[test]
    fn retained_knot_tail_and_surface_ragged_inactive_rows_are_counted() {
        let k = Kernel::default();
        let curve =
            crv_basic::Curve::with_indices(vec![CPoint::default(); 2], 1, 1, vec![0.0; 4096], 3)
                .unwrap();
        let work = budget_left(&k, 1024);
        assert!(curve_nurb(&k, &work, &curve).is_err());
        assert!(matches!(
            work.check(&k),
            Err(MeshError::BudgetExceeded { .. })
        ));
        let mut rows = vec![vec![CPoint::default(); 2]; 2];
        rows.push(vec![CPoint::default(); 4096]);
        rows.push(Vec::new());
        let surface = srf_basic::Surface::with_indices(
            rows,
            vec![0.0; 4],
            vec![0.0; 4],
            srf_basic::SurfaceIndices {
                n: 1,
                m: 1,
                p: 1,
                q: 1,
                r: 3,
                s: 3,
            },
        )
        .unwrap();
        let work = budget_left(&k, 1024);
        assert!(surface_nurb(&k, &work, &surface).is_err());
        assert!(matches!(
            work.check(&k),
            Err(MeshError::BudgetExceeded { .. })
        ));
        assert_eq!(surface.row(0).unwrap().len(), 2);
    }
    #[test]
    fn malformed_declared_degrees_refuse_without_allocating_from_them() {
        let k = Kernel::default();
        for degree in [2, usize::MAX] {
            let raw = crv_basic::Curve::with_indices(
                vec![CPoint::default(); 2],
                1,
                degree,
                vec![0.0; 4],
                3,
            )
            .unwrap();
            assert!(matches!(
                curve_nurb(&k, &MeshWork::new(), &raw),
                Err(SolidError::InvalidInput { .. })
            ));
        }
        let raw = srf_basic::Surface::with_indices(
            vec![vec![CPoint::default(); 2]; 2],
            vec![0.0; 4],
            vec![0.0; 4],
            srf_basic::SurfaceIndices {
                n: 1,
                m: 1,
                p: 1,
                q: usize::MAX,
                r: 3,
                s: 3,
            },
        )
        .unwrap();
        assert!(matches!(
            surface_nurb(&k, &MeshWork::new(), &raw),
            Err(SolidError::InvalidInput { .. })
        ));
    }
    #[test]
    fn raw_revolution_polar_curve_is_not_hidden_by_ellipse_accessor() {
        let k = Kernel::default();
        let mut rev = SurfOfRevolution::empty();
        rev.polar_curve = Some(backed_curve(4096));
        assert!(rev.polar_curve().is_none()); // Raw non-Ellipse still owns storage.
        let body = with_surface(Surface::from(rev));
        let work = budget_left(&k, 1024);
        assert!(matches!(
            check_native_payload_with_work(&k, &work, &body),
            Err(MeshError::BudgetExceeded { .. })
        ));
    }
    #[test]
    fn shared_backing_and_repeated_preflights_use_one_cumulative_budget() {
        let k = Kernel::default();
        let body = with_curve(backed_curve(1500));
        let work = budget_left(&k, 2500);
        check_native_payload_with_work(&k, &work, &body).unwrap();
        assert!(matches!(
            check_native_payload_with_work(&k, &work, &body),
            Err(MeshError::BudgetExceeded { .. })
        ));
    }
    #[test]
    fn exact_native_cancellation_precedes_budget_and_owner_refusal() {
        let token = crate::kernel::CancelToken::new();
        let mut k = Kernel::default();
        k.set_cancel_token(token.clone());
        let work = MeshWork::new();
        assert!(!work.try_reserve_cells(2_000_001));
        token.cancel();
        assert!(
            matches!(check_native_payload_with_work(&k, &work, &Brep::new()),
            Err(MeshError::Kernel(error)) if error.is_cancelled())
        );
    }
    #[test]
    fn complete_nested_owner_chain_is_bounded_without_heap_queue() {
        let k = Kernel::default();
        let mut surface = Surface::from(Plane::from_normal(Vec3::ZERO, Vec3::Z));
        for _ in 0..16 {
            let iso =
                IsoCurve::from_surface(&k, surface, SurfParamType::U, 0.0, true, false).unwrap();
            let mut extrusion = SurfOfExtrusion::empty();
            extrusion.gen_curve = Some(Curve::from(iso));
            surface = Surface::from(extrusion);
        }
        let work = MeshWork::new();
        let mut walk = Walk::new(&k, &work).unwrap();
        walk.root(NestedGeometry::Surface(&surface)).unwrap(); // Exactly depth32.
        let mut walk = Walk::new(&k, &work).unwrap();
        walk.push(Item::Root(NestedGeometry::Surface(&surface)), 1)
            .unwrap();
        assert!(matches!(
            walk.drain(),
            Err(SolidError::Unsupported {
                reason: "owned geometry exceeds MAX_GEOMETRY_NESTING",
                ..
            })
        ));
    }
    #[test]
    fn lazy_absence_is_not_filled_and_yields_no_adoption_token() {
        let k = Kernel::default();
        let surface = Surface::from(Plane::from_normal(Vec3::ZERO, Vec3::Z));
        let SurfaceKind::Plane(plane) = surface.kind() else {
            panic!("plane")
        };
        assert!(plane.base().gw_nurb().is_none());
        let body = with_surface(surface);
        check_native_payload_with_work(&k, &MeshWork::new(), &body).unwrap();
        let surface = body
            .faces()
            .iter()
            .next()
            .unwrap()
            .1
            .surface
            .as_ref()
            .unwrap();
        let SurfaceKind::Plane(plane) = surface.kind() else {
            panic!("plane")
        };
        assert!(plane.base().gw_nurb().is_none());
    }

    #[test]
    fn completed_trim_cache_tail_uses_same_budget_and_is_not_consumed() {
        use crate::surface::surface::p2::TrimCacheSlot;
        use crate::surface::surface_cache::p1::{AltCacheKey, AltSrfCache, AltSrfCacheType};
        let k = Kernel::default();
        let surface = Surface::from(Plane::from_normal(Vec3::ZERO, Vec3::Z));
        surface
            .attach_trim_cache(|cache| {
                cache.base_mut().alt_caches_mut().push(AltSrfCache::new(
                    Some(vec![backed_curve(4096)]),
                    None,
                    AltSrfCacheType::Silhouette,
                    0.05,
                    0.0,
                    &AltCacheKey::default(),
                ));
            })
            .unwrap();
        let body = with_surface(surface);
        assert!(matches!(
            check_native_payload_with_work(&k, &budget_left(&k, 512), &body),
            Err(MeshError::BudgetExceeded { .. })
        ));
        let shared = budget_left(&k, 7000);
        check_native_payload_with_work(&k, &shared, &body).unwrap();
        assert!(matches!(
            check_native_payload_with_work(&k, &shared, &body),
            Err(MeshError::BudgetExceeded { .. })
        ));
        let surface = body
            .faces()
            .iter()
            .next()
            .unwrap()
            .1
            .surface
            .as_ref()
            .unwrap();
        let TrimCacheSlot::Stored(cache) = surface.take_trim_cache() else {
            panic!("cache was lost")
        };
        assert_eq!(cache.base().alt_caches().len(), 1);
        Surface::store_trim_cache(*cache);
    }
    #[test]
    fn checked_out_trim_cache_remains_checked_out_after_refusal() {
        use crate::surface::surface::p2::TrimCacheSlot;
        let k = Kernel::default();
        let surface = Surface::from(Plane::from_normal(Vec3::ZERO, Vec3::Z));
        surface.attach_trim_cache(|_| {}).unwrap();
        let TrimCacheSlot::Stored(cache) = surface.take_trim_cache() else {
            panic!("cache")
        };
        let body = with_surface(surface);
        assert!(matches!(
            check_native_payload_with_work(&k, &MeshWork::new(), &body),
            Err(MeshError::Kernel(SolidError::Unsupported { .. }))
        ));
        let surface = body
            .faces()
            .iter()
            .next()
            .unwrap()
            .1
            .surface
            .as_ref()
            .unwrap();
        assert!(matches!(
            surface.take_trim_cache(),
            TrimCacheSlot::CheckedOut
        ));
        Surface::store_trim_cache(*cache);
    }
    #[test]
    fn retained_surface_cache_loans_cannot_nest_or_clear_the_nested_cache() {
        use crate::surface::surface::p2::TrimCacheSlot;
        let k = Kernel::default();
        let body = with_surface(Surface::from(Plane::from_normal(Vec3::ZERO, Vec3::Z)));
        let (id, face) = body.faces().iter().next().unwrap();
        let surface = face.surface.as_ref().unwrap();
        surface
            .attach_trim_cache(|cache| {
                let nested = Surface::from(Plane::from_normal(Vec3::ZERO, Vec3::Z));
                nested.attach_trim_cache(|_| {}).unwrap();
                cache
                    .base_mut()
                    .subdivision_surfaces_mut()
                    .push((crate::EntityRef::Face(id), nested));
            })
            .unwrap();
        assert!(matches!(
            check_native_payload_with_work(&k, &MeshWork::new(), &body),
            Err(MeshError::Kernel(SolidError::Unsupported { .. }))
        ));
        let TrimCacheSlot::Stored(mut cache) = surface.take_trim_cache() else {
            panic!("outer cache")
        };
        let nested = &cache.base_mut().subdivision_surfaces_mut()[0].1;
        let TrimCacheSlot::Stored(inner) = nested.take_trim_cache() else {
            panic!("nested cache lost")
        };
        Surface::store_trim_cache(*inner);
        Surface::store_trim_cache(*cache);
    }
}
