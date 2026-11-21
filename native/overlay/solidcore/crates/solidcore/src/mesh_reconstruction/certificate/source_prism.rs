//! Complete exact-view constant-extrusion analysis (not upstream).
//!
//! For a chosen cap normal, prove every retained vertex is at exactly one of two
//! levels, all lower/upper vertices pair by ONE common normal translation, both complete
//! cap triangle 2-chains have inverse translated boundaries, and every side triangle
//! belongs to one boundary-edge rectangle whose complete oriented boundary is checked.
//! A compact planar 2-chain is determined by its boundary, so the caps and each side
//! strip are complete, not merely suggested by their vertices. `SourceManifold` already
//! proves embedding, closed orientation and exact redundant-facet regularization.
//! An endpoint view additionally binds a proven whole-time `SourceMotion`; its error
//! is retained separately and MUST be composed before any final native-body adoption.
//!
//! Output is a source product proof only. Actual final B-rep support/cap-trim/product
//! identity and the whole 2D oriented profile isotopy are still required before a curved
//! reconstruction token can be constructed. No sampling or guessed nesting is accepted.
//!
//! Deviations: none. No recursion. All work and internal reference allocation share
//! the calling public workflow's `MeshWork`. A failed exact identity is no proof.
use super::super::work::MeshWork;
use super::exact_geometry as x;
use super::source_view::ExactSourceView;
use crate::geom::expansion;
use crate::kernel::Kernel;
use crate::{Result, SolidError};
use std::collections::{BTreeMap, BTreeSet};

const OP: &str = "mesh_reconstruction::certificate::source_prism";
fn invariant(reason: &'static str) -> SolidError {
    SolidError::PortInvariant {
        operation: OP,
        reason,
    }
}
fn equal(a: &x::E, b: &x::E) -> bool {
    x::sub(a, b).is_some_and(|d| x::zero(&d))
}
pub(super) fn normal(t: [&x::P; 3]) -> Option<x::P> {
    let [a, b, c] = t;
    x::cross(&x::difference(b, a)?, &x::difference(c, a)?)
}
fn same_point(a: &x::P, b: &x::P) -> bool {
    a.iter().zip(b).all(|(a, b)| equal(a, b))
}
fn translated(p: &x::P, d: &x::P) -> Option<x::P> {
    let [a, b, c] = p;
    let [da, db, dc] = d;
    Some([x::add(a, da)?, x::add(b, db)?, x::add(c, dc)?])
}
fn hint(p: &x::P) -> Option<[u64; 3]> {
    let p = p.each_ref().map(|e| expansion::to_f64(e));
    p.iter().all(|v| v.is_finite()).then_some(key(p))
}
fn key(p: [f64; 3]) -> [u64; 3] {
    p.map(|v| if v == 0. { 0 } else { v.to_bits() })
}
pub(super) fn boundary(
    k: &Kernel,
    work: &MeshWork,
    triangles: &[[u32; 3]],
) -> Result<Option<BTreeSet<(u32, u32)>>> {
    let mut edges: BTreeMap<(u32, u32), Vec<(u32, u32)>> = BTreeMap::new();
    for &[a, b, c] in triangles {
        work.spend_core(k, 1)?;
        for (u, v) in [(a, b), (b, c), (c, a)] {
            work.reserve_cells_core(k, 1)?;
            edges.entry((u.min(v), u.max(v))).or_default().push((u, v));
        }
    }
    let mut result = BTreeSet::new();
    for uses in edges.values() {
        work.spend_core(k, 1)?;
        match *uses.as_slice() {
            [(u, v)] => {
                work.reserve_cells_core(k, 1)?;
                result.insert((u, v));
            }
            [(u, v), (x, y)] if u == y && v == x => {}
            _ => return Ok(None),
        }
    }
    Ok(Some(result))
}
/// An exact source product, including complete cap triangle chains and oriented profile
/// rims. Original alias ids are retained; no finite point set stands in for a cap region.
pub(crate) struct SourcePrism<'a, 'raw> {
    /// SAME immutable exact coordinate view on the original proven retained complex.
    pub(crate) view: ExactSourceView<'a, 'raw>,
    pub(crate) cap_levels: [x::E; 2],
    pub(crate) translation: x::P,
    pub(crate) cap_normal: x::P,
    /// Boundary/side alias partners only; cap interior triangulations may differ.
    pub(crate) upper_to_lower: BTreeMap<u32, u32>,
    pub(crate) upper_cap: Vec<usize>,
    pub(crate) lower_cap: Vec<usize>,
    /// On the lower cap's point set, wound as the upper/outward cap (+normal).
    pub(crate) profile_rims: Vec<Vec<u32>>,
}

/// ONE complete source-product proof over the same original or proved-motion view.
/// All downstream consumers must retain this view; no raw-coordinate downgrade exists.
pub(crate) fn prove_source_prism_with_work<'a, 'raw>(
    k: &Kernel,
    work: &MeshWork,
    view: ExactSourceView<'a, 'raw>,
    normal_axis: &x::P,
) -> Result<Option<SourcePrism<'a, 'raw>>> {
    work.spend_core(k, 0)?;
    if x::dot(normal_axis, normal_axis)
        .and_then(|v| x::sign(&v))
        .is_none_or(|s| s <= 0)
    {
        return Ok(None);
    }
    let source = view.source();
    let mut aliases = BTreeSet::new();
    for triangle in &source.aliases {
        work.spend_core(k, 1)?;
        if let Some([a, b, c]) = *triangle {
            work.reserve_cells_core(k, 3)?;
            aliases.extend([a, b, c]);
        }
    }
    let mut points = BTreeMap::new();
    for &alias in &aliases {
        work.reserve_cells_core(k, 1)?;
        let p = view
            .position_with_work(k, work, alias)?
            .ok_or_else(|| invariant("proven retained view alias position missing"))?;
        points.insert(alias, p);
    }
    let point = |alias: u32| {
        points
            .get(&alias)
            .map(AsRef::as_ref)
            .ok_or_else(|| invariant("retained exact view cache missing alias"))
    };
    let mut levels: Vec<x::E> = Vec::new();
    let mut height = BTreeMap::new();
    for &alias in &aliases {
        work.spend_core(k, 1)?;
        let Some(value) = x::dot(normal_axis, point(alias)?) else {
            return Ok(None);
        };
        if !levels.iter().any(|v| equal(v, &value)) {
            work.reserve_cells_core(k, 1)?;
            levels.push(value.clone());
            if levels.len() > 2 {
                return Ok(None);
            }
        }
        work.reserve_cells_core(k, 1)?;
        height.insert(alias, value);
    }
    let [low, high] = levels.as_slice() else {
        return Ok(None);
    };
    let Some(order) = x::sub(high, low).and_then(|v| x::sign(&v)) else {
        return Ok(None);
    };
    let (low, high) = match order.cmp(&0) {
        core::cmp::Ordering::Greater => (low, high),
        core::cmp::Ordering::Less => (high, low),
        core::cmp::Ordering::Equal => return Ok(None),
    };
    let mut lower = BTreeSet::new();
    let mut upper = BTreeSet::new();

    for (&alias, value) in &height {
        work.spend_core(k, 1)?;
        if equal(value, low) {
            work.reserve_cells_core(k, 1)?;
            lower.insert(alias);
        } else if equal(value, high) {
            work.reserve_cells_core(k, 1)?;
            upper.insert(alias);
        } else {
            return Ok(None);
        }
    }
    // Cap interiors may be triangulated differently. Only actual side/boundary
    // vertices must pair; complete cap 2-chain boundaries are verified below.
    let mut pair_lower = BTreeSet::new();
    let mut pair_upper = BTreeSet::new();
    for triangle in &source.aliases {
        work.spend_core(k, 1)?;
        let Some(t) = *triangle else {
            continue;
        };
        if t.iter().all(|v| lower.contains(v)) || t.iter().all(|v| upper.contains(v)) {
            continue;
        }
        for v in t {
            if lower.contains(&v) {
                work.reserve_cells_core(k, 1)?;
                pair_lower.insert(v);
            } else {
                work.reserve_cells_core(k, 1)?;
                pair_upper.insert(v);
            }
        }
    }
    if pair_lower.len() != pair_upper.len() || pair_lower.len() < 3 {
        return Ok(None);
    }
    let mut upper_points: BTreeMap<[u64; 3], Vec<u32>> = BTreeMap::new();
    for &v in &pair_upper {
        work.spend_core(k, 1)?;
        let Some(key) = hint(point(v)?) else {
            return Ok(None);
        };
        work.reserve_cells_core(k, 2)?;
        upper_points.entry(key).or_default().push(v);
    }
    let &first = pair_lower
        .first()
        .ok_or_else(|| invariant("a nonempty proved cap boundary has no first alias"))?;
    let first_point = point(first)?;
    let mut translation = None;
    for &top in &pair_upper {
        work.spend_core(k, 1)?;
        let Some(d) = x::difference(point(top)?, first_point) else {
            return Ok(None);
        };
        if x::cross(&d, normal_axis).is_some_and(|n| n.iter().all(x::zero))
            && x::dot(&d, normal_axis)
                .and_then(|v| x::sign(&v))
                .is_some_and(|s| s > 0)
        {
            translation = Some(d);
            break;
        }
    }
    let Some(translation) = translation else {
        return Ok(None);
    };
    let mut pairs = BTreeMap::new();
    let mut top_used = BTreeSet::new();
    let mut lower_to_upper = BTreeMap::new();
    for &bottom in &pair_lower {
        work.spend_core(k, 1)?;
        let Some(exact) = translated(point(bottom)?, &translation) else {
            return Ok(None);
        };
        let Some(key) = hint(&exact) else {
            return Ok(None);
        };
        let Some(candidates) = upper_points.get(&key) else {
            return Ok(None);
        };
        let mut matched = None;
        for &top in candidates {
            work.spend_core(k, 1)?;
            if same_point(&exact, point(top)?) && matched.replace(top).is_some() {
                return Ok(None);
            }
        }
        let Some(top) = matched else {
            return Ok(None);
        };
        work.reserve_cells_core(k, 3)?;
        if !top_used.insert(top) {
            return Ok(None);
        }
        pairs.insert(top, bottom);
        lower_to_upper.insert(bottom, top);
    }
    if top_used != pair_upper {
        return Ok(None);
    }
    let mut lower_triangles = Vec::new();
    let mut upper_triangles = Vec::new();
    let mut lower_cap = Vec::new();
    let mut upper_cap = Vec::new();
    let mut sides: BTreeMap<(u32, u32), Vec<[u32; 3]>> = BTreeMap::new();
    for (id, triangle) in source.aliases.iter().enumerate() {
        work.spend_core(k, 1)?;
        let Some(triangle) = *triangle else {
            continue;
        };
        let bottom = triangle.iter().all(|p| lower.contains(p));
        let top = triangle.iter().all(|p| upper.contains(p));
        let [a, b, c] = triangle;
        let exact = [point(a)?, point(b)?, point(c)?];
        if bottom || top {
            let Some(orientation) = normal(exact)
                .and_then(|n| x::dot(&n, normal_axis))
                .and_then(|v| x::sign(&v))
            else {
                return Ok(None);
            };
            if bottom {
                if orientation >= 0 {
                    return Ok(None);
                }
                work.reserve_cells_core(k, 2)?;
                lower_triangles.push(triangle);
                lower_cap.push(id);
            } else {
                if orientation <= 0 {
                    return Ok(None);
                }
                work.reserve_cells_core(k, 2)?;
                upper_triangles.push(triangle);
                upper_cap.push(id);
            }
        } else {
            let mut base = BTreeSet::new();
            for p in triangle {
                work.reserve_cells_core(k, 1)?;
                if lower.contains(&p) {
                    base.insert(p);
                } else {
                    base.insert(
                        *pairs.get(&p).ok_or_else(|| {
                            invariant("a proved upper vertex has no lower partner")
                        })?,
                    );
                }
            }
            let mut ids = base.into_iter();
            let (Some(a), Some(b), None) = (ids.next(), ids.next(), ids.next()) else {
                return Ok(None);
            };
            work.reserve_cells_core(k, 1)?;
            sides.entry((a, b)).or_default().push(triangle);
        }
    }
    if lower_cap.is_empty() || upper_cap.is_empty() {
        return Ok(None);
    }
    let Some(lower_boundary) = boundary(k, work, &lower_triangles)? else {
        return Ok(None);
    };
    let Some(upper_boundary) = boundary(k, work, &upper_triangles)? else {
        return Ok(None);
    };
    let mut upper_projected = BTreeSet::new();
    for &(u, v) in &upper_boundary {
        work.spend_core(k, 1)?;
        work.reserve_cells_core(k, 1)?;
        upper_projected.insert((
            *pairs
                .get(&u)
                .ok_or_else(|| invariant("an upper boundary alias is not paired"))?,
            *pairs
                .get(&v)
                .ok_or_else(|| invariant("an upper boundary alias is not paired"))?,
        ));
    }
    let mut reversed_lower = BTreeSet::new();
    for &(u, v) in &lower_boundary {
        work.spend_core(k, 1)?;
        work.reserve_cells_core(k, 1)?;
        reversed_lower.insert((v, u));
    }
    if upper_projected != reversed_lower || sides.len() != lower_boundary.len() {
        return Ok(None);
    }
    for &(u, v) in &lower_boundary {
        work.spend_core(k, 1)?;
        let Some(triangles) = sides.remove(&(u.min(v), u.max(v))) else {
            return Ok(None);
        };
        let Some(actual) = boundary(k, work, &triangles)? else {
            return Ok(None);
        };
        let (&up, &vp) = (
            lower_to_upper
                .get(&u)
                .ok_or_else(|| invariant("a lower boundary alias is not paired"))?,
            lower_to_upper
                .get(&v)
                .ok_or_else(|| invariant("a lower boundary alias is not paired"))?,
        );
        work.reserve_cells_core(k, 4)?;
        let expected: BTreeSet<_> = [(v, u), (u, up), (up, vp), (vp, v)].into_iter().collect();
        if actual != expected {
            return Ok(None);
        }
    }
    if !sides.is_empty() {
        return Ok(None);
    }
    let mut outgoing = BTreeMap::new();
    let mut incoming = BTreeSet::new();
    for &(u, v) in &upper_projected {
        work.spend_core(k, 1)?;
        work.reserve_cells_core(k, 2)?;
        if outgoing.insert(u, v).is_some() || !incoming.insert(v) {
            return Ok(None);
        }
    }
    if outgoing.len() != incoming.len() || incoming.iter().any(|v| !outgoing.contains_key(v)) {
        return Ok(None);
    }
    let mut visited = BTreeSet::new();
    let mut profile_rims = Vec::new();
    for &start in outgoing.keys() {
        work.spend_core(k, 1)?;
        if visited.contains(&start) {
            continue;
        }
        let mut rim = Vec::new();
        let mut p = start;
        loop {
            work.spend_core(k, 1)?;
            work.reserve_cells_core(k, 1)?;
            if !visited.insert(p) {
                if p == start {
                    break;
                }
                return Ok(None);
            }
            work.reserve_output_core(k, 1)?;
            rim.push(p);
            p = *outgoing
                .get(&p)
                .ok_or_else(|| invariant("a checked profile boundary is open"))?;
        }
        if rim.len() < 3 {
            return Ok(None);
        }
        work.reserve_output_core(k, 1)?;
        profile_rims.push(rim);
    }
    work.spend_core(k, 0)?;
    let coefficient_count = low
        .len()
        .checked_add(high.len())
        .and_then(|n| {
            normal_axis
                .iter()
                .try_fold(n, |n, c| n.checked_add(c.len()))
        })
        .ok_or_else(|| invariant("exact product output storage overflow"))?;
    work.reserve_cells_core(k, coefficient_count)?;
    drop(points);
    Ok(Some(SourcePrism {
        view,
        cap_levels: [low.clone(), high.clone()],
        translation,
        cap_normal: normal_axis.clone(),
        upper_to_lower: pairs,
        upper_cap,
        lower_cap,
        profile_rims,
    }))
}

#[cfg(test)]
mod tests {
    use super::super::super::types::MeshInput;
    use super::super::source_topology::{validate_source_weld_with_work, SourceTopology};
    use super::*;
    use crate::kernel::KernelOptions;
    fn box_input() -> MeshInput {
        MeshInput {
            positions: vec![
                [0., 0., 0.],
                [20., 0., 0.],
                [20., 10., 0.],
                [0., 10., 0.],
                [0., 0., 5.],
                [20., 0., 5.],
                [20., 10., 5.],
                [0., 10., 5.],
            ],
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
    #[test]
    fn complete_product_does_not_require_identical_cap_triangulations() {
        let k = Kernel::new(&KernelOptions::default());
        let work = MeshWork::new();
        let mut input = box_input();
        input.positions.push([10., 5., 0.]);
        input
            .triangles
            .splice(0..2, [[0, 8, 1], [1, 8, 2], [2, 8, 3], [3, 8, 0]]);
        let prepared =
            super::super::super::prepare::prepare_conversion(&k, &input, 0.05, &[]).unwrap();
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
            SourceTopology::Undecided(why) => panic!("source proof declined: {why:?}"),
        };
        let product = prove_source_prism_with_work(
            &k,
            &work,
            ExactSourceView::original(&source),
            &x::point([0., 0., 1.]).unwrap(),
        )
        .unwrap()
        .unwrap();
        assert_eq!(product.lower_cap.len(), 4);
        assert_eq!(product.upper_cap.len(), 2);
        assert_eq!(product.profile_rims.len(), 1);
        assert_eq!(product.profile_rims[0].len(), 4);
        assert!(x::equal_point(&product.translation, [0., 0., 5.]));
    }
    #[test]
    fn nearly_two_levels_is_not_an_exact_source_product() {
        let k = Kernel::new(&KernelOptions::default());
        let work = MeshWork::new();
        let mut input = box_input();
        input.positions[6][2] += 1e-9;
        let prepared =
            super::super::super::prepare::prepare_conversion(&k, &input, 0.05, &[]).unwrap();
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
            SourceTopology::Undecided(why) => panic!("source proof declined: {why:?}"),
        };
        assert!(prove_source_prism_with_work(
            &k,
            &work,
            ExactSourceView::original(&source),
            &x::point([0., 0., 1.]).unwrap()
        )
        .unwrap()
        .is_none());
    }
    /// The tilted frame is constructed exactly, not obtained by rounding an
    /// orthogonal projection. D=5*(A cross B); the x offset is below one f64 ulp
    /// at x=20 and therefore detects accidental endpoint-to-f64 substitution.
    #[test]
    fn same_original_complex_has_exact_dyadic_endpoint_product_without_rounding() {
        use super::super::source_motion::{prove_source_motion_with_work, SourceMotionVerdict};
        let k = Kernel::new(&KernelOptions::default());
        let work = MeshWork::new();
        let input = box_input();
        let prepared =
            super::super::super::prepare::prepare_conversion(&k, &input, 0.05, &[]).unwrap();
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
            SourceTopology::Undecided(why) => panic!("source proof declined: {why:?}"),
        };
        let delta = 2.0_f64.powi(-60);
        let endpoints: Vec<_> = (0..source.alias_count())
            .map(|id| {
                let [a, b, c] = source.position(u32::try_from(id).unwrap()).unwrap();
                [
                    x::add(&x::scalar(a).unwrap(), &x::scalar(delta).unwrap()).unwrap(),
                    x::sub(&x::scalar(b).unwrap(), &x::scalar(c / 1024.).unwrap()).unwrap(),
                    x::add(&x::scalar(b / 1024.).unwrap(), &x::scalar(c).unwrap()).unwrap(),
                ]
            })
            .collect();
        let motion =
            match prove_source_motion_with_work(&k, &work, &source, &endpoints, 0.05).unwrap() {
                SourceMotionVerdict::Proven(p) => p,
                SourceMotionVerdict::Undecided(why) => panic!("whole motion declined: {why}"),
            };
        let view = ExactSourceView::motion(&motion);
        assert!(std::ptr::eq(view.source(), &raw const source));
        assert_eq!(view.alias_count(), source.alias_count());
        assert_eq!(
            view.triangles().collect::<Vec<_>>(),
            source
                .aliases
                .iter()
                .enumerate()
                .filter_map(|(id, t)| t.map(|t| (id, t)))
                .collect::<Vec<_>>()
        );
        assert!(view.prior_motion_upper() > 0. && view.prior_motion_upper() < 0.05);
        let normal = x::point([0., -1. / 1024., 1.]).unwrap();
        let product = prove_source_prism_with_work(&k, &work, view, &normal)
            .unwrap()
            .unwrap();
        assert!(std::ptr::eq(product.view.source(), &raw const source));
        assert!(same_point(
            &product.translation,
            &x::point([0., -5. / 1024., 5.]).unwrap()
        ));
        assert_eq!(product.lower_cap.len(), 2);
        assert_eq!(product.upper_cap.len(), 2);
        assert_eq!(product.profile_rims.len(), 1);
        assert_eq!(product.profile_rims[0].len(), 4);
        let ring = product
            .view
            .alias_points_with_work(&k, &work, &product.profile_rims[0])
            .unwrap();
        assert_eq!(ring.len(), 4);
        assert!(ring
            .iter()
            .any(|p| expansion::to_f64(&p[0]) == 20. && !equal(&p[0], &x::scalar(20.).unwrap())));
        let alias = (0..source.alias_count())
            .find(|&id| {
                source
                    .position(u32::try_from(id).unwrap())
                    .is_some_and(|p| p[0] == 20.)
            })
            .unwrap();
        let exact = product
            .view
            .position_with_work(&k, &work, u32::try_from(alias).unwrap())
            .unwrap()
            .unwrap();
        assert!(matches!(exact, std::borrow::Cow::Borrowed(_)));
        assert_eq!(expansion::to_f64(&exact[0]), 20.);
        assert!(!equal(&exact[0], &x::scalar(20.).unwrap()));
        let raw_view = ExactSourceView::original(&source);
        let raw = raw_view
            .position_with_work(&k, &work, u32::try_from(alias).unwrap())
            .unwrap()
            .unwrap();
        assert!(matches!(raw, std::borrow::Cow::Owned(_)));
        assert_eq!(raw_view.prior_motion_upper(), 0.);
        // The original coordinate view is not substituted for this endpoint product.
        assert!(prove_source_prism_with_work(
            &k,
            &work,
            ExactSourceView::original(&source),
            &normal
        )
        .unwrap()
        .is_none());
    }
    #[test]
    fn near_level_raw_refusal_does_not_preclude_proved_endpoint_analysis() {
        use super::super::source_motion::{prove_source_motion_with_work, SourceMotionVerdict};
        let k = Kernel::new(&KernelOptions::default());
        let work = MeshWork::new();
        let mut input = box_input();
        input.positions[6][2] += 1e-9;
        let prepared =
            super::super::super::prepare::prepare_conversion(&k, &input, 0.05, &[]).unwrap();
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
            SourceTopology::Undecided(why) => panic!("source proof declined: {why:?}"),
        };
        let n = x::point([0., 0., 1.]).unwrap();
        assert!(
            prove_source_prism_with_work(&k, &work, ExactSourceView::original(&source), &n)
                .unwrap()
                .is_none()
        );
        let endpoints: Vec<_> = (0..source.alias_count())
            .map(|id| {
                let [a, b, c] = source.position(u32::try_from(id).unwrap()).unwrap();
                x::point([a, b, if c > 4. { 5. } else { c }]).unwrap()
            })
            .collect();
        let motion =
            match prove_source_motion_with_work(&k, &work, &source, &endpoints, 0.05).unwrap() {
                SourceMotionVerdict::Proven(p) => p,
                SourceMotionVerdict::Undecided(why) => panic!("whole motion declined: {why}"),
            };
        let view = ExactSourceView::motion(&motion);
        let product = prove_source_prism_with_work(&k, &work, view, &n)
            .unwrap()
            .unwrap();
        assert_eq!(product.lower_cap.len() + product.upper_cap.len(), 4);
        assert!(product.view.prior_motion_upper() > 0. && product.view.prior_motion_upper() < 1e-8);
        assert!(std::ptr::eq(product.view.source(), &raw const source));
        // No reproved moved MeshInput, alternate weld or discarded mask exists.
    }
    #[test]
    fn rounded_endpoint_key_collision_never_proves_a_product_partner() {
        use super::super::source_motion::{prove_source_motion_with_work, SourceMotionVerdict};
        let k = Kernel::new(&KernelOptions::default());
        let work = MeshWork::new();
        let input = box_input();
        let prepared =
            super::super::super::prepare::prepare_conversion(&k, &input, 0.05, &[]).unwrap();
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
            SourceTopology::Undecided(why) => panic!("source proof declined: {why:?}"),
        };
        let mut endpoints = Vec::new();
        for id in 0..source.alias_count() {
            let p = source.position(u32::try_from(id).unwrap()).unwrap();
            let mut exact = x::point(p).unwrap();
            if p == [20., 10., 5.] {
                exact[0] = x::add(&exact[0], &x::scalar(2.0_f64.powi(-60)).unwrap()).unwrap();
                assert_eq!(hint(&exact), Some(key(p)));
                assert!(!same_point(&exact, &x::point(p).unwrap()));
            }
            endpoints.push(exact);
        }
        let motion =
            match prove_source_motion_with_work(&k, &work, &source, &endpoints, 0.05).unwrap() {
                SourceMotionVerdict::Proven(p) => p,
                SourceMotionVerdict::Undecided(why) => panic!("whole motion declined: {why}"),
            };
        let view = ExactSourceView::motion(&motion);
        let n = x::point([0., 0., 1.]).unwrap();
        assert!(prove_source_prism_with_work(&k, &work, view, &n)
            .unwrap()
            .is_none());
        // The original source happens to be a prism; it is NEVER substituted for
        // this declined endpoint analysis by the analysis function or a consumer.
        assert!(
            prove_source_prism_with_work(&k, &work, ExactSourceView::original(&source), &n)
                .unwrap()
                .is_some()
        );
    }
}
