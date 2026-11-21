//! Complete source-shell nesting and oriented material proof (not upstream).
//!
//! `SourceManifold` already proves each connected closed shell embedded and all shells
//! mutually disjoint. Hence a WHOLE connected shell lies inside or outside another
//! shell; one exact nonboundary representative classifies that component, not sampled
//! geometry. Every triangle/ray intersection is decided with exact expansion signs.
//! A ray through a trim simplex or coplanar triangle is unusable; a different fixed
//! direction only steers another complete proof. No numerical hit count accepts.
//!
//! The containment forest and alternating outward/cavity signed component volumes
//! prove material winding0/1. Negative cavity shells are valid; globally inside-out,
//! inconsistent or ambiguous nesting refuses. Final native region binding is separate.
//! Deviations: none. No recursion; <=256 shells,16 ray candidates, shared `MeshWork`.
use super::super::work::MeshWork;
use super::exact_geometry as x;
use super::source_topology::SourceManifold;
use crate::{Kernel, Result};

pub(crate) struct SourceNesting<'a, 'raw> {
    _source: &'a SourceManifold<'raw>,
    pub(crate) parents: Vec<Option<usize>>,
    pub(crate) outward: Vec<bool>,
}
pub(crate) enum SourceNestingCover<'a, 'raw> {
    Proven(SourceNesting<'a, 'raw>),
    Undecided(&'static str),
}
/// None: this direction has no exact strict ray classification. Some(false) is
/// a proved non-hit; Some(true) is an exact INTERIOR triangle hit with t>0.
fn ray_hit(origin: [f64; 3], direction: [f64; 3], t: [[f64; 3]; 3]) -> Option<bool> {
    let o = x::point(origin)?;
    let d = x::point(direction)?;
    let [a, b, c] = t.map(x::point);
    let (a, b, c) = (a?, b?, c?);
    let e1 = x::difference(&b, &a)?;
    let e2 = x::difference(&c, &a)?;
    let p = x::cross(&d, &e2)?;
    let det = x::dot(&e1, &p)?;
    let det_sign = x::sign(&det)?;
    let s = x::difference(&o, &a)?;
    if det_sign == 0 {
        return (x::sign(&x::dot(&x::cross(&e1, &e2)?, &s)?)? != 0).then_some(false);
    }
    let q = x::cross(&s, &e1)?;
    let flip = if det_sign > 0 { 1. } else { -1. };
    let det = x::scale(&det, flip)?;
    let u = x::scale(&x::dot(&s, &p)?, flip)?;
    let v = x::scale(&x::dot(&d, &q)?, flip)?;
    let time = x::scale(&x::dot(&e2, &q)?, flip)?;
    let us = x::sign(&u)?;
    let vs = x::sign(&v)?;
    let ts = x::sign(&time)?;
    let rest = x::sub(&det, &x::add(&u, &v)?)?;
    let rs = x::sign(&rest)?;
    if us < 0 || vs < 0 || rs < 0 || ts < 0 {
        return Some(false);
    }
    if us == 0 || vs == 0 || rs == 0 || ts == 0 {
        return None;
    }
    Some(true)
}
const RAYS: [[f64; 3]; 16] = [
    [1., 2., 3.],
    [2., 3., 5.],
    [3., 5., 7.],
    [5., 7., 11.],
    [7., 11., 13.],
    [11., 13., 17.],
    [13., 17., 19.],
    [17., 19., 23.],
    [-1., 2., 5.],
    [2., -3., 7.],
    [3., 5., -11.],
    [-5., 7., 13.],
    [7., -11., 17.],
    [11., 13., -19.],
    [-13., 17., 23.],
    [17., -19., 29.],
];
fn inside_component(
    k: &Kernel,
    work: &MeshWork,
    source: &SourceManifold<'_>,
    point: [f64; 3],
    component: usize,
) -> Result<Option<bool>> {
    let Some(triangles) = source.components.get(component) else {
        return Ok(None);
    };
    for ray in RAYS {
        work.spend_core(k, 1)?;
        let mut odd = false;
        let mut decided = true;
        for &id in triangles {
            work.spend_core(k, 128)?;
            let Some(t) = source.original_triangle(id) else {
                return Ok(None);
            };
            match ray_hit(point, ray, t) {
                Some(true) => odd = !odd,
                Some(false) => {}
                None => {
                    decided = false;
                    break;
                }
            }
        }
        if decided {
            return Ok(Some(odd));
        }
    }
    Ok(None)
}
pub(crate) fn source_nesting_with_work<'a, 'raw>(
    k: &Kernel,
    work: &MeshWork,
    source: &'a SourceManifold<'raw>,
) -> Result<SourceNestingCover<'a, 'raw>> {
    macro_rules! refuse {
        ($why:expr) => {
            return Ok(SourceNestingCover::Undecided($why))
        };
    }
    work.spend_core(k, 0)?;
    let count = source.components.len();
    if count == 0 || count > 256 || source.signed_volumes.len() != count {
        refuse!("source shell nesting is outside its bounded input contract");
    }
    work.reserve_cells_core(k, count * count + count * 3)?;
    let mut inside = vec![vec![false; count]; count];
    for (a, (component, row)) in source.components.iter().zip(&mut inside).enumerate() {
        let Some(&id) = component.first() else {
            refuse!("a proved source shell has no triangle");
        };
        let Some([point, _, _]) = source.original_triangle(id) else {
            refuse!("an authoritative source shell triangle is missing");
        };
        for (b, value) in row.iter_mut().enumerate() {
            work.spend_core(k, 1)?;
            if a == b {
                continue;
            }
            let Some(classified) = inside_component(k, work, source, point, b)? else {
                refuse!("no exact nondegenerate ray classified a source-shell containment");
            };
            *value = classified;
        }
    }
    let depth: Vec<_> = inside
        .iter()
        .map(|row| row.iter().filter(|&&v| v).count())
        .collect();
    let mut parents = Vec::new();
    let mut outward = Vec::new();
    for (a, ((row_a, &depth_a), volume)) in inside
        .iter()
        .zip(&depth)
        .zip(&source.signed_volumes)
        .enumerate()
    {
        work.spend_core(k, 1)?;
        for (b, (row_b, &depth_b)) in inside.iter().zip(&depth).enumerate() {
            let (Some(&a_in_b), Some(&b_in_a)) = (row_a.get(b), row_b.get(a)) else {
                refuse!("a source-shell containment row is incomplete");
            };
            if a_in_b {
                if b_in_a || depth_b >= depth_a {
                    refuse!("source shell containment is cyclic or inconsistent");
                }
                for (c, row_c) in inside.iter().enumerate() {
                    work.spend_core(k, 1)?;
                    let (Some(&a_in_c), Some(&b_in_c), Some(&c_in_b)) =
                        (row_a.get(c), row_b.get(c), row_c.get(b))
                    else {
                        refuse!("a source-shell nesting chain is incomplete");
                    };
                    if a_in_c && b != c && !b_in_c && !c_in_b {
                        refuse!("source shell containers do not form a nesting chain");
                    }
                }
            }
        }
        let mut parent = None;
        for (b, (&a_in_b, &depth_b)) in row_a.iter().zip(&depth).enumerate() {
            if a_in_b && depth_b + 1 == depth_a && parent.replace(b).is_some() {
                refuse!("source shell immediate container is ambiguous");
            }
        }
        if depth_a > 0 && parent.is_none() {
            refuse!("source shell has no complete immediate container");
        }
        let sign = if volume.is_positive() {
            1
        } else if volume.hi < 0. {
            -1
        } else {
            refuse!("source shell signed volume is not strict");
        };
        let expected = if depth_a % 2 == 0 { 1 } else { -1 };
        if sign != expected {
            refuse!(
                "source outward/cavity orientation does not define material winding zero or one"
            );
        }
        parents.push(parent);
        outward.push(sign > 0);
    }
    work.spend_core(k, 0)?;
    Ok(SourceNestingCover::Proven(SourceNesting {
        _source: source,
        parents,
        outward,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn ray_hits_are_exact_interior_events_not_edge_votes() {
        let t = [[0., 0., 0.], [2., 0., 0.], [0., 2., 0.]];
        assert_eq!(ray_hit([0.5, 0.5, -1.], [0., 0., 1.], t), Some(true));
        assert_eq!(ray_hit([3., 3., -1.], [0., 0., 1.], t), Some(false));
        assert_eq!(ray_hit([1., 1., -1.], [0., 0., 1.], t), None);
        assert_eq!(ray_hit([0.5, 0.5, 0.], [1., 0., 0.], t), None);
    }
    fn nested_boxes(reverse_inner: bool) -> super::super::super::types::MeshInput {
        let mut positions = vec![
            [0., 0., 0.],
            [20., 0., 0.],
            [20., 10., 0.],
            [0., 10., 0.],
            [0., 0., 5.],
            [20., 0., 5.],
            [20., 10., 5.],
            [0., 10., 5.],
        ];
        let outer = vec![
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
        ];
        positions.extend([
            [5., 3., 1.],
            [15., 3., 1.],
            [15., 7., 1.],
            [5., 7., 1.],
            [5., 3., 4.],
            [15., 3., 4.],
            [15., 7., 4.],
            [5., 7., 4.],
        ]);
        let mut triangles = outer.clone();
        triangles.extend(outer.into_iter().map(|mut t| {
            if reverse_inner {
                t.swap(1, 2);
            }
            t.map(|i| i + 8)
        }));
        super::super::super::types::MeshInput {
            positions,
            triangles,
        }
    }
    #[test]
    fn a_negative_inner_shell_is_a_valid_cavity_not_an_inside_out_part() {
        let k = Kernel::new(&crate::kernel::KernelOptions::default());
        let work = MeshWork::new();
        let input = nested_boxes(true);
        let prepared = super::super::super::prepare::prepare_conversion_with_work(
            &k,
            &work,
            &input,
            0.05,
            &[],
        )
        .unwrap();
        let source = match super::super::source_topology::validate_source_weld_with_work(
            &k,
            &work,
            &input.positions,
            &input.triangles,
            &prepared.weld,
        )
        .unwrap()
        {
            super::super::source_topology::SourceTopology::Proven(p) => p,
            super::super::source_topology::SourceTopology::Undecided(why) => {
                panic!("source: {why:?}")
            }
        };
        match source_nesting_with_work(&k, &work, &source).unwrap() {
            SourceNestingCover::Proven(p) => {
                assert_eq!(p.parents, vec![None, Some(0)]);
                assert_eq!(p.outward, vec![true, false]);
            }
            SourceNestingCover::Undecided(why) => panic!("exact cavity nesting: {why}"),
        }
    }
    #[test]
    fn nested_positive_shells_do_not_define_material_winding_zero_or_one() {
        let k = Kernel::new(&crate::kernel::KernelOptions::default());
        let work = MeshWork::new();
        let input = nested_boxes(false);
        let prepared = super::super::super::prepare::prepare_conversion_with_work(
            &k,
            &work,
            &input,
            0.05,
            &[],
        )
        .unwrap();
        let source = match super::super::source_topology::validate_source_weld_with_work(
            &k,
            &work,
            &input.positions,
            &input.triangles,
            &prepared.weld,
        )
        .unwrap()
        {
            super::super::source_topology::SourceTopology::Proven(p) => p,
            super::super::source_topology::SourceTopology::Undecided(why) => {
                panic!("source: {why:?}")
            }
        };
        assert!(matches!(
            source_nesting_with_work(&k, &work, &source).unwrap(),
            SourceNestingCover::Undecided(_)
        ));
    }
}
