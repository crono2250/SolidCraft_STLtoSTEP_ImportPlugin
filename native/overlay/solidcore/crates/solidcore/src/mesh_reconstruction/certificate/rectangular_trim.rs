//! Exact complete UV-rectangle trim proof (not upstream).
//!
//! Every actual native trim is a complete affine UV segment, every oriented end
//! exactly meets its next end, and the segments partition each domain side once.
//! Thus the sole simple closed loop is exactly the rectangle boundary. Cached
//! `rectangular_trim` flags, corner classifications and sample probes are not proof.
//! This certifies the PARAMETER domain only, not its 3D embedding or material map.
//! A separate `RectangleLayout` is explicitly ONLY a coherent parameter-witness claim;
//! its constructor shares native-loop extraction but never asserts the raw predicate.
//!
//! Deviations: none. No recursion; 8192 trim uses and shared `MeshWork` guards.
use super::super::work::MeshWork;
use super::exact_geometry as x;
use super::exact_planar::affine_ends;
use crate::kernel::Kernel;
use crate::mass::integrator::properties::region_material;
use crate::nurbs::b_spline_surface_n_lib::p2::OrientType;
use crate::topology::{edgeuse::p1 as eu, loopuse, Brep, EdgeId, EdgeuseId, FaceId, FaceuseId};
use crate::Result;

pub(crate) struct RectangleEdge {
    pub(crate) edge: EdgeId,
    pub(crate) use_id: EdgeuseId,
    /// Actual UV expression in the material-boundary use's traversal order.
    pub(crate) ends: [x::P; 2],
}
pub(crate) struct RectangleTrim<'a> {
    pub(crate) rebuilt: &'a Brep,
    pub(crate) face: FaceId,
    pub(crate) faceuse: FaceuseId,
    /// umin, umax, vmin, vmax, copied only after every actual trim was checked.
    pub(crate) domain: [f64; 4],
    pub(crate) edges: Vec<RectangleEdge>,
}
/// An UNTRUSTED coherent parameter-rectangle layout, not a trim certificate.
/// `ends` are chosen exact rectangle sides in actual use order. A consumer must
/// still prove every complete stored UV root/S image fits the SAME model boundary
/// and native edge/vertex zones, plus whole surface/model/CW/material obligations.
pub(crate) struct RectangleLayout<'a> {
    pub(crate) rebuilt: &'a Brep,
    pub(crate) face: FaceId,
    pub(crate) faceuse: FaceuseId,
    pub(crate) domain: [f64; 4],
    pub(crate) edges: Vec<RectangleEdge>,
}
impl<'a> RectangleTrim<'a> {
    /// Forget proof strength when feeding the common final product verifier; an
    /// exact raw rectangle is also one permissible coherent rectangle layout.
    pub(crate) fn into_layout(self) -> RectangleLayout<'a> {
        RectangleLayout {
            rebuilt: self.rebuilt,
            face: self.face,
            faceuse: self.faceuse,
            domain: self.domain,
            edges: self.edges,
        }
    }
}
fn eq(a: &x::E, b: &x::E) -> bool {
    x::sub(a, b).is_some_and(|d| x::zero(&d))
}
fn order(a: &x::E, b: &x::E) -> Option<i32> {
    x::sub(a, b).and_then(|d| x::sign(&d))
}
fn same_point(a: &x::P, b: &x::P) -> bool {
    x::difference(a, b).is_some_and(|d| d.iter().all(x::zero))
}
/// Verifies the complete domain boundary with one winding, allowing collinear
/// subdivisions. A missing/overlapping segment cannot disappear in this partition.
fn rectangle_boundary(
    k: &Kernel,
    work: &MeshWork,
    domain: [f64; 4],
    ends: &[[x::P; 2]],
) -> Result<bool> {
    let [umin, umax, vmin, vmax] = domain;
    if !(domain.iter().all(|p| p.is_finite()) && umin < umax && vmin < vmax)
        || ends.len() < 4
        || ends.len() > 8192
    {
        return Ok(false);
    }
    let [Some(umin), Some(umax), Some(vmin), Some(vmax)] = domain.map(x::scalar) else {
        return Ok(false);
    };
    let mut sides: [Vec<(x::E, x::E)>; 4] = core::array::from_fn(|_| Vec::new());
    let mut winding = None;
    for (i, [a, b]) in ends.iter().enumerate() {
        work.spend_core(k, 1)?;
        let Some([next, _]) = ends.get(i + 1).or_else(|| ends.first()) else {
            return Ok(false);
        };
        let [au, av, az] = a;
        let [bu, bv, bz] = b;
        if !a.iter().chain(b).all(|p| x::sign(p).is_some())
            || !x::zero(az)
            || !x::zero(bz)
            || !same_point(b, next)
        {
            return Ok(false);
        }
        let candidates = [
            (av, bv, &vmin, au, bu, &umin, &umax, 1),
            (au, bu, &umax, av, bv, &vmin, &vmax, 1),
            (av, bv, &vmax, au, bu, &umin, &umax, -1),
            (au, bu, &umin, av, bv, &vmin, &vmax, -1),
        ];
        let mut found = None;
        for (side, (ac, bc, boundary, avar, bvar, min, max, direction)) in
            candidates.into_iter().enumerate()
        {
            if !eq(ac, boundary) || !eq(bc, boundary) {
                continue;
            }
            let Some(sign) = order(bvar, avar) else {
                return Ok(false);
            };
            if sign == 0 {
                return Ok(false);
            }
            let (lo, hi) = if sign > 0 { (avar, bvar) } else { (bvar, avar) };
            if order(lo, min).is_none_or(|s| s < 0) || order(max, hi).is_none_or(|s| s < 0) {
                return Ok(false);
            }
            if found.is_some() {
                return Ok(false);
            }
            found = Some((side, lo.clone(), hi.clone(), sign * direction));
        }
        let Some((side, lo, hi, sense)) = found else {
            return Ok(false);
        };
        if winding.is_some_and(|w| w != sense) {
            return Ok(false);
        }
        winding = Some(sense);
        work.reserve_cells_core(k, 1)?;
        let Some(segments) = sides.get_mut(side) else {
            return Ok(false);
        };
        segments.push((lo, hi));
    }
    for (side, segments) in sides.into_iter().enumerate() {
        work.spend_core(k, 1)?;
        let (min, max) = if side == 0 || side == 2 {
            (&umin, &umax)
        } else {
            (&vmin, &vmax)
        };
        let mut cursor = min.clone();
        work.reserve_cells_core(k, segments.len())?;
        let mut used = vec![false; segments.len()];
        for _ in 0..segments.len() {
            let mut next = None;
            for (i, ((lo, _), &already_used)) in segments.iter().zip(&used).enumerate() {
                work.spend_core(k, 1)?;
                if !already_used && eq(lo, &cursor) && next.replace(i).is_some() {
                    return Ok(false);
                }
            }
            let Some(i) = next else { return Ok(false) };
            let (Some(mark), Some((_, hi))) = (used.get_mut(i), segments.get(i)) else {
                return Ok(false);
            };
            *mark = true;
            cursor.clone_from(hi);
        }
        if !eq(&cursor, max) {
            return Ok(false);
        }
    }
    Ok(true)
}
/// `faceuse` is a candidate only: actual face ownership, mate and material regions
/// are re-read. This does not accept an arbitrary caller-selected UV loop.
pub(super) fn actual_affine_loop_with_work<'a>(
    k: &Kernel,
    work: &MeshWork,
    b: &'a Brep,
    face: FaceId,
    faceuse: FaceuseId,
) -> Result<Option<RectangleLayout<'a>>> {
    work.spend_core(k, 0)?;
    let record = b.faceuse(faceuse)?;
    if record.face != Some(face) {
        return Ok(None);
    }
    let Some(mate) = record.mate else {
        return Ok(None);
    };
    if b.faceuse(mate)?.face != Some(face) || b.faceuse(mate)?.mate != Some(faceuse) {
        return Ok(None);
    }
    let (Some(a), Some(c)) = (
        eu::faceuse_region(b, faceuse)?,
        eu::faceuse_region(b, mate)?,
    ) else {
        return Ok(None);
    };
    if region_material(b, a)? || !region_material(b, c)? {
        return Ok(None);
    }
    let loops = &record.loopuses;
    let [lu] = loops.as_slice() else {
        return Ok(None);
    };
    let d = b.face(face)?.uv_domain;
    if !d.is_bounded() {
        return Ok(None);
    }
    let domain = [d.u_min(), d.u_max(), d.v_min(), d.v_max()];
    let mut uses = Vec::new();
    let complete = loopuse::visit_edgeuses_bounded(b, *lu, 8192, |id| {
        work.spend_core(k, 1)?;
        work.reserve_cells_core(k, 1)?;
        uses.push(id);
        Ok(())
    })?;
    if !complete || uses.len() < 3 {
        return Ok(None);
    }
    work.reserve_cells_core(k, uses.len())?;
    let mut edges = Vec::new();
    for u in uses {
        work.spend_core(k, 1)?;
        let record = b.edgeuse(u)?;
        let Some(edge) = record.edge else {
            return Ok(None);
        };
        let (Some(curve), _) = eu::uv_trim_curve(b, u)? else {
            return Ok(None);
        };
        work.reserve_cells_core(k, 2)?;
        let Some(mut ends) = affine_ends(curve, b.edge(edge)?.interval, true) else {
            return Ok(None);
        };
        match record.orientation {
            OrientType::Same => {}
            OrientType::Opposite => ends.swap(0, 1),
            OrientType::Unknown => return Ok(None),
        }
        edges.push(RectangleEdge {
            edge,
            use_id: u,
            ends,
        });
    }
    Ok(Some(RectangleLayout {
        rebuilt: b,
        face,
        faceuse,
        domain,
        edges,
    }))
}

/// The ORIGINAL exact raw UV predicate remains unchanged: no tolerance expansion,
/// rectangular flag, clamped-endpoint substitute or coherent-layout claim passes it.
pub(crate) fn prove_rectangular_trim_with_work<'a>(
    k: &Kernel,
    work: &MeshWork,
    b: &'a Brep,
    face: FaceId,
    faceuse: FaceuseId,
) -> Result<Option<RectangleTrim<'a>>> {
    let Some(layout) = actual_affine_loop_with_work(k, work, b, face, faceuse)? else {
        return Ok(None);
    };
    work.reserve_cells_core(k, layout.edges.len())?;
    let ends: Vec<_> = layout.edges.iter().map(|e| e.ends.clone()).collect();
    if !rectangle_boundary(k, work, layout.domain, &ends)? {
        return Ok(None);
    }
    Ok(Some(RectangleTrim {
        rebuilt: b,
        face,
        faceuse,
        domain: layout.domain,
        edges: layout.edges,
    }))
}
/// Choose one exact corner cycle as STEERING ONLY. Nearest first corner is a
/// deterministic exact comparison, not geometric acceptance; all actual roots
/// must subsequently fit the SAME chosen model/native zones. No retry is made.
pub(crate) fn rectangle_layout_claim_with_work<'a>(
    k: &Kernel,
    work: &MeshWork,
    b: &'a Brep,
    face: FaceId,
    faceuse: FaceuseId,
) -> Result<Option<RectangleLayout<'a>>> {
    let Some(mut layout) = actual_affine_loop_with_work(k, work, b, face, faceuse)? else {
        return Ok(None);
    };
    if layout.edges.len() != 4 {
        return Ok(None);
    }
    let [umin, umax, vmin, vmax] = layout.domain;
    if !(layout.domain.iter().all(|v| v.is_finite()) && umin < umax && vmin < vmax) {
        return Ok(None);
    }
    let sense = match b.faceuse(faceuse)?.orientation {
        OrientType::Same => true,
        OrientType::Opposite => false,
        OrientType::Unknown => return Ok(None),
    };
    work.reserve_cells_core(k, 4)?;
    let [Some(a), Some(c), Some(d), Some(e)] = [
        [umin, vmin, 0.],
        [umax, vmin, 0.],
        [umax, vmax, 0.],
        [umin, vmax, 0.],
    ]
    .map(x::point) else {
        return Ok(None);
    };
    let corners = [a, c, d, e];
    let Some(first) = layout.edges.first().and_then(|e| e.ends.first()) else {
        return Ok(None);
    };
    let mut chosen = None;
    for (index, corner) in corners.iter().enumerate() {
        work.spend_core(k, 1)?;
        let Some(distance) = x::difference(first, corner).and_then(|d| x::dot(&d, &d)) else {
            return Ok(None);
        };
        let replace = match &chosen {
            None => true,
            Some((_, old)) => match x::sub(&distance, old).and_then(|d| x::sign(&d)) {
                Some(s) => s < 0,
                None => return Ok(None),
            },
        };
        if replace {
            chosen = Some((index, distance));
        }
    }
    let Some((start, _)) = chosen else {
        return Ok(None);
    };
    for (i, edge) in layout.edges.iter_mut().enumerate() {
        work.spend_core(k, 1)?;
        let at = |i: usize| -> Option<usize> {
            if sense {
                start.checked_add(i)?.checked_rem(4)
            } else {
                start.checked_add(4)?.checked_sub(i)?.checked_rem(4)
            }
        };
        let (Some(a), Some(z)) = (
            at(i).and_then(|i| corners.get(i)),
            i.checked_add(1).and_then(at).and_then(|i| corners.get(i)),
        ) else {
            return Ok(None);
        };
        work.reserve_cells_core(k, 2)?;
        edge.ends = [a.clone(), z.clone()];
    }
    Ok(Some(layout))
}

/// Complete rectangle of a finite Native cone with one implicit collapsed
/// side. Native stores no 3D edge for that side. Both consecutive seam uses
/// must share exactly the same actual apex vertex. The full missing segment
/// is allowed only at the analytic cone's exact zero-radius end.
pub(crate) fn prove_implicit_pole_rectangle_with_work<'a>(
    k: &Kernel,
    work: &MeshWork,
    b: &'a Brep,
    id: FaceId,
    use_id: FaceuseId,
    values: &super::analytic_ruling::NativeRadialValues<'_>,
) -> Result<Option<(RectangleTrim<'a>, crate::topology::VertexId)>> {
    use crate::surface::surface::SurfaceKind;
    let Some(surface) = crate::topology::face::p2::surface(b, id)? else {
        return Ok(None);
    };
    let SurfaceKind::Cone(cone) = surface.kind() else {
        return Ok(None);
    };
    if !core::ptr::eq(values.authority().definition(), surface)
        || cone.base_radius() != 0.
        || cone.rev().step_uv_domain().v_min() != 0.
        || cone.rev().is_out_of_bounds_enabled()
    {
        return Ok(None);
    }
    let Some(layout) = actual_affine_loop_with_work(k, work, b, id, use_id)? else {
        return Ok(None);
    };
    if layout.domain != values.authority().domain() || layout.edges.len() != 3 {
        return Ok(None);
    }
    let swap = cone.rev().swap_uv();
    let height_coordinate = usize::from(!swap);
    let arc_coordinate = usize::from(swap);
    let [u0, u1, v0, v1] = layout.domain;
    let (lo, hi, length) = if swap {
        (u0, u1, [v0, v1])
    } else {
        (v0, v1, [u0, u1])
    };
    let boundary = if cone.inside_out() { hi } else { lo };
    let at_pole = |p: &x::P| x::scalar(boundary).is_some_and(|v| eq(&p[height_coordinate], &v));
    let arc_ends = |a: &x::P, z: &x::P| {
        let [Some(lo), Some(hi)] = length.map(x::scalar) else {
            return false;
        };
        let (p, q) = (&a[arc_coordinate], &z[arc_coordinate]);
        (eq(p, &lo) && eq(q, &hi)) || (eq(p, &hi) && eq(q, &lo))
    };
    let mut implicit = None;
    let mut ends = Vec::new();
    for (prev, next) in layout.edges.iter().zip(layout.edges.iter().cycle().skip(1)) {
        work.spend_core(k, 128)?;
        work.reserve_cells_core(k, 64)?;
        ends.push(prev.ends.clone());
        let (a, z) = (&prev.ends[1], &next.ends[0]);
        if same_point(a, z) {
            continue;
        }
        if implicit.is_some()
            || prev.edge != next.edge
            || !at_pole(a)
            || !at_pole(z)
            || !arc_ends(a, z)
            || b.edgeuse(prev.use_id)?.orientation == b.edgeuse(next.use_id)?.orientation
        {
            return Ok(None);
        }
        let Some(vuse) = eu::vertexuse(b, next.use_id)? else {
            return Ok(None);
        };
        let Some(v) = crate::topology::vertexuse::vertex(b, vuse)? else {
            return Ok(None);
        };
        let prev_end = match b.edgeuse(prev.use_id)?.orientation {
            OrientType::Same => crate::topology::edge::end_vertex(b, prev.edge)?,
            OrientType::Opposite => crate::topology::edge::start_vertex(b, prev.edge)?,
            OrientType::Unknown => return Ok(None),
        };
        if prev_end != Some(v) {
            return Ok(None);
        }
        let v3 = crate::topology::vertex::point(b, v)?;
        let analytic = cone.rev().position().origin();
        let region_radius = b.tolerance().max(crate::topology::vertex::tolerance(b, v)?);
        let Some(point) = x::vec(v3) else {
            return Ok(None);
        };
        let Some(pole) = x::vec(analytic) else {
            return Ok(None);
        };
        let Some(delta) = x::difference(&point, &pole) else {
            return Ok(None);
        };
        let Some(squared) = x::dot(&delta, &delta).and_then(|e| x::interval(&e)) else {
            return Ok(None);
        };
        let tol = crate::blend::fillet_section::interval::Ivl::from(region_radius);
        if !(region_radius.is_finite() && region_radius > 0.) || squared.hi > (tol * tol).lo {
            return Ok(None);
        }
        implicit = Some(v);
        ends.push([a.clone(), z.clone()]);
    }
    let Some(apex) = implicit else {
        return Ok(None);
    };
    if !rectangle_boundary(k, work, layout.domain, &ends)? {
        return Ok(None);
    }
    Ok(Some((
        RectangleTrim {
            rebuilt: b,
            face: id,
            faceuse: use_id,
            domain: layout.domain,
            edges: layout.edges,
        },
        apex,
    )))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::KernelOptions;
    fn p(x: f64, y: f64) -> x::P {
        x::point([x, y, 0.]).unwrap()
    }
    #[test]
    fn complete_rectangle_allows_boundary_subdivision() {
        let k = Kernel::new(&KernelOptions::default());
        let work = MeshWork::new();
        let ring = [p(0., 0.), p(0.25, 0.), p(1., 0.), p(1., 2.), p(0., 2.)];
        let edges: Vec<_> = (0..ring.len())
            .map(|i| [ring[i].clone(), ring[(i + 1) % ring.len()].clone()])
            .collect();
        assert!(rectangle_boundary(&k, &work, [0., 1., 0., 2.], &edges).unwrap());
    }
    #[test]
    fn corner_samples_cannot_hide_an_interior_diagonal() {
        let k = Kernel::new(&KernelOptions::default());
        let work = MeshWork::new();
        let ring = [p(0., 0.), p(1., 0.), p(0., 2.), p(1., 2.)];
        let edges: Vec<_> = (0..ring.len())
            .map(|i| [ring[i].clone(), ring[(i + 1) % ring.len()].clone()])
            .collect();
        assert!(!rectangle_boundary(&k, &work, [0., 1., 0., 2.], &edges).unwrap());
    }
}
