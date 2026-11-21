//! Actual open planar-sheet trim incidence, separate from a closed solid (not upstream).
//!
//! Every actual planar lamina face and its native loops/edges/vertices are bound. Both
//! face sides and each edge-use mate are checked; no void/material pair is assumed.
//! This is structural evidence only. The consuming sheet verifier must separately
//! bind its actual support/orientation proof and its full source-rim/trim geometry,
//! nesting and noncrossing correspondence before accepting the open sheet.
//!
//! Deviations: none. No recursion; 8192 loops, 262144 boundary uses, shared `MeshWork`.
use super::super::work::MeshWork;
use super::target_complex::TargetEdgeUse;
use crate::kernel::Kernel;
use crate::nurbs::b_spline_surface_n_lib::p2::OrientType;
use crate::surface::surface::SurfaceKind;
use crate::topology::{edge, edgeuse::p1 as eu, face::p2 as face, loopuse};
use crate::topology::{Brep, EdgeuseId, FaceId, FaceuseId, VertexId};
use crate::Result;
use std::collections::BTreeSet;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum OpenFaceRefusal {
    NotPlanarFace,
    InvalidFaceSides,
    NotLamina,
    InvalidLoopIncidence,
    HiddenOrSharedBoundary,
    InputBudget,
}
pub(crate) enum OpenFaceCover<'a> {
    Proven(OpenPlanarFace<'a>),
    Undecided(OpenFaceRefusal),
}
pub(crate) struct OpenPlanarFace<'a> {
    brep: &'a Brep,
    pub(crate) face: FaceId,
    /// Same-oriented side of the actual plane, not a material/void classification.
    pub(crate) faceuse: FaceuseId,
    pub(crate) loops: Vec<Vec<TargetEdgeUse>>,
}
impl<'a> OpenPlanarFace<'a> {
    pub(crate) fn brep(&self) -> &'a Brep {
        self.brep
    }
}
fn start_vertex(b: &Brep, u: EdgeuseId) -> Result<Option<VertexId>> {
    let Some(vu) = b.edgeuse(u)?.vertexuse else {
        return Ok(None);
    };
    Ok(b.vertexuse(vu)?.vertex)
}
/// No failure from the closed-solid extractor is converted into this result. Ops
/// invokes this distinct theorem only for the explicitly planned `PlanarSheet` tool.
pub(crate) fn open_planar_face_with_work<'a>(
    k: &Kernel,
    work: &MeshWork,
    b: &'a Brep,
    f: FaceId,
) -> Result<OpenFaceCover<'a>> {
    macro_rules! refuse {
        ($why:ident) => {
            return Ok(OpenFaceCover::Undecided(OpenFaceRefusal::$why))
        };
    }
    work.spend_core(k, 0)?;
    if !b.face_list().contains(&f) {
        refuse!(NotPlanarFace);
    }
    let Some(surface) = &b.face(f)?.surface else {
        refuse!(NotPlanarFace);
    };
    if !matches!(surface.kind_with_nurb(k)?, SurfaceKind::Plane(_)) {
        refuse!(NotPlanarFace);
    }
    let (Some(a), Some(c)) = face::faceuses(b, f)? else {
        refuse!(InvalidFaceSides);
    };
    let (same, other) = match (b.faceuse(a)?.orientation, b.faceuse(c)?.orientation) {
        (OrientType::Same, OrientType::Opposite) => (a, c),
        (OrientType::Opposite, OrientType::Same) => (c, a),
        _ => {
            refuse!(InvalidFaceSides);
        }
    };
    for (u, m) in [(same, other), (other, same)] {
        work.spend_core(k, 1)?;
        if b.faceuse(u)?.face != Some(f) || b.faceuse(u)?.mate != Some(m) {
            refuse!(InvalidFaceSides);
        }
    }
    let native_loops = &b.faceuse(same)?.loopuses;
    if native_loops.is_empty() || native_loops.len() > 8192 {
        refuse!(InputBudget);
    }
    let mut loop_ids = BTreeSet::new();
    let mut edges = BTreeSet::new();
    let mut vertices = BTreeSet::new();
    let mut mates = BTreeSet::new();
    let mut loops = Vec::new();
    let mut count = 0usize;
    for &lu in native_loops {
        work.spend_core(k, 1)?;
        if !loop_ids.insert(lu) {
            refuse!(InvalidLoopIncidence);
        }
        let list = loopuse::edgeuses(b, lu, None, None)?;
        if list.is_empty() || list.len() > 262144 - count {
            refuse!(InputBudget);
        }
        work.reserve_cells_core(k, list.len())?;
        count += list.len();
        let mut rim = Vec::new();
        let mut uses = BTreeSet::new();
        for (index, &u) in list.iter().enumerate() {
            work.spend_core(k, 1)?;
            if !uses.insert(u) || eu::faceuse(b, u)? != Some(same) {
                refuse!(InvalidLoopIncidence);
            }
            let record = b.edgeuse(u)?;
            let Some(e) = record.edge else {
                refuse!(InvalidLoopIncidence);
            };
            if !edges.insert(e) {
                refuse!(HiddenOrSharedBoundary);
            }
            let (Some(a), Some(z)) = edge::start_end_vertices(b, e)? else {
                refuse!(InvalidLoopIncidence);
            };
            let forward = match record.orientation {
                OrientType::Same => true,
                OrientType::Opposite => false,
                OrientType::Unknown => {
                    refuse!(InvalidLoopIncidence);
                }
            };
            let (start, end) = if forward { (a, z) } else { (z, a) };
            let Some(&next) = list.get(index + 1).or_else(|| list.first()) else {
                refuse!(InvalidLoopIncidence);
            };
            if record.ccw != Some(next)
                || b.edgeuse(next)?.cw != Some(u)
                || start_vertex(b, u)? != Some(start)
                || start_vertex(b, next)? != Some(end)
                || !vertices.insert(start)
            {
                refuse!(InvalidLoopIncidence);
            }
            let Some(m) = eu::mate(b, u)? else {
                refuse!(NotLamina);
            };
            let pair = &b.edge(e)?.edgeuses;
            if pair.len() != 2
                || !pair.contains(&u)
                || !pair.contains(&m)
                || !mates.insert(m)
                || b.edgeuse(m)?.edge != Some(e)
                || eu::mate(b, m)? != Some(u)
                || eu::faceuse(b, m)? != Some(other)
                || start_vertex(b, m)? != Some(end)
                || b.edgeuse(m)?.orientation
                    != if forward {
                        OrientType::Opposite
                    } else {
                        OrientType::Same
                    }
            {
                refuse!(NotLamina);
            }
            rim.push(TargetEdgeUse {
                edge: e,
                use_id: u,
                face: f,
                faceuse: same,
                start,
                end,
                forward,
            });
        }
        loops.push(rim);
    }
    // Every opposite-side loop use must be the mate of exactly one inspected use.
    let other_loops = &b.faceuse(other)?.loopuses;
    if other_loops.len() != native_loops.len() {
        refuse!(InvalidLoopIncidence);
    }
    let mut other_seen = BTreeSet::new();
    for &lu in other_loops {
        work.spend_core(k, 1)?;
        for u in loopuse::edgeuses(b, lu, None, None)? {
            work.spend_core(k, 1)?;
            if !mates.contains(&u) || !other_seen.insert(u) {
                refuse!(InvalidLoopIncidence);
            }
        }
    }
    if other_seen != mates {
        refuse!(InvalidLoopIncidence);
    }
    work.spend_core(k, 0)?;
    Ok(OpenFaceCover::Proven(OpenPlanarFace {
        brep: b,
        face: f,
        faceuse: same,
        loops,
    }))
}

/// A complete immutable assignment of every actual final planar lamina face.
/// Geometrically disjoint components and source/component correspondence are separate
/// obligations. A shared-edge subdivision is deliberately undecided by this sufficient
/// lamina theorem; it never silently drops an extra face from a union's final result.
pub(crate) struct OpenPlanarComplex<'a> {
    brep: &'a Brep,
    pub(crate) faces: Vec<OpenPlanarFace<'a>>,
}
impl<'a> OpenPlanarComplex<'a> {
    pub(crate) fn brep(&self) -> &'a Brep {
        self.brep
    }
}
pub(crate) enum OpenComplexCover<'a> {
    Proven(OpenPlanarComplex<'a>),
    Undecided(OpenFaceRefusal),
}
pub(crate) fn open_planar_faces_with_work<'a>(
    k: &Kernel,
    work: &MeshWork,
    b: &'a Brep,
) -> Result<OpenComplexCover<'a>> {
    macro_rules! refuse {
        ($why:ident) => {
            return Ok(OpenComplexCover::Undecided(OpenFaceRefusal::$why))
        };
    }
    work.spend_core(k, 0)?;
    if b.face_list().is_empty() || b.face_list().len() > 8192 {
        refuse!(InputBudget);
    }
    let mut face_ids = BTreeSet::new();
    let mut edges = BTreeSet::new();
    let mut vertices = BTreeSet::new();
    let mut faces = Vec::new();
    let mut count = 0usize;
    for &f in b.face_list() {
        work.spend_core(k, 1)?;
        if !face_ids.insert(f) {
            refuse!(HiddenOrSharedBoundary);
        }
        let face = match open_planar_face_with_work(k, work, b, f)? {
            OpenFaceCover::Proven(face) => face,
            OpenFaceCover::Undecided(why) => return Ok(OpenComplexCover::Undecided(why)),
        };
        for rim in &face.loops {
            for u in rim {
                work.spend_core(k, 1)?;
                if count >= 262144 {
                    refuse!(InputBudget);
                }
                count += 1;
                if !edges.insert(u.edge) || !vertices.insert(u.start) {
                    refuse!(HiddenOrSharedBoundary);
                }
            }
        }
        work.reserve_output_core(k, 1)?;
        faces.push(face);
    }
    if edges.len() != b.edge_list().len() || vertices.len() != b.vertex_list().len() {
        refuse!(HiddenOrSharedBoundary);
    }
    Ok(OpenComplexCover::Proven(OpenPlanarComplex {
        brep: b,
        faces,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::curve::{curve::Curve, line::Line};
    use crate::kernel::KernelOptions;
    use crate::math::Point3;
    fn rectangle(x0: f64, y0: f64, x1: f64, y1: f64, reverse: bool) -> Vec<Curve> {
        let mut points = [
            Point3::new(x0, y0, 0.),
            Point3::new(x1, y0, 0.),
            Point3::new(x1, y1, 0.),
            Point3::new(x0, y1, 0.),
        ];
        if reverse {
            points.reverse();
        }
        (0..4)
            .map(|i| Curve::from(Line::from_points(points[i], points[(i + 1) % 4], 3)))
            .collect()
    }
    #[test]
    fn actual_native_sheet_hole_keeps_every_loop() {
        let mut k = Kernel::new(&KernelOptions::default());
        let mut curves = rectangle(0., 0., 10., 10., false);
        curves.extend(rectangle(3., 3., 7., 7., true));
        let b = crate::primitive::api_trim_ops::create_planar_faces(&mut k, &curves).unwrap();
        let work = MeshWork::new();
        match open_planar_faces_with_work(&k, &work, &b).unwrap() {
            OpenComplexCover::Proven(p) => {
                assert_eq!(p.faces.len(), 1);
                assert_eq!(p.faces[0].loops.len(), 2);
                assert_eq!(p.faces[0].loops.iter().map(Vec::len).sum::<usize>(), 8);
            }
            OpenComplexCover::Undecided(why) => {
                panic!("actual lamina trim extraction declined: {why:?}")
            }
        }
    }
    #[test]
    fn closed_box_is_never_adopted_as_a_sheet() {
        let mut k = Kernel::new(&KernelOptions::default());
        let b = crate::primitive::api_primitives::create_box(
            &mut k,
            Point3::new(0., 0., 0.),
            20.,
            10.,
            5.,
        )
        .unwrap();
        assert!(matches!(
            open_planar_faces_with_work(&k, &MeshWork::new(), &b).unwrap(),
            OpenComplexCover::Undecided(_)
        ));
    }
}
