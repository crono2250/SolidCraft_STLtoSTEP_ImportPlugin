//! Exact affine axial coordinates on the SAME original weld-alias inventory.
//!
//! Finite row (u,v,h) denotes EXACTLY O+u*A+v*B+h*C, with a positive
//! non-singular dyadic frame. Rows are numerical proposals until the independent
//! whole-time SourceMotion proves the original surface moves to these points.
//! The borrowed AxialSourceView then binds that motion's exact endpoint owner,
//! so using row coordinates in a radial proof does NOT round world coordinates
//! back to f64 or replace/re-weld the original source.
//!
//! Not an adoption certificate. Source/final material and whole target surface/
//! trim correspondence remain independent mandatory consumers.
//! Deviations: no recursion; shared MeshWork, unchanged source alias count.
use super::super::work::MeshWork;
use super::exact_geometry as x;
use super::source_motion::SourceMotion;
use super::source_view::ExactSourceView;
use crate::blend::fillet_section::interval::Ivl;
use crate::{Kernel, Result, SolidError};

const OP: &str = "mesh_reconstruction::certificate::axial_frame";
fn refused(reason: &'static str) -> SolidError {
    SolidError::Unsupported {
        operation: OP,
        reason,
    }
}
fn invariant(reason: &'static str) -> SolidError {
    SolidError::PortInvariant {
        operation: OP,
        reason,
    }
}
fn charge(k: &Kernel, work: &MeshWork, slots: usize) -> Result<()> {
    let steps = slots
        .checked_mul(16)
        .ok_or_else(|| refused("axial allocation/work overflow"))?;
    work.spend_core(k, steps)?;
    work.reserve_cells_core(k, slots)
}
#[derive(Debug)]
pub(crate) struct AxialEndpointProposal {
    pub(crate) origin: [f64; 3],
    /// Exact affine columns, not claims of orthonormality.
    pub(crate) columns: [[f64; 3]; 3],
    pub(crate) rows: Vec<[f64; 3]>,
}
/// Private factory result. Its points and row/frame inputs stay immutable while
/// the independent source motion and all downstream geometric proofs borrow it.
pub(crate) struct AxialModel<'a> {
    proposal: &'a AxialEndpointProposal,
    points: Vec<x::P>,
    radial_metric: f64,
}
impl AxialModel<'_> {
    pub(crate) fn points(&self) -> &[x::P] {
        &self.points
    }
    pub(crate) fn radial_metric(&self) -> f64 {
        self.radial_metric
    }
    pub(crate) fn proposal(&self) -> &AxialEndpointProposal {
        self.proposal
    }
}
fn iv(v: [f64; 3]) -> [Ivl; 3] {
    v.map(Ivl::from)
}
fn dot(a: [Ivl; 3], b: [Ivl; 3]) -> Ivl {
    a.into_iter()
        .zip(b)
        .fold(Ivl::from(0.), |sum, (x, y)| sum + x * y)
}

/// Build exact coordinate data only; expected_aliases comes from the SAME
/// source preflight, before any row allocation. It is not a geometry verdict.
pub(crate) fn build_axial_model<'a>(
    k: &Kernel,
    work: &MeshWork,
    expected_aliases: usize,
    p: &'a AxialEndpointProposal,
) -> Result<AxialModel<'a>> {
    work.spend_core(k, 32)?;
    if expected_aliases == 0
        || expected_aliases != p.rows.len()
        || !p
            .origin
            .iter()
            .chain(p.columns.iter().flatten())
            .all(|v| v.is_finite())
    {
        return Err(refused(
            "axial frame or original alias inventory is invalid",
        ));
    }
    // Frame scalars are one-term expansions. Cross(A,B) needs at most4
    // terms/component. Its three products by C and complete sum need <=24.
    // 1024 logical coefficient/header slots bounds all actual Native scale/add
    // intermediates, exact determinant, and the fixed interval Gram calculation.
    charge(k, work, 1024)?;
    let [column_a, column_b, column_c] = p.columns;
    let a = x::point(column_a).ok_or_else(|| refused("axial A is outside exact range"))?;
    let b = x::point(column_b).ok_or_else(|| refused("axial B is outside exact range"))?;
    let c = x::point(column_c).ok_or_else(|| refused("axial C is outside exact range"))?;
    let normal =
        x::cross(&a, &b).ok_or_else(|| refused("axial frame cross is outside exact range"))?;
    let determinant =
        x::dot(&normal, &c).ok_or_else(|| refused("axial determinant is outside exact range"))?;
    if x::sign(&determinant) != Some(1) {
        return Err(refused("axial frame is singular or reverses orientation"));
    }
    // Largest row sum of the symmetric2x2 Gram matrix bounds its maximum
    // eigenvalue. This is an upper operator norm of the ACTUAL dyadic lift
    // (du,dv)->du*A+dv*B, never an assumed unit-frame metric.
    let aa = dot(iv(column_a), iv(column_a));
    let bb = dot(iv(column_b), iv(column_b));
    let ab = dot(iv(column_a), iv(column_b));
    let row_a = aa + Ivl::from(ab.mag());
    let row_b = bb + Ivl::from(ab.mag());
    let gram = Ivl::from(row_a.hi.max(row_b.hi));
    let metric = gram.sqrt();
    if !metric.is_finite() || metric.lo <= 0. {
        return Err(refused("axial radial lift is not finitely bounded"));
    }
    let origin =
        x::point(p.origin).ok_or_else(|| refused("axial origin is outside exact range"))?;
    let mut points = Vec::new();
    for row in &p.rows {
        work.spend_core(k, 3)?;
        if !row.iter().all(|v| v.is_finite()) {
            return Err(refused("axial row is not finite"));
        }
        // Per coordinate:3 scalar scales10 each, add(1,2)=9,
        // add(3,2)=15, add(5,2)=21;3*75 plus ownedP/output headers <256.
        // The exact-zero compaction in x changes none of the exact values.
        charge(k, work, 256)?;
        work.reserve_output_core(k, 1)?;
        let coordinate = |o: &x::E, a: &x::E, b: &x::E, c: &x::E| -> Result<x::E> {
            let [u, v, h] = *row;
            let value = x::scale(a, u)
                .and_then(|ua| x::add(o, &ua))
                .and_then(|q| x::add(&q, &x::scale(b, v)?))
                .and_then(|q| x::add(&q, &x::scale(c, h)?))
                .ok_or_else(|| refused("exact axial endpoint expression is outside range"))?;
            if value.is_empty() || value.len() > 7 {
                return Err(invariant("fixed axial endpoint term bound changed"));
            }
            Ok(value)
        };
        let [ox, oy, oz] = &origin;
        let [ax, ay, az] = &a;
        let [bx, by, bz] = &b;
        let [cx, cy, cz] = &c;
        points.push([
            coordinate(ox, ax, bx, cx)?,
            coordinate(oy, ay, by, cy)?,
            coordinate(oz, az, bz, cz)?,
        ]);
    }
    work.spend_core(k, 0)?;
    Ok(AxialModel {
        proposal: p,
        points,
        radial_metric: metric.hi,
    })
}

/// Exact common coordinates of an INDEPENDENTLY proved source motion.
/// Pointer comparison is only immutable borrow/owner binding; it proves no
/// geometry, coincidence, identity hash or cached successful verdict.
pub(crate) struct AxialSourceView<'a, 'frame, 'raw> {
    world: ExactSourceView<'a, 'raw>,
    model: &'a AxialModel<'frame>,
}
impl<'a, 'frame, 'raw> AxialSourceView<'a, 'frame, 'raw> {
    pub(crate) fn bind(
        model: &'a AxialModel<'frame>,
        motion: &'a SourceMotion<'a, 'raw>,
    ) -> Result<Self> {
        if !std::ptr::eq(model.points(), motion.endpoints())
            || model.points().len() != motion.source().alias_count()
            || model.proposal.rows.len() != motion.source().alias_count()
        {
            return Err(refused(
                "axial coordinates are not this source motion's exact endpoint owner",
            ));
        }
        Ok(Self {
            world: ExactSourceView::motion(motion),
            model,
        })
    }
    /// Bind a second cardinal chart to the same complete source motion by
    /// exact equality of every original alias endpoint. No motion is rerun.
    pub(crate) fn bind_same_world(
        k: &Kernel,
        w: &MeshWork,
        model: &'a AxialModel<'frame>,
        motion: &'a SourceMotion<'a, 'raw>,
    ) -> Result<Self> {
        let original = motion.endpoints();
        if original.len() != model.points().len()
            || original.len() != motion.source().alias_count()
            || original.len() != model.proposal.rows.len()
        {
            return Err(refused(
                "second cardinal chart has a different alias inventory",
            ));
        }
        for (a, b) in original.iter().zip(model.points()) {
            w.spend_core(k, 64)?;
            if a != b {
                return Err(refused(
                    "second cardinal chart moves an already bound original endpoint",
                ));
            }
        }
        Ok(Self {
            world: ExactSourceView::motion(motion),
            model,
        })
    }

    pub(crate) fn world(&self) -> &ExactSourceView<'a, 'raw> {
        &self.world
    }
    pub(crate) fn model(&self) -> &AxialModel<'frame> {
        self.model
    }
    pub(crate) fn row_with_work(&self, k: &Kernel, work: &MeshWork, id: u32) -> Result<[f64; 3]> {
        work.spend_core(k, 3)?;
        usize::try_from(id)
            .ok()
            .and_then(|i| self.model.proposal.rows.get(i))
            .copied()
            .ok_or_else(|| invariant("proved axial alias row is missing"))
    }
    pub(crate) fn world_error_upper(&self, local: f64) -> Result<f64> {
        if !local.is_finite() || local < 0. {
            return Err(refused("axial distance is not finite nonnegative"));
        }
        let bound = Ivl::from(local) * Ivl::from(self.model.radial_metric)
            + Ivl::from(self.world.prior_motion_upper());
        if !bound.is_finite() {
            return Err(refused("whole axial world distance overflow"));
        }
        Ok(bound.hi)
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn exact_pose_and_rows_keep_their_affine_geometry() {
        let p = AxialEndpointProposal {
            origin: [10., 20., 30.],
            columns: [[0., 1., 0.], [0., 0., 1.], [1., 0., 0.]],
            rows: vec![[2., 3., 4.], [-1., 2., 5.]],
        };
        let k = Kernel::default();
        let w = MeshWork::new();
        let m = build_axial_model(&k, &w, 2, &p).unwrap();
        assert!(x::equal_point(&m.points()[0], [14., 22., 33.]));
        assert!(x::equal_point(&m.points()[1], [15., 19., 32.]));
        assert!(m.radial_metric() >= 1. && m.radial_metric() < 1.000000000001);
        assert!(std::ptr::eq(m.proposal(), &p));
    }
    #[test]
    fn non_unit_frame_uses_a_proved_radial_metric() {
        let p = AxialEndpointProposal {
            origin: [0.; 3],
            columns: [[3., 0., 0.], [0., 4., 0.], [0., 0., 2.]],
            rows: vec![[1., 2., 3.]],
        };
        let m = build_axial_model(&Kernel::default(), &MeshWork::new(), 1, &p).unwrap();
        assert!(m.radial_metric() >= 4. && m.radial_metric() < 4.00000000001);
        assert!(x::equal_point(&m.points()[0], [3., 8., 6.]));
    }
    #[test]
    fn singular_or_wrong_alias_inventory_never_produces_a_model() {
        let p = AxialEndpointProposal {
            origin: [0.; 3],
            columns: [[1., 0., 0.], [1., 0., 0.], [0., 0., 1.]],
            rows: vec![[0.; 3]],
        };
        assert!(build_axial_model(&Kernel::default(), &MeshWork::new(), 1, &p).is_err());
        assert!(build_axial_model(&Kernel::default(), &MeshWork::new(), 2, &p).is_err());
    }
}
