//! Exact coordinates on one immutable proven retained source complex (not upstream).
//!
//! The original form owns only per-read expansion conversions; a motion form borrows
//! the exact endpoints of an opaque whole-time `SourceMotion` proof. Neither form
//! rebuilds/welds a `MeshInput` or transfers its discarded-facet mask to a new mesh.
//! This is shared geometric input, NOT final body/native-CW acceptance.
//! Deviations: no recursion; every owned conversion uses the SAME workflow budget.
use super::super::work::MeshWork;
use super::exact_geometry as x;
use super::source_motion::SourceMotion;
use super::source_topology::SourceManifold;
use crate::{Kernel, Result, SolidError};
use std::borrow::Cow;

const OP: &str = "mesh_reconstruction::certificate::source_view";
enum Coordinates<'a, 'raw> {
    Original,
    Motion(&'a SourceMotion<'a, 'raw>),
}
/// Closed construction: callers cannot supply an unproved replacement coordinate array.
pub(crate) struct ExactSourceView<'a, 'raw> {
    source: &'a SourceManifold<'raw>,
    coordinates: Coordinates<'a, 'raw>,
}
impl<'a, 'raw> ExactSourceView<'a, 'raw> {
    pub(crate) fn original(source: &'a SourceManifold<'raw>) -> Self {
        Self {
            source,
            coordinates: Coordinates::Original,
        }
    }
    pub(crate) fn motion(motion: &'a SourceMotion<'a, 'raw>) -> Self {
        Self {
            source: motion.source(),
            coordinates: Coordinates::Motion(motion),
        }
    }
    pub(crate) fn source(&self) -> &'a SourceManifold<'raw> {
        self.source
    }
    pub(crate) fn alias_count(&self) -> usize {
        self.source.alias_count()
    }
    pub(crate) fn raw_triangle_count(&self) -> usize {
        self.source.aliases.len()
    }
    pub(crate) fn retained_triangle_count(&self) -> usize {
        self.source.retained_count
    }
    /// Outer None is out of range; inner None is an independently proved dropped raw facet.
    pub(crate) fn retained_raw_triangle(&self, id: usize) -> Option<Option<[u32; 3]>> {
        self.source.aliases.get(id).copied()
    }
    /// Bound already proved over the WHOLE original retained surface trajectory.
    /// It must be added outward to later model/actual bounds before final adoption.
    pub(crate) fn prior_motion_upper(&self) -> f64 {
        match &self.coordinates {
            Coordinates::Original => 0.,
            Coordinates::Motion(motion) => motion.distance_upper(),
        }
    }
    /// The alias inventory is the original retained CW complex in original raw order.
    pub(crate) fn triangles(&self) -> impl Iterator<Item = (usize, [u32; 3])> + '_ {
        self.source
            .aliases
            .iter()
            .enumerate()
            .filter_map(|(id, t)| t.map(|t| (id, t)))
    }
    /// Transfer the SAME view's complete alias ring into the exact graph checker.
    /// These points are still untrusted there until whole ring/alias binding.
    pub(crate) fn alias_points_with_work(
        &self,
        k: &Kernel,
        work: &MeshWork,
        aliases: &[u32],
    ) -> Result<Vec<x::P>> {
        let mut out = Vec::new();
        for &alias in aliases {
            let point =
                self.position_with_work(k, work, alias)?
                    .ok_or(SolidError::PortInvariant {
                        operation: OP,
                        reason: "proven alias ring point missing",
                    })?;
            let point = match point {
                Cow::Owned(p) => p,
                Cow::Borrowed(p) => copy_point_with_work(k, work, p)?,
            };
            work.reserve_output_core(k, 1)?;
            out.push(point);
        }
        Ok(out)
    }
    pub(crate) fn position_with_work(
        &self,
        k: &Kernel,
        work: &MeshWork,
        alias: u32,
    ) -> Result<Option<Cow<'_, x::P>>> {
        work.spend_core(k, 1)?;
        match &self.coordinates {
            Coordinates::Original => {
                let Some(p) = self.source.position(alias) else {
                    return Ok(None);
                };
                work.reserve_cells_core(k, 4)?;
                let p = x::point(p).ok_or(SolidError::PortInvariant {
                    operation: OP,
                    reason: "proven finite original alias lacks exact coordinates",
                })?;
                Ok(Some(Cow::Owned(p)))
            }
            Coordinates::Motion(motion) => {
                let Some(p) = usize::try_from(alias)
                    .ok()
                    .and_then(|id| motion.endpoints().get(id))
                else {
                    return Ok(None);
                };
                let count = p
                    .iter()
                    .try_fold(1usize, |n, c| n.checked_add(c.len()))
                    .ok_or(SolidError::Unsupported {
                        operation: OP,
                        reason: "exact endpoint storage overflow",
                    })?;
                work.spend_core(k, count)?;
                Ok(Some(Cow::Borrowed(p)))
            }
        }
    }
}

/// Charge every stored expansion component BEFORE copying an exact endpoint.
pub(crate) fn copy_point_with_work(k: &Kernel, work: &MeshWork, p: &x::P) -> Result<x::P> {
    let count = p
        .iter()
        .try_fold(1usize, |n, c| n.checked_add(c.len()))
        .ok_or(SolidError::Unsupported {
            operation: OP,
            reason: "exact point storage count overflow",
        })?;
    work.spend_core(k, count)?;
    work.reserve_cells_core(k, count)?;
    Ok(p.clone())
}
/// Only an input conversion. Complete graph/source alias binding remains mandatory.
pub(crate) fn exact_points_with_work(
    k: &Kernel,
    work: &MeshWork,
    p: &[[f64; 3]],
) -> Result<Vec<x::P>> {
    let mut out = Vec::new();
    for &p in p {
        work.spend_core(k, 1)?;
        work.reserve_cells_core(k, 4)?;
        out.push(x::point(p).ok_or(SolidError::Unsupported {
            operation: OP,
            reason: "source ring coordinate is not finite",
        })?);
    }
    Ok(out)
}
/// Exact dyadic source-cell interpolation; NO rounded endpoint reconstruction.
pub(crate) fn exact_at_with_work(
    k: &Kernel,
    work: &MeshWork,
    a: &x::P,
    b: &x::P,
    t: f64,
) -> Result<x::P> {
    work.spend_core(k, 1)?;
    if !t.is_finite() || !(0.0..=1.0).contains(&t) {
        return Err(SolidError::Unsupported {
            operation: OP,
            reason: "source split is outside unit interval",
        });
    }
    let count = a
        .iter()
        .chain(b)
        .try_fold(1usize, |n, c| n.checked_add(c.len()))
        .and_then(|n| n.checked_mul(8))
        .ok_or(SolidError::Unsupported {
            operation: OP,
            reason: "source split storage count overflow",
        })?;
    // An exact difference has at most la+lb terms; scale at most twice that;
    // adding a needs at most 3la+2lb. Eight times input terms covers both
    // intermediates and final storage. This is a size proof, not epsilon pruning.
    work.spend_core(k, count)?;
    work.reserve_cells_core(k, count)?;
    let coordinate = |a: &x::E, b: &x::E| {
        x::sub(b, a)
            .and_then(|d| x::scale(&d, t))
            .and_then(|d| x::add(a, &d))
    };
    let [ax, ay, az] = a;
    let [bx, by, bz] = b;
    let [Some(x), Some(y), Some(z)] = [coordinate(ax, bx), coordinate(ay, by), coordinate(az, bz)]
    else {
        return Err(SolidError::Unsupported {
            operation: OP,
            reason: "exact source split arithmetic undecided",
        });
    };
    Ok([x, y, z])
}
