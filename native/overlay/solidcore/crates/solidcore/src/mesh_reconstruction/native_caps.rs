//! Actual immutable native incidence and explicit real-join cap allowances.
//! This is not a substitute for cap sectors, collars or material/nesting proof.
use super::certificate::TargetComplex;
use super::certificate::{point_distance_upper, PointBox};
use super::profile_chain::ChainGraphCover;
use super::{MeshError, MeshWork};
use crate::blend::fillet_section::interval::Ivl;
use crate::geom::tol::zone_tol3d;
use crate::topology::{edge, vertex, VertexId};
use crate::Kernel;
const OP: &str = "mesh_reconstruction::profile_native_caps";
type Result<T> = core::result::Result<T, MeshError>;
fn unsure(n: usize) -> MeshError {
    MeshError::Undecided { stage: OP, work: n }
}
pub(crate) struct JoinCap {
    pub(crate) vertex: VertexId,
    pub(crate) native_radius: f64,
    pub(crate) source: PointBox,
    pub(crate) actual_vertex: [f64; 3],
    /// Complete chosen endpoint→native-vertex→endpoint connection lies within
    /// this distance of the corresponding source point by convexity of distance.
    pub(crate) correspondence_upper: f64,
}
/// Bound to the actual immutable native complex and full graph, never to an
/// unverified caller copy of edge geometry or a boolean claim of coincidence.
pub(crate) struct NativeCaps<'a> {
    pub(crate) complex: &'a TargetComplex<'a>,
    pub(crate) graph: &'a ChainGraphCover<'a>,
    pub(crate) caps: Vec<JoinCap>,
}
pub(crate) fn bind_native_caps<'a>(
    k: &Kernel,
    work: &MeshWork,
    complex: &'a TargetComplex<'a>,
    patch: usize,
    rim: usize,
    graph: &'a ChainGraphCover<'a>,
    tolerance: f64,
) -> Result<NativeCaps<'a>> {
    work.check(k)?;
    let b = complex.brep();
    let Some(rim) = complex.patches.get(patch).and_then(|p| p.rims.get(rim)) else {
        return Err(unsure(0));
    };
    if rim.len() != graph.uses.len() || rim.is_empty() || !tolerance.is_finite() || tolerance <= 0.
    {
        return Err(unsure(0));
    }
    work.reserve_output(k, rim.len())?;
    let mut caps = Vec::new();
    for (i, (target, usage)) in rim.iter().zip(graph.uses).enumerate() {
        work.spend(k, 1)?;
        let Some(curve) = edge::curve(b, target.edge)? else {
            return Err(unsure(i));
        };
        // Pointer identity is only a borrow binding, never a geometric hash or ordering.
        if !std::ptr::eq(curve, usage.curve) || usage.forward != target.forward {
            return Err(unsure(i));
        }
        let used = edge::interval(b, target.edge)?;
        if used.min() != usage.interval.min() || used.max() != usage.interval.max() {
            return Err(unsure(i));
        }
        let (start, end) = if target.forward {
            (
                edge::start_vertex(b, target.edge)?,
                edge::end_vertex(b, target.edge)?,
            )
        } else {
            (
                edge::end_vertex(b, target.edge)?,
                edge::start_vertex(b, target.edge)?,
            )
        };
        if start != Some(target.start) || end != Some(target.end) {
            return Err(unsure(i));
        }
        let previous = if i == 0 { rim.last() } else { rim.get(i - 1) }.ok_or_else(|| unsure(i))?;
        if previous.end != target.start {
            return Err(unsure(i));
        }
        let previous_index = if i == 0 { rim.len() - 1 } else { i - 1 };
        work.spend(
            k,
            graph.cells.len().checked_mul(2).ok_or_else(|| unsure(i))?,
        )?;
        let first = graph
            .cells
            .iter()
            .find(|c| c.claim.curve == i)
            .ok_or_else(|| unsure(i))?;
        let last = graph
            .cells
            .iter()
            .rev()
            .find(|c| c.claim.curve == previous_index)
            .ok_or_else(|| unsure(i))?;
        let [source, _] = first.source;
        let [_, incoming] = last.endpoints;
        let [outgoing, _] = first.endpoints;
        let point = vertex::point(b, target.start)?;
        let actual_vertex = [point.x, point.y, point.z];
        if actual_vertex.iter().any(|v| !v.is_finite()) {
            return Err(unsure(i));
        }
        let enclosure = actual_vertex.map(Ivl::from);
        let native_radius = zone_tol3d(k, vertex::tolerance(b, target.start)?);
        // Do not enlarge a native vertex ball with a guessed epsilon/edge tolerance.
        if !native_radius.is_finite()
            || point_distance_upper(incoming, enclosure)? > native_radius
            || point_distance_upper(outgoing, enclosure)? > native_radius
        {
            return Err(unsure(i));
        }
        let upper = point_distance_upper(source, incoming)?
            .max(point_distance_upper(source, outgoing)?)
            .max(point_distance_upper(source, enclosure)?);
        if !crate::geom::certified::above(tolerance, upper) {
            return Err(unsure(i));
        }
        caps.push(JoinCap {
            vertex: target.start,
            native_radius,
            source,
            actual_vertex,
            correspondence_upper: upper,
        });
    }
    work.check(k)?;
    Ok(NativeCaps {
        complex,
        graph,
        caps,
    })
}
