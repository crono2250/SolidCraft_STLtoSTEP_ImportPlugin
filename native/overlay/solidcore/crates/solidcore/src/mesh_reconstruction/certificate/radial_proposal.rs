//! Deterministic source-only proposal for one standalone cone or frustum.
//!
//! Axis hints, affine coordinates, end planes and circle fits here are not
//! certificates. A separate proof rechecks displacement and embedding of this
//! exact alias inventory, all side triangles, filled caps, and final Native
//! geometry. Finish choosing before a body or required proof is attempted.
//! Deviations: none. No recursion. At most the prepared axis budget.
use super::super::frame::FrameGeometry;
use super::super::regions::fit_circle;
use super::super::types::{invalid, Result};
use super::super::work::{MeshWork, Work};
use super::radial_band::RadiusLaw;
use super::radial_frame::AxialEndpointProposal;
use super::radial_source::RadialPatchClaim;
use super::source_view::ExactSourceView;
use crate::eval::Frame;
use crate::math::Vec3;
use crate::Kernel;
use std::collections::{BTreeMap, BTreeSet};

pub(crate) struct RadialSolidProposal {
    pub(crate) chart: AxialEndpointProposal,
    pub(crate) side: RadialPatchClaim,
}

// Original topology determines whether a filled end is one disk. This
// choice prevents a plate's separate outside and hole circles from being
// fitted as one unrelated standalone cone before the required proof starts.
fn one_cap_cycle(k: &Kernel, work: &MeshWork, halfedges: &BTreeSet<(u32, u32)>) -> Result<bool> {
    if halfedges.len() < 3 {
        return Ok(false);
    }
    let mut outgoing = BTreeMap::new();
    let mut incoming = BTreeSet::new();
    for &(a, b) in halfedges {
        work.spend(k, 4096)?;
        work.reserve_cells(k, 4)?;
        if a == b || outgoing.insert(a, b).is_some() || !incoming.insert(b) {
            return Ok(false);
        }
    }
    let Some((&start, _)) = outgoing.first_key_value() else {
        return Ok(false);
    };
    let mut cursor = start;
    for i in 0..halfedges.len() {
        work.spend(k, 4096)?;
        let Some(next) = outgoing.remove(&cursor) else {
            return Ok(false);
        };
        if next == start {
            return Ok(i + 1 == halfedges.len());
        }
        cursor = next;
    }
    Ok(false)
}

fn endpoint_proposal(
    k: &Kernel,
    budget: &MeshWork,
    source: &ExactSourceView<'_, '_>,
    axis: Vec3,
    tolerance: f64,
) -> Result<Option<RadialSolidProposal>> {
    let Some(first) = source.source().position(0) else {
        return Ok(None);
    };
    let origin = Vec3::from_array(first);
    let Some(frame) = Frame::from_normal(origin, axis) else {
        return Ok(None);
    };
    let (u, v, h) = (
        Vec3::from_array(frame.x_axis),
        Vec3::from_array(frame.y_axis),
        frame.normal(),
    );
    let mut rows = Vec::new();
    let mut lo = f64::INFINITY;
    let mut hi = -f64::INFINITY;
    for id in 0..source.alias_count() {
        budget.spend(k, 32)?;
        budget.reserve_cells(k, 4)?;
        let alias =
            u32::try_from(id).map_err(|_| invalid("radial proposal alias index overflow"))?;
        let Some(p) = source.source().position(alias) else {
            return Err(invalid("original alias disappeared from radial proposal"));
        };
        let diff = Vec3::from_array(p) - origin;
        let row = [diff.dot(u), diff.dot(v), diff.dot(h)];
        if row.iter().any(|a| !a.is_finite()) {
            return Ok(None);
        }
        let [_, _, z] = row;
        lo = lo.min(z);
        hi = hi.max(z);
        rows.push(row);
    }
    // Small snapping only proposes a common height. Nothing is moved unless
    // the shared whole-source motion certificate approves the endpoint rows.
    let height = hi - lo;
    let snap = (tolerance * 0.001).min(height * 0.001);
    if !(height.is_finite() && height > 2. * tolerance && snap > 0.) {
        return Ok(None);
    }
    for [_, _, z] in &mut rows {
        budget.spend(k, 4)?;
        if *z - lo <= snap {
            *z = lo;
        } else if hi - *z <= snap {
            *z = hi;
        }
    }
    let mut rings = [BTreeSet::new(), BTreeSet::new()];
    let mut side = Vec::new();
    let mut end_cells = [0_usize; 2];
    let mut end_boundaries = [BTreeSet::new(), BTreeSet::new()];
    for (id, tri) in source.triangles() {
        budget.spend(k, 48)?;
        let heights = tri.map(|v| {
            rows.get(v as usize).map(|p| {
                let [_, _, z] = *p;
                z
            })
        });
        let [Some(a), Some(b), Some(c)] = heights else {
            return Err(invalid("original triangle lost its radial alias"));
        };
        let cap = if a == lo && b == lo && c == lo {
            Some(0)
        } else if a == hi && b == hi && c == hi {
            Some(1)
        } else {
            None
        };
        if let Some(i) = cap {
            end_cells[i] += 1;
            let boundary = &mut end_boundaries[i];
            let [a, b, c] = tri;
            for (u, v) in [(a, b), (b, c), (c, a)] {
                budget.spend(k, 4096)?;
                if !boundary.remove(&(v, u)) {
                    budget.reserve_cells(k, 2)?;
                    if !boundary.insert((u, v)) {
                        return Err(invalid("original cap has duplicate directed use"));
                    }
                }
            }
            continue;
        }
        budget.reserve_output(k, 1)?;
        side.push(id);
        for (alias, z) in tri.into_iter().zip([a, b, c]) {
            if z == lo || z == hi {
                budget.spend(k, 4_096)?;
                budget.reserve_cells(k, 2)?;
                let [lower, upper] = &mut rings;
                if z == lo {
                    lower.insert(alias);
                } else {
                    upper.insert(alias);
                }
            }
        }
    }
    let [lower, upper] = rings;
    let [bottom_faces, top_faces] = end_cells;
    if side.is_empty()
        || (lower.len() == 1) != (bottom_faces == 0)
        || (upper.len() == 1) != (top_faces == 0)
        || upper.len() < 5
        || (lower.len() != 1 && lower.len() < 5)
    {
        return Ok(None);
    }
    let [bottom, top] = &end_boundaries;
    if (bottom_faces != 0 && !one_cap_cycle(k, budget, bottom)?) || !one_cap_cycle(k, budget, top)?
    {
        return Ok(None);
    }
    // If the single apex was at the upper end this axis direction is only a
    // proposal miss. Its opposite will place it at the low end and produce
    // the exact-zero-base cone form used by Native.
    let work = Work::with_budget(k, budget)?;
    let fit = |ring: &BTreeSet<u32>| -> Result<Option<([f64; 2], f64)>> {
        let mut points = Vec::new();
        for alias in ring {
            budget.spend(k, 64)?;
            budget.reserve_cells(k, 4)?;
            let Some(&[x, y, _]) = rows.get(*alias as usize) else {
                return Err(invalid("radial circle alias missing"));
            };
            points.push(Vec3::new(x, y, 0.));
        }
        if let [q] = points.as_slice() {
            return Ok(Some(([q.x, q.y], 0.)));
        }
        Ok(fit_circle(&points, Vec3::Z, &work).map(|(c, r)| ([c.x, c.y], r)))
    };
    let Some(([lx, ly], low_radius)) = fit(&lower)? else {
        work.check()?;
        return Ok(None);
    };
    let Some(([hx, hy], high_radius)) = fit(&upper)? else {
        work.check()?;
        return Ok(None);
    };
    work.check()?;
    if ![lx, ly, hx, hy, low_radius, high_radius]
        .into_iter()
        .all(f64::is_finite)
        || (lx - hx).hypot(ly - hy) > tolerance
        || (low_radius - high_radius).abs() <= tolerance
        || high_radius <= tolerance
        || (low_radius > 0. && low_radius <= tolerance)
    {
        return Ok(None);
    }
    let center = if low_radius == 0. {
        [lx, ly]
    } else {
        [0.5 * lx + 0.5 * hx, 0.5 * ly + 0.5 * hy]
    };
    Ok(Some(RadialSolidProposal {
        chart: AxialEndpointProposal {
            origin: frame.origin,
            columns: [frame.x_axis, frame.y_axis, h.to_array()],
            rows,
        },
        side: RadialPatchClaim {
            triangles: side,
            center,
            law: RadiusLaw {
                height: [lo, hi],
                radius: [low_radius, high_radius],
            },
            concave: false,
        },
    }))
}

pub(crate) fn propose_radial_solid_with_work(
    k: &Kernel,
    work: &MeshWork,
    source: &ExactSourceView<'_, '_>,
    axes: &[Vec3],
    tolerance: f64,
) -> Result<Option<RadialSolidProposal>> {
    for &axis in axes.iter().take(16) {
        for axis in [axis, -axis] {
            if let Some(proposal) = endpoint_proposal(k, work, source, axis, tolerance)? {
                return Ok(Some(proposal));
            }
        }
    }
    work.check(k)?;
    Ok(None)
}

impl RadialSolidProposal {
    /// Native construction of the chosen radial solid. The returned body is
    /// a candidate and must go through the normal canonical re-import and
    /// complete body proof before adoption.
    pub(crate) fn build_candidate(&self, k: &mut Kernel, w: &MeshWork) -> Result<crate::Brep> {
        use crate::geom::axis2_placement::Axis2Placement;
        use crate::primitive::api_primitives::create_cone;
        use crate::topology::brep::p5::transform;

        w.spend(k, 256)?;
        let [lo, hi] = self.side.law.height;
        let [r0, r1] = self.side.law.radius;
        let [cx, cy] = self.side.center;
        let [u, v, h] = self.chart.columns.map(Vec3::from_array);
        let o = Vec3::from_array(self.chart.origin) + cx * u + cy * v + lo * h;
        let frame = Axis2Placement::new(o, u, v);
        let mut b = create_cone(k, Vec3::ZERO, r0, r1, hi - lo)?;
        super::native_radial_topology::construct_exact_cone_seams(k, w, &mut b)?;
        transform(k, &mut b, &frame, None, false)?;
        w.check(k)?;
        Ok(b)
    }
}
