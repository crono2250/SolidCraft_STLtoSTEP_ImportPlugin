//! Coaxial joins and disjoint radial motion envelopes in the exact source chart.
//!
//! Each input patch already covers its finite (angle,height) domain. A band
//! join uses the same actual source edge cycle with reversed incidence, at the
//! same height and radius. Consequently the two radial homotopies agree along
//! the entire join. Different bores stay disjoint if the sum of their outer
//! radius envelopes is strictly smaller than centre separation at every
//! common height. A concentric bore stays inside its outer wall if the two
//! annular envelopes are strictly nested. The radius terms are affine within
//! each overlap, so the complete tests use the two ends of each overlap.
//!
//! This does not cover a polygonal stock wall, cap or canonical Native trim.
//! Deviations: none. Work/cell admission uses the shared MeshWork.
use super::super::work::MeshWork;
use super::radial_band::RadiusLaw;
use super::radial_source::SourceRadialPatch;
use crate::blend::fillet_section::interval::Ivl;
use crate::{Kernel, Result, SolidError};
use std::collections::BTreeSet;

const OP: &str = "mesh_reconstruction::certificate::radial_stack";
fn refusal(reason: &'static str) -> SolidError {
    SolidError::Unsupported {
        operation: OP,
        reason,
    }
}

pub(crate) struct SourceRadialStack<'a, 's, 'v, 'f, 'r> {
    patches: &'a [SourceRadialPatch<'s, 'v, 'f, 'r>],
    world_upper: f64,
}
impl<'a, 's, 'v, 'f, 'r> SourceRadialStack<'a, 's, 'v, 'f, 'r> {
    pub(crate) fn patches(&self) -> &'a [SourceRadialPatch<'s, 'v, 'f, 'r>] {
        self.patches
    }
    pub(crate) fn world_upper(&self) -> f64 {
        self.world_upper
    }
}

/// The two cycles may have different starting aliases. They must comprise the
/// same directed edges, in opposite senses, with no omitted or duplicated link.
pub(super) fn opposite_ring(k: &Kernel, w: &MeshWork, left: &[u32], right: &[u32]) -> Result<bool> {
    if left.len() != right.len() || left.len() < 3 {
        return Ok(false);
    }
    w.spend_core(k, right.len())?;
    let Some(first) = left.first() else {
        return Ok(false);
    };
    let Some(start) = right.iter().position(|x| x == first) else {
        return Ok(false);
    };
    // Reversing the prefix ending at the anchor, then the tail, gives a
    // complete cycle in opposite order without input-dependent modulo.
    let Some(prefix) = right.get(..=start) else {
        return Ok(false);
    };
    let Some(tail) = right.get(start + 1..) else {
        return Ok(false);
    };
    w.spend_core(k, left.len())?;
    Ok(left.iter().eq(prefix.iter().rev().chain(tail.iter().rev())))
}

pub(super) fn rim_at<'a>(
    k: &Kernel,
    w: &MeshWork,
    band: &'a SourceRadialPatch<'_, '_, '_, '_>,
    level: f64,
) -> Result<&'a [u32]> {
    for rim in band.rims() {
        let Some(&id) = rim.first() else {
            return Err(refusal("source band rim is empty"));
        };
        let [_, _, height] = band.source().row_with_work(k, w, id)?;
        if height == level {
            return Ok(rim);
        }
    }
    Err(refusal("shared positive radius level has no source rim"))
}

pub(crate) fn prove_source_radial_stack_with_work<'a, 's, 'v, 'f, 'r>(
    k: &Kernel,
    w: &MeshWork,
    patches: &'a [SourceRadialPatch<'s, 'v, 'f, 'r>],
) -> Result<SourceRadialStack<'a, 's, 'v, 'f, 'r>> {
    let first = patches
        .first()
        .ok_or_else(|| refusal("empty radial stack"))?;
    let mut seen = BTreeSet::new();
    let mut world_upper = 0_f64;
    for patch in patches {
        w.spend_core(k, 1)?;
        if !core::ptr::eq(first.source(), patch.source())
            || patch.claim().center != first.claim().center
            || patch.claim().concave != first.claim().concave
        {
            return Err(refusal(
                "radial stack has distinct chart, axis or material senses",
            ));
        }
        for &id in &patch.claim().triangles {
            // A BTreeSet of usize has at most usize::BITS levels. This
            // allowance covers comparisons and its split path per insert.
            w.spend_core(k, 4_096)?;
            w.reserve_cells_core(k, 2)?;
            if !seen.insert(id) {
                return Err(refusal("a source triangle belongs to two radial bands"));
            }
        }
        world_upper = world_upper.max(patch.world_upper());
    }
    for pair in patches.windows(2) {
        let [lo, hi] = pair else {
            return Err(refusal("missing neighbouring radial bands"));
        };
        let [_, level] = lo.claim().law.height;
        let [other_level, _] = hi.claim().law.height;
        let [_, radius] = lo.claim().law.radius;
        let [other_radius, _] = hi.claim().law.radius;
        if level != other_level
            || radius != other_radius
            || radius <= 0.
            || !opposite_ring(k, w, rim_at(k, w, lo, level)?, rim_at(k, w, hi, level)?)?
        {
            return Err(refusal(
                "radial stack does not share one complete positive-radius join",
            ));
        }
    }
    Ok(SourceRadialStack {
        patches,
        world_upper,
    })
}

#[derive(Clone, Copy)]
struct Envelope {
    law: RadiusLaw,
    error: f64,
}
impl Envelope {
    fn radius(self, height: f64) -> Ivl {
        let [a, b] = self.law.height;
        let [r, s] = self.law.radius.map(Ivl::from);
        if height == a {
            r
        } else if height == b {
            s
        } else {
            r + (s - r) * ((Ivl::from(height) - Ivl::from(a)) / (Ivl::from(b) - Ivl::from(a)))
        }
    }
    fn of(patch: &SourceRadialPatch<'_, '_, '_, '_>) -> Self {
        Self {
            law: patch.claim().law,
            error: patch.local_upper(),
        }
    }
}
enum Separation {
    /// Two exterior bounds are disjoint even while both walls move.
    Disjoint { distance: Ivl },
    /// The first radial wall surrounds the second, with a common centre.
    FirstOutside,
}
fn separate_pair(a: Envelope, b: Envelope, kind: &Separation) -> bool {
    let [la, ha] = a.law.height;
    let [lb, hb] = b.law.height;
    let lo = la.max(lb);
    let hi = ha.min(hb);
    if lo > hi {
        return true;
    }
    for level in [lo, hi] {
        let (ar, br) = (a.radius(level), b.radius(level));
        let delta = Ivl::from(a.error) + Ivl::from(b.error);
        let margin = match *kind {
            Separation::Disjoint { distance } => distance - ar - br - delta,
            Separation::FirstOutside => ar - br - delta,
        };
        if !margin.is_finite() || !margin.is_positive() {
            return false;
        }
    }
    true
}

/// In one exact chart, prove strict separation of the whole *moving* radial
/// walls, including all joins. This is a complete pair test for these coaxial
/// stacks only and cannot stand in for a polygonal wall or cap theorem.
pub(crate) fn separate_source_radial_stacks_with_work(
    k: &Kernel,
    w: &MeshWork,
    first: &SourceRadialStack<'_, '_, '_, '_, '_>,
    second: &SourceRadialStack<'_, '_, '_, '_, '_>,
) -> Result<()> {
    w.spend_core(k, 1)?;
    let a = first
        .patches
        .first()
        .ok_or_else(|| refusal("missing first stack"))?;
    let b = second
        .patches
        .first()
        .ok_or_else(|| refusal("missing second stack"))?;
    if !core::ptr::eq(a.source(), b.source()) {
        return Err(refusal("radial separation needs one exact source chart"));
    }
    let kind = match (a.claim().concave, b.claim().concave) {
        (true, true) => {
            let [ax, ay] = a.claim().center.map(Ivl::from);
            let [bx, by] = b.claim().center.map(Ivl::from);
            let dx = ax - bx;
            let dy = ay - by;
            let distance = (dx * dx + dy * dy).sqrt();
            if !distance.is_finite() || !distance.is_positive() {
                return Err(refusal(
                    "separate radial bores lack distinct proven centres",
                ));
            }
            Separation::Disjoint { distance }
        }
        (false, true) if a.claim().center == b.claim().center => Separation::FirstOutside,
        _ => return Err(refusal("unsupported radial wall and bore relation")),
    };
    for x in first.patches {
        let x = Envelope::of(x);
        for y in second.patches {
            w.spend_core(k, 64)?;
            if !separate_pair(x, Envelope::of(y), &kind) {
                return Err(refusal(
                    "complete moving radius envelopes have no strict separation",
                ));
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_conical_join_needs_both_uses_of_the_same_source_edges() {
        let k = Kernel::default();
        let w = MeshWork::new();
        let a = [1, 2, 3, 4];
        assert!(opposite_ring(&k, &w, &a, &[3, 2, 1, 4]).unwrap());
        assert!(!opposite_ring(&k, &w, &a, &[3, 2, 1, 9]).unwrap());
        assert!(!opposite_ring(&k, &w, &a, &[1, 2, 3, 4]).unwrap());
    }

    fn envelope(height: [f64; 2], radius: [f64; 2], error: f64) -> Envelope {
        Envelope {
            law: RadiusLaw { height, radius },
            error,
        }
    }

    #[test]
    fn moving_countersink_cannot_round_through_a_neighbouring_bore() {
        let taper = envelope([1., 3.], [1., 2.], 0.02);
        let bore = envelope([0., 3.], [1., 1.], 0.01);
        assert!(!separate_pair(
            taper,
            bore,
            &Separation::Disjoint {
                distance: Ivl::from(3.02)
            }
        ));
        assert!(separate_pair(
            taper,
            bore,
            &Separation::Disjoint {
                distance: Ivl::from(3.04)
            }
        ));
    }

    #[test]
    fn coaxial_cut_inside_stock_must_keep_the_thin_wall() {
        let cut = envelope([1., 3.], [1., 2.], 0.03);
        let narrow_wall = envelope([0., 4.], [2.04, 2.04], 0.02);
        let wider_wall = envelope([0., 4.], [2.06, 2.06], 0.02);
        assert!(!separate_pair(narrow_wall, cut, &Separation::FirstOutside));
        assert!(separate_pair(wider_wall, cut, &Separation::FirstOutside));
    }
}
