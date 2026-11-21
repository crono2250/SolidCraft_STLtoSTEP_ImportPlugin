//! Whole-triangle, same-height radial error for a finite affine radius law.
//!
//! In polar coordinates the finite conical reference has radius R(z), affine in
//! height. Every squared residual |p_xy|^2-R(z)^2 is a degree-two triangular
//! Bernstein polynomial. Its SIX coefficients enclose the complete triangle,
//! not a vertex residual. Divide by a strictly positive lower bound for
//! |p_xy|+R(z). At a declared exact pole the fan factorisation p=t*q,
//! R=t*r reduces the WHOLE triangle to its opposite edge; it never divides by
//! a zero radius or treats an apex normal as regular.
//!
//! This is only a radial distance bound. Source embedding, finite-domain
//! coverage/degree, native trims/CW/material, original identity and final
//! canonical-body adoption are deliberately NOT certified by this result.
//!
//! References: Farin, Curves and Surfaces for CAGD, triangular Bernstein convex
//! hull property; Lipman2014, doi:10.1137/130939754 (the separate degree consumer).
//! Deviations: iterative complete quartering, depth20, one shared MeshWork.
use super::super::primitive_certificate::{norm2_range, quarters, Triangle};
use super::super::work::MeshWork;
use crate::blend::fillet_section::interval::Ivl;
use crate::{Kernel, Result, SolidError};

const OP: &str = "mesh_reconstruction::certificate::radial_band";
const MAX_DEPTH: u8 = 20;

fn refused(reason: &'static str) -> SolidError {
    SolidError::Unsupported {
        operation: OP,
        reason,
    }
}

/// Input data, not an acceptance token. Coordinates are in one independently
/// bound axial chart. A non-isometric world lift needs its own operator bound.
#[derive(Clone, Copy, Debug)]
pub(crate) struct RadiusLaw {
    pub(crate) height: [f64; 2],
    pub(crate) radius: [f64; 2],
}
impl RadiusLaw {
    pub(super) fn valid(self) -> bool {
        let [lo, hi] = self.height;
        let [a, b] = self.radius;
        lo.is_finite()
            && hi.is_finite()
            && lo < hi
            && a.is_finite()
            && b.is_finite()
            && a >= 0.
            && b >= 0.
            && (a > 0. || b > 0.)
    }
    fn at(self, height: Ivl) -> Ivl {
        let [lo, hi] = self.height;
        let [a, b] = self.radius;
        Ivl::from(a)
            + (Ivl::from(b) - Ivl::from(a))
                * ((height - Ivl::from(lo)) / (Ivl::from(hi) - Ivl::from(lo)))
    }
}

fn scalar(value: Ivl, exact: f64) -> bool {
    value.lo == exact && value.hi == exact
}
fn radial_dot(a: [Ivl; 3], b: [Ivl; 3]) -> Ivl {
    let [ax, ay, _] = a;
    let [bx, by, _] = b;
    ax * bx + ay * by
}
fn magnitude(values: impl IntoIterator<Item = Ivl>) -> Option<f64> {
    let mut upper = 0_f64;
    for value in values {
        if !value.is_finite() {
            return None;
        }
        upper = upper.max(value.mag());
    }
    Some(upper)
}
fn residual_bound(points: &Triangle, radii: [Ivl; 3]) -> Option<f64> {
    let [a, b, c] = *points;
    let [ra, rb, rc] = radii;
    let minimum = ra.lo.min(rb.lo).min(rc.lo);
    if minimum <= 0. || !minimum.is_finite() {
        return None;
    }
    let error = magnitude([
        radial_dot(a, a) - ra * ra,
        radial_dot(b, b) - rb * rb,
        radial_dot(c, c) - rc * rc,
        radial_dot(a, b) - ra * rb,
        radial_dot(b, c) - rb * rc,
        radial_dot(c, a) - rc * ra,
    ])?;
    let flat = points.map(|[x, y, _]| [x, y, Ivl::from(0.)]);
    let rho2 = norm2_range(&flat);
    if !rho2.is_finite() {
        return None;
    }
    let rho = Ivl::new(rho2.lo.max(0.), rho2.hi.max(0.)).sqrt();
    let denominator = Ivl::from(minimum) + Ivl::from(rho.lo);
    if !denominator.is_finite() || denominator.lo <= 0. {
        return None;
    }
    let bound = Ivl::from(error) / denominator;
    bound.is_finite().then_some(bound.hi)
}

/// Exact pole fan factorisation, including every barycentric point. The
/// opposite edge must have strictly positive radii inside the finite domain. This branch
/// cannot be selected by a guessed near-zero coordinate or a vertex residual.
fn pole_fan(points: &Triangle, law: RadiusLaw) -> Option<f64> {
    for (height, radius) in law.height.into_iter().zip(law.radius) {
        if radius != 0. {
            continue;
        }
        for (i, p) in points.iter().enumerate() {
            let [x, y, z] = *p;
            if !scalar(x, 0.) || !scalar(y, 0.) || !scalar(z, height) {
                continue;
            }
            let mut edge = points
                .iter()
                .enumerate()
                .filter_map(|(j, q)| (i != j).then_some(*q));
            let (Some(a), Some(b), None) = (edge.next(), edge.next(), edge.next()) else {
                return None;
            };
            let [_, _, za] = a;
            let [_, _, zb] = b;
            let [lo, hi] = law.height;
            if za.lo < lo || za.hi > hi || zb.lo < lo || zb.hi > hi {
                return None;
            }
            // R(apex)=0 exactly. For arbitrary barycentric t,u,
            // P=(1-t)*apex+t*Q(u) and R(P.h)=t*R(Q.h).
            // Therefore the entire fan error is at most the whole opposite
            // edge error, even when that edge has different positive heights.
            let ra = law.at(za);
            let rb = law.at(zb);
            return residual_bound(&[a, b, b], [ra, rb, rb]);
        }
    }
    None
}

pub(crate) struct RadialDistance<'a> {
    triangle: &'a Triangle,
    law: RadiusLaw,
    upper: f64,
    cells: usize,
}
impl RadialDistance<'_> {
    pub(crate) fn upper(&self) -> f64 {
        self.upper
    }
    pub(crate) fn cells(&self) -> usize {
        self.cells
    }
    pub(crate) fn inputs(&self) -> (&Triangle, RadiusLaw) {
        (self.triangle, self.law)
    }
}

/// Bound the complete same-height radial correction, with original budget and
/// cancellation. Failure never returns a weaker sampled/faceted proof.
pub(crate) fn prove_radial_distance_with_work<'a>(
    k: &Kernel,
    work: &MeshWork,
    triangle: &'a Triangle,
    law: RadiusLaw,
    maximum: f64,
) -> Result<RadialDistance<'a>> {
    work.spend_core(k, 1)?;
    if !law.valid()
        || !maximum.is_finite()
        || maximum < 0.
        || triangle.iter().flatten().any(|x| !x.is_finite())
    {
        return Err(refused("invalid radial reference or source triangle"));
    }
    // Fixed degree2 expression/storage admission precedes BOTH branches.
    work.spend_core(k, 256)?;
    work.reserve_cells_core(k, 128)?;
    if let Some(upper) = pole_fan(triangle, law) {
        if upper <= maximum {
            return Ok(RadialDistance {
                triangle,
                law,
                upper,
                cells: 1,
            });
        }
        return Err(refused("whole pole fan exceeds radial tolerance"));
    }
    // Quartering cannot make a pole-containing triangle strictly regular.
    // Refuse unresolved zero-radius domains rather than chasing the pole.
    let touches_pole = law
        .height
        .into_iter()
        .zip(law.radius)
        .filter(|(_, radius)| *radius == 0.)
        .any(|(height, _)| {
            triangle
                .iter()
                .any(|[_, _, z]| z.lo <= height && height <= z.hi)
        });
    if touches_pole {
        return Err(refused(
            "zero-radius source requires an exact complete pole fan",
        ));
    }
    work.reserve_cells_core(k, 1)?;
    let mut pending = vec![(*triangle, 0u8)];
    let (mut upper, mut cells) = (0_f64, 0usize);
    while let Some((cell, depth)) = pending.pop() {
        work.spend_core(k, 256)?;
        work.reserve_cells_core(k, 128)?;
        cells = cells
            .checked_add(1)
            .ok_or_else(|| refused("radial cell count overflow"))?;
        let radii = cell.map(|[_, _, height]| law.at(height));
        if let Some(bound) = residual_bound(&cell, radii) {
            if bound <= maximum {
                upper = upper.max(bound);
                continue;
            }
        }
        if depth >= MAX_DEPTH {
            return Err(refused("whole radial bound remains unresolved"));
        }
        work.reserve_cells_core(k, 4)?;
        for quarter in quarters(&cell).into_iter().rev() {
            pending.push((quarter, depth + 1));
        }
    }
    work.spend_core(k, 0)?;
    Ok(RadialDistance {
        triangle,
        law,
        upper,
        cells,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    fn p(x: f64, y: f64, z: f64) -> [Ivl; 3] {
        [x, y, z].map(Ivl::from)
    }
    #[test]
    fn full_frustum_triangle_not_only_vertices_is_bounded() {
        let angle = std::f64::consts::PI / 32.;
        let tri = [
            p(5., 0., 0.),
            p(5. * angle.cos(), 5. * angle.sin(), 0.),
            p(3., 0., 4.),
        ];
        let law = RadiusLaw {
            height: [0., 4.],
            radius: [5., 3.],
        };
        let k = Kernel::default();
        let proof = prove_radial_distance_with_work(&k, &MeshWork::new(), &tri, law, 0.05).unwrap();
        assert!(proof.upper() > 0.);
        assert!(proof.upper() < 0.05);
        assert_eq!(proof.inputs().0.as_ptr(), tri.as_ptr());
        assert!(proof.cells() > 0);
        // Tests sample independently for a regression; acceptance above uses ALL
        // Bernstein coefficients and is independent of this test grid.
        for i in 0..=24 {
            for j in 0..=24 - i {
                let a = f64::from(i) / 24.;
                let b = f64::from(j) / 24.;
                let c = 1. - a - b;
                let xyz = std::array::from_fn::<_, 3, _>(|d| {
                    tri[0][d].lo * a + tri[1][d].lo * b + tri[2][d].lo * c
                });
                let [x, y, z] = xyz;
                let residual = (x.hypot(y) - (5. - z * 0.5)).abs();
                assert!(residual <= proof.upper());
            }
        }
    }
    #[test]
    fn zero_vertex_residual_does_not_authorize_rounding_a_coarse_cone() {
        let tri = [p(5., 0., 0.), p(0., 5., 0.), p(3., 0., 4.)];
        let law = RadiusLaw {
            height: [0., 4.],
            radius: [5., 3.],
        };
        assert!(prove_radial_distance_with_work(
            &Kernel::default(),
            &MeshWork::new(),
            &tri,
            law,
            0.05
        )
        .is_err());
    }
    #[test]
    fn exact_apex_fan_uses_whole_opposite_edge() {
        let angle = std::f64::consts::PI / 32.;
        let tri = [
            p(0., 0., 4.),
            p(5., 0., 0.),
            p(5. * angle.cos(), 5. * angle.sin(), 0.),
        ];
        let law = RadiusLaw {
            height: [0., 4.],
            radius: [5., 0.],
        };
        let proof =
            prove_radial_distance_with_work(&Kernel::default(), &MeshWork::new(), &tri, law, 0.05)
                .unwrap();
        assert!(proof.upper() > 0.);
        assert!(proof.upper() < 0.05);
    }
    #[test]
    fn displaced_or_fake_apex_is_not_silently_snapped() {
        let tri = [p(0.001, 0., 4.), p(5., 0., 0.), p(4.9, 0.5, 0.)];
        assert!(prove_radial_distance_with_work(
            &Kernel::default(),
            &MeshWork::new(),
            &tri,
            RadiusLaw {
                height: [0., 4.],
                radius: [5., 0.]
            },
            0.05
        )
        .is_err());
    }
    #[test]
    fn radius_law_interior_bulge_is_rejected() {
        let tri = [p(5., 0., 0.), p(5., 0.2, 0.), p(5., 0., 2.)];
        assert!(prove_radial_distance_with_work(
            &Kernel::default(),
            &MeshWork::new(),
            &tri,
            RadiusLaw {
                height: [0., 4.],
                radius: [5., 3.]
            },
            0.05
        )
        .is_err());
    }
    #[test]
    fn a_regular_cell_inside_a_cone_does_not_need_a_fake_pole() {
        let angle = 0.1_f64;
        let tri = [
            p(3.75, 0., 1.),
            p(3.75 * angle.cos(), 3.75 * angle.sin(), 1.),
            p(2.5, 0., 2.),
        ];
        let law = RadiusLaw {
            height: [0., 4.],
            radius: [5., 0.],
        };
        assert!(prove_radial_distance_with_work(
            &Kernel::default(),
            &MeshWork::new(),
            &tri,
            law,
            0.05
        )
        .is_ok());
    }
    #[test]
    fn a_complete_pole_fan_can_have_a_sloped_opposite_edge() {
        let angle = 0.1_f64;
        let tri = [
            p(0., 0., 4.),
            p(5., 0., 0.),
            p(2.5 * angle.cos(), 2.5 * angle.sin(), 2.),
        ];
        let law = RadiusLaw {
            height: [0., 4.],
            radius: [5., 0.],
        };
        assert!(prove_radial_distance_with_work(
            &Kernel::default(),
            &MeshWork::new(),
            &tri,
            law,
            0.05
        )
        .is_ok());
    }
}
