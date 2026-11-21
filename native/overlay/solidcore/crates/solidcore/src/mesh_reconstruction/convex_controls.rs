//! Sufficient GLOBAL convex control-chain test using existing exact expansions.
//! Local turn signs alone cannot reject multi-winding stars and are not used.
use super::certificate::exact_geometry as x;
use super::{MeshError, MeshWork};
use crate::Kernel;
const OP: &str = "mesh_reconstruction::profile_convex_chain";
type Result<T> = core::result::Result<T, MeshError>;
fn unsure(n: usize) -> MeshError {
    MeshError::Undecided { stage: OP, work: n }
}
/// Exact homogeneous coordinates, not independently rounded Euclidean controls.
pub(crate) struct Control {
    pub(crate) xyz: x::P,
    pub(crate) w: x::E,
}
fn equal(a: &Control, b: &Control) -> Option<bool> {
    let aw = &a.w;
    let bw = &b.w;
    let mut same = true;
    for (ac, bc) in a.xyz.iter().zip(&b.xyz) {
        same &= x::zero(&x::sub(&x::mul(ac, bw)?, &x::mul(bc, aw)?)?);
    }
    Some(same)
}
fn projection(p: &Control, axes: [usize; 2]) -> Option<x::P> {
    let [u, v] = axes;
    Some([p.xyz.get(u)?.clone(), p.xyz.get(v)?.clone(), p.w.clone()])
}
fn det(a: &x::P, b: &x::P, c: &x::P) -> Option<i32> {
    x::sign(&x::dot(&x::cross(a, b)?, c)?)
}
fn equal_projection(a: &x::P, b: &x::P) -> Option<bool> {
    let [ax, ay, aw] = a;
    let [bx, by, bw] = b;
    Some(
        x::zero(&x::sub(&x::mul(ax, bw)?, &x::mul(bx, aw)?)?)
            && x::zero(&x::sub(&x::mul(ay, bw)?, &x::mul(by, aw)?)?),
    )
}
/// A convex projected control boundary, not an actual join/trim certificate.
/// Whole positive rational span hulls can use it only after actual immutable
/// span membership and all real join connectors have been independently bound.
pub(crate) struct ConvexControls<'a> {
    pub(crate) original: &'a [Control],
    pub(crate) orientation: i32,
    pub(crate) retained: Vec<usize>,
    pub(crate) axes: [usize; 2],
}
/// Independently require every other control in the same CLOSED half-plane of
/// EVERY oriented boundary edge; exact-zero collinear controls are allowed.
/// Remove only consecutive exactly identical 3D projective points. Distinct 3D
/// points with equal projection, nonadjacent repeated vertices and unsafe exact
/// arithmetic refuse. There is no angular sample sum or fitted epsilon.
pub(crate) fn convex_controls<'a>(
    k: &Kernel,
    work: &MeshWork,
    controls: &'a [Control],
    axes: [usize; 2],
) -> Result<ConvexControls<'a>> {
    let [u, v] = axes;
    if u == v || u > 2 || v > 2 || controls.len() < 3 {
        return Err(unsure(0));
    }
    work.reserve_output(k, controls.len())?;
    let mut retained = Vec::<usize>::new();
    for (i, c) in controls.iter().enumerate() {
        work.spend(k, 1)?;
        if x::sign(&c.w) != Some(1) {
            return Err(unsure(i));
        }
        if let Some(&previous) = retained.last() {
            let Some(p) = controls.get(previous) else {
                return Err(unsure(i));
            };
            match equal(p, c) {
                Some(true) => continue,
                Some(false) => {}
                None => return Err(unsure(i)),
            }
        }
        retained.push(i);
    }
    if let (Some(&a), Some(&b)) = (retained.first(), retained.last()) {
        let (Some(a), Some(b)) = (controls.get(a), controls.get(b)) else {
            return Err(unsure(0));
        };
        match equal(a, b) {
            Some(true) => {
                retained.pop();
            }
            Some(false) => {}
            None => return Err(unsure(0)),
        }
    }
    if retained.len() < 3 {
        return Err(unsure(0));
    }
    let mut orientation = 0;
    for (position, &id) in retained.iter().enumerate() {
        let Some(a) = controls.get(id).and_then(|p| projection(p, axes)) else {
            return Err(unsure(position));
        };
        let next = position.checked_add(1).ok_or_else(|| unsure(position))?;
        let next_id = if next == retained.len() {
            retained.first()
        } else {
            retained.get(next)
        }
        .copied()
        .ok_or_else(|| unsure(position))?;
        let Some(b) = controls.get(next_id).and_then(|p| projection(p, axes)) else {
            return Err(unsure(position));
        };
        // Projectively identical adjacent points would collapse a 3D segment in
        // the projection; even distinct nonplanar controls must refuse here.
        if equal_projection(&a, &b) != Some(false) {
            return Err(unsure(position));
        }
        for &other_id in &retained {
            work.spend(k, 1)?;
            if other_id == id || other_id == next_id {
                continue;
            }
            let Some(c) = controls.get(other_id).and_then(|p| projection(p, axes)) else {
                return Err(unsure(position));
            };
            let Some(turn) = det(&a, &b, &c) else {
                return Err(unsure(position));
            };
            if turn != 0 {
                if orientation == 0 {
                    orientation = turn;
                } else if turn != orientation {
                    return Err(unsure(position));
                }
            }
        }
    }
    if orientation == 0 {
        return Err(unsure(controls.len()));
    }
    // The global half-plane condition rules out a winding star. Explicit repeat
    // rejection also excludes a second traversal along the same convex hull.
    for (position, &id) in retained.iter().enumerate() {
        let Some(a) = controls.get(id) else {
            return Err(unsure(position));
        };
        for &other in retained.iter().skip(position + 1) {
            work.spend(k, 1)?;
            let Some(b) = controls.get(other) else {
                return Err(unsure(position));
            };
            let (Some(pa), Some(pb)) = (projection(a, axes), projection(b, axes)) else {
                return Err(unsure(position));
            };
            if equal_projection(&pa, &pb) != Some(false) {
                return Err(unsure(position));
            }
        }
    }
    work.check(k)?;
    Ok(ConvexControls {
        original: controls,
        orientation,
        retained,
        axes,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    fn control(x: f64, y: f64, z: f64) -> Control {
        Control {
            xyz: x::point([x, y, z]).unwrap(),
            w: x::scalar(1.).unwrap(),
        }
    }
    #[test]
    fn global_half_planes_allow_exact_collinear_hull_controls() {
        let controls = [
            control(0., 0., 0.),
            control(1., 0., 0.),
            control(2., 0., 0.),
            control(2., 1., 0.),
            control(0., 1., 0.),
        ];
        let proof =
            convex_controls(&Kernel::default(), &MeshWork::new(), &controls, [0, 1]).unwrap();
        assert_eq!(proof.orientation, 1);
    }
    #[test]
    fn locally_positive_winding_star_is_not_convex_boundary() {
        let controls = [
            control(0., 3., 0.),
            control(-2., -3., 0.),
            control(3., 1., 0.),
            control(-3., 1., 0.),
            control(2., -3., 0.),
        ];
        assert!(convex_controls(&Kernel::default(), &MeshWork::new(), &controls, [0, 1]).is_err());
    }
    #[test]
    fn repeated_projection_cannot_hide_a_second_nonplanar_turn() {
        let controls = [
            control(0., 0., 0.),
            control(1., 0., 0.),
            control(0., 1., 0.),
            control(0., 0., 1.),
            control(1., 0., 1.),
            control(0., 1., 1.),
        ];
        assert!(convex_controls(&Kernel::default(), &MeshWork::new(), &controls, [0, 1]).is_err());
    }
}

fn direction(a: &x::P, b: &x::P) -> Option<[x::E; 2]> {
    let [ax, ay, aw] = a;
    let [bx, by, bw] = b;
    Some([
        x::sub(&x::mul(bx, aw)?, &x::mul(ax, bw)?)?,
        x::sub(&x::mul(by, aw)?, &x::mul(ay, bw)?)?,
    ])
}
fn linear_side(origin: &x::P, normal: &[x::E; 2], point: &x::P) -> Option<i32> {
    let [dx, dy] = direction(origin, point)?;
    let [nx, ny] = normal;
    x::sign(&x::add(&x::mul(&dx, nx)?, &x::mul(&dy, ny)?)?)
}
/// Whole positive-control-hull separation. A shared join, if supplied, is an
/// exact projective point present in BOTH hulls; only that point may intersect.
/// This lemma handles arbitrary concave chains pairwise, not only convex rims.
/// All tests cover complete rational hulls, never sampled curve locations.
pub(crate) fn separated_control_hulls(
    k: &Kernel,
    work: &MeshWork,
    a: &[Control],
    b: &[Control],
    axes: [usize; 2],
    join: Option<&Control>,
) -> Result<bool> {
    let [u, v] = axes;
    if a.is_empty() || b.is_empty() || u == v || u > 2 || v > 2 {
        return Err(unsure(0));
    }
    if let Some(j) = join {
        if x::sign(&j.w) != Some(1)
            || !a.iter().any(|p| equal(p, j) == Some(true))
            || !b.iter().any(|p| equal(p, j) == Some(true))
        {
            return Err(unsure(0));
        }
    }
    let prepare = |controls: &[Control]| -> Result<Vec<x::P>> {
        let mut out = Vec::new();
        work.reserve_output(k, controls.len())?;
        for p in controls {
            work.spend(k, 1)?;
            if x::sign(&p.w) != Some(1) {
                return Err(unsure(0));
            }
            out.push(projection(p, axes).ok_or_else(|| unsure(0))?);
        }
        Ok(out)
    };
    let aa = prepare(a)?;
    let bb = prepare(b)?;
    let join = match join {
        Some(j) => Some(projection(j, axes).ok_or_else(|| unsure(0))?),
        None => None,
    };
    if let Some(j) = &join {
        if !aa.iter().any(|p| equal_projection(p, j) == Some(true))
            || !bb.iter().any(|p| equal_projection(p, j) == Some(true))
        {
            return Err(unsure(0));
        }
    }
    let total = aa.len().checked_add(bb.len()).ok_or_else(|| unsure(0))?;
    work.reserve_output(k, total)?;
    let all = aa.iter().chain(&bb).collect::<Vec<_>>();
    for (i, &p) in all.iter().enumerate() {
        for &q in all.iter().skip(i + 1) {
            work.spend(k, 1)?;
            let [dx, dy] = direction(p, q).ok_or_else(|| unsure(i))?;
            if x::zero(&dx) && x::zero(&dy) {
                continue;
            }
            // Polygon edge normals suffice for full-dimensional hulls. Direction
            // axes additionally handle degenerate collinear line-segment hulls.
            let minus_dy = x::scale(&dy, -1.).ok_or_else(|| unsure(i))?;
            for normal in [[dx.clone(), dy.clone()], [minus_dy, dx.clone()]] {
                for origin in all.iter().copied().filter(|origin| {
                    join.as_ref()
                        .is_none_or(|j| equal_projection(origin, j) == Some(true))
                }) {
                    work.spend(k, 1)?;
                    let summarize = |points: &[x::P]| -> Result<(bool, bool, bool, bool, bool)> {
                        let (
                            mut nonpositive,
                            mut nonnegative,
                            mut negative,
                            mut positive,
                            mut zeros_only_join,
                        ) = (true, true, true, true, true);
                        for p in points {
                            work.spend(k, 1)?;
                            let side = linear_side(origin, &normal, p).ok_or_else(|| unsure(i))?;
                            nonpositive &= side <= 0;
                            nonnegative &= side >= 0;
                            negative &= side < 0;
                            positive &= side > 0;
                            if side == 0 {
                                zeros_only_join &= join
                                    .as_ref()
                                    .is_some_and(|j| equal_projection(p, j) == Some(true));
                            }
                        }
                        Ok((
                            nonpositive,
                            nonnegative,
                            negative,
                            positive,
                            zeros_only_join,
                        ))
                    };
                    let (an, ap, asn, asp, az) = summarize(&aa)?;
                    let (bn, bp, bsn, bsp, bz) = summarize(&bb)?;
                    let proven = if join.is_some() {
                        ((an && bp) || (ap && bn)) && (az || bz)
                    } else {
                        (an && bsp) || (asn && bp) || (ap && bsn) || (asp && bn)
                    };
                    if proven {
                        work.check(k)?;
                        return Ok(true);
                    }
                }
            }
        }
    }
    work.check(k)?;
    Ok(false)
}

#[cfg(test)]
mod hull_tests {
    use super::*;
    fn c(x: f64, y: f64) -> Control {
        Control {
            xyz: x::point([x, y, 0.]).unwrap(),
            w: x::scalar(1.).unwrap(),
        }
    }
    #[test]
    fn adjacent_line_hulls_only_meet_at_the_exact_shared_join() {
        let a = [c(-1., 0.), c(0., 0.)];
        let b = [c(0., 0.), c(0., 1.)];
        let join = c(0., 0.);
        assert!(separated_control_hulls(
            &Kernel::default(),
            &MeshWork::new(),
            &a,
            &b,
            [0, 1],
            Some(&join)
        )
        .unwrap());
    }
    #[test]
    fn disjoint_collinear_hulls_need_the_direction_axis() {
        let a = [c(0., 0.), c(1., 0.)];
        let b = [c(2., 0.), c(3., 0.)];
        assert!(separated_control_hulls(
            &Kernel::default(),
            &MeshWork::new(),
            &a,
            &b,
            [0, 1],
            None
        )
        .unwrap());
    }
    #[test]
    fn overlapping_control_hulls_are_never_proved_disjoint() {
        let a = [c(0., 0.), c(2., 0.), c(0., 2.)];
        let b = [c(0.25, 0.25), c(0.5, 0.25), c(0.25, 0.5)];
        assert!(!separated_control_hulls(
            &Kernel::default(),
            &MeshWork::new(),
            &a,
            &b,
            [0, 1],
            None
        )
        .unwrap());
    }
}
