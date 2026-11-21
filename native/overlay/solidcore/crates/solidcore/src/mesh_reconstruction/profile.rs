//! Common native source-profile fitting: one implementation for section and prism paths.
//! Line/circle residual checks select candidates; acceptance is a separate whole-domain proof.
use super::numeric::Vec2Numeric;
use crate::math::Vec2;
use crate::prism::profile::{Loop2, Seg2};
const MAX_FIT_POINTS: usize = 4096;
pub(crate) fn polygon(points: &[Vec2]) -> Loop2 {
    let mut segs = Vec::new();
    if points.is_empty() {
        return Loop2 { segs };
    }
    for (a, b) in points
        .iter()
        .zip(points.iter().cycle().skip(1))
        .take(points.len())
    {
        segs.push(Seg2::Line { a: *a, b: *b });
    }
    Loop2 { segs }
}
pub(crate) fn circle(center: Vec2, radius: f64) -> Loop2 {
    circle_from(center, radius, 0.)
}
pub(crate) fn circle_from(center: Vec2, radius: f64, start: f64) -> Loop2 {
    Loop2 {
        segs: vec![Seg2::Arc {
            center,
            radius,
            start,
            sweep: std::f64::consts::TAU,
        }],
    }
}
/// Used only for the known line segments in source-polyline fitting.
pub(crate) fn line_parameter(s: &Seg2, p: Vec2) -> f64 {
    let Seg2::Line { a, b } = s else {
        return 0.;
    };
    let direction = *b - *a;
    let length2 = direction.length_squared();
    if length2 > 0. && length2.is_finite() {
        ((p - *a).dot(direction) / length2).clamp(0., 1.)
    } else {
        0.
    }
}
/// The circle through three points: centre and radius.
fn circle3(a: Vec2, b: Vec2, c: Vec2) -> Option<(Vec2, f64)> {
    let u = b - a;
    let v = c - a;
    let d = 2. * u.cross(v);
    if d.abs() <= 1e-18 {
        return None;
    }
    let center = a + Vec2::new(
        v.y * u.len2() - u.y * v.len2(),
        u.x * v.len2() - v.x * u.len2(),
    ) / d;
    let radius = center.dist(a);
    (radius.is_finite() && center.x.is_finite() && center.y.is_finite()).then_some((center, radius))
}

/// A closed polyline as lines and circular arcs. Arcs are taken only over runs of at least
/// three steps of at most 30° whose vertices lie within `fit` of one circle and whose chords
/// stay within `tolerance` of it; everything else stays straight.
pub(crate) fn fit_profile(points: &[Vec2], tolerance: f64, fit: f64) -> Loop2 {
    let points = &drop_collinear(points, fit * 0.5);
    let n = points.len();
    if !(3..=MAX_FIT_POINTS).contains(&n) {
        return polygon(points);
    }
    let get = |i: usize| points.get(i % n).copied().unwrap_or(Vec2::new(0., 0.));
    let turn = |i: usize| {
        let (a, b, c) = (get(i + n - 1), get(i), get(i + 1));
        let (u, v) = (b - a, c - b);
        u.cross(v).atan2(u.dot(v)).abs()
    };
    // Start at the sharpest corner so no straight run or arc is split by the loop's seam; in a
    // loop without corners (tangent lines and arcs), at the start of its longest straight side.
    let sharpest = (0..n)
        .max_by(|a, b| turn(*a).total_cmp(&turn(*b)))
        .unwrap_or(0);
    let start = if turn(sharpest) >= 20f64.to_radians() {
        sharpest
    } else {
        (0..n)
            .max_by(|a, b| {
                get(*a)
                    .dist(get(*a + 1))
                    .total_cmp(&get(*b).dist(get(*b + 1)))
            })
            .unwrap_or(0)
    };
    let at = |i: usize| get(start + i);
    let line_fits = |i: usize, j: usize| {
        let (a, b) = (at(i), at(j));
        if a.dist(b) <= fit {
            return false;
        }
        let edge = Seg2::Line { a, b };
        (i + 1..j).all(|k| {
            let p = at(k);
            edge.point_at(line_parameter(&edge, p)).dist(p) <= fit
        })
    };
    // (centre, radius, start angle, sweep) of an arc through points i..=j.
    let arc_fits = |i: usize, j: usize| -> Option<(Vec2, f64, f64, f64)> {
        if j < i + 3 {
            return None;
        }
        // Three points spread over the run (its ends coincide when it closes the loop).
        let third = (j - i) / 3;
        let (center, radius) = circle3(at(i), at(i + third), at(i + 2 * third))?;
        if radius <= fit * 10. {
            return None;
        }
        let mut sweep = 0.;
        let mut direction = 0f64;
        for k in i..j {
            let (a, b) = (at(k) - center, at(k + 1) - center);
            if (at(k + 1).dist(center) - radius).abs() > fit {
                return None;
            }
            let step = a.cross(b).atan2(a.dot(b));
            if direction == 0. {
                direction = step.signum();
            }
            if step * direction <= 0.
                || step.abs() > std::f64::consts::PI / 6. + 1e-9
                || radius * (1. - (step.abs() * 0.5).cos()) > tolerance
            {
                return None;
            }
            sweep += step;
        }
        let full = (sweep.abs() - std::f64::consts::TAU).abs() <= 1e-6;
        if sweep.abs() < 3f64.to_radians() || (sweep.abs() > std::f64::consts::TAU - 1e-6 && !full)
        {
            return None;
        }
        let a = at(i) - center;
        Some((center, radius, a.y.atan2(a.x), sweep))
    };
    let mut segs: Vec<Seg2> = Vec::new();
    let mut i = 0;
    while i < n {
        let mut line_end = i + 1;
        while line_end < n && line_fits(i, line_end + 1) {
            line_end += 1;
        }
        let mut arc = None;
        let mut j = i + 3;
        while j <= n {
            match arc_fits(i, j) {
                Some(a) => arc = Some((j, a)),
                None => break,
            }
            j += 1;
        }
        match arc {
            Some((j, (center, radius, start, sweep))) if j > line_end => {
                if i == 0 && j == n && (sweep.abs() - std::f64::consts::TAU).abs() <= 1e-6 {
                    let circle = circle_from(center, radius, start);
                    return if sweep < 0. {
                        circle.reversed()
                    } else {
                        circle
                    };
                }
                segs.push(Seg2::Arc {
                    center,
                    radius,
                    start,
                    sweep,
                });
                i = j;
            }
            _ => {
                segs.push(Seg2::Line {
                    a: at(i),
                    b: at(line_end),
                });
                i = line_end;
            }
        }
    }
    Loop2 {
        segs: close_gaps(merge_segments(segs, fit)),
    }
}

/// Make each segment start exactly where the one before ends: lines take the end points of
/// the segments beside them (an arc's end, from its angles, sits within the fit of the vertex it
/// was fitted to), and two arcs that meet get a joining line when they miss by more than
/// rounding.
pub(crate) fn close_gaps(segs: Vec<Seg2>) -> Vec<Seg2> {
    let n = segs.len();
    if n < 2 {
        return segs;
    }
    let mut out: Vec<Seg2> = segs.clone();
    for k in 0..n {
        let (Some(prev), Some(next)) = (segs.get((k + n - 1) % n), segs.get((k + 1) % n)) else {
            continue;
        };
        if let Some(Seg2::Line { a, b }) = out.get_mut(k) {
            *a = prev.end();
            if matches!(next, Seg2::Arc { .. }) {
                *b = next.start();
            }
        }
    }
    let mut joined = Vec::new();
    for k in 0..n {
        let (Some(cur), Some(next)) = (out.get(k), out.get((k + 1) % n)) else {
            continue;
        };
        joined.push(*cur);
        if matches!(cur, Seg2::Arc { .. })
            && matches!(next, Seg2::Arc { .. })
            && cur.end().dist(next.start()) > 1e-9
        {
            joined.push(Seg2::Line {
                a: cur.end(),
                b: next.start(),
            });
        }
    }
    joined.retain(|s| !matches!(s, Seg2::Line { a, b } if a.dist(*b) <= 1e-12));
    joined
}

/// The polyline without points lying on the straight line between their neighbours (the
/// section of a faceted wall crosses each facet's diagonal mid-chord).
pub(crate) fn drop_collinear(points: &[Vec2], within: f64) -> Vec<Vec2> {
    let mut out: Vec<Vec2> = points.to_vec();
    if out.len() > MAX_FIT_POINTS * 4 {
        return out;
    }
    let mut changed = true;
    while changed && out.len() > 3 {
        changed = false;
        let mut kept: Vec<Vec2> = Vec::new();
        let n = out.len();
        let mut skip_next = false;
        for i in 0..n {
            let (Some(a), Some(b), Some(c)) =
                (out.get((i + n - 1) % n), out.get(i), out.get((i + 1) % n))
            else {
                continue;
            };
            if !skip_next && kept.len() + (n - i) > 3 {
                let edge = Seg2::Line { a: *a, b: *c };
                let t = line_parameter(&edge, *b);
                if a.dist(*c) > 0. && t > 0. && t < 1. && edge.point_at(t).dist(*b) <= within {
                    // Drop it; keep its neighbour so two adjacent points are never judged
                    // against each other's removal in one pass.
                    skip_next = true;
                    changed = true;
                    continue;
                }
            }
            skip_next = false;
            kept.push(*b);
        }
        out = kept;
    }
    out
}

/// Join neighbouring arcs of one circle (including across the loop's seam).
fn merge_segments(mut segs: Vec<Seg2>, fit: f64) -> Vec<Seg2> {
    let joined = |a: &Seg2, b: &Seg2| -> Option<Seg2> {
        match (a, b) {
            (
                Seg2::Arc {
                    center: c0,
                    radius: r0,
                    start,
                    sweep: s0,
                },
                Seg2::Arc {
                    center: c1,
                    radius: r1,
                    sweep: s1,
                    ..
                },
            ) if c0.dist(*c1) <= fit
                && (r0 - r1).abs() <= fit
                && s0 * s1 > 0.
                && (s0 + s1).abs() < std::f64::consts::TAU - 1e-6 =>
            {
                Some(Seg2::Arc {
                    center: *c0,
                    radius: *r0,
                    start: *start,
                    sweep: s0 + s1,
                })
            }
            _ => None,
        }
    };
    let mut changed = true;
    while changed && segs.len() > 2 {
        changed = false;
        let n = segs.len();
        for k in 0..n {
            let (Some(a), Some(b)) = (segs.get(k), segs.get((k + 1) % n)) else {
                continue;
            };
            if let Some(m) = joined(a, b) {
                if k + 1 < n {
                    segs = segs
                        .into_iter()
                        .enumerate()
                        .filter_map(|(i, s)| {
                            if i == k {
                                Some(m)
                            } else if i == k + 1 {
                                None
                            } else {
                                Some(s)
                            }
                        })
                        .collect();
                } else {
                    segs.pop();
                    if let Some(first) = segs.first_mut() {
                        *first = m;
                    }
                }
                changed = true;
                break;
            }
        }
    }
    segs
}

/// The shared existing straight-extrusion loop fitter, preserving its line/arc
/// ordering. Selected-region section fitting above remains a separate guided job.
pub(crate) fn fit_loop(points: &[Vec2], tolerance: f64, epsilon: f64) -> Loop2 {
    super::analytic::fit_loop(points, tolerance, epsilon)
}
