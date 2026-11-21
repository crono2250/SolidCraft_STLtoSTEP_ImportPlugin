use super::{Vec3, mesh::MeshInput, reconstruct};

#[test]
fn native_annular_prism_cold_step_preserves_hole() {
    // Original public fixture, identical to the host-smoke STL after f32 import.
    let n = 128u32;
    let mut mesh = MeshInput {
        positions: Vec::new(),
        triangles: Vec::new(),
    };
    for (z, r) in [(0., 10.), (0., 3.), (3., 10.), (3., 3.)] {
        for i in 0..n {
            let a = std::f64::consts::TAU * f64::from(i) / f64::from(n);
            mesh.positions.push(Vec3::new(
                f64::from((r * a.cos()) as f32),
                f64::from((r * a.sin()) as f32),
                z,
            ));
        }
    }
    for i in 0..n {
        let j = (i + 1) % n;
        let (a, b, c, d) = (i, j, n + i, n + j);
        let (e, f, g, h) = (2 * n + i, 2 * n + j, 3 * n + i, 3 * n + j);
        mesh.triangles.extend([
            [a, c, d],
            [a, d, b],
            [e, f, h],
            [e, h, g],
            [a, b, f],
            [a, f, e],
            [c, g, h],
            [c, h, d],
        ]);
    }
    let original = mesh.clone();
    let step = match reconstruct(&mesh, 0.05, "Annular prism") {
        Ok(step) => step,
        Err(error) => panic!("certified annular prism failed: {error:?}"),
    };
    assert_eq!(mesh, original);
    assert!(step.contains("MANIFOLD_SOLID_BREP"));
    assert_eq!(
        step.matches("CYLINDRICAL_SURFACE").count(),
        2,
        "both analytic walls, including the designed bore, must survive"
    );
}

#[test]
fn native_stepped_stock_cold_step_preserves_planes() {
    let mut mesh = MeshInput {
        positions: Vec::new(),
        triangles: Vec::new(),
    };
    // Two centered rectangles of different widths AND depths, so no axis
    // gives a constant section. The horizontal shoulder has one inner rim.
    for (z, half_width, half_depth) in [(0., 8., 6.), (2., 8., 6.), (2., 4., 2.), (5., 4., 2.)] {
        for [x, y] in [[-1., -1.], [1., -1.], [1., 1.], [-1., 1.]] {
            mesh.positions
                .push(Vec3::new(x * half_width, y * half_depth, z));
        }
    }
    mesh.triangles
        .extend([[0, 2, 1], [0, 3, 2], [12, 13, 14], [12, 14, 15]]);
    for i in 0..4u32 {
        let j = (i + 1) % 4;
        for row in [0, 4, 8] {
            mesh.triangles.extend([
                [row + i, row + j, row + 4 + j],
                [row + i, row + 4 + j, row + 4 + i],
            ]);
        }
    }
    let original = mesh.clone();
    let step = match reconstruct(&mesh, 0.05, "Stepped planar stock") {
        Ok(step) => step,
        Err(error) => panic!("certified stepped stock failed: {error:?}"),
    };
    assert_eq!(mesh, original);
    assert_eq!(step.matches("MANIFOLD_SOLID_BREP").count(), 1);
    assert_eq!(step.matches("=PLANE(").count(), 11);
    assert!(!step.contains("CYLINDRICAL_SURFACE"));
}

#[test]
fn native_radial_frustum_roundtrips_as_a_conical_surface() {
    let n = 64u32;
    let mut mesh = MeshInput {
        positions: Vec::new(),
        triangles: Vec::new(),
    };
    for (height, radius) in [(0., 8.), (5., 4.)] {
        for i in 0..n {
            let angle = std::f64::consts::TAU * f64::from(i) / f64::from(n);
            mesh.positions.push(Vec3::new(
                f64::from((radius * angle.cos()) as f32),
                f64::from((radius * angle.sin()) as f32),
                height,
            ));
        }
    }
    mesh.positions.push(Vec3::new(0., 0., 0.));
    mesh.positions.push(Vec3::new(0., 0., 5.));
    for a in 0..n {
        let b = (a + 1) % n;
        mesh.triangles.extend([
            [a, b, b + n],
            [a, b + n, a + n],
            [2 * n, b, a],
            [2 * n + 1, a + n, b + n],
        ]);
    }
    let source = mesh.clone();
    let step = reconstruct(&mesh, 0.05, "Circular frustum").unwrap();
    assert_eq!(mesh, source);
    assert_eq!(step.matches("MANIFOLD_SOLID_BREP").count(), 1);
    assert_eq!(step.matches("=CONICAL_SURFACE(").count(), 1);
    assert_eq!(step.matches("=PLANE(").count(), 2);
}

#[test]
fn native_radial_cone_closes_at_the_single_apex() {
    let count = 64u32;
    let mut mesh = MeshInput {
        positions: vec![Vec3::new(0., 0., 0.)],
        triangles: Vec::new(),
    };
    for i in 0..count {
        let angle = std::f64::consts::TAU * f64::from(i) / f64::from(count);
        mesh.positions.push(Vec3::new(
            f64::from((4. * angle.cos()) as f32),
            f64::from((4. * angle.sin()) as f32),
            5.,
        ));
    }
    mesh.positions.push(Vec3::new(0., 0., 5.));
    for a in 1..=count {
        let b = a % count + 1;
        mesh.triangles.extend([[0, b, a], [count + 1, a, b]]);
    }
    let step = reconstruct(&mesh, 0.05, "Cone with a single apex").unwrap();
    assert_eq!(step.matches("MANIFOLD_SOLID_BREP").count(), 1);
    assert_eq!(step.matches("=CONICAL_SURFACE(").count(), 1);
    assert_eq!(step.matches("=PLANE(").count(), 1);
}

fn rectangular_bored_blank(bore_rings: &[(f64, f64)]) -> MeshInput {
    let mut angles = (0..64)
        .map(|i| std::f64::consts::TAU * f64::from(i) / 64.)
        .collect::<Vec<_>>();
    angles.extend([
        (6_f64).atan2(8.),
        (6_f64).atan2(-8.),
        (-6_f64).atan2(-8.).rem_euclid(std::f64::consts::TAU),
        (-6_f64).atan2(8.).rem_euclid(std::f64::consts::TAU),
    ]);
    angles.sort_by(f64::total_cmp);
    angles.dedup();
    let n = angles.len() as u32;
    let mut mesh = MeshInput {
        positions: Vec::new(),
        triangles: Vec::new(),
    };
    for z in [0., 5.] {
        for &a in &angles {
            let (y, x) = a.sin_cos();
            let radius = (8. / x.abs()).min(6. / y.abs());
            mesh.positions.push(Vec3::new(
                f64::from((x * radius) as f32),
                f64::from((y * radius) as f32),
                z,
            ));
        }
    }
    for &(z, radius) in bore_rings {
        for &a in &angles {
            let (y, x) = a.sin_cos();
            mesh.positions.push(Vec3::new(
                f64::from((x * radius) as f32),
                f64::from((y * radius) as f32),
                z,
            ));
        }
    }
    let last = (1 + bore_rings.len() as u32) * n;
    for a in 0..n {
        let b = (a + 1) % n;
        mesh.triangles.extend([
            [a, b, n + b],
            [a, n + b, n + a],
            [a, 2 * n + a, 2 * n + b],
            [a, 2 * n + b, b],
            [n + a, n + b, last + b],
            [n + a, last + b, last + a],
        ]);
        for offset in (2 * n..last).step_by(n as usize) {
            mesh.triangles.extend([
                [offset + a, offset + n + a, offset + n + b],
                [offset + a, offset + n + b, offset + b],
            ]);
        }
    }
    mesh
}

#[test]
fn native_axial_countersink_keeps_its_conical_and_cylindrical_walls() {
    let mesh = rectangular_bored_blank(&[(0., 2.), (3., 2.), (5., 4.)]);
    let input = mesh.clone();
    let step = reconstruct(&mesh, 0.05, "Cylindrical through hole and conical entry").unwrap();
    assert_eq!(mesh, input);
    assert_eq!(step.matches("MANIFOLD_SOLID_BREP").count(), 1);
    assert_eq!(step.matches("=PLANE(").count(), 6);
    assert_eq!(step.matches("=CONICAL_SURFACE(").count(), 1);
    assert_eq!(step.matches("=CYLINDRICAL_SURFACE(").count(), 1);
}

#[test]
fn stepped_bore_preserves_both_cylinders_and_the_annular_shoulder() {
    for [lo, hi] in [[2., 4.], [4., 2.]] {
        let mesh = rectangular_bored_blank(&[(0., lo), (3., lo), (3., hi), (5., hi)]);
        let step = reconstruct(&mesh, 0.05, "Through hole with a square shoulder").unwrap();
        assert_eq!(step.matches("MANIFOLD_SOLID_BREP").count(), 1);
        assert_eq!(step.matches("=PLANE(").count(), 7);
        assert_eq!(step.matches("=CONICAL_SURFACE(").count(), 0);
        assert_eq!(step.matches("=CYLINDRICAL_SURFACE(").count(), 2);
    }
}

#[test]
fn independent_stl_shells_reconstruct_together_with_stable_solid_names() {
    fn two_boxes(gap: f64) -> MeshInput {
        let mut input = MeshInput {
            positions: Vec::new(),
            triangles: Vec::new(),
        };
        for (offset, x) in [(0u32, 0.), (8, 6. + gap)] {
            input.positions.extend([
                Vec3::new(x, 0., 0.),
                Vec3::new(x + 6., 0., 0.),
                Vec3::new(x + 6., 4., 0.),
                Vec3::new(x, 4., 0.),
                Vec3::new(x, 0., 3.),
                Vec3::new(x + 6., 0., 3.),
                Vec3::new(x + 6., 4., 3.),
                Vec3::new(x, 4., 3.),
            ]);
            input.triangles.extend(
                [
                    [0, 2, 1],
                    [0, 3, 2],
                    [4, 5, 6],
                    [4, 6, 7],
                    [0, 1, 5],
                    [0, 5, 4],
                    [1, 2, 6],
                    [1, 6, 5],
                    [2, 3, 7],
                    [2, 7, 6],
                    [3, 0, 4],
                    [3, 4, 7],
                ]
                .map(|face| face.map(|n| n + offset)),
            );
        }
        input
    }
    let bodies = two_boxes(5.);
    let result = super::reconstruct_with_names(&bodies, 0.05, "Parts").unwrap();
    assert_eq!(result.body_names, ["Parts", "Parts (2)"]);
    assert_eq!(result.step.matches("MANIFOLD_SOLID_BREP").count(), 2);
    assert!(result.step.contains("'Parts (2)'"));
    let unsafe_gap = two_boxes(0.025);
    let result = super::reconstruct_with_names(&unsafe_gap, 0.05, "Close solid pair");
    assert!(matches!(result,Err(error) if error.message.contains("expanded solid bounds")));
}

#[test]
fn separately_drilled_perpendicular_bores_keep_two_cylindrical_faces() {
    use std::collections::BTreeMap;
    let side = 20_f64;
    let radius = 1.25;
    let outline = [[0., 0.], [side, 0.], [side, side], [0., side]];
    let tools: [Option<[f64; 2]>; 3] = [Some([6., 8.]), None, Some([13., 14.])];
    let world = |axis: usize, z: f64, uv: [f64; 2]| {
        let mut p = [0.; 3];
        p[axis] = z;
        p[(axis + 1) % 3] = uv[0];
        p[(axis + 2) % 3] = uv[1];
        p
    };
    let mid = |[x, y]: [f64; 2]| [[x, 0.], [side, y], [x, side], [0., y]];
    let mut outer_contacts = Vec::new();
    for (axis, center) in tools.iter().enumerate() {
        if let Some(c) = center {
            for level in [0., side] {
                outer_contacts.extend(mid(*c).map(|p| world(axis, level, p)));
            }
        }
    }
    let mut cells = Vec::<[[f64; 3]; 3]>::new();
    for axis in 0..3usize {
        let radial = tools[axis].map(|[x, y]| {
            let corner_angles =
                outline.map(|[a, b]| (b - y).atan2(a - x).rem_euclid(std::f64::consts::TAU));
            let mut angles = (0..64)
                .map(|i| f64::from(i) * std::f64::consts::TAU / 64.)
                .collect::<Vec<_>>();
            angles.extend(corner_angles);
            angles.sort_by(f64::total_cmp);
            angles.dedup();
            let stations = corner_angles.map(|a| {
                angles
                    .iter()
                    .position(|&v| v == a)
                    .expect("generated corner ray")
            });
            let ring = angles
                .into_iter()
                .map(|a| [x + radius * a.cos(), y + radius * a.sin()])
                .collect::<Vec<_>>();
            (ring, stations)
        });
        for level in [0., side] {
            for i in 0..4 {
                let j = (i + 1) % 4;
                let [a, b] = [outline[i], outline[j]].map(|p| world(axis, level, p));
                let varying = (0..3).find(|&c| a[c] != b[c]).expect("nonzero outer side");
                let mut outer = vec![a, b];
                outer.extend(outer_contacts.iter().copied().filter(|p| {
                    (0..3).all(|c| c == varying || p[c] == a[c])
                        && p[varying] >= a[varying].min(b[varying])
                        && p[varying] <= a[varying].max(b[varying])
                }));
                outer.sort_by(|p, q| p[varying].total_cmp(&q[varying]));
                outer.dedup();
                if a[varying] > b[varying] {
                    outer.reverse();
                }
                let mut push = |mut tri: [[f64; 3]; 3]| {
                    if level == 0. {
                        tri.swap(1, 2);
                    }
                    cells.push(tri);
                };
                if let (Some((ring, stations)), Some(center)) = (&radial, tools[axis]) {
                    let m = world(axis, level, mid(center)[i]);
                    let middle = outer
                        .iter()
                        .position(|p| *p == m)
                        .expect("matched stock boundary split point");
                    let [from, to] = [stations[i], stations[j]];
                    let [first, last] = [ring[from], ring[to]].map(|p| world(axis, level, p));
                    for side in outer[..=middle].windows(2) {
                        push([side[0], side[1], first]);
                    }
                    for side in outer[middle..].windows(2) {
                        push([side[0], side[1], last]);
                    }
                    let length = (ring.len() + to - from) % ring.len();
                    for offset in 0..length {
                        let p = world(axis, level, ring[(from + offset) % ring.len()]);
                        let q = world(axis, level, ring[(from + offset + 1) % ring.len()]);
                        push([m, q, p]);
                    }
                } else {
                    let center = world(axis, level, [side / 2.; 2]);
                    for edge in outer.windows(2) {
                        push([edge[0], edge[1], center]);
                    }
                }
            }
        }
        if let Some((ring, _)) = radial {
            for i in 0..ring.len() {
                let [u, v] = [ring[i], ring[(i + 1) % ring.len()]];
                let [a, b, c, d] = [
                    world(axis, 0., u),
                    world(axis, side, u),
                    world(axis, side, v),
                    world(axis, 0., v),
                ];
                cells.extend([[a, b, c], [a, c, d]]);
            }
        }
    }
    let mut mesh = MeshInput {
        positions: Vec::new(),
        triangles: Vec::new(),
    };
    let mut ids = BTreeMap::<[u64; 3], u32>::new();
    for tri in cells {
        let indices = tri.map(|p| {
            let p = p.map(|x| f64::from(x as f32));
            let key = p.map(|x| if x == 0. { 0 } else { x.to_bits() });
            *ids.entry(key).or_insert_with(|| {
                let id = mesh.positions.len() as u32;
                mesh.positions.push(Vec3::new(p[0], p[1], p[2]));
                id
            })
        });
        mesh.triangles.push(indices);
    }
    let step = reconstruct(&mesh, 0.05, "Independent perpendicular through holes").unwrap();
    assert_eq!(step.matches("MANIFOLD_SOLID_BREP").count(), 1);
    assert_eq!(step.matches("=PLANE(").count(), 6);
    assert_eq!(step.matches("=CYLINDRICAL_SURFACE(").count(), 2);
}
