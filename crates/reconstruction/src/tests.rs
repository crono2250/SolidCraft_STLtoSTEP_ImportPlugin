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

#[test]
fn native_axial_countersink_keeps_its_conical_and_cylindrical_walls() {
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
    for (z, radius) in [(0., 2.), (3., 2.), (5., 4.)] {
        for &a in &angles {
            let (y, x) = a.sin_cos();
            mesh.positions.push(Vec3::new(
                f64::from((x * radius) as f32),
                f64::from((y * radius) as f32),
                z,
            ));
        }
    }
    for a in 0..n {
        let b = (a + 1) % n;
        mesh.triangles.extend([
            [a, b, n + b],
            [a, n + b, n + a],
            [a, 2 * n + a, 2 * n + b],
            [a, 2 * n + b, b],
            [n + a, n + b, 4 * n + b],
            [n + a, 4 * n + b, 4 * n + a],
        ]);
        for offset in [2 * n, 3 * n] {
            mesh.triangles.extend([
                [offset + a, offset + n + a, offset + n + b],
                [offset + a, offset + n + b, offset + b],
            ]);
        }
    }
    let input = mesh.clone();
    let step = reconstruct(&mesh, 0.05, "Cylindrical through hole and conical entry").unwrap();
    assert_eq!(mesh, input);
    assert_eq!(step.matches("MANIFOLD_SOLID_BREP").count(), 1);
    assert_eq!(step.matches("=PLANE(").count(), 6);
    assert_eq!(step.matches("=CONICAL_SURFACE(").count(), 1);
    assert_eq!(step.matches("=CYLINDRICAL_SURFACE(").count(), 1);
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
