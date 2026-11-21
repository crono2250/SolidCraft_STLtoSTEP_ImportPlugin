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
