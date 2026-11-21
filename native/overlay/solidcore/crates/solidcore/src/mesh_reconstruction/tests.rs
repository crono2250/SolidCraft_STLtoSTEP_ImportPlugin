//! Public synthetic regressions moved to native source-array fixtures.
//! These exercise planning/fitting/proofs without app Body, record, Ops, or private models.
//! Full reconstructed-volume/STEP/Undo assertions remain in their original integration suites
//! until the independently certified Ops dispatch exists; no planning test replaces them.
use super::*;
use crate::math::{Vec2, Vec3};
use crate::prism::profile::Seg2;
use crate::Kernel;

pub(super) fn box_mesh(w: f64, h: f64, d: f64) -> MeshInput {
    MeshInput {
        positions: vec![
            [0., 0., 0.],
            [w, 0., 0.],
            [w, h, 0.],
            [0., h, 0.],
            [0., 0., d],
            [w, 0., d],
            [w, h, d],
            [0., h, d],
        ],
        triangles: vec![
            [0, 3, 2],
            [0, 2, 1],
            [4, 5, 6],
            [4, 6, 7],
            [0, 1, 5],
            [0, 5, 4],
            [3, 7, 6],
            [3, 6, 2],
            [0, 4, 7],
            [0, 7, 3],
            [1, 2, 6],
            [1, 6, 5],
        ],
    }
}
fn cylinder_wall(point: Vec3, radius: f64, lo: f64, hi: f64, concave: bool) -> MeshInput {
    let n = 128usize;
    let mut positions = Vec::new();
    for z in [lo, hi] {
        for i in 0..n {
            let a = std::f64::consts::TAU * i as f64 / n as f64;
            positions.push((point + Vec3::new(radius * a.cos(), radius * a.sin(), z)).to_array());
        }
    }
    let mut triangles = Vec::new();
    for i in 0..n {
        let a = i as u32;
        let b = ((i + 1) % n) as u32;
        for mut triangle in [[a, b, a + n as u32], [a + n as u32, b, b + n as u32]] {
            if concave {
                triangle.swap(1, 2);
            }
            triangles.push(triangle);
        }
    }
    MeshInput {
        positions,
        triangles,
    }
}
fn cone_fan(apex: Vec3, half_angle: f64, depth: f64, concave: bool) -> MeshInput {
    let n = 128usize;
    let mut positions = vec![apex.to_array()];
    let radius = depth * half_angle.tan();
    for i in 0..n {
        let a = std::f64::consts::TAU * i as f64 / n as f64;
        positions.push((apex + Vec3::new(radius * a.cos(), radius * a.sin(), depth)).to_array());
    }
    let mut triangles = Vec::new();
    for i in 0..n {
        let mut triangle = [0, ((i + 1) % n + 1) as u32, (i + 1) as u32];
        if concave {
            triangle.swap(1, 2);
        }
        triangles.push(triangle);
    }
    MeshInput {
        positions,
        triangles,
    }
}
fn spherical_cap(center: Vec3, radius: f64) -> MeshInput {
    let (nu, nv) = (96usize, 20usize);
    let mut positions = Vec::new();
    for j in 0..=nv {
        let v = 0.45 + (1.50 - 0.45) * j as f64 / nv as f64;
        for i in 0..nu {
            let u = std::f64::consts::TAU * i as f64 / nu as f64;
            positions.push(
                (center
                    + Vec3::new(
                        radius * v.cos() * u.cos(),
                        radius * v.sin(),
                        radius * v.cos() * u.sin(),
                    ))
                .to_array(),
            );
        }
    }
    let mut triangles = Vec::new();
    for j in 0..nv {
        for i in 0..nu {
            let a = (j * nu + i) as u32;
            let b = (j * nu + (i + 1) % nu) as u32;
            let c = ((j + 1) * nu + i) as u32;
            let d = ((j + 1) * nu + (i + 1) % nu) as u32;
            triangles.extend([[a, b, c], [c, b, d]]);
        }
    }
    // u then latitude has inward orientation, as a spherical pocket's source surface.
    MeshInput {
        positions,
        triangles,
    }
}
fn toroidal_fillet() -> MeshInput {
    let (nu, nv) = (192usize, 24usize);
    let mut positions = Vec::new();
    for j in 0..=nv {
        let v = std::f64::consts::FRAC_PI_2 * j as f64 / nv as f64;
        for i in 0..nu {
            let u = std::f64::consts::TAU * i as f64 / nu as f64;
            positions.push([
                (17. + 3. * v.cos()) * u.cos(),
                (17. + 3. * v.cos()) * u.sin(),
                7. + 3. * v.sin(),
            ]);
        }
    }
    let mut triangles = Vec::new();
    for j in 0..nv {
        for i in 0..nu {
            let a = (j * nu + i) as u32;
            let b = (j * nu + (i + 1) % nu) as u32;
            let c = ((j + 1) * nu + i) as u32;
            let d = ((j + 1) * nu + (i + 1) % nu) as u32;
            triangles.extend([[a, b, c], [c, b, d]]);
        }
    }
    MeshInput {
        positions,
        triangles,
    }
}

#[test]
fn fits_lines_arcs_and_full_circles_with_original_area_tolerances() {
    let circle: Vec<_> = (0..48)
        .map(|i| {
            let angle = f64::from(i) * 7.5f64.to_radians();
            Vec2::new(5. + 3. * angle.cos(), 3. * angle.sin())
        })
        .collect();
    let fitted = profile::fit_profile(&circle, 0.05, 1e-6);
    assert!(
        fitted.segs.iter().all(|s| matches!(s, Seg2::Arc { .. })),
        "{:?}",
        fitted.segs
    );
    let sweep: f64 = fitted
        .segs
        .iter()
        .map(|s| {
            if let Seg2::Arc { sweep, .. } = s {
                *sweep
            } else {
                0.
            }
        })
        .sum();
    assert!((sweep - std::f64::consts::TAU).abs() < 1e-9);
    assert!((fitted.signed_area().unwrap().value - std::f64::consts::PI * 9.).abs() < 1e-6);
    let mut points = Vec::new();
    for (cx, cy, start) in [
        (18., 2., -90.),
        (18., 8., 0.),
        (2., 8., 90.),
        (2., 2., 180.),
    ] {
        for k in 0..=9 {
            let a = (start + f64::from(k) * 10.).to_radians();
            points.push(Vec2::new(cx + 2. * a.cos(), cy + 2. * a.sin()));
        }
    }
    let fitted = profile::fit_profile(&points, 0.05, 1e-6);
    assert_eq!(
        (
            fitted
                .segs
                .iter()
                .filter(|s| matches!(s, Seg2::Arc { .. }))
                .count(),
            fitted
                .segs
                .iter()
                .filter(|s| matches!(s, Seg2::Line { .. }))
                .count()
        ),
        (4, 4)
    );
    assert!(
        (fitted.signed_area().unwrap().value - (200. - (4. - std::f64::consts::PI) * 4.)).abs()
            < 1e-6
    );
    let square = [
        Vec2::new(0., 0.),
        Vec2::new(5., 0.),
        Vec2::new(10., 0.),
        Vec2::new(10., 10.),
        Vec2::new(0., 10.),
    ];
    assert_eq!(profile::fit_profile(&square, 0.05, 1e-6).segs.len(), 4);
}
#[test]
fn prism_policy_never_rounds_a_coarse_hexagonal_hole() {
    let points: Vec<_> = (0..6)
        .map(|i| {
            let a = f64::from(i) * std::f64::consts::TAU / 6.;
            Vec2::new(10. * a.cos(), 10. * a.sin())
        })
        .collect();
    assert_eq!(profile::fit_loop(&points, 1., 1e-6).segs.len(), 6);
}
#[test]
fn native_picks_find_original_bore_dimensions_and_material_side() {
    let k = Kernel::default();
    let input = cylinder_wall(Vec3::new(12., 15., 0.), 4., 8., 20., true);
    let bore = recognize_region(
        &k,
        &input,
        Vec3::new(16., 15., 14.),
        SurfaceKind::Auto,
        0.02,
    )
    .unwrap();
    let Primitive::Cylinder {
        radius,
        axis,
        point,
    } = bore.surface
    else {
        panic!("{:?}", bore.surface)
    };
    assert!((radius - 4.).abs() < 1e-3 && axis.z.abs() > 0.9999);
    assert!((point.x - 12.).abs() < 1e-3 && (point.y - 15.).abs() < 1e-3);
    assert!(bore.concave);
    assert!((bore.area - std::f64::consts::TAU * 4. * 12.).abs() < 1.);
}
#[test]
fn native_apex_fit_keeps_original_59_degree_drill_angle() {
    let k = Kernel::default();
    let tip_height = 4. / 59f64.to_radians().tan();
    let apex = Vec3::new(12., 15., 8. - tip_height);
    let input = cone_fan(apex, 59f64.to_radians(), tip_height, true);
    let tip = recognize_region(
        &k,
        &input,
        Vec3::new(13.5, 15., 7.4),
        SurfaceKind::Auto,
        0.02,
    )
    .unwrap();
    let Primitive::Cone {
        half_angle,
        axis,
        apex: fitted,
    } = tip.surface
    else {
        panic!("{:?}", tip.surface)
    };
    assert!(
        (half_angle.to_degrees() - 59.).abs() < 0.1,
        "{}",
        half_angle.to_degrees()
    );
    assert!(axis.z > 0.9999 && (fitted.z - apex.z).abs() < 1e-3);
    assert_eq!(
        fitted, apex,
        "a complete source fan keeps its intrinsic pole exactly"
    );
    assert!(tip.concave);
    assert!(input
        .positions
        .iter()
        .any(|p| (Vec3::from_array(*p) - fitted).length() < 1e-9));
    assert!(input.positions.iter().all(|p| Primitive::Cone {
        apex,
        axis: Vec3::Z,
        half_angle: 59f64.to_radians()
    }
    .signed_distance(Vec3::from_array(*p))
    .abs()
        < 1e-7));
    let measures = tip.measurements;
    assert!((measures.full_angle_degrees.unwrap() - 118.).abs() < 0.2);
}
#[test]
fn native_pocket_sphere_preserves_original_radius_and_center_tolerances() {
    let k = Kernel::default();
    let center = Vec3::new(28., -2., 10.);
    let input = spherical_cap(center, 5.);
    let ball = recognize_region(
        &k,
        &input,
        Vec3::new(28., 2.5, 10.5),
        SurfaceKind::Sphere,
        0.02,
    )
    .unwrap();
    let Primitive::Sphere {
        center: got,
        radius,
    } = ball.surface
    else {
        panic!("{:?}", ball.surface)
    };
    assert!((radius - 5.).abs() < 1e-3 && (got - center).length() < 1e-3);
    assert!(ball.concave);
}
#[test]
fn native_fillet_torus_keeps_original_major_minor_and_axis_tolerances() {
    let k = Kernel::default();
    let input = toroidal_fillet();
    for kind in [SurfaceKind::Auto, SurfaceKind::Torus] {
        let region = recognize_region(&k, &input, Vec3::new(19.1, 0., 9.1), kind, 0.02).unwrap();
        let Primitive::Torus {
            major,
            minor,
            axis,
            center,
        } = region.surface
        else {
            panic!("{:?}", region.surface)
        };
        assert!(
            (major - 17.).abs() < 0.01 && (minor - 3.).abs() < 0.01,
            "{major} {minor}"
        );
        assert!(axis.z.abs() > 0.9999 && (center.z - 7.).abs() < 0.01);
        assert!(!region.concave);
    }
}
#[test]
fn native_alignment_preserves_original_turned_box_position_and_size_assertions() {
    let k = Kernel::default();
    let mut input = box_mesh(40., 30., 10.);
    let turn = Vec3::new(1., 2., 3.);
    for p in &mut input.positions {
        *p = (Vec3::from_array(*p).rotate_vec_about_axis(turn, 0.8) + Vec3::new(5., -7., 3.))
            .to_array();
    }
    let alignment = align_to_axes(&k, &input, 0.02, false).unwrap();
    let mut lo = Vec3::new(f64::INFINITY, f64::INFINITY, f64::INFINITY);
    let mut hi = -lo;
    for p in &input.positions {
        let q = Vec3::from_array(*p).rotate_vec_about_axis(alignment.axis, alignment.angle)
            + alignment.translation;
        lo = Vec3::new(lo.x.min(q.x), lo.y.min(q.y), lo.z.min(q.z));
        hi = Vec3::new(hi.x.max(q.x), hi.y.max(q.y), hi.z.max(q.z));
    }
    let size = hi - lo;
    let mut dims = [size.x, size.y, size.z];
    dims.sort_by(f64::total_cmp);
    assert!(
        lo.x.abs() < 1e-6 && lo.y.abs() < 1e-6 && lo.z.abs() < 1e-6,
        "{lo:?}"
    );
    assert!(
        (dims[0] - 10.).abs() < 1e-3
            && (dims[1] - 30.).abs() < 1e-3
            && (dims[2] - 40.).abs() < 1e-3,
        "{dims:?}"
    );
    assert!((size.z - 10.).abs() < 1e-3);
}
#[test]
fn native_grid_rounding_keeps_original_design_intent_threshold() {
    let k = Kernel::default();
    let input = cylinder_wall(Vec3::new(20., 15., 0.), 3.99, 0., 10., true);
    let picks = [MeshPick {
        point: [23.99, 15., 5.],
        kind: SurfaceKind::Auto,
    }];
    for (tolerance, grid, expected) in [(0.05, 0., 7.98), (0.05, 0.05, 8.), (0.005, 1., 7.98)] {
        let tools = fit_tools(&k, &input, tolerance, &picks, false, grid).unwrap();
        let measures = tools.first().unwrap().surface.measurements();
        assert!((measures.diameter.unwrap() - expected).abs() < 1e-3);
    }
}
#[test]
fn native_box_segmentation_and_faceted_plan_remain_six_planes() {
    let k = Kernel::default();
    let input = box_mesh(20., 10., 5.);
    let regions = recognize_all(&k, &input, 0.01).unwrap();
    assert_eq!(regions.len(), 6);
    assert!(regions
        .iter()
        .all(|r| r.surface.kind() == SurfaceKind::Plane));
    assert_eq!(
        regions.iter().map(|r| r.triangles.len()).sum::<usize>(),
        input.triangles.len()
    );
    let work = MeshWork::new();
    let plan = faceted_plan_with_work(&k, &work, &input, 0.01).unwrap();
    assert_eq!(plan.faces.len(), 6);
    let mut original_ids: Vec<_> = plan
        .into_source_patch_claims_with_work(&k, &work)
        .unwrap()
        .into_iter()
        .flatten()
        .collect();
    original_ids.sort_unstable();
    assert_eq!(original_ids, (0..12).collect::<Vec<u32>>());
}
#[test]
fn zero_area_source_triangle_is_dropped_but_original_triangle_ids_survive() {
    let k = Kernel::default();
    let mut input = box_mesh(20., 10., 5.);
    let kept = input.triangles.len();
    input.positions.push([10., 0., 0.]);
    input.triangles.push([0, 8, 1]);
    let source = source::SourceMesh::checked(&input).unwrap();
    let welded = source::weld(&k, &source, 0.01).unwrap();
    assert_eq!(welded.triangles.len(), kept);
    assert_eq!(
        welded.source_triangles,
        (0..kept).map(|i| Some(i as u32)).collect::<Vec<_>>()
    );
    let work = MeshWork::new();
    let plan = faceted_plan_with_work(&k, &work, &input, 0.01).unwrap();
    assert_eq!(plan.faces.len(), 6);
    let mut original_ids: Vec<_> = plan
        .into_source_patch_claims_with_work(&k, &work)
        .unwrap()
        .into_iter()
        .flatten()
        .collect();
    original_ids.sort_unstable();
    assert_eq!(original_ids, (0..12).collect::<Vec<u32>>());
    let sliver = MeshInput {
        positions: vec![[0., 0., 0.], [1., 0., 0.], [2., 0., 0.]],
        triangles: vec![[0, 1, 2]],
    };
    assert!(source::weld(&k, &source::SourceMesh::checked(&sliver).unwrap(), 0.05).is_err());
}
#[test]
fn malformed_source_inputs_remain_typed_failures() {
    let k = Kernel::default();
    let input = box_mesh(10., 10., 10.);
    for tolerance in [f64::NAN, 0., -1., 5.] {
        assert!(recognize_region(&k, &input, Vec3::ZERO, SurfaceKind::Auto, tolerance).is_err());
    }
    assert!(recognize_region(
        &k,
        &input,
        Vec3::new(f64::NAN, 0., 0.),
        SurfaceKind::Auto,
        0.05
    )
    .is_err());
    let mut bad = input.clone();
    bad.triangles.push([u32::MAX, 0, 1]);
    assert!(prepare_conversion(&k, &bad, 0.05, &[]).is_err());
}

#[test]
fn source_count_admission_uses_the_real_workflow_before_materializing_arrays() {
    for purpose in [InputPurpose::Conversion, InputPurpose::Recognition] {
        admit_input_counts(purpose, 150_000, 50_000).unwrap();
        assert!(matches!(
            admit_input_counts(purpose, 150_000, 50_001),
            Err(MeshError::InputLimit {
                count: 50_001,
                limit: 50_000,
                unit: "triangles",
                ..
            })
        ));
        assert!(matches!(
            admit_input_counts(purpose, 150_001, 50_000),
            Err(MeshError::InputLimit {
                count: 150_001,
                limit: 150_000,
                unit: "vertices",
                ..
            })
        ));
    }
    admit_input_counts(InputPurpose::Deviation, 600_000, 200_000).unwrap();
    assert!(matches!(
        admit_input_counts(InputPurpose::Deviation, 600_001, 200_000),
        Err(MeshError::InputLimit {
            count: 600_001,
            limit: 600_000,
            unit: "vertices",
            ..
        })
    ));
    assert!(matches!(
        admit_input_counts(InputPurpose::Deviation, 0, usize::MAX),
        Err(MeshError::InputLimit {
            count: usize::MAX,
            limit: 200_000,
            unit: "triangles",
            ..
        })
    ));
    assert!(matches!(
        admit_input_counts(InputPurpose::Conversion, usize::MAX, 0),
        Err(MeshError::InputLimit {
            count: usize::MAX,
            limit: 150_000,
            unit: "vertices",
            ..
        })
    ));
}

#[test]
fn source_materialization_admission_shares_cells_and_keeps_cancellation_typed() {
    let k = Kernel::default();
    let work = MeshWork::new();
    admit_input_counts_with_work(&k, &work, InputPurpose::Deviation, 600_000, 200_000).unwrap();
    admit_input_counts_with_work(&k, &work, InputPurpose::Deviation, 600_000, 200_000).unwrap();
    assert!(matches!(
        admit_input_counts_with_work(&k, &work, InputPurpose::Deviation, 600_000, 200_000),
        Err(MeshError::BudgetExceeded {
            stage: "complete mesh workflow certificate cells",
            ..
        })
    ));
    assert!(
        work.check(&k).is_err(),
        "a refused preallocation must leave the shared budget latched"
    );
    let token = crate::kernel::CancelToken::new();
    let mut k = Kernel::default();
    k.set_cancel_token(token.clone());
    token.cancel();
    assert!(
        matches!(admit_input_counts_with_work(&k, &MeshWork::new(), InputPurpose::Conversion, 1, 1), Err(MeshError::Kernel(error)) if error.is_cancelled())
    );
}

fn cone_with_two_rings(apex: Vec3, half_angle: f64, depth: f64, concave: bool) -> MeshInput {
    let n = 128usize;
    let mut positions = vec![apex.to_array()];
    for height in [depth / 2., depth] {
        let radius = height * half_angle.tan();
        for i in 0..n {
            let angle = std::f64::consts::TAU * i as f64 / n as f64;
            positions.push(
                (apex + Vec3::new(radius * angle.cos(), radius * angle.sin(), height)).to_array(),
            );
        }
    }
    let mut triangles = Vec::new();
    for i in 0..n {
        let low = (1 + i) as u32;
        let next = (1 + (i + 1) % n) as u32;
        let high = low + n as u32;
        let high_next = next + n as u32;
        for mut triangle in [
            [0, next, low],
            [low, next, high_next],
            [low, high_next, high],
        ] {
            if concave {
                triangle.swap(1, 2);
            }
            triangles.push(triangle);
        }
    }
    MeshInput {
        positions,
        triangles,
    }
}

#[test]
fn native_multiring_apex_keeps_raw_pole_and_whole_selected_patch() {
    let k = Kernel::default();
    let depth = 4. / 59f64.to_radians().tan();
    let apex = Vec3::new(12., 15., 8. - depth);
    let input = cone_with_two_rings(apex, 59f64.to_radians(), depth, true);
    let region = recognize_region(
        &k,
        &input,
        Vec3::new(13.5, 15., 7.4),
        SurfaceKind::Cone,
        0.02,
    )
    .unwrap();
    assert_eq!(
        region.triangles.len(),
        input.triangles.len(),
        "the selected cone includes both the star and the extra ring band"
    );
    let Primitive::Cone {
        apex: got,
        axis,
        half_angle,
    } = region.surface
    else {
        panic!("{:?}", region.surface)
    };
    assert_eq!(
        got, apex,
        "extra regular triangles cannot release the intrinsic complete source pole"
    );
    assert!(axis.z > 0.9999 && (half_angle.to_degrees() - 59.).abs() < 0.1);
    assert!(region.concave);
    let work = MeshWork::new();
    let selected: Vec<_> = (0..input.triangles.len())
        .map(|i| u32::try_from(i).unwrap())
        .collect();
    let proof = certify_primitive_region_with_work(
        &k,
        &work,
        &input,
        &region.surface,
        &selected,
        true,
        0.02,
    )
    .unwrap();
    assert!(proof.upper_bound() <= 0.02);
    let tools = fit_tools_with_work(
        &k,
        &work,
        &input,
        0.02,
        &[MeshPick {
            point: [13.5, 15., 7.4],
            kind: SurfaceKind::Cone,
        }],
        false,
        0.,
    )
    .unwrap();
    assert_eq!(tools.len(), 1);
    assert_eq!(tools[0].source_triangles, selected);
    assert!(matches!(tools[0].surface, Primitive::Cone { apex: got, .. } if got == apex));
    work.check(&k).unwrap();
}

#[test]
fn native_grid_rounding_preserves_complete_source_pole() {
    let k = Kernel::default();
    let depth = 4. / 59f64.to_radians().tan();
    let apex = Vec3::new(12.007, 15.007, 8. - depth);
    let input = cone_fan(apex, 59f64.to_radians(), depth, true);
    let work = MeshWork::new();
    let tools = fit_tools_with_work(
        &k,
        &work,
        &input,
        0.02,
        &[MeshPick {
            point: [13.507, 15.007, 7.4],
            kind: SurfaceKind::Cone,
        }],
        false,
        0.01,
    )
    .unwrap();
    assert_eq!(tools.len(), 1);
    assert_eq!(tools[0].source_triangles.len(), input.triangles.len());
    assert!(matches!(tools[0].surface, Primitive::Cone { apex: got, .. } if got == apex));
    let ToolGeometry::Cone { origin, .. } = &tools[0].geometry else {
        panic!("expected a native cone request")
    };
    assert_eq!(*origin, apex);
    work.check(&k).unwrap();
}

#[test]
fn native_pole_free_frustum_keeps_original_axis_offset_rounding() {
    let k = Kernel::default();
    let depth = 4. / 59f64.to_radians().tan();
    let apex = Vec3::new(12.007, 15.007, 8. - depth);
    let mut input = cone_with_two_rings(apex, 59f64.to_radians(), depth, true);
    input.triangles.retain(|t| !t.contains(&0));
    let picks = [MeshPick {
        point: [15.007, 15.007, 7.6],
        kind: SurfaceKind::Cone,
    }];
    let unrounded = fit_tools(&k, &input, 0.02, &picks, false, 0.).unwrap();
    let rounded = fit_tools(&k, &input, 0.02, &picks, false, 0.01).unwrap();
    let (
        Primitive::Cone {
            apex: raw,
            axis,
            half_angle,
        },
        Primitive::Cone {
            apex: grid,
            axis: grid_axis,
            half_angle: grid_angle,
        },
    ) = (unrounded[0].surface, rounded[0].surface)
    else {
        panic!("expected cone supports")
    };
    assert_eq!(grid.x, (raw.x / 0.01).round() * 0.01);
    assert_eq!(grid.y, (raw.y / 0.01).round() * 0.01);
    assert_eq!(grid.z, raw.z);
    assert_eq!(axis, grid_axis);
    assert_eq!(half_angle, grid_angle);
    assert_eq!(unrounded[0].source_triangles, rounded[0].source_triangles);
    assert_eq!(rounded[0].source_triangles.len(), input.triangles.len());
}

#[test]
fn native_fixed_source_pole_survives_rigid_transform_and_actual_cone_construction() {
    use crate::surface::implicit::AnalyticSupport;
    let depth = 4. / 59f64.to_radians().tan();
    let apex = Vec3::new(12.007, 15.007, 8. - depth);
    for angle in [0., 0.47] {
        let mut k = Kernel::default();
        let work = MeshWork::new();
        let transform = |p: Vec3| p.rotate_vec_about_axis(Vec3::X, angle) + Vec3::new(-3., 7., 2.);
        let pole = transform(apex);
        let mut input = cone_with_two_rings(apex, 59f64.to_radians(), depth, true);
        for p in &mut input.positions {
            *p = transform(Vec3::from_array(*p)).to_array();
        }
        let pick = transform(Vec3::new(13.507, 15.007, 7.4));
        let tools = fit_tools_with_work(
            &k,
            &work,
            &input,
            0.02,
            &[MeshPick {
                point: pick.to_array(),
                kind: SurfaceKind::Cone,
            }],
            false,
            0.01,
        )
        .unwrap();
        assert_eq!(tools.len(), 1);
        let selected = &tools[0];
        assert_eq!(selected.source_triangles.len(), input.triangles.len());
        assert!(matches!(selected.surface, Primitive::Cone { apex: got, .. } if got == pole));
        let ToolGeometry::Cone { origin, .. } = &selected.geometry else {
            panic!("expected a native cone request")
        };
        assert_eq!(*origin, pole);
        let mut body = build_tool(&mut k, &selected.geometry).unwrap();
        let mut cones = 0;
        for &face in body.face_list() {
            let surface = body.face(face).unwrap().surface.as_ref().unwrap();
            if let Some(AnalyticSupport::Cone {
                placement,
                base_radius,
                ..
            }) = AnalyticSupport::of(surface)
            {
                assert_eq!(placement.origin(), pole);
                assert_eq!(base_radius, 0.);
                cones += 1;
            }
        }
        assert!(
            cones > 0,
            "actual construction must retain a cone with its zero-radius pole"
        );
        let proof =
            certify_fitted_tool_with_work(&k, &work, &input, selected, &mut body, 0.02).unwrap();
        assert!(proof.upper_bound() <= 0.02);
        work.check(&k).unwrap();
    }
}

#[test]
fn profile_work_admission_counts_container_nodes_before_shadow_comparison() {
    let k = Kernel::default();
    let work = MeshWork::new();
    work.spend(&k, 199_999_999).unwrap();
    let empty = crate::prism::profile::Region2 {
        outer: crate::prism::profile::Loop2 { segs: Vec::new() },
        holes: Vec::new(),
    };
    let regions = vec![empty.clone(), empty];
    let result = same_shadow_with_work(&k, &work, &regions, &regions, 0.01, 1e-9);
    assert!(
        matches!(result, Err(MeshError::BudgetExceeded { .. })),
        "{result:?}"
    );
    assert!(matches!(
        work.check(&k),
        Err(MeshError::BudgetExceeded { .. })
    ));
}

#[test]
fn profile_work_admission_keeps_empty_shadow_comparison_meaning() {
    let k = Kernel::default();
    let work = MeshWork::new();
    assert_eq!(
        same_shadow_with_work(&k, &work, &[], &[], 0.01, 1e-9).unwrap(),
        Some(true)
    );
}

#[test]
fn sketch_copy_counts_cancel_before_overflow_and_charge_full_inline_bezier() {
    let mut k = Kernel::default();
    let work = MeshWork::new();
    work.reserve_cells(&k, 2_000_000 - 22).unwrap();
    assert!(matches!(
        admit_sketch_copy_with_work(&k, &work, SketchCopyPart::Segments { previous: 0 }, 1),
        Err(MeshError::BudgetExceeded { .. })
    ));
    let token = crate::kernel::CancelToken::new();
    k.set_cancel_token(token.clone());
    token.cancel();
    assert!(matches!(admit_sketch_copy_with_work(&k, &MeshWork::new(),
        SketchCopyPart::Regions, usize::MAX), Err(e) if e.is_cancelled()));
    assert!(
        matches!(sketch_geometry_with_work(&k, &MeshWork::new(), &[], f64::NAN),
        Err(e) if e.is_cancelled())
    );
}
#[test]
fn sketch_shared_factory_preserves_empty_input_and_invalid_empty_region() {
    let k = Kernel::default();
    let work = MeshWork::new();
    assert!(sketch_geometry_with_work(&k, &work, &[], 0.05)
        .unwrap()
        .geometry
        .is_empty());
    let empty = crate::prism::profile::Region2::default();
    assert!(matches!(
        sketch_geometry_with_work(&k, &work, &[empty], 0.05),
        Err(MeshError::InvalidInput { .. })
    ));
}

#[test]
fn sketch_shared_factory_keeps_clockwise_circle_joining() {
    let k = Kernel::default();
    let work = MeshWork::new();
    let region = crate::prism::profile::Region2 {
        outer: profile::circle(Vec2::new(0., 0.), 1.).reversed(),
        holes: Vec::new(),
    };
    let drawing = sketch_geometry_with_work(&k, &work, &[region], 0.05).unwrap();
    assert_eq!(
        drawing.geometry,
        vec![SketchGeometry::Circle {
            center: Vec2::new(0., 0.),
            radius: 1.
        }]
    );
    work.check(&k).unwrap();
}

#[test]
fn faceted_source_chart_keeps_unit_scale_source_origins_and_complete_polygonal_holes() {
    let mut input = MeshInput {
        positions: Vec::new(),
        triangles: Vec::new(),
    };
    let ring = [
        [7., -3.],
        [12., -3.],
        [12., 0.],
        [7., 0.],
        [8., -2.],
        [9., -2.],
        [9., -1.],
        [8., -1.],
    ];
    for z in [11., 13.] {
        for [x, y] in ring {
            input.positions.push([x, y, z]);
        }
    }
    for i in 0u32..4 {
        let j = (i + 1) % 4;
        // Complete top/bottom annuli plus outward outer and inward hole walls.
        for mut t in [[i, j, j + 4], [i, j + 4, i + 4]] {
            t.swap(1, 2);
            input.triangles.push(t);
        }
        input
            .triangles
            .extend([[i + 8, j + 8, j + 12], [i + 8, j + 12, i + 12]]);
        input.triangles.extend([[i, j, j + 8], [i, j + 8, i + 8]]);
        input
            .triangles
            .extend([[j + 4, i + 4, i + 12], [j + 4, i + 12, j + 12]]);
    }
    let mut k = Kernel::default();
    let work = MeshWork::new();
    let plan = faceted_plan_with_work(&k, &work, &input, 0.01).unwrap();
    assert_eq!(plan.faces.len(), 10);
    let anchors: Vec<_> = plan
        .faces
        .iter()
        .map(|f| match f.loops[0][0] {
            NativeEdge::Line { a, .. } => a,
        })
        .collect();
    let body = build_faceted(&mut k, &plan).unwrap();
    assert_eq!(body.face_list().len(), 10);
    let mut caps_with_hole = 0usize;
    for &id in body.face_list() {
        let surface = body.face(id).unwrap().surface.as_ref().unwrap();
        let crate::surface::surface::SurfaceKind::Plane(plane) =
            surface.kind_with_nurb(&k).unwrap()
        else {
            panic!("faceted source must remain Plane");
        };
        assert_eq!([plane.uv_scale().x, plane.uv_scale().y], [1., 1.]);
        assert!(
            anchors
                .iter()
                .any(|p| p.to_array() == plane.position().origin().to_array()),
            "an unrelated sphere-gauge origin replaced the source anchor"
        );
        assert!(plane.step_uv_domain().is_bounded());
        let (same, other) = crate::topology::face::faceuses(&body, id).unwrap();
        let fu = same.or(other).unwrap();
        if body.faceuse(fu).unwrap().loopuses.len() == 2 {
            caps_with_hole += 1;
        }
    }
    assert_eq!(
        caps_with_hole, 2,
        "both caps retain the complete outer+hole family"
    );
}

#[test]
fn faceted_source_chart_rejects_bad_normals_open_loops_and_nonfinite_endpoints() {
    let mut k = Kernel::default();
    let work = MeshWork::new();
    let plan = faceted_plan_with_work(&k, &work, &box_mesh(5., 3., 2.), 0.01).unwrap();
    let mut zero = plan.clone();
    zero.faces[0].normal = Vec3::ZERO;
    assert!(build_faceted(&mut k, &zero).is_err());
    let mut bad = plan.clone();
    let NativeEdge::Line { a, .. } = &mut bad.faces[0].loops[0][0];
    a.x = f64::NAN;
    assert!(build_faceted(&mut k, &bad).is_err());
    let mut open = plan;
    open.faces[0].loops[0].pop();
    assert!(build_faceted(&mut k, &open).is_err());
}

#[test]
fn faceted_empty_loop_inventory_is_bounded_and_cancel_precedes_its_refusal() {
    let mut k = Kernel::default();
    let plan = FacetedPlan {
        faces: vec![FacetedFace {
            normal: Vec3::Z,
            source_triangles: Vec::new(),
            loops: vec![Vec::new(); 150_001],
        }],
    };
    assert!(matches!(
        build_faceted(&mut k, &plan),
        Err(MeshError::BudgetExceeded { limit: 150_000, .. })
    ));
    let token = crate::kernel::CancelToken::new();
    k.set_cancel_token(token.clone());
    token.cancel();
    assert!(
        matches!(build_faceted(&mut k,&plan),Err(MeshError::Kernel(error)) if error.is_cancelled())
    );
}

#[test]
fn recognition_handoff_counts_are_cumulative_and_cancel_precedes_a_bad_inventory() {
    let region = MeshRegion {
        surface: Primitive::Plane {
            point: Vec3::ZERO,
            normal: Vec3::Z,
        },
        measurements: PrimitiveMeasures::default(),
        triangles: vec![0; 8192],
        area: 1.,
        max_deviation: 0.,
        rms_deviation: 0.,
        concave: false,
    };
    let mut k = Kernel::default();
    let work = MeshWork::new();
    let mut accepted = 0usize;
    while admit_region_handoff_with_work(&k, &work, std::slice::from_ref(&region)).is_ok() {
        accepted += 1;
        assert!(
            accepted < 30,
            "same shared output-reference budget must stop repeated handoffs"
        );
    }
    assert!(accepted > 1);
    assert!(matches!(
        work.check(&k),
        Err(MeshError::BudgetExceeded {
            stage: "complete mesh workflow output references",
            ..
        })
    ));
    assert!(
        admit_pick_handoff_with_work(&k, &work, &[]).is_err(),
        "empty output cannot reset a latched workflow"
    );
    let too_many = vec![
        MeshPick {
            point: [0.; 3],
            kind: SurfaceKind::Auto
        };
        2000
    ];
    assert!(admit_pick_handoff_with_work(&k, &MeshWork::new(), &too_many).is_err());
    let token = crate::kernel::CancelToken::new();
    k.set_cancel_token(token.clone());
    token.cancel();
    assert!(
        matches!(admit_pick_handoff_with_work(&k, &work, &too_many), Err(MeshError::Kernel(error)) if error.is_cancelled())
    );
}

#[test]
fn all_surface_pick_points_read_original_corners_without_reintroducing_dropped_degenerate_adjacency(
) {
    let mut source = box_mesh(20., 10., 5.);
    source.positions.push([10., 0., 0.]);
    source.triangles = std::iter::once([0, 8, 1]).chain(source.triangles).collect();
    let original = source.clone();
    let k = Kernel::default();
    let regions = recognize_all(&k, &source, 0.02).unwrap();
    assert_eq!(regions.iter().map(|r| r.triangles.len()).sum::<usize>(), 12);
    let ids: std::collections::BTreeSet<_> = regions
        .iter()
        .flat_map(|r| r.triangles.iter().copied())
        .collect();
    assert_eq!(ids, (1u32..13).collect());
    let picks = picks_for_all(&k, &source, 0.02).unwrap();
    assert_eq!(picks.len(), 6);
    for (region, pick) in regions.iter().zip(&picks) {
        let corners = |index: u32| {
            let [a, b, c] = source.triangles[index as usize];
            [
                Vec3::from_array(source.positions[a as usize]),
                Vec3::from_array(source.positions[b as usize]),
                Vec3::from_array(source.positions[c as usize]),
            ]
        };
        let area = |index: u32| {
            let [a, b, c] = corners(index);
            (b - a).cross(c - a).length() * 0.5
        };
        let triangle = region
            .triangles
            .iter()
            .copied()
            .max_by(|a, b| area(*a).total_cmp(&area(*b)))
            .unwrap();
        let [a, b, c] = corners(triangle);
        assert_eq!(
            pick.point,
            ((a + b + c) / 3.).to_array(),
            "original triangle id and equal-area ordering must survive"
        );
    }
    assert_eq!(source, original);
    let mut invalid = source;
    invalid.triangles.push(invalid.triangles[1]);
    let error = picks_for_all(&k, &invalid, 0.02).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("more than two incident triangles"),
        "positive nonmanifold faces must still be refused: {error}"
    );
}
