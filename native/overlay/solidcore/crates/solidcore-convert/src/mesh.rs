//! Mesh records and native reconstruction descriptors, field for field. This module does not
//! weld, transform, fit, measure, classify or validate geometry; those are kernel operations.
use solidcore::mesh_reconstruction as k;
use solidcore_record::mesh as r;

use crate::{record_vec3, vec3};

/// The original record mesh as the kernel's arrays, preserving indices and order.
#[must_use]
pub fn input(mesh: &r::MeshInput) -> k::MeshInput {
    input_borrowed(mesh.into())
}

/// Copy borrowed original arrays fieldwise. Ops must admit and charge the counts
/// to its shared workflow before calling; this converter computes no geometry.
#[must_use]
pub fn input_borrowed(mesh: r::MeshInputRef<'_>) -> k::MeshInput {
    k::MeshInput {
        positions: mesh.positions.iter().map(|p| [p.x, p.y, p.z]).collect(),
        triangles: mesh.triangles.to_vec(),
    }
}

/// The kernel's original indexed mesh as record data, preserving indices and order.
#[must_use]
pub fn record_input(mesh: &k::MeshInput) -> r::MeshInput {
    r::MeshInput {
        positions: mesh
            .positions
            .iter()
            .map(|p| solidcore_record::Vec3::new(p[0], p[1], p[2]))
            .collect(),
        triangles: mesh.triangles.clone(),
    }
}

/// A requested surface family as the kernel's discriminator.
#[must_use]
pub fn kind(kind: r::SurfaceKind) -> k::SurfaceKind {
    match kind {
        r::SurfaceKind::Auto => k::SurfaceKind::Auto,
        r::SurfaceKind::Plane => k::SurfaceKind::Plane,
        r::SurfaceKind::Cylinder => k::SurfaceKind::Cylinder,
        r::SurfaceKind::Cone => k::SurfaceKind::Cone,
        r::SurfaceKind::Sphere => k::SurfaceKind::Sphere,
        r::SurfaceKind::Torus => k::SurfaceKind::Torus,
    }
}

/// The kernel's surface family as the record's discriminator.
#[must_use]
pub fn record_kind(kind: k::SurfaceKind) -> r::SurfaceKind {
    match kind {
        k::SurfaceKind::Auto => r::SurfaceKind::Auto,
        k::SurfaceKind::Plane => r::SurfaceKind::Plane,
        k::SurfaceKind::Cylinder => r::SurfaceKind::Cylinder,
        k::SurfaceKind::Cone => r::SurfaceKind::Cone,
        k::SurfaceKind::Sphere => r::SurfaceKind::Sphere,
        k::SurfaceKind::Torus => r::SurfaceKind::Torus,
    }
}

/// A record primitive as the kernel's, without normalising any direction.
#[must_use]
pub fn primitive(surface: r::Primitive) -> k::Primitive {
    match surface {
        r::Primitive::Plane { point, normal } => k::Primitive::Plane {
            point: vec3(point),
            normal: vec3(normal),
        },
        r::Primitive::Cylinder {
            point,
            axis,
            radius,
        } => k::Primitive::Cylinder {
            point: vec3(point),
            axis: vec3(axis),
            radius,
        },
        r::Primitive::Cone {
            apex,
            axis,
            half_angle,
        } => k::Primitive::Cone {
            apex: vec3(apex),
            axis: vec3(axis),
            half_angle,
        },
        r::Primitive::Sphere { center, radius } => k::Primitive::Sphere {
            center: vec3(center),
            radius,
        },
        r::Primitive::Torus {
            center,
            axis,
            major,
            minor,
        } => k::Primitive::Torus {
            center: vec3(center),
            axis: vec3(axis),
            major,
            minor,
        },
    }
}

/// A native primitive as record data, without changing its units or parameters.
#[must_use]
pub fn record_primitive(surface: k::Primitive) -> r::Primitive {
    match surface {
        k::Primitive::Plane { point, normal } => r::Primitive::Plane {
            point: record_vec3(point),
            normal: record_vec3(normal),
        },
        k::Primitive::Cylinder {
            point,
            axis,
            radius,
        } => r::Primitive::Cylinder {
            point: record_vec3(point),
            axis: record_vec3(axis),
            radius,
        },
        k::Primitive::Cone {
            apex,
            axis,
            half_angle,
        } => r::Primitive::Cone {
            apex: record_vec3(apex),
            axis: record_vec3(axis),
            half_angle,
        },
        k::Primitive::Sphere { center, radius } => r::Primitive::Sphere {
            center: record_vec3(center),
            radius,
        },
        k::Primitive::Torus {
            center,
            axis,
            major,
            minor,
        } => r::Primitive::Torus {
            center: record_vec3(center),
            axis: record_vec3(axis),
            major,
            minor,
        },
    }
}

/// A selected point and requested family as native data.
#[must_use]
pub fn pick(pick: &r::MeshPick) -> k::MeshPick {
    k::MeshPick {
        point: [pick.point.x, pick.point.y, pick.point.z],
        kind: kind(pick.kind),
    }
}

/// A native pick as record data.
#[must_use]
pub fn record_pick(pick: &k::MeshPick) -> r::MeshPick {
    r::MeshPick {
        point: solidcore_record::Vec3::new(pick.point[0], pick.point[1], pick.point[2]),
        kind: record_kind(pick.kind),
    }
}

/// Display data copied to native fields; absence is not filled by geometry computation.
#[must_use]
pub fn measurements(value: &r::PrimitiveMeasures) -> k::PrimitiveMeasures {
    k::PrimitiveMeasures {
        diameter: value.diameter,
        full_angle_degrees: value.full_angle_degrees,
    }
}

/// Native display data copied to record fields.
#[must_use]
pub fn record_measurements(value: &k::PrimitiveMeasures) -> r::PrimitiveMeasures {
    r::PrimitiveMeasures {
        diameter: value.diameter,
        full_angle_degrees: value.full_angle_degrees,
    }
}

/// A recognised region as native data. This does not certify the supplied descriptor.
#[must_use]
pub fn region(region: &r::MeshRegion) -> k::MeshRegion {
    k::MeshRegion {
        surface: primitive(region.surface),
        measurements: region.measurements.as_ref().map(measurements).unwrap_or(
            k::PrimitiveMeasures {
                diameter: None,
                full_angle_degrees: None,
            },
        ),
        triangles: region.triangles.clone(),
        area: region.area,
        max_deviation: region.max_deviation,
        rms_deviation: region.rms_deviation,
        concave: region.concave,
    }
}

/// A native region as record data. The returned fitting metrics carry no acceptance proof.
#[must_use]
pub fn record_region(region: &k::MeshRegion) -> r::MeshRegion {
    r::MeshRegion {
        surface: record_primitive(region.surface),
        measurements: Some(record_measurements(&region.measurements)),
        triangles: region.triangles.clone(),
        area: region.area,
        max_deviation: region.max_deviation,
        rms_deviation: region.rms_deviation,
        concave: region.concave,
    }
}

/// Move a recognised native region into record data without copying its original
/// triangle IDs. Ops must admit the fixed payload/return containers beforehand.
#[must_use]
pub fn record_region_owned(region: k::MeshRegion) -> r::MeshRegion {
    r::MeshRegion {
        surface: record_primitive(region.surface),
        measurements: Some(record_measurements(&region.measurements)),
        triangles: region.triangles,
        area: region.area,
        max_deviation: region.max_deviation,
        rms_deviation: region.rms_deviation,
        concave: region.concave,
    }
}

/// A native descriptive deviation report as record data, without recomputing its metrics.
#[must_use]
pub fn record_deviation(report: &k::Deviation) -> r::Deviation {
    r::Deviation {
        max: report.max,
        mean: report.mean,
        rms: report.rms,
        within: report.within,
        vertices: report.vertices,
        worst: report
            .worst
            .iter()
            .map(|(point, distance)| (record_vec3(*point), *distance))
            .collect(),
    }
}

/// The kernel's outlined plane and profiles as the record's, retaining profile order.
#[must_use]
pub fn record_outline(
    plane: &solidcore::eval::Frame,
    regions: &[solidcore::prism::profile::Region2],
) -> r::SurfaceOutline {
    r::SurfaceOutline {
        plane: crate::record_plane(plane),
        regions: regions.iter().map(crate::record_region2).collect(),
    }
}

/// A native rigid alignment as record fields, without composing the transform.
#[must_use]
pub fn record_alignment(alignment: &k::Alignment) -> r::Alignment {
    r::Alignment {
        translation: record_vec3(alignment.translation),
        axis: record_vec3(alignment.axis),
        angle: alignment.angle,
        angle_degrees: alignment.angle_degrees,
        rotate: alignment.rotate,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use solidcore_record::Vec3;

    #[test]
    fn original_arrays_and_pick_order_survive_the_boundary() {
        let mesh = r::MeshInput {
            positions: vec![
                Vec3::new(-0.0, 1.25, 5.0),
                Vec3::new(2.0, -3.5, 7.0),
                Vec3::new(0.0, 0.0, 9.0),
            ],
            triangles: vec![[2, 0, 1], [1, 0, 2]],
        };
        let roundtrip = record_input(&input(&mesh));
        assert_eq!(roundtrip, mesh);
        assert_eq!(roundtrip.positions[0].x.to_bits(), (-0.0f64).to_bits());
        let picks = [
            r::MeshPick {
                point: Vec3::new(0.0, 5.0, 2.0),
                kind: r::SurfaceKind::Cone,
            },
            r::MeshPick {
                point: Vec3::new(1.0, 0.0, -0.0),
                kind: r::SurfaceKind::Plane,
            },
        ];
        let native: Vec<_> = picks.iter().map(pick).collect();
        let records: Vec<_> = native.iter().map(record_pick).collect();
        assert_eq!(records, picks);
        assert_eq!(records[1].point.z.to_bits(), (-0.0f64).to_bits());
    }

    #[test]
    fn primitive_parameters_are_copied_without_normalising_or_fitting() {
        let surfaces = [
            r::Primitive::Plane {
                point: Vec3::new(1.0, 2.0, 3.0),
                normal: Vec3::new(0.0, 0.0, 4.0),
            },
            r::Primitive::Cylinder {
                point: Vec3::new(2.0, 3.0, 4.0),
                axis: Vec3::new(0.0, 7.0, 0.0),
                radius: 3.125,
            },
            r::Primitive::Cone {
                apex: Vec3::new(-1.0, -2.0, -3.0),
                axis: Vec3::new(8.0, 0.0, 0.0),
                half_angle: 0.321,
            },
            r::Primitive::Sphere {
                center: Vec3::new(5.0, 6.0, 7.0),
                radius: 9.75,
            },
            r::Primitive::Torus {
                center: Vec3::new(1.0, -2.0, 3.0),
                axis: Vec3::new(0.0, 0.0, 6.0),
                major: 12.5,
                minor: 1.75,
            },
        ];
        for surface in surfaces {
            assert_eq!(record_primitive(primitive(surface)), surface);
        }
    }

    #[test]
    fn region_indices_and_metrics_are_preserved_without_a_certificate_claim() {
        let region = r::MeshRegion {
            surface: r::Primitive::Sphere {
                center: Vec3::new(1.0, 2.0, 3.0),
                radius: 7.0,
            },
            measurements: Some(r::PrimitiveMeasures::default()),
            triangles: vec![5, 1, 4],
            area: 9.125,
            max_deviation: 0.0025,
            rms_deviation: 0.00125,
            concave: true,
        };
        assert_eq!(record_region(&self::region(&region)), region);
        let native = self::region(&region);
        let storage = native.triangles.as_ptr();
        let moved = record_region_owned(native);
        assert_eq!(
            moved.triangles.as_ptr(),
            storage,
            "the owned converter must move the original-ID backing"
        );
        assert_eq!(moved, region);
    }
}

/// Precomputed native sketch entities as record data; no endpoint/circle evaluation occurs here.
#[must_use]
pub fn record_sketch_geometry(geometry: &k::SketchGeometry) -> r::SketchGeometry {
    match geometry {
        k::SketchGeometry::Line { a, b } => r::SketchGeometry::Line {
            a: crate::record_vec2(*a),
            b: crate::record_vec2(*b),
        },
        k::SketchGeometry::Arc { center, a, b } => r::SketchGeometry::Arc {
            center: crate::record_vec2(*center),
            a: crate::record_vec2(*a),
            b: crate::record_vec2(*b),
        },
        k::SketchGeometry::Circle { center, radius } => r::SketchGeometry::Circle {
            center: crate::record_vec2(*center),
            radius: *radius,
        },
    }
}

/// A native drawing and its already-computed tolerance as records.
#[must_use]
pub fn record_sketch_drawing(drawing: &k::SketchDrawing) -> r::SketchDrawing {
    r::SketchDrawing {
        geometry: drawing
            .geometry
            .iter()
            .map(record_sketch_geometry)
            .collect(),
        join_tolerance: drawing.join_tolerance,
    }
}
