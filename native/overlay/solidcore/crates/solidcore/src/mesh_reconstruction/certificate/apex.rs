//! Exact selected apex-star incidence prerequisite; no primitive normal claim.
use super::super::types::MeshInput;
use super::super::work::MeshWork;
use crate::kernel::Kernel;
use crate::{Result, SolidError};
use std::collections::{BTreeMap, BTreeSet};
const OP: &str = "mesh_reconstruction::certificate::ordered_apex_link";

/// Factual source-star incidence, shared by candidate steering and final acceptance.
/// An incomplete star is a geometric fact; cancellation and malformed data stay errors.
pub(crate) enum ApexLink {
    Absent,
    Complete(Vec<[f64; 3]>),
    Incomplete(&'static str),
}

/// Original-coordinate apex-star link in source winding order. None means no selected
/// source triangle contains this EXACT point. A selected but incomplete/ambiguous star
/// returns typed Unsupported; it may never be treated as a regular non-pole patch.
///
/// Coordinates, raw ids, incidence and link closure are independently recomputed; no
/// recognizer weld/rim flag is trusted. This certifies the fan's combinatorial star,
/// not its cone angular degree or orientation. The analytic primitive verifier must
/// additionally establish positive regular-ring heights, consistent strict radial
/// sector signs and winding ±1 around the actual primitive axis.
pub(crate) fn ordered_apex_link_with_work(
    k: &Kernel,
    work: &MeshWork,
    input: &MeshInput,
    selected: &[u32],
    apex: [f64; 3],
) -> Result<Option<Vec<[f64; 3]>>> {
    match inspect_apex_link(
        k,
        work,
        &input.triangles,
        input.positions.len(),
        |id| input.positions.get(id).copied(),
        selected,
        apex,
    )? {
        ApexLink::Absent => Ok(None),
        ApexLink::Complete(link) => Ok(Some(link)),
        ApexLink::Incomplete(reason) => Err(SolidError::Unsupported {
            operation: OP,
            reason,
        }),
    }
}

/// The SAME incidence algorithm over native vectors, without cloning a whole mesh.
pub(crate) fn inspect_vector_apex_link_with_work(
    k: &Kernel,
    work: &MeshWork,
    positions: &[crate::math::Vec3],
    triangles: &[[u32; 3]],
    selected: &[u32],
    apex: crate::math::Vec3,
) -> Result<ApexLink> {
    inspect_apex_link(
        k,
        work,
        triangles,
        positions.len(),
        |id| positions.get(id).map(|p| p.to_array()),
        selected,
        apex.to_array(),
    )
}

fn inspect_apex_link(
    k: &Kernel,
    work: &MeshWork,
    triangles: &[[u32; 3]],
    positions_len: usize,
    point_at: impl Fn(usize) -> Option<[f64; 3]>,
    selected: &[u32],
    apex: [f64; 3],
) -> Result<ApexLink> {
    let unsupported = |reason| SolidError::Unsupported {
        operation: OP,
        reason,
    };
    if triangles.len() > 200_000
        || positions_len > 600_000
        || selected.len() > triangles.len()
        || !apex.iter().all(|v| v.is_finite())
    {
        return Err(unsupported(
            "an apex-star input is invalid or exceeds its work budget",
        ));
    }
    let key = |p: [f64; 3]| p.map(|v| if v == 0.0 { 0 } else { v.to_bits() });
    let mut requested = BTreeSet::new();
    for &id in selected {
        work.spend_core(k, 1)?;
        let id = usize::try_from(id)
            .map_err(|_| unsupported("a selected apex triangle id does not fit this machine"))?;
        work.reserve_output_core(k, 1)?;
        if id >= triangles.len() || !requested.insert(id) {
            return Err(unsupported(
                "selected apex triangle ids are missing or duplicated",
            ));
        }
    }
    let mut outgoing = BTreeMap::new();
    let mut incoming = BTreeSet::new();
    let mut points = BTreeMap::new();
    let mut found = 0_usize;
    let mut excluded = 0_usize;
    for (id, triangle) in triangles.iter().enumerate() {
        work.spend_core(k, 1)?;
        let mut corners = Vec::new();
        for &vertex in triangle {
            let vertex = usize::try_from(vertex)
                .map_err(|_| unsupported("an apex source vertex id does not fit this machine"))?;
            let point = point_at(vertex)
                .ok_or_else(|| unsupported("an apex source triangle vertex is missing"))?;
            if !point.iter().all(|v| v.is_finite()) {
                return Err(unsupported("an apex source vertex is not finite"));
            }
            corners.push(point);
        }
        let [Some(&a), Some(&b), Some(&c)] = [corners.first(), corners.get(1), corners.get(2)]
        else {
            return Err(unsupported("an apex triangle lacks three corners"));
        };
        let hit = [a, b, c].map(|p| p == apex);
        if !hit.iter().any(|v| *v) {
            continue;
        }
        if !requested.contains(&id) {
            excluded += 1;
            continue;
        }
        found += 1;
        let (u, v) = match hit {
            [true, false, false] => (b, c),
            [false, true, false] => (c, a),
            [false, false, true] => (a, b),
            _ => {
                return Ok(ApexLink::Incomplete(
                    "an apex triangle collapses two raw corners to the pole",
                ));
            }
        };
        let (u_key, v_key) = (key(u), key(v));
        if u_key == v_key || incoming.contains(&v_key) || outgoing.contains_key(&u_key) {
            return Ok(ApexLink::Incomplete(
                "the selected apex star has ambiguous oriented incidence",
            ));
        }
        let point_refs =
            usize::from(!points.contains_key(&u_key)) + usize::from(!points.contains_key(&v_key));
        work.reserve_output_core(k, 2 + point_refs)?;
        incoming.insert(v_key);
        outgoing.insert(u_key, v_key);
        points.insert(u_key, u);
        points.insert(v_key, v);
    }
    if found == 0 {
        return Ok(ApexLink::Absent);
    }
    if excluded != 0
        || found < 3
        || outgoing.len() != incoming.len()
        || incoming.iter().any(|p| !outgoing.contains_key(p))
    {
        return Ok(ApexLink::Incomplete(
            "the selected apex star is incomplete or not a closed fan",
        ));
    }
    let &start = outgoing
        .keys()
        .next()
        .ok_or_else(|| unsupported("the selected apex star has no link"))?;
    let mut visited = BTreeSet::new();
    let mut point = start;
    let mut ring = Vec::new();
    loop {
        work.spend_core(k, 1)?;
        if !visited.insert(point) {
            if point == start {
                break;
            }
            return Ok(ApexLink::Incomplete(
                "the selected apex link crosses another link",
            ));
        }
        work.reserve_output_core(k, 1)?;
        ring.push(
            *points
                .get(&point)
                .ok_or_else(|| unsupported("an apex link point is missing"))?,
        );
        point = *outgoing
            .get(&point)
            .ok_or_else(|| unsupported("the selected apex link is open"))?;
    }
    if ring.len() != found {
        return Ok(ApexLink::Incomplete(
            "the selected apex link has more than one cycle",
        ));
    }
    Ok(ApexLink::Complete(ring))
}

/// Single-job convenience entry. Public workflows must use the shared-work variant.
pub(crate) fn ordered_apex_link(
    k: &Kernel,
    input: &MeshInput,
    selected: &[u32],
    apex: [f64; 3],
) -> Result<Option<Vec<[f64; 3]>>> {
    let work = MeshWork::new();
    work.spend_core(k, 0)?;
    let result = ordered_apex_link_with_work(k, &work, input, selected, apex);
    work.spend_core(k, 0)?;
    result
}

#[cfg(test)]
mod star_inspection_tests {
    use super::*;
    use crate::math::Vec3;
    #[test]
    fn one_incidence_engine_serves_steering_and_strict_acceptance() {
        let input = MeshInput {
            positions: vec![[0., 0., 0.], [1., 0., 1.], [0., 1., 1.], [-1., -1., 1.]],
            triangles: vec![[0, 1, 2], [0, 2, 3], [0, 3, 1]],
        };
        let k = Kernel::default();
        let work = MeshWork::new();
        let selected = [0, 1, 2];
        let raw = ordered_apex_link_with_work(&k, &work, &input, &selected, [0.; 3])
            .unwrap()
            .unwrap();
        let native: Vec<_> = input
            .positions
            .iter()
            .copied()
            .map(Vec3::from_array)
            .collect();
        let ApexLink::Complete(vectors) = inspect_vector_apex_link_with_work(
            &k,
            &work,
            &native,
            &input.triangles,
            &selected,
            Vec3::ZERO,
        )
        .unwrap() else {
            panic!("complete fan was not recognized")
        };
        assert_eq!(vectors, raw);
        assert!(matches!(
            inspect_vector_apex_link_with_work(
                &k,
                &work,
                &native,
                &input.triangles,
                &[0, 1],
                Vec3::ZERO
            )
            .unwrap(),
            ApexLink::Incomplete(_)
        ));
        assert!(
            ordered_apex_link_with_work(&k, &work, &input, &[0, 1], [0.; 3]).is_err(),
            "an incomplete steering fact must never become an acceptance certificate"
        );
    }
}
