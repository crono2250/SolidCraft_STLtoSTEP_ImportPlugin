//! Native-only reconstruction and STEP export, independent of the SolidCraft application.
#![forbid(unsafe_code)]
#![deny(clippy::unwrap_used, clippy::expect_used, clippy::panic)]
pub use solidcore_ops::mesh::ErrorClass as FailureClass;
use solidcore_record::mesh::{MeshInput, MeshInputRef};

pub const SDK_REVISION: &str = "11684d744efd619677b4a2347672b081a86f3e81";
pub const ALGORITHM_VERSION: &str = solidcore_ops::mesh::ALGORITHM_VERSION;
pub const FACE_ORDER_VERSION: &str = solidcore_ops::mesh::FACE_ORDER_VERSION;

#[derive(Debug)]
pub struct Failure {
    pub class: FailureClass,
    pub message: String,
}
impl std::fmt::Display for Failure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}
impl std::error::Error for Failure {}
fn failed(message: impl ToString) -> Failure {
    Failure {
        class: FailureClass::Failed,
        message: message.to_string(),
    }
}

/// A complete source-to-final certificate precedes adoption; candidates are never exported.
pub fn reconstruct(input: &MeshInput, tolerance: f64, name: &str) -> Result<String, Failure> {
    reconstruct_with_names(input, tolerance, name).map(|result| result.step)
}

/// A complete STEP result and its stable body inventory for atomic Doc import.
pub struct Reconstruction {
    pub step: String,
    pub body_names: Vec<String>,
}

pub fn reconstruct_with_names(
    input: &MeshInput,
    tolerance: f64,
    name: &str,
) -> Result<Reconstruction, Failure> {
    solidcore_ops::session::set_fixes(include_str!("../../../native/fixes.txt").lines())
        .map_err(|e| failed(format!("{e:?}")))?;
    let result = solidcore_ops::mesh::reconstruct_certified_bodies(
        MeshInputRef {
            positions: &input.positions,
            triangles: &input.triangles,
        },
        tolerance,
    )
    .map_err(|e| Failure {
        class: e.class(),
        message: e.to_string(),
    })?
    .ok_or_else(|| Failure {
        class: FailureClass::Unsupported,
        message:
            "This mesh is outside the supported certified solid families; no geometry was converted"
                .into(),
    })?;
    let header = solidcore_step::write::product::Header {
        description: "Certified analytic mesh reconstruction".into(),
        preprocessor_version: format!("STLtoSTEP plugin {ALGORITHM_VERSION}"),
        originating_system: "SolidCraft STLtoSTEP Import Plugin".into(),
        ..Default::default()
    };
    let body_names = (0..result.len())
        .map(|i| {
            if i == 0 {
                return name.to_owned();
            }
            let suffix = format!(" ({})", i + 1);
            let stem: String = name
                .chars()
                .take(128usize.saturating_sub(suffix.len()))
                .collect();
            format!("{stem}{suffix}")
        })
        .collect::<Vec<_>>();
    let bodies = result
        .iter()
        .zip(&body_names)
        .map(|(solid, name)| solidcore_step::write::product::ExportBody {
            name: name.clone(),
            record: solid.record(),
            color: None,
            faces: vec![],
        })
        .collect();
    let step = solidcore_step::write::product::bodies(bodies, &header).map_err(failed)?;
    Ok(Reconstruction { step, body_names })
}
pub use solidcore_record::{Vec3, mesh};

#[cfg(test)]
mod tests;
