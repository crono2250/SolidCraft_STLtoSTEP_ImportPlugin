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
    solidcore_ops::session::set_fixes(include_str!("../../../native/fixes.txt").lines())
        .map_err(|e| failed(format!("{e:?}")))?;
    let result = solidcore_ops::mesh::reconstruct_single_product(
        MeshInputRef { positions: &input.positions, triangles: &input.triangles }, tolerance
    ).map_err(|e| Failure { class:e.class(), message:e.to_string() })?.ok_or_else(||
        Failure { class:FailureClass::Unsupported,
                  message:"This mesh is not a supported certified constant-section solid; no geometry was converted".into() }
    )?;
    let header = solidcore_step::write::product::Header {
        description: "Certified analytic mesh reconstruction".into(),
        preprocessor_version: format!("STLtoSTEP plugin {ALGORITHM_VERSION}"),
        originating_system: "SolidCraft STLtoSTEP Import Plugin".into(),
        ..Default::default()
    };
    solidcore_step::write::product::bodies(
        vec![solidcore_step::write::product::ExportBody {
            name: name.into(),
            record: result.record(),
            color: None,
            faces: vec![],
        }],
        &header,
    )
    .map_err(failed)
}
pub use solidcore_record::{Vec3, mesh};

#[cfg(test)]
mod tests;
