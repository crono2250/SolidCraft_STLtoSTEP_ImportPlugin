//! Command-plugin adapter. Geometry lives in the Native Core extension.
#![deny(unsafe_code)]
#![deny(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::todo,
    clippy::unimplemented
)]
use serde::Deserialize;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use stl_reconstruction::{Vec3, mesh::MeshInput};

#[cfg(target_arch = "wasm32")]
mod component;

const JSON_LIMIT: usize = 1024 * 1024;
const SDK_LOCK: &[u8] = include_bytes!("../../../sdk-lock.json");

#[derive(Clone, Debug)]
pub enum Error {
    Input { field: String, reason: String },
    Unsupported(String),
    Limit(String),
    Cancelled,
    Command { command: String, reason: String },
    Permission(String),
    Manifest { field: String, reason: String },
    Trap(String),
}
fn invalid(field: &str, reason: impl ToString) -> Error {
    Error::Input {
        field: field.into(),
        reason: reason.to_string(),
    }
}
impl From<&str> for Error {
    fn from(reason: &str) -> Self {
        invalid("params", reason)
    }
}
impl From<stl_reconstruction::Failure> for Error {
    fn from(error: stl_reconstruction::Failure) -> Self {
        use stl_reconstruction::FailureClass;
        match error.class {
            FailureClass::InvalidInput => invalid("mesh", error.message),
            FailureClass::Unsupported => Self::Unsupported(error.message),
            FailureClass::LimitExceeded => Self::Limit(error.message),
            FailureClass::Cancelled => Self::Cancelled,
            FailureClass::Failed => Self::Trap(error.message),
        }
    }
}

pub trait Host {
    fn run(&mut self, command: &str, args: Value) -> Result<Value, Error>;
    fn cancelled(&self) -> bool {
        false
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Params {
    bodies: Vec<String>,
    #[serde(default = "tolerance")]
    tolerance: f64,
    name: Option<String>,
}
fn tolerance() -> f64 {
    0.05
}

#[derive(Clone, Deserialize)]
struct Mesh {
    body: String,
    component: u64,
    frame: String,
    positions: Vec<[f64; 3]>,
    triangles: Vec<[u32; 3]>,
}

fn plain(s: &str) -> bool {
    !s.trim().is_empty() && s.chars().count() <= 128 && !s.chars().any(char::is_control)
}

fn identity(mesh: &Mesh, tolerance: f64) -> String {
    let mut hash = Sha256::new();
    hash.update(b"stl-to-step-native-source-v1\0");
    for field in [
        env!("CARGO_PKG_VERSION").as_bytes(),
        stl_reconstruction::ALGORITHM_VERSION.as_bytes(),
        stl_reconstruction::FACE_ORDER_VERSION.as_bytes(),
        SDK_LOCK,
        mesh.body.as_bytes(),
    ] {
        hash.update((field.len() as u64).to_le_bytes());
        hash.update(field);
    }
    hash.update(mesh.component.to_le_bytes());
    hash.update(tolerance.to_le_bytes());
    hash.update((mesh.positions.len() as u64).to_le_bytes());
    for point in &mesh.positions {
        for coordinate in point {
            hash.update(coordinate.to_le_bytes());
        }
    }
    hash.update((mesh.triangles.len() as u64).to_le_bytes());
    for triangle in &mesh.triangles {
        for index in triangle {
            hash.update(index.to_le_bytes());
        }
    }
    format!("{:x}", hash.finalize())
}

fn call(host: &mut impl Host, command: &str, args: Value) -> Result<Value, Error> {
    if host.cancelled() {
        return Err(Error::Cancelled);
    }
    if serde_json::to_vec(&args)
        .map_err(|e| Error::Trap(e.to_string()))?
        .len()
        > JSON_LIMIT
    {
        return Err(Error::Limit(
            "command exceeds the host's 1 MiB transfer limit".into(),
        ));
    }
    let result = host.run(command, args)?;
    if let Some(error) = result.get("error").filter(|v| !v.is_null()) {
        return Err(Error::Command {
            command: command.into(),
            reason: error.to_string(),
        });
    }
    Ok(result)
}

/// The host owns the transaction, cancellation/adoption, undo, and saved ordinary features.
pub fn execute(host: &mut impl Host, entry: &str, args: Value) -> Result<Value, Error> {
    if entry != "convert" {
        return Err(invalid("entry", "unknown plugin entry"));
    }
    let params: Params = serde_json::from_value(args)
        .map_err(|e| invalid("params", format!("invalid parameters: {e}")))?;
    let [body] = params.bodies.as_slice() else {
        return Err("select exactly one mesh body".into());
    };
    if !plain(body)
        || params
            .name
            .as_deref()
            .is_some_and(|n| !plain(n) || n == body)
    {
        return Err(
            "use plain body/name text, at most 128 characters; the output name must differ".into(),
        );
    }
    if !params.tolerance.is_finite() || !(1e-6..=1.).contains(&params.tolerance) {
        return Err("tolerance must be between 0.000001 and 1 mm".into());
    }
    let value = call(
        host,
        "model.mesh",
        json!({"body":body,"tolerance":params.tolerance}),
    )?;
    let mesh: Mesh = serde_json::from_value(value)
        .map_err(|e| invalid("mesh", format!("invalid host mesh: {e}")))?;
    if mesh.body != *body || mesh.frame != "component-local-mm" {
        return Err("the host returned another body or coordinate frame".into());
    }
    if mesh.positions.is_empty()
        || mesh.positions.len() > 8192
        || mesh.triangles.is_empty()
        || mesh.triangles.len() > 16384
    {
        return Err("mesh is empty or exceeds 8192 vertices / 16384 triangles".into());
    }
    if mesh
        .positions
        .iter()
        .flatten()
        .any(|v| !v.is_finite() || v.abs() > 100_000.)
        || mesh
            .triangles
            .iter()
            .flatten()
            .any(|i| *i as usize >= mesh.positions.len())
    {
        return Err("mesh contains invalid coordinates or vertex indices".into());
    }

    // model.mesh is a general read API. Only a mesh body's intrinsic triangles may
    // authorize reconstruction; a solid's display tessellation must never do so.
    let inspected = call(host, "inspect.measure", json!({"bodies":[body]}))?;
    let measured = inspected
        .get("bodies")
        .and_then(Value::as_array)
        .filter(|rows| rows.len() == 1)
        .and_then(|rows| rows.first())
        .ok_or_else(|| Error::Trap("host did not identify the selected body".into()))?;
    if measured.get("name").and_then(Value::as_str) != Some(body.as_str())
        || measured.get("measured_by").and_then(Value::as_str) != Some("mesh")
    {
        return Err(Error::Unsupported("Select an imported mesh body; solid/sheet display meshes are not reconstruction inputs".into()));
    }
    let name = params.name.unwrap_or_else(|| {
        let prefix: String = body.chars().take(122).collect();
        format!("{prefix} Solid")
    });
    let inventory = call(host, "inspect.measure", json!({"names_only":true}))?;
    let names = inventory
        .get("bodies")
        .and_then(Value::as_array)
        .ok_or_else(|| Error::Trap("host did not return its body-name inventory".into()))?;
    if names.iter().any(|row| {
        ["name", "definition"]
            .iter()
            .any(|key| row.get(*key).and_then(Value::as_str) == Some(name.as_str()))
    }) {
        return Err(invalid(
            "name",
            "A body with that output name already exists; choose another name",
        ));
    }

    let fingerprint = identity(&mesh, params.tolerance);
    let source = MeshInput {
        positions: mesh
            .positions
            .iter()
            .map(|p| Vec3::new(p[0], p[1], p[2]))
            .collect(),
        triangles: mesh.triangles,
    };
    if host.cancelled() {
        return Err(Error::Cancelled);
    }
    let restored = stl_reconstruction::reconstruct_with_names(&source, params.tolerance, &name)?;
    if restored.body_names.iter().skip(1).any(|output| {
        names.iter().any(|row| {
            ["name", "definition"]
                .iter()
                .any(|key| row.get(*key).and_then(Value::as_str) == Some(output.as_str()))
        })
    }) {
        return Err(invalid(
            "name",
            "A body with a generated output name already exists; choose another name",
        ));
    }
    // Build and prove completely before the first edit. No partial candidate/faceted adoption.
    let imported = call(
        host,
        "timeline.add",
        json!({"feature": {
            "type":"import", "name":name, "body_names":restored.body_names, "component":mesh.component,
            "file":format!("stl-to-step-{fingerprint}.step"), "step":restored.step
        }}),
    )?;
    call(
        host,
        "timeline.add",
        json!({"feature": {
            "type":"remove", "name":format!("Replace {body}"), "bodies":[body], "component":mesh.component
        }}),
    )?;
    Ok(json!({
        "name":name, "body_names":restored.body_names, "feature":imported.get("feature"), "source_body":body,
        "source_fingerprint":fingerprint, "source_retained":"timeline-input",
        "algorithm":stl_reconstruction::ALGORITHM_VERSION,
        "face_order":stl_reconstruction::FACE_ORDER_VERSION,
        "rebuild":"recorded-step"
    }))
}

#[cfg(test)]
mod tests;
