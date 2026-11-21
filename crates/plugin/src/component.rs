//! Current published craft:plugin@0.2.0; errors keep their original category.
// Only generated canonical-ABI code may contain unsafe operations.
#[allow(unsafe_code)]
mod bindings {
    wit_bindgen::generate!({ path: "wit", world: "command-plugin" });
}
use super::{Error, Host, JSON_LIMIT, execute, invalid};
use bindings::craft::plugin::{
    commands, control,
    types::{CommandFailure, FieldFailure, PluginError},
};
use bindings::exports::craft::plugin::entry::Guest;

fn from_wire(error: PluginError) -> Error {
    match error {
        PluginError::PermissionDenied(s) => Error::Permission(s),
        PluginError::CommandFailed(c) => Error::Command {
            command: c.command,
            reason: c.reason,
        },
        PluginError::LimitExceeded(s) => Error::Limit(s),
        PluginError::InvalidManifest(f) => Error::Manifest {
            field: f.field,
            reason: f.reason,
        },
        PluginError::InvalidInput(f) => Error::Input {
            field: f.field,
            reason: f.reason,
        },
        PluginError::Trap(s) => Error::Trap(s),
        PluginError::Cancelled => Error::Cancelled,
        PluginError::Unsupported(s) => Error::Unsupported(s),
    }
}
fn to_wire(error: Error) -> PluginError {
    match error {
        Error::Permission(s) => PluginError::PermissionDenied(s),
        Error::Command { command, reason } => {
            PluginError::CommandFailed(CommandFailure { command, reason })
        }
        Error::Limit(s) => PluginError::LimitExceeded(s),
        Error::Manifest { field, reason } => {
            PluginError::InvalidManifest(FieldFailure { field, reason })
        }
        Error::Input { field, reason } => PluginError::InvalidInput(FieldFailure { field, reason }),
        Error::Trap(s) => PluginError::Trap(s),
        Error::Cancelled => PluginError::Cancelled,
        Error::Unsupported(s) => PluginError::Unsupported(s),
    }
}
struct EngineHost;
impl Host for EngineHost {
    fn run(&mut self, command: &str, args: serde_json::Value) -> Result<serde_json::Value, Error> {
        let reply = commands::run(command, &args.to_string()).map_err(from_wire)?;
        if reply.len() > JSON_LIMIT {
            return Err(Error::Limit("host reply exceeds 1 MiB".into()));
        }
        serde_json::from_str(&reply).map_err(|e| Error::Trap(e.to_string()))
    }
    fn cancelled(&self) -> bool {
        control::cancelled()
    }
}
struct Plugin;
impl Guest for Plugin {
    fn execute(entry: String, params: String) -> Result<String, PluginError> {
        if params.len() > JSON_LIMIT {
            return Err(PluginError::LimitExceeded("parameters exceed 1 MiB".into()));
        }
        let args = serde_json::from_str(&params).map_err(|e| to_wire(invalid("params", e)))?;
        let result = execute(&mut EngineHost, &entry, args).map_err(to_wire)?;
        serde_json::to_string(&result).map_err(|e| PluginError::Trap(e.to_string()))
    }
}
// The export macro also generates canonical-ABI shims; handwritten adapter code stays denied.
#[allow(unsafe_code)]
mod abi_exports {
    use super::{Plugin, bindings};
    bindings::export!(Plugin with_types_in bindings);
}
