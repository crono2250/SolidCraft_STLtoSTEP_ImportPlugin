use super::*;

struct ReadOnly {
    reply: Value,
    calls: Vec<String>,
    cancel: bool,
    mesh: bool,
    occupied: Vec<String>,
}
impl Host for ReadOnly {
    fn run(&mut self, command: &str, args: Value) -> Result<Value, Error> {
        self.calls.push(command.into());
        match command {
            "model.mesh" => Ok(self.reply.clone()),
            "inspect.measure" if args.get("names_only") == Some(&Value::Bool(true)) => {
                let rows: Vec<_> = std::iter::once("Mesh1".to_owned())
                    .chain(self.occupied.clone())
                    .map(|name| json!({"name":name,"definition":name}))
                    .collect();
                Ok(json!({"body_count":rows.len(),"bodies":rows}))
            }
            "inspect.measure" => Ok(
                json!({"body_count":1,"bodies":[{"name":"Mesh1","measured_by":if self.mesh {"mesh"}else{"smlib"}}]}),
            ),
            _ => panic!("Invalid or unsupported input must never edit the design: {command}"),
        }
    }
    fn cancelled(&self) -> bool {
        self.cancel
    }
}
fn host() -> ReadOnly {
    ReadOnly {
        reply: json!({
            "body":"Mesh1", "component":1, "frame":"component-local-mm",
            "positions":[[0.,0.,0.]], "triangles":[[0,0,2]]
        }),
        calls: vec![],
        cancel: false,
        mesh: true,
        occupied: vec![],
    }
}
#[test]
fn rejects_invalid_parameters_before_host_call() {
    for args in [
        json!({"bodies":[]}),
        json!({"bodies":["Mesh1","Mesh2"]}),
        json!({"bodies":["Mesh1"],"tolerance":0}),
        json!({"bodies":["Mesh1"],"tolerance":2}),
        json!({"bodies":["Mesh1"],"all_surfaces":true}),
        json!({"bodies":["Mesh1"],"picks":[]}),
        json!({"bodies":["Mesh1"],"name":"Mesh1"}),
    ] {
        let mut h = host();
        assert!(matches!(
            execute(&mut h, "convert", args),
            Err(Error::Input { .. })
        ));
        assert!(h.calls.is_empty());
    }
}
#[test]
fn invalid_source_does_not_request_edits() {
    let mut h = host();
    assert!(execute(&mut h, "convert", json!({"bodies":["Mesh1"]})).is_err());
    assert_eq!(h.calls, ["model.mesh"]);
}
#[test]
fn mismatched_source_identity_and_cancellation_are_refused() {
    let mut h = host();
    h.reply["body"] = json!("Other");
    assert!(execute(&mut h, "convert", json!({"bodies":["Mesh1"]})).is_err());
    let mut h = host();
    h.cancel = true;
    assert!(matches!(
        execute(&mut h, "convert", json!({"bodies":["Mesh1"]})),
        Err(Error::Cancelled)
    ));
    assert!(h.calls.is_empty());
}
#[test]
fn identity_binds_selection_parameters_geometry_and_component() {
    let a: Mesh = serde_json::from_value(host().reply).unwrap();
    let key = identity(&a, 0.05);
    let mut b = a.clone();
    b.body = "Mesh2".into();
    assert_ne!(key, identity(&b, 0.05));
    b = a.clone();
    b.component = 2;
    assert_ne!(key, identity(&b, 0.05));
    b = a.clone();
    b.positions[0][0] = 1.;
    assert_ne!(key, identity(&b, 0.05));
    assert_ne!(key, identity(&a, 0.01));
    assert_eq!(key, identity(&a, 0.05));
}
#[test]
fn host_command_failures_are_not_reported_as_unsupported_geometry() {
    let mut h = host();
    h.reply = json!({"error":"synthetic host failure"});
    assert!(
        matches!(execute(&mut h,"convert",json!({"bodies":["Mesh1"]})),
                    Err(Error::Command { command,.. }) if command=="model.mesh")
    );
    assert_eq!(h.calls, ["model.mesh"]);
}
#[test]
fn a_solids_display_mesh_is_never_sent_to_reconstruction() {
    let mut h = host();
    h.reply["triangles"] = json!([[0, 0, 0]]);
    h.mesh = false;
    assert!(matches!(
        execute(&mut h, "convert", json!({"bodies":["Mesh1"]})),
        Err(Error::Unsupported(_))
    ));
    assert_eq!(h.calls, ["model.mesh", "inspect.measure"]);
}
#[test]
fn output_name_cannot_overwrite_an_unrelated_body() {
    let mut h = host();
    h.reply["triangles"] = json!([[0, 0, 0]]);
    h.occupied = vec!["Existing".into()];
    assert!(
        matches!(execute(&mut h,"convert",json!({"bodies":["Mesh1"],"name":"Existing"})),
                    Err(Error::Input { field,.. }) if field=="name")
    );
    assert_eq!(
        h.calls,
        ["model.mesh", "inspect.measure", "inspect.measure"]
    );
}
