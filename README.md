# SolidCraft STL to STEP Import Plugin

This repository builds a **standalone WebAssembly command plugin** for SolidCraft.
It carries the Native reconstruction work from the STL conversion project without
depending on the legacy `solidcraft-kernel` crate or modifying the installed application.

The Native-only guarantee applies to reconstruction inside this plugin. Document
adoption uses SolidCraft's standard STEP importer; in 0.45.0 that existing host
path still routes through `solidcraft-kernel`. The plugin does not ship or link
that crate, and does not change the installed host's backend.

## Download and install

1. Open **Actions > Build installable plugin** and choose a successful run.
2. Download the **stl-to-step-import-0.2.0** artifact.
3. In SolidCraft, choose **Preferences > Plugins > Install plugin...** and select
   that downloaded ZIP **without extracting it**.
4. Review the plugin name and permissions, then install.

Artifacts are retained for 30 days. Use **Run workflow** to build another copy after expiry.

The Actions download itself is an installable ZIP: `plugin.json` and `plugin.wasm`
are at its root. There is no second ZIP to unpack or source code to compile.
The Wasm package is platform independent; it needs a native SolidCraft build with
the `commands@0.2` plugin host. The compatibility target is SolidCraft **0.45.0**.

Open/import an STL using SolidCraft's normal mesh importer, select one mesh body,
then use **Surface > STL to STEP Import > convert** (also available in Plugins).
The default tolerance is **0.05 mm**. Export the resulting solid with SolidCraft's
normal **STEP export** command.

## Current support and limits

The plugin reconstructs these closed solid families when the source geometry
and the exported Native solid pass the full geometric and topology checks:

- Constant-section profiles with straight or circular boundaries and through holes.
- Orthogonal stepped blanks with exact planar faces.
- Right circular cones and frustums, including the finite apex of a complete cone.
- Rectangular blanks with separate coaxial through-hole bands, including conical
  entries at a change in axial radius.
- Multiple disjoint supported solids in one STL, when the tolerance envelopes
  of their bounding boxes remain separate. The command adopts all solids together.

Connected milled parts requiring multiple machining directions, abrupt bore
shoulders, arbitrary freeform
surfaces, sheet meshes and selected-face feature fitting remain outside these
families. Unsupported or damaged inputs return an error and keep the original
mesh body. The plugin applies the requested tolerance and existing host limits.
- The host transfer boundary permits at most 8,192 vertices, 16,384 triangles and
  1 MiB per command/result; a smaller mesh can still exceed the byte budget.
- The manifest requests 100 billion fuel, 128 MiB linear memory, a 1 MiB guest stack
  and a 30-second deadline. These are limits, not measured peak-memory claims.
  Existing host ceilings are not changed by this plugin.

Solid/sheet display tessellations are refused: only intrinsic mesh-body triangles authorize reconstruction.
An existing unrelated body cannot be overwritten by the output name.

The original mesh import stays in the timeline. A successful call adds an ordinary
embedded STEP import and retires the current mesh body in **one undo transaction**.
Undo restores the mesh. The output remains usable after removing the plugin.
The result is a **frozen reconstruction**, not a live plugin feature: parameter edits
do not rerun Wasm. Undo or suppress the replacement to recover the source before
running another conversion. Source identity includes body/component, geometry,
tolerance, algorithm, face ordering and the exact SDK/Native extension identity.

The plugin requests only `inspect.measure`, `model.mesh` and `timeline.add`. It requests no file folder,
network, clock, application-setting or other-plugin grants. Native computation is
inside the Wasm guest; the host owns background execution, cancellation and atomic adoption.

## Build from source

Build-tool bootstrap supports x86-64 Windows and Linux.
Prerequisites: Python 3.12+, Git, and Rust **1.99.1** with the
`wasm32-unknown-unknown` standard library.

```sh
python3 tools/prepare_sdk.py
cargo fetch --locked
cargo test --workspace --locked
cargo build --locked --release -p solidcraft-stl-to-step-plugin --target wasm32-unknown-unknown
python3 tools/package.py
python3 tools/verify_package.py dist/stl-to-step-import-0.2.0.zip
```

For distributable builds, remap the checkout and Cargo-home prefixes using
`RUSTFLAGS=--remap-path-prefix=...` as the workflow does. Packaging refuses
components containing Windows build paths. `package.py` downloads and verifies
the exact `wasm-tools` and Binaryen releases in `sdk-lock.json`; it does not install system tools.
Rust uses the size-focused z release profile. The packaging compiler runs Binaryen -Oz, similar-function merging and
size convergence without --fast-math, then validates the
component against the existing installer limits.

`prepare_sdk.py` verifies a pinned public SolidCraft source archive and applies
only the project's **solidcore/** extension, with editable Rust modules in
native/overlay/ and a small SDK integration diff. It never includes `crates/kernel`,
the app/runtime/UI, local workflow tools, private STL files or screenshots.
The SDK is a build input under ignored `vendor/sdk/`, not a runtime dependency.
The installer ZIP contains only the manifest, component, license, instructions and
content checksums and the required dependency notices.

CI also runs the inherited Native mesh/Ops regressions and the real portable
SolidCraft host against independently generated box, annular-prism and tetrahedron inputs. It checks installation,
conversion, STEP, one undo/redo, preserved mesh history, planar-face sketching and
reopening without the plugin. Check the actual run before relying on its artifact;
a workflow definition alone is not evidence of a passing build.

## License and origin

Apache-2.0; see [LICENSE](LICENSE) and [NOTICE](NOTICE).
The published Native SDK revision, archive digest and extension digest are recorded
in [sdk-lock.json](sdk-lock.json). Supplied private models, screenshots, derived
private geometry and private validation records are never included in this repository
or its Actions artifacts.
