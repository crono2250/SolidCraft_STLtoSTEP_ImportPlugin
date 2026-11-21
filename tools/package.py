#!/usr/bin/env python3
"""Build an installable ZIP. Actions uploads package contents, so its artifact ZIP installs too."""
from pathlib import Path
import argparse, hashlib, json, os, re, shutil, subprocess, tomllib, zipfile
from licenses import write_notices
from wasm_tools import get
from binaryen import get as get_optimizer

ROOT = Path(__file__).resolve().parents[1]

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--wasm", type=Path)
    parser.add_argument("--output", type=Path, default=ROOT / "dist",
                        help="Write a package into a fresh output directory")
    args = parser.parse_args()
    target = Path(os.environ.get("CARGO_TARGET_DIR", ROOT / "target"))
    core = args.wasm or target / "wasm32-unknown-unknown/release/solidcraft_stl_to_step_plugin.wasm"
    manifest = ROOT / "plugin/plugin.json"
    version = json.loads(manifest.read_text())["version"]
    if tomllib.loads((ROOT / "crates/plugin/Cargo.toml").read_text())["package"]["version"] != version:
        raise RuntimeError("Manifest and guest crate versions differ")
    output_dir = args.output.resolve()
    package = output_dir / "package"
    if package.exists():
        raise RuntimeError("Package output already exists; preserve prior results or use a fresh output")
    package.mkdir(parents=True)
    tool = get()
    # Size optimization preserves Wasm numeric semantics: no fast-math or host-limit changes.
    optimized = output_dir / "optimized-core.wasm"
    optimizer=get_optimizer()
    release=json.loads((ROOT/"sdk-lock.json").read_text())["wasm_release"]
    profile=tomllib.loads((ROOT/"Cargo.toml").read_text())["profile"]["release"]
    for key in ("opt-level","lto","codegen-units","strip","panic"):
        if profile[key]!=release[key.replace("-","_")]:
            raise RuntimeError("Release profile and pinned compiler recipe differ: "+key)
    subprocess.run([str(optimizer),str(core),*release["binaryen_flags"],"-o",str(optimized)],
                   check=True,env=dict(os.environ,BINARYEN_CORES=os.environ.get("BINARYEN_CORES","2")),timeout=1800)
    subprocess.run([str(tool),"validate",str(optimized)],check=True)
    subprocess.run([str(tool), "component", "new", str(optimized), "-o", str(package / "plugin.wasm")], check=True)
    subprocess.run([str(tool), "validate", str(package / "plugin.wasm")], check=True)
    wit = subprocess.check_output([str(tool), "component", "wit", str(package / "plugin.wasm")], text=True)
    if "craft:plugin" not in wit or "@0.2.0" not in wit or "export craft:plugin/entry@0.2.0;" not in wit or "wasi:" in wit:
        raise RuntimeError("Component contract is not the supported non-WASI command plugin")
    data = (package / "plugin.wasm").read_bytes()
    if len(data) > 16 * 1024 * 1024:
        raise RuntimeError("Component exceeds the command-plugin installer size limit")
    if re.search(rb"(?<![A-Za-z0-9_])[A-Za-z]:[\\\\/]", data) or b"192.168." in data:
        raise RuntimeError("Component contains a local build path or local network address")
    shutil.copy2(manifest, package / "plugin.json")
    shutil.copy2(ROOT / "LICENSE", package / "LICENSE")
    (package / "README.txt").write_text(
        "Install this ZIP from SolidCraft Preferences > Plugins > Install plugin.\n"
        "Import an STL normally, select the mesh, then Surface > STL to STEP Import > convert.\n"
        "Supports certified prisms, cones, stepped blocks, countersunk holes and separated solids.\n"
        "Reconstruction is Native-only; the app's standard Doc STEP importer uses its existing backend.\n"
        "See https://github.com/crono2250/SolidCraft_STLtoSTEP_ImportPlugin for limitations.\n")
    shutil.copy2(ROOT / "NOTICE", package / "NOTICE")
    write_notices(package)
    sums = []
    for path in sorted(package.iterdir()):
        sums.append(hashlib.sha256(path.read_bytes()).hexdigest() + "  " + path.name)
    (package / "SHA256SUMS.txt").write_text("\n".join(sums) + "\n")
    version = json.loads(manifest.read_text())["version"]
    archive = output_dir / ("stl-to-step-import-" + version + ".zip")
    with zipfile.ZipFile(archive, "x", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as output:
        for path in sorted(package.iterdir()):
            info = zipfile.ZipInfo(path.name, date_time=(2026,1,1,0,0,0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            output.writestr(info, path.read_bytes())
    print(archive)
    print("SHA256", hashlib.sha256(archive.read_bytes()).hexdigest())

if __name__ == "__main__":
    main()
