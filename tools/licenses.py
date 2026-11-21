"""Redistribution notices from the exact locked package graph, not a generated source list."""
from pathlib import Path
import json, os, re, subprocess
ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"MIT","MIT-0","Apache-2.0","BSD-2-Clause","BSD-3-Clause","Zlib","ISC","Unicode-3.0","Unicode-DFS-2016","CC0-1.0","Unlicense","LLVM-exception"}

def write_notices(package):
    cargo = os.environ.get("CARGO", "cargo")
    meta=json.loads(subprocess.check_output([cargo,"metadata","--locked","--offline","--format-version","1",
                                            "--filter-platform","wasm32-unknown-unknown"],cwd=ROOT))
    sections=[]
    for p in sorted(meta["packages"], key=lambda p:(p["name"],p["version"])):
        license=p.get("license") or ""
        tokens=set(re.findall(r"[A-Za-z0-9.-]+",license))-{"OR","AND","WITH"}
        if not tokens or not tokens <= ALLOWED:
            raise RuntimeError("Unapproved dependency license: "+p["name"]+" "+license)
        home=Path(p["manifest_path"]).parent
        candidates=[]
        for pattern in ("LICENSE*","LICENCE*","COPYING*","NOTICE*"):
            candidates.extend(f for f in home.glob(pattern) if f.is_file())
        if p.get("license_file"):
            candidates.append(home/p["license_file"])
        if not candidates:
            if (ROOT/"vendor/sdk/solidcore") in home.parents:
                candidates=[ROOT/"vendor/sdk/solidcore/LICENSE",ROOT/"vendor/sdk/solidcore/NOTICE"]
            elif ROOT in home.parents:
                candidates=[ROOT/"LICENSE",ROOT/"NOTICE"]
        if not candidates:
            raise RuntimeError("Missing redistribution notice for "+p["name"])
        text="\n".join(f.read_text(encoding="utf-8") for f in sorted(set(candidates)))
        sections.append(p["name"]+" "+p["version"]+"\nLicense: "+license+"\n"+text)
    (package/"THIRD_PARTY_LICENSES.txt").write_text("\n\n".join(sections)+"\n",encoding="utf-8")
    rustc=os.environ.get("RUSTC","rustc")
    sysroot=Path(subprocess.check_output([rustc,"--print","sysroot"],text=True).strip())
    notice=sysroot/"share/doc/rust/COPYRIGHT-library.html"
    if not notice.is_file():
        raise RuntimeError("Rust standard-library redistribution notices are required")
    (package/"RUST-LIBRARY-COPYRIGHT.html").write_bytes(notice.read_bytes())
