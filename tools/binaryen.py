"""Pinned, task-local Wasm size optimizer. No global installation or fast-math."""
from pathlib import Path
import hashlib,json,platform,shutil,tarfile,urllib.request
ROOT=Path(__file__).resolve().parents[1]
def get():
    lock=json.loads((ROOT/"sdk-lock.json").read_text())["binaryen"]
    system=platform.system()
    if platform.machine().lower() not in ("amd64","x86_64") or system not in ("Windows","Linux"):
        raise RuntimeError("Binaryen bootstrap supports x86-64 Windows/Linux")
    suffix="windows" if system=="Windows" else "linux"
    name="binaryen-version_"+lock["version"]+"-x86_64-"+suffix+".tar.gz"
    cache=ROOT/".cache/tools"
    cache.mkdir(parents=True,exist_ok=True)
    archive=cache/name
    if not archive.exists():
        partial=archive.with_suffix(".partial")
        with urllib.request.urlopen("https://github.com/WebAssembly/binaryen/releases/download/version_"+lock["version"]+"/"+name,timeout=60) as response,partial.open("xb") as output:
            shutil.copyfileobj(response,output)
        if hashlib.file_digest(partial.open("rb"),"sha256").hexdigest()!=lock[suffix+"_sha256"]:
            raise RuntimeError("Binaryen download hash mismatch; partial retained")
        partial.rename(archive)
    if hashlib.file_digest(archive.open("rb"),"sha256").hexdigest()!=lock[suffix+"_sha256"]:
        raise RuntimeError("Binaryen archive hash mismatch")
    binary="wasm-opt.exe" if system=="Windows" else "wasm-opt"
    with tarfile.open(archive) as source:
        matches=[m for m in source if m.isfile() and Path(m.name).name==binary]
        if len(matches)!=1: raise RuntimeError("Unexpected Binaryen archive")
        stream=source.extractfile(matches[0])
        if stream is None: raise RuntimeError("Unreadable Binaryen executable")
        with stream: data=stream.read()
    exe=cache/binary
    exe.write_bytes(data)
    if system!="Windows": exe.chmod(0o755)
    return exe
