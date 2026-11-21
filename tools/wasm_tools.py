#!/usr/bin/env python3
"""Download the exact published wasm-tools binary recorded in sdk-lock.json."""
from pathlib import Path, PurePosixPath
import hashlib, json, os, platform, shutil, tarfile, urllib.request, zipfile
ROOT = Path(__file__).resolve().parents[1]

def get():
    lock = json.loads((ROOT / "sdk-lock.json").read_text())["wasm_tools"]
    system = platform.system()
    if platform.machine().lower() not in ("amd64", "x86_64"):
        raise RuntimeError("Build tool bootstrap supports x86-64 Windows/Linux")
    windows = system == "Windows"
    if not windows and system != "Linux":
        raise RuntimeError("Build on Windows or Linux; the plugin itself is platform independent")
    suffix = "x86_64-windows.zip" if windows else "x86_64-linux.tar.gz"
    name = "wasm-tools-" + lock["version"] + "-" + suffix
    cache = ROOT / ".cache/tools"
    cache.mkdir(parents=True, exist_ok=True)
    archive = cache / name
    exe = cache / ("wasm-tools.exe" if windows else "wasm-tools")
    expected = lock["windows_sha256" if windows else "linux_sha256"]
    if not archive.exists():
        url = "https://github.com/bytecodealliance/wasm-tools/releases/download/v" + lock["version"] + "/" + name
        with urllib.request.urlopen(url, timeout=60) as response, archive.open("xb") as output:
            shutil.copyfileobj(response, output)
    with archive.open("rb") as stream:
        if hashlib.file_digest(stream, "sha256").hexdigest() != expected:
            raise RuntimeError("wasm-tools archive hash mismatch")
    if windows:
        with zipfile.ZipFile(archive) as source:
            matches = [m for m in source.infolist() if PurePosixPath(m.filename).name == "wasm-tools.exe"]
            if len(matches) != 1:
                raise RuntimeError("Unexpected wasm-tools archive")
            data = source.read(matches[0])
    else:
        with tarfile.open(archive) as source:
            matches = [m for m in source.getmembers() if m.isfile() and PurePosixPath(m.name).name == "wasm-tools"]
            if len(matches) != 1:
                raise RuntimeError("Unexpected wasm-tools archive")
            stream = source.extractfile(matches[0])
            if stream is None:
                raise RuntimeError("Unreadable wasm-tools binary")
            with stream:
                data = stream.read()
    # Recreate from the hash-checked archive instead of trusting a cached executable.
    exe.write_bytes(data)
    if not windows:
        exe.chmod(0o755)
    return exe

if __name__ == "__main__":
    print(get())
