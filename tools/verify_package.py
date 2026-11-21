#!/usr/bin/env python3
"""Check the exact downloaded Actions ZIP, not a source tree or a nested ZIP."""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, zipfile
def verify(path):
    with zipfile.ZipFile(path) as archive:
        entries = archive.infolist()
        names = {e.filename for e in entries}
        expected = {"plugin.json", "plugin.wasm", "LICENSE", "NOTICE", "README.txt", "THIRD_PARTY_LICENSES.txt", "RUST-LIBRARY-COPYRIGHT.html", "SHA256SUMS.txt"}
        if names != expected or len(entries) != len(expected):
            raise RuntimeError("Archive must have the installable package at its root")
        if path.stat().st_size > 64*1024*1024 or sum(e.file_size for e in entries) > 64*1024*1024:
            raise RuntimeError("Archive exceeds installer size limits")
        if any(e.file_size > 16*1024*1024 or PurePosixPath(e.filename).is_absolute() for e in entries):
            raise RuntimeError("Archive exceeds package limits")
        if archive.testzip() is not None:
            raise RuntimeError("Corrupt package")
        manifest = json.loads(archive.read("plugin.json"))
        if manifest["id"] != "stl-to-step-import" or manifest["runtime"]["module"] != "plugin.wasm":
            raise RuntimeError("Wrong package identity")
        covered=set()
        for line in archive.read("SHA256SUMS.txt").decode().splitlines():
            expected_hash, name = line.split("  ", 1)
            if name in covered or name not in expected - {"SHA256SUMS.txt"} or hashlib.sha256(archive.read(name)).hexdigest() != expected_hash:
                raise RuntimeError("Package content hash mismatch: " + name)
            covered.add(name)
        if covered != expected - {"SHA256SUMS.txt"}:
            raise RuntimeError("Incomplete content checksum inventory")
        if archive.read("plugin.wasm")[:8] != b"\x00asm\x0d\x00\x01\x00":
            raise RuntimeError("A WebAssembly component is required, not a core module")
    print("Verified installable package", path)
if __name__ == "__main__":
    p=argparse.ArgumentParser();p.add_argument("archive",type=Path);verify(p.parse_args().archive)
