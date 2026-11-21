#!/usr/bin/env python3
"""Materialize an immutable Native-only SDK; never edit the installed SolidCraft app."""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, os, shutil, subprocess, tarfile, tempfile, urllib.request

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / "vendor/sdk"

def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()

def tree(path):
    return {str(p.relative_to(path)).replace("\\", "/"): digest(p)
            for p in sorted(path.rglob("*")) if p.is_file()}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--archive", type=Path)
    args = parser.parse_args()
    lock = json.loads((ROOT / "sdk-lock.json").read_text())
    if digest(ROOT / "native/fixes.txt") != lock["native_fixes_sha256"]:
        raise RuntimeError("Native fix selection differs from sdk-lock.json")
    if digest(ROOT / "native/sdk-Cargo.lock") != lock["native_cargo_lock_sha256"]:
        raise RuntimeError("Native SDK dependency lock differs from sdk-lock.json")
    patch = ROOT / lock["native_patch"]
    if digest(patch) != lock["native_patch_sha256"]:
        raise RuntimeError("Native extension hash does not match sdk-lock.json")
    overlay_lock = ROOT / "native/overlay-lock.json"
    if digest(overlay_lock) != lock["native_overlay_lock_sha256"]:
        raise RuntimeError("Native module manifest differs from sdk-lock.json")
    overlay = json.loads(overlay_lock.read_text())
    if tree(ROOT / "native/overlay") != {item["path"]: item["sha256"] for item in overlay}:
        raise RuntimeError("Native module source differs from its manifest")
    if DEST.exists():
        receipt = DEST / ".sdk-receipt.json"
        if not receipt.exists():
            raise RuntimeError("SDK has no preparation receipt; preserve it before a fresh preparation")
        saved = json.loads(receipt.read_text())
        actual = tree(DEST)
        actual.pop(".sdk-receipt.json", None)
        if saved["lock_sha256"] != digest(ROOT / "sdk-lock.json") or saved["files"] != actual:
            raise RuntimeError("Prepared SDK changed; existing sources retained")
        print("Verified prepared Native SDK", lock["revision"], len(actual), "files")
        return
    archive = args.archive or ROOT / ".cache" / ("sdk-" + lock["revision"] + ".tar.gz")
    archive.parent.mkdir(parents=True, exist_ok=True)
    if not archive.exists():
        partial = archive.with_suffix(archive.suffix + ".partial")
        if partial.exists():
            raise RuntimeError("Partial SDK download retained; inspect before retrying")
        request = urllib.request.Request(lock["archive"], headers={"User-Agent": "STLtoSTEP-plugin-build"})
        with urllib.request.urlopen(request, timeout=60) as response, partial.open("xb") as output:
            shutil.copyfileobj(response, output)
        if digest(partial) != lock["sha256"]:
            raise RuntimeError("SDK archive hash mismatch; failed download retained")
        partial.rename(archive)
    if digest(archive) != lock["sha256"]:
        raise RuntimeError("SDK archive hash mismatch")
    parent = ROOT / "vendor"
    parent.mkdir(exist_ok=True)
    staging = Path(tempfile.mkdtemp(prefix=".sdk-", dir=parent))
    prefix = "solidcraft-" + lock["revision"]
    with tarfile.open(archive, "r:gz") as source:
        for member in source:
            parts = PurePosixPath(member.name).parts
            if not parts or parts[0] != prefix or len(parts) < 2 or parts[1] != "solidcore":
                continue
            relative = PurePosixPath(*parts[1:])
            if relative.is_absolute() or any(p in ("", ".", "..") or ":" in p for p in relative.parts):
                raise RuntimeError("Unsafe SDK archive path")
            if member.issym() or member.islnk():
                # No build input is allowed to be a link. Such entries are never followed.
                continue
            if not member.isfile():
                continue
            output = staging.joinpath(*relative.parts)
            output.parent.mkdir(parents=True, exist_ok=True)
            stream = source.extractfile(member)
            if stream is None:
                raise RuntimeError("Unreadable SDK entry")
            with stream, output.open("xb") as dest:
                shutil.copyfileobj(stream, dest)
    subprocess.run(["git", "apply", "--whitespace=nowarn",
                    "--directory=" + staging.relative_to(ROOT).as_posix(), str(patch)],
                   cwd=ROOT, check=True)
    for item in overlay:
        relative = PurePosixPath(item["path"])
        if not relative.parts or relative.parts[0] != "solidcore" or ".." in relative.parts:
            raise RuntimeError("Invalid Native module target")
        destination = staging.joinpath(*relative.parts)
        if destination.exists():
            raise RuntimeError("Native module would replace upstream source: " + item["path"])
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT / "native/overlay" / item["path"], destination)
    for item in overlay:
        if digest(staging / item["path"]) != item["sha256"]:
            raise RuntimeError("Native module changed during source preparation")
    if digest(patch) != lock["native_patch_sha256"] or json.loads((ROOT / "sdk-lock.json").read_text()) != lock:
        raise RuntimeError("SDK inputs changed during source preparation")
    shutil.copy2(ROOT / "native/sdk-Cargo.lock", staging / "solidcore/Cargo.lock")
    receipt = {"revision": lock["revision"], "lock_sha256": digest(ROOT / "sdk-lock.json"),
               "archive_sha256": digest(archive), "files": tree(staging)}
    (staging / ".sdk-receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    staging.rename(DEST)
    print("Prepared verified Native SDK", lock["revision"], len(receipt["files"]), "files")

if __name__ == "__main__":
    main()
