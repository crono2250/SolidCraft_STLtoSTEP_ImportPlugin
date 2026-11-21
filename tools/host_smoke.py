#!/usr/bin/env python3
"""Use an official portable CLI and an isolated plugin/data directory. Installs no application."""
from pathlib import Path
import argparse, hashlib, json, math, os, platform, shutil, subprocess, tarfile, urllib.request, zipfile

from perpendicular_fixture import geometry as perpendicular_bore_cells

ROOT = Path(__file__).resolve().parents[1]
VERSION = "0.45.0"
HOSTS = {
    "Windows": ("solidcraft-windows-x64-portable.zip", "747bb16c65032ed2b2050b83d12c7d97dff84d480de29c1455afaf667ab753d1", "solidcraft-cli.exe"),
    "Linux": ("solidcraft-0.45.0-linux-x86_64.tar.gz", "78170f546e1442db9d14637a4b8a8e6b39b543009d3d3d857cbd65f09afa37f8", "solidcraft-cli"),
}

def sha(path):
    with path.open("rb") as f:
        return hashlib.file_digest(f, "sha256").hexdigest()

def host_cli():
    if os.environ.get("SOLIDCRAFT_CLI"):
        cli = Path(os.environ["SOLIDCRAFT_CLI"]).resolve()
        expected = os.environ.get("SOLIDCRAFT_CLI_SHA256")
        if not expected or sha(cli) != expected:
            raise RuntimeError("An explicit CLI must also have its exact SHA-256")
        return cli
    system = platform.system()
    name, expected, binary = HOSTS[system]
    cache = ROOT / ".cache/host"
    cache.mkdir(parents=True, exist_ok=True)
    archive = cache / name
    if not archive.exists():
        with urllib.request.urlopen("https://github.com/tangency-labs/solidcraft/releases/download/v" + VERSION + "/" + name,
                                    timeout=60) as response, archive.open("xb") as output:
            shutil.copyfileobj(response, output)
    if sha(archive) != expected:
        raise RuntimeError("Official host archive hash mismatch")
    if system == "Windows":
        with zipfile.ZipFile(archive) as z:
            matches = [m for m in z.infolist() if Path(m.filename).name == binary]
            if len(matches) != 1:
                raise RuntimeError("Unexpected host archive")
            data = z.read(matches[0])
    else:
        with tarfile.open(archive) as z:
            matches = [m for m in z.getmembers() if m.isfile() and Path(m.name).name == binary]
            if len(matches) != 1:
                raise RuntimeError("Unexpected host archive")
            stream = z.extractfile(matches[0])
            if stream is None:
                raise RuntimeError("Unreadable host binary")
            with stream:
                data = stream.read()
    cli = cache / binary
    cli.write_bytes(data)
    if system != "Windows":
        cli.chmod(0o755)
    return cli

def synthetic_box(path):
    # Original procedural public fixture: 10 x 20 x 30 mm, outward triangles.
    p = [(0,0,0),(10,0,0),(10,20,0),(0,20,0),(0,0,30),(10,0,30),(10,20,30),(0,20,30)]
    triangles = [(0,3,2),(0,2,1),(4,5,6),(4,6,7),(0,1,5),(0,5,4),(3,7,6),(3,6,2),(0,4,7),(0,7,3),(1,2,6),(1,6,5)]
    lines = ["solid synthetic_box"]
    for t in triangles:
        lines.extend(["facet normal 0 0 0", "outer loop"])
        lines.extend("vertex " + " ".join(map(str,p[i])) for i in t)
        lines.extend(["endloop","endfacet"])
    path.write_text("\n".join(lines + ["endsolid synthetic_box"]) + "\n")

def synthetic_mesh(path, points, triangles, label):
    lines=["solid "+label]
    for triangle in triangles:
        lines.extend(["facet normal 0 0 0","outer loop"])
        lines.extend("vertex "+" ".join(map(str,points[i])) for i in triangle)
        lines.extend(["endloop","endfacet"])
    path.write_text("\n".join(lines+["endsolid "+label])+"\n")

def synthetic_tube(path):
    n=128
    points=[]
    for z,radius in [(0.,10.),(0.,3.),(3.,10.),(3.,3.)]:
        points.extend((radius*math.cos(2*math.pi*i/n),radius*math.sin(2*math.pi*i/n),z) for i in range(n))
    triangles=[]
    for i in range(n):
        j=(i+1)%n
        a,b,c,d=i,j,n+i,n+j
        e,f,g,h=2*n+i,2*n+j,3*n+i,3*n+j
        triangles.extend([(a,c,d),(a,d,b),(e,f,h),(e,h,g),(a,b,f),(a,f,e),(c,g,h),(c,h,d)])
    synthetic_mesh(path,points,triangles,"procedural_tube")

def synthetic_axial_bore(path, rings):
    """An independently generated axisymmetric through bore."""
    angles = sorted({math.tau * i / 64 for i in range(64)} |
                    {math.atan2(y, x) % math.tau
                     for x in (-8., 8.) for y in (-6., 6.)})
    n = len(angles)
    points = []
    for z in (0., 5.):
        for angle in angles:
            x, y = math.cos(angle), math.sin(angle)
            radius = min(8. / abs(x) if x else math.inf,
                         6. / abs(y) if y else math.inf)
            points.append((radius * x, radius * y, z))
    for z, r in rings:
        for angle in angles:
            points.append((r * math.cos(angle), r * math.sin(angle), z))
    last = (1 + len(rings)) * n
    triangles = []
    for a in range(n):
        b = (a + 1) % n
        triangles.extend([(a, b, n+b), (a, n+b, n+a),
                          (a, 2*n+a, 2*n+b), (a, 2*n+b, b),
                          (n+a, n+b, last+b), (n+a, last+b, last+a)])
        for offset in range(2*n, last, n):
            triangles.extend([(offset+a, offset+n+a, offset+n+b),
                              (offset+a, offset+n+b, offset+b)])
    synthetic_mesh(path, points, triangles, "procedural countersunk plate")


def synthetic_radial(path, lower_radius, upper_radius, height):
    """Original public 64-sector geometry with outward STL winding."""
    n = 64
    points = []
    for z, radius in ((0., lower_radius), (height, upper_radius)):
        if radius:
            for i in range(n):
                a = math.tau * i / n
                points.append((radius * math.cos(a), radius * math.sin(a), z))
    triangles = []
    if lower_radius:
        points.extend([(0., 0., 0.), (0., 0., height)])
        for a in range(n):
            b = (a + 1) % n
            triangles.extend([(a, b, n + b), (a, n + b, n + a),
                              (2 * n, b, a), (2 * n + 1, n + a, n + b)])
    else:
        points.extend([(0., 0., 0.), (0., 0., height)])
        for a in range(n):
            b = (a + 1) % n
            triangles.extend([(n, b, a), (n + 1, a, b)])
    synthetic_mesh(path, points, triangles, "procedural radial solid")


def synthetic_stepped_block(path):
    points = []
    for z, x, y in ((0., 8., 6.), (2., 8., 6.), (2., 4., 2.), (5., 4., 2.)):
        points.extend([(sx * x, sy * y, z) for sx, sy in
                       ((-1., -1.), (1., -1.), (1., 1.), (-1., 1.))])
    triangles = [(0, 2, 1), (0, 3, 2), (12, 13, 14), (12, 14, 15)]
    for a in range(4):
        b = (a + 1) % 4
        for offset in (0, 4, 8):
            i, j = offset + a, offset + b
            triangles.extend([(i, j, j + 4), (i, j + 4, i + 4)])
    synthetic_mesh(path, points, triangles, "procedural stepped blank")


def check_stock_variants(out, installed, approval, run, command):
    def one(label, make, volume, planes, cones, cylinders=0):
        mesh = out / f"{label}-source.stl"
        source = out / f"{label}-source.sc"
        restored = out / f"{label}-restored.json"
        exported = out / f"{label}-restored.step"
        make(mesh)
        imported = run(f"{label}-source", [
            command("file.insert_mesh", path=str(mesh)),
            command("inspect.measure"),
        ], save=source)
        if imported[1]["body_count"] != 1:
            raise RuntimeError(f"{label} fixture does not have exactly one source body")
        original = imported[1]["bodies"][0]["name"]
        result = run(f"{label}-convert", [
            command("plugin.run", path=str(installed), approval=approval, entry="convert",
                    params={"bodies": [original], "tolerance": 0.05, "name": "Reconstructed"}),
            command("inspect.measure"),
            command("file.export", path=str(exported)),
            command("file.save_as", path=str(restored), format="json", cache=False, preview=False),
        ], model=source)
        measured = result[1]
        if measured["body_count"] != 1 or measured["bodies"][0]["name"] != "Reconstructed":
            raise RuntimeError(f"{label} did not atomically replace its active source")
        value = measured["bodies"][0]["volume_mm3"]
        if not math.isclose(value, volume, rel_tol=2e-5, abs_tol=1e-5):
            raise RuntimeError(f"{label} volume differs from its analytic formula: {value}")
        text = exported.read_text()
        if text.count("MANIFOLD_SOLID_BREP") != 1 or "FACETED_BREP" in text:
            raise RuntimeError(f"{label} is not exactly one solid STEP body")
        if (text.count("CONICAL_SURFACE") != cones or text.count("PLANE(") != planes
                or text.count("CYLINDRICAL_SURFACE") != cylinders):
            raise RuntimeError(f"{label} lost a designed plane or cone")
        if not any(f.get("type") == "mesh_import" for f in json.loads(restored.read_text())["features"]):
            raise RuntimeError(f"{label} lost its original mesh import")
        cold = run(f"{label}-cold", [command("inspect.measure")], model=restored)[0]
        if cold["body_count"] != 1 or not math.isclose(
                cold["bodies"][0]["volume_mm3"], volume, rel_tol=2e-5, abs_tol=1e-5):
            raise RuntimeError(f"{label} changed after a cache-free reopen")

    one("stepped", synthetic_stepped_block, 16. * 12. * 2. + 8. * 4. * 3., 11, 0)
    one("frustum", lambda path: synthetic_radial(path, 8., 4., 5.),
        math.pi * 5. * (64. + 32. + 16.) / 3., 2, 1)
    one("cone", lambda path: synthetic_radial(path, 0., 4., 5.),
        math.pi * 5. * 16. / 3., 1, 1)

    one("countersink", lambda path: synthetic_axial_bore(path, ((0., 2.), (3., 2.), (5., 4.))),
        960. - math.pi * (12. + 56. / 3.), 6, 1, 1)
    one("counterbore", lambda path: synthetic_axial_bore(path, ((0., 2.), (3., 2.), (3., 4.), (5., 4.))),
        960. - math.pi * (12. + 32.), 7, 0, 2)

    def perpendicular(path):
        geometry = perpendicular_bore_cells()
        points = sorted({p for cell in geometry for p in cell})
        indices = {p: i for i, p in enumerate(points)}
        synthetic_mesh(path, points, [[indices[p] for p in cell] for cell in geometry],
                       "procedural perpendicular bores")

    one("perpendicular", perpendicular, 20. ** 3 - 2. * math.pi * 1.25 ** 2 * 20., 6, 0, 2)


def check_disjoint(out, installed, approval, run, command):
    points = [(0,0,0),(2,0,0),(2,3,0),(0,3,0),(0,0,4),(2,0,4),(2,3,4),(0,3,4)]
    faces = [(0,3,2),(0,2,1),(4,5,6),(4,6,7),(0,1,5),(0,5,4),
             (3,7,6),(3,6,2),(0,4,7),(0,7,3),(1,2,6),(1,6,5)]
    mesh = out / "disjoint-source.stl"
    source = out / "disjoint-source.sc"
    output = out / "disjoint-restored.step"
    saved = out / "disjoint-restored.json"
    synthetic_mesh(mesh, points + [(x+8,y,z) for x,y,z in points],
                   faces + [tuple(i + len(points) for i in face) for face in faces],
                   "procedural separated boxes")
    imported = run("disjoint-import", [command("file.insert_mesh", path=str(mesh)),
                                       command("inspect.measure")], save=source)[1]
    if imported["body_count"] != 1:
        raise RuntimeError("The disconnected STL must enter the command as one source mesh")
    original = imported["bodies"][0]["name"]
    rows = run("disjoint-convert", [
        command("plugin.run", path=str(installed), approval=approval, entry="convert",
                params={"bodies":[original], "tolerance":0.05, "name":"Separate parts"}),
        command("inspect.measure"),
        command("file.export", path=str(output)),
        command("edit.undo"), command("inspect.measure"),
        command("edit.redo"), command("inspect.measure"),
        command("file.save_as", path=str(saved), format="json", cache=False, preview=False),
    ], model=source)
    def proves_two(measurement):
        return (measurement["body_count"] == 2
                and {b["name"] for b in measurement["bodies"]} == {"Separate parts", "Separate parts (2)"}
                and all(math.isclose(b["volume_mm3"], 24., rel_tol=1e-8) for b in measurement["bodies"]))
    if not proves_two(rows[1]) or not proves_two(rows[6]):
        raise RuntimeError("The two analytic solids were not adopted in a single command")
    if rows[4]["body_count"] != 1 or rows[4]["bodies"][0]["name"] != original:
        raise RuntimeError("One undo did not restore the original disconnected mesh")
    if output.read_text().count("MANIFOLD_SOLID_BREP") != 2:
        raise RuntimeError("STEP did not contain two separately reconstructed solids")
    if not proves_two(run("disjoint-cold", [command("inspect.measure")], model=saved)[0]):
        raise RuntimeError("Independent solids changed after cache-free reopening")


def official_failure_cases(out, installed, invoke, run, command, source_body):
    # Use the existing host runner: expected failure and model assertions share one live session.
    suite=out/"failure-cases/stl-to-step-import"
    shutil.copytree(installed,suite)
    tests=suite/"tests"
    tests.mkdir()
    shutil.copy2(out/"source.sc",tests/"source.sc")
    cases={
        "invalid-input":{"entry":"convert","design":"source.sc",
            "params":{"bodies":[source_body],"all_surfaces":True},
            "expect":{"error":"invalid_input","model":{"body_count":1,"total":{"volume_mm3":6000.}}}},
    }
    solid=run("solid-input",[command("solid.box",length="10 mm",width="20 mm",height="30 mm",name="ExistingSolid"),
                              command("inspect.measure")],save=out/"solid.sc")
    solid_name=solid[1]["bodies"][0]["name"]
    shutil.copy2(out/"solid.sc",tests/"solid.sc")
    cases["display-mesh"]={"entry":"convert","design":"solid.sc",
        "params":{"bodies":[solid_name],"name":"Unused"},
        "expect":{"error":"unsupported","model":{"body_count":1,"total":{"volume_mm3":6000.}}}}
    tetra=out/"procedural-tetra.stl"
    synthetic_mesh(tetra,[(0.,0.,0.),(2.,0.,0.),(0.,3.,0.),(0.,0.,4.)],
                   [(0,2,1),(0,1,3),(0,3,2),(1,2,3)],"procedural_tetra")
    tetra_source=run("tetra-input",[command("file.insert_mesh",path=str(tetra)),command("inspect.measure")],
                     save=out/"tetra.sc")
    tetra_name=tetra_source[1]["bodies"][0]["name"]
    shutil.copy2(out/"tetra.sc",tests/"tetra.sc")
    cases["unsupported-shape"]={"entry":"convert","design":"tetra.sc",
        "params":{"bodies":[tetra_name],"name":"Unused"},
        "expect":{"error":"unsupported","model":{"body_count":1,"total":{"volume_mm3":4.}}}}
    for name,case in cases.items():
        (tests/(name+".json")).write_text(json.dumps(case,indent=2))
    invoke("expected-failures",["plugin","test",suite,"--json","--require-cases","--out",out/"failure-results"])
    low=out/"low-fuel/stl-to-step-import"
    shutil.copytree(installed,low)
    manifest=json.loads((low/"plugin.json").read_text())
    manifest["runtime"]["limits"]["fuel"]=1
    (low/"plugin.json").write_text(json.dumps(manifest,indent=2))
    inventory=low/"SHA256SUMS.txt"
    inventory.write_text("".join(sha(low/name)+"  "+name+"\n" for name in sorted(p.name for p in low.iterdir() if p.is_file() and p.name!="SHA256SUMS.txt")))
    (low/"tests").mkdir()
    shutil.copy2(out/"source.sc",low/"tests/source.sc")
    (low/"tests/fuel.json").write_text(json.dumps({
        "entry":"convert","design":"source.sc","params":{"bodies":[source_body]},
        "expect":{"error":"exhausted","model":{"body_count":1,"total":{"volume_mm3":6000.}}}
    },indent=2))
    invoke("fuel-rollback",["plugin","test",low,"--json","--require-cases","--out",out/"fuel-results"])

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("package",type=Path)
    parser.add_argument("--out",type=Path,default=ROOT/".cache/host-validation")
    args=parser.parse_args()
    out=args.out.resolve()
    if out.exists():
        raise RuntimeError("Validation output already exists; retain prior results and choose a fresh --out")
    out.mkdir(parents=True)
    package=args.package.resolve()
    cli=host_cli()
    env=dict(os.environ)
    env.update(LOCALAPPDATA=str(out/"data"), XDG_DATA_HOME=str(out/"data"),
               SOLIDCRAFT_RECOVERY_DIR=str(out/"recovery"), RUST_TEST_THREADS="2", RAYON_NUM_THREADS="2")
    plugins=out/"plugins"
    def invoke(label, argv):
        with (out/(label+".log")).open("wb") as log:
            result=subprocess.run([str(cli),"--plugins-dir",str(plugins),"--keep-plugin-approvals"]+list(map(str,argv)),
                                  cwd=out,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=180)
        if result.returncode:
            raise RuntimeError(label+" failed; original log retained, exit="+str(result.returncode))
    def command(command_name,**params):
        return {"command":command_name,"params":params}
    def run(label,commands,model=None,save=None):
        script=out/(label+".json")
        result=out/(label+"-results.json")
        script.write_text(json.dumps(commands,indent=2))
        argv=["run",script,"--results","--json-out",result]
        if model: argv+=["--in",model]
        if save: argv+=["--save",save]
        invoke(label,argv)
        raw=json.loads(result.read_text(encoding="utf-8-sig"))
        rows=raw.get("results",raw) if isinstance(raw,dict) else raw
        return [r["result"] if isinstance(r,dict) and "result" in r and "command" in r else r for r in rows]
    invoke("package-check",["plugin","check",package,"--json"])
    description=run("install-review",[command("plugin.install",path=str(package),dry_run=True)])[0]
    run("install",[command("plugin.install",path=str(package),approval=description["approval"],
                           archive=description["archive"],approve={})])
    installed=plugins/"stl-to-step-import"
    mesh=out/"synthetic-box.stl"
    synthetic_box(mesh)
    before=run("source",[command("file.insert_mesh",path=str(mesh)),command("inspect.measure")],
               save=out/"source.sc")
    if before[1]["body_count"]!=1:
        raise RuntimeError("Procedural source was not imported as one body")
    source_body=before[1]["bodies"][0]["name"]
    step=out/"restored.step"
    saved=out/"restored.json"
    converted=run("convert",[
        command("plugin.run",path=str(installed),approval=description["approval"],entry="convert",
                params={"bodies":[source_body],"tolerance":0.05,"name":"Restored"}),
        command("inspect.measure",bodies=["Restored"]),
        command("edit.undo"),command("inspect.measure"),
        command("edit.redo"),command("inspect.measure",bodies=["Restored"]),
        command("file.export",path=str(step)),
        command("file.save_as",path=str(saved),format="json",cache=False,preview=False),
    ],model=out/"source.sc",save=out/"restored.sc")
    def check_volume(measurement):
        bodies=measurement["bodies"]
        if len(bodies)!=1 or not math.isclose(bodies[0]["volume_mm3"],6000.,rel_tol=1e-8,abs_tol=1e-6):
            raise RuntimeError("Restored volume differs from the procedural source")
    check_volume(converted[1]);check_volume(converted[5])
    if converted[3]["body_count"]!=1 or converted[3]["bodies"][0]["name"]!=source_body:
        raise RuntimeError("Single undo did not restore the source mesh")
    text=step.read_text()
    if "MANIFOLD_SOLID_BREP" not in text or "FACETED_BREP" in text:
        raise RuntimeError("Export is not the analytic solid STEP")
    model=json.loads(saved.read_text())
    if not any(f.get("type")=="mesh_import" for f in model["features"]):
        raise RuntimeError("Original mesh import was not kept in history")
    faces=run("faces",[command("model.faces",body="Restored")],model=out/"restored.sc")[0]["faces"]
    planar=next(f for f in faces if f.get("plane_normal"))
    attached=out/"attached.sc"
    sketch_commands=[]
    if before[0].get("component") is not None:
        sketch_commands.append(command("component.activate",component=before[0]["component"]))
    run("sketch",sketch_commands+[
        command("sketch.create",plane={"body":"Restored","face":planar["point"],"index":planar["index"]},name="Side sketch"),
        command("sketch.finish"),
    ],model=out/"restored.sc",save=attached)
    # A fresh process and no plugin directory: the saved ordinary features are self-contained.
    plugins=out/"without-plugins"
    invoke("cold-reopen",["eval",saved,"--json-out",out/"cold-measure.json"])
    check_volume(json.loads((out/"cold-measure.json").read_text(encoding="utf-8-sig")))
    invoke("sketch-reopen",["eval",attached,"--json-out",out/"sketch-measure.json"])

    plugins=out/"plugins"
    tube_mesh=out/"procedural-tube.stl"
    synthetic_tube(tube_mesh)
    tube_before=run("tube-source",[command("file.insert_mesh",path=str(tube_mesh)),command("inspect.measure")],
                    save=out/"tube-source.sc")
    tube_name=tube_before[1]["bodies"][0]["name"]
    tube_result=run("tube-convert",[
        command("plugin.run",path=str(installed),approval=description["approval"],entry="convert",
                params={"bodies":[tube_name],"tolerance":0.05,"name":"TubeSolid"}),
        command("inspect.measure",bodies=["TubeSolid"]),
        command("file.export",path=str(out/"tube.step")),
        command("file.save_as",path=str(out/"tube.json"),format="json",cache=False,preview=False)
    ],model=out/"tube-source.sc")
    actual=tube_result[1]["bodies"][0]["volume_mm3"]
    expected=math.pi*(10.*10.-3.*3.)*3.
    if not math.isclose(actual,expected,rel_tol=1e-8,abs_tol=1e-6):
        raise RuntimeError("Reconstruction did not preserve the designed through hole")
    if "CYLINDRICAL_SURFACE" not in (out/"tube.step").read_text():
        raise RuntimeError("Tube STEP lost its analytic cylinder surfaces")
    plugins=out/"without-plugins"
    invoke("tube-reopen",["eval",out/"tube.json","--json-out",out/"tube-cold.json"])
    cold=json.loads((out/"tube-cold.json").read_text(encoding="utf-8-sig"))
    if not math.isclose(cold["bodies"][0]["volume_mm3"],expected,rel_tol=1e-8,abs_tol=1e-6):
        raise RuntimeError("Tube changed on cache-free reopening")
    plugins=out/"plugins"
    check_stock_variants(out, installed, description["approval"], run, command)
    check_disjoint(out, installed, description["approval"], run, command)
    official_failure_cases(out,installed,invoke,run,command,source_body)

    (out/"receipt.json").write_text(json.dumps({
        "status":"passed","compatibility_target":VERSION,"host_sha256":sha(cli),"package_sha256":sha(package),
        "component_sha256":sha(installed/"plugin.wasm"),
        "checks":["installable archive","one transaction undo/redo","analytic STEP","original mesh history",
                  "planar face sketch","cache-free reopening without plugin","analytic through hole","typed failure and fuel rollback"],
        "fixture":"procedural box, annular prism, stepped blank, circular frustum, pointed cone, countersunk plate, stepped counterbore, perpendicular stock bores, separated boxes and tetrahedron",
    },indent=2)+"\n")
    print("Passed real-host package/install/convert/STEP/undo/sketch/reopen")

if __name__=="__main__":
    main()
