#!/usr/bin/env python3
"""Portable verification of the real PSD proof and optional vowel benchmark.

Requires an already prepared pinned toolchain and Mathlib checkout. Downloads,
global installs, publication and modification of dependency sources are outside
this command. All generated files go to the new, external --output directory.
"""
from pathlib import Path
from hashlib import sha256
from datetime import datetime, timezone
import argparse
import json
import importlib.metadata
import os
import platform
import re
import subprocess
import sys
import time
import tomllib

ROOT = Path(__file__).resolve().parent


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", type=Path, required=True,
                        help="Existing Lean 4.34.0 directory containing bin/lean, lake and leanchecker")
    parser.add_argument("--mathlib-root", type=Path, required=True,
                        help="Existing pinned Mathlib checkout with its dependencies and compiled imports")
    parser.add_argument("--output", type=Path, required=True,
                        help="New directory outside this repository; must not already exist")
    parser.add_argument("--benchmark-archive", type=Path,
                        help="Optional externally acquired pinned H95 ZIP; never extracted or bundled")
    parser.add_argument("--figures", action="store_true",
                        help="Also export all five figure formats from the reviewed aggregate results")
    parser.add_argument("--anonymous-figures", action="store_true",
                        help="Use neutral figure author metadata; requires --figures")
    args = parser.parse_args()
    require(not args.anonymous_figures or args.figures, "--anonymous-figures requires --figures")
    require(sys.version_info >= (3, 11), "Python 3.11 or newer is required")
    require(__debug__, "Run without -O: the exact rational checker uses assertions")
    output = args.output.resolve()
    require(not output.is_relative_to(ROOT), "Verification output must be outside the repository")
    require(not output.exists(), "The output directory already exists; choose a fresh path")
    mathlib = args.mathlib_root.resolve(strict=True)
    toolchain = args.toolchain.resolve(strict=True)
    require(not mathlib.is_relative_to(ROOT), "Use an external dependency checkout")
    lean, lake, checker = [str(toolchain / "bin" / name) for name in ("lean", "lake", "leanchecker")]
    require(all(Path(x).is_file() for x in (lean, lake, checker)), "Missing toolchain executable")
    output.mkdir(parents=True, exist_ok=False)
    settings = json.loads((ROOT / "environment.json").read_text())
    theorem_map = json.loads((ROOT / "theorem_map.json").read_text())
    modules = theorem_map["modules"]
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env["PATH"] = str(toolchain / "bin") + os.pathsep + env.get("PATH", "")
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    env["MATHLIB_CACHE_DIR"] = str(output / "cache" / "mathlib")
    env["LAKE_CACHE_DIR"] = str(output / "cache" / "lake")
    env["MPLCONFIGDIR"] = str(output / "cache" / "matplotlib")
    runs = []
    artifacts = {}
    benchmark = {"status": "NOT_RUN_NO_BENCHMARK_ARCHIVE",
                 "reason": "Pass --benchmark-archive to reproduce all nine cohorts and 399 speaker omissions."}
    figures = {"status": "NOT_RUN_NO_FIGURES_OPTION"}

    def run(name, command, cwd=mathlib, run_env=env):
        started = time.monotonic()
        stdout, stderr = output / f"{name}.stdout.log", output / f"{name}.stderr.log"
        with stdout.open("w") as out, stderr.open("w") as err:
            process = subprocess.run(command, cwd=cwd, env=run_env, stdout=out, stderr=err)
        runs.append({"name": name, "command": command, "exit_code": process.returncode,
            "elapsed_seconds": time.monotonic()-started,
            "stdout_sha256": digest(stdout), "stderr_sha256": digest(stderr)})
        (output / "commands.json").write_text(json.dumps(runs, indent=2)+"\n")
        require(process.returncode == 0, f"{name} failed: inspect its logs in {output}")
        return stdout.read_text()

    try:
        manifest = json.loads((ROOT / "repository_manifest.json").read_text())
        inventory = {f["path"]: f for f in manifest["files"]}
        actual = []
        for directory, dirs, files in os.walk(ROOT, followlinks=False):
            dirs[:] = [d for d in dirs if not (Path(directory) == ROOT and d == ".git")]
            for name in dirs + files:
                require(not (Path(directory) / name).is_symlink(), "Symlink in repository snapshot")
            for name in files:
                p = Path(directory) / name
                actual.append(p.relative_to(ROOT).as_posix())
        require(set(actual) == set(inventory) | {"repository_manifest.json", "SHA256SUMS"},
                "Repository inventory differs from manifest")
        for name, info in inventory.items():
            p = ROOT / name
            require(p.stat().st_size == info["bytes"] and digest(p) == info["sha256"],
                    "Repository manifest hash mismatch: " + name)
        checksums = {}
        for line in (ROOT / "SHA256SUMS").read_text().splitlines():
            checksum, name = line.split("  ", 1)
            require(name not in checksums, "Duplicate checksum path")
            checksums[name] = checksum
        require(set(checksums) == set(actual) - {"SHA256SUMS"}, "Incomplete repository checksum inventory")
        require(all(digest(ROOT / name) == value for name, value in checksums.items()),
                "Repository checksum mismatch")

        require(run("lean_commit", [lean, "--githash"]).strip() == settings["lean_commit"], "Lean commit mismatch")
        lean_version = run("lean_version", [lean, "--version"]).strip()
        lake_version = run("lake_version", [lake, "--version"]).strip()
        require("5.0.0-src+293d5d0" in lake_version, "Lake version mismatch")
        require((ROOT / "lean-toolchain").read_text().strip() == settings["lean_toolchain"], "Repository toolchain mismatch")
        require((mathlib / "lean-toolchain").read_text().strip() == settings["lean_toolchain"], "Mathlib toolchain mismatch")
        require(run("mathlib_commit", ["git", "rev-parse", "HEAD"]).strip() == settings["mathlib"]["commit"], "Mathlib commit mismatch")
        require(not run("mathlib_status", ["git", "status", "--porcelain", "--untracked-files=no"]).strip(), "Mathlib tracked source changes")
        require(digest(mathlib / "lake-manifest.json") == settings["mathlib"]["manifest_sha256"], "Mathlib lock mismatch")
        require(digest(mathlib / "LICENSE") == settings["mathlib"]["license_sha256"], "Mathlib license mismatch")
        upstream = json.loads((mathlib / "lake-manifest.json").read_text())
        expected_deps = {p["name"]: (p["url"], p["commit"]) for p in settings["dependencies"]}
        require({p["name"]: (p["url"], p["rev"]) for p in upstream["packages"]} == expected_deps,
                "Upstream dependency pins mismatch")
        for name, (_, revision) in expected_deps.items():
            path = mathlib / ".lake" / "packages" / name
            require(run("dependency_"+name, ["git", "rev-parse", "HEAD"], cwd=path).strip() == revision,
                    f"Dependency commit mismatch: {name}")
            require(not run("dependency_status_"+name,
                ["git", "status", "--porcelain", "--untracked-files=no"], cwd=path).strip(),
                f"Dependency tracked source changes: {name}")
        config = tomllib.loads((ROOT / "lakefile.toml").read_text())
        require(config["lean_lib"][0]["roots"] == list(modules), "Lake module roots mismatch")
        require(config["require"][0]["rev"] == settings["mathlib"]["commit"], "Lake Mathlib pin mismatch")
        package_lock = json.loads((ROOT / "lake-manifest.json").read_text())
        require({p["name"]: (p["url"], p["rev"]) for p in package_lock["packages"]} ==
            expected_deps | {"mathlib": (settings["mathlib"]["url"], settings["mathlib"]["commit"])},
            "Repository dependency lock mismatch")

        run("exact_checks", [sys.executable, str(ROOT / "exact_checks.py"),
            "--output", str(output / "exact_results.json")], cwd=ROOT)
        exact = json.loads((output / "exact_results.json").read_text())
        require(exact["two_dimensional_psd_pairs_checked"] == 12544, "Missing PSD test cases")
        require(exact["two_dimensional_attaining_witnesses_checked"] == 2304, "Missing attaining cases")
        require(exact["shared_reference_three_target_tuples_checked"] == 729, "Missing shared-reference tuples")
        require(exact["failures"] == [], "Exact checks reported failures")

        run("recorded_benchmark_artifacts", [sys.executable, str(ROOT / "benchmark_artifacts.py"),
            "--results-root", str(ROOT / "expected"), "--output", str(output / "recorded_tables")], cwd=ROOT)
        for table in (ROOT / "expected" / "tables").glob("*.csv"):
            require(digest(table) == digest(output / "recorded_tables" / table.name),
                    "Recorded table/figure data mismatch: " + table.name)
        if args.benchmark_archive is not None:
            archive = args.benchmark_archive.resolve(strict=True)
            require(not archive.is_relative_to(ROOT), "Keep public input outside the repository")
            required_numpy = settings["python"]["analysis_requirement"].split("==", 1)[1]
            require(importlib.metadata.version("numpy") == required_numpy, "Benchmark NumPy pin mismatch")
            require(digest(archive) == "2560548591e3a726c88549b6dc9d226995616c26874d601c69fee8b9eee9d730",
                    "Benchmark archive hash mismatch")
            for representation in ("raw_hz", "raw_complete", "lobanov_complete"):
                run("benchmark_"+representation, [sys.executable, str(ROOT / "analyze_vowel_summaries.py"),
                    "--archive", str(archive), "--representation", representation,
                    "--leave-one-speaker-out", "--output", str(output / "benchmark" / representation)], cwd=ROOT)
            run("reproduced_benchmark_artifacts", [sys.executable, str(ROOT / "benchmark_artifacts.py"),
                "--results-root", str(output / "benchmark"), "--compare-with", str(ROOT / "expected"),
                "--output", str(output / "reproduced_tables")], cwd=ROOT)
            run("independent_decimal_audit", [sys.executable, str(ROOT / "independent_decimal_audit.py"),
                "--archive", str(archive), "--results-root", str(output / "benchmark"),
                "--output", str(output / "independent_results.json")], cwd=ROOT)
            independent = json.loads((output / "independent_results.json").read_text())
            require(independent["coverage"] == {"main_cohorts": 9, "speaker_omissions": 399,
                    "order_questions": 269280, "main_nearest_witnesses": 133}, "Incomplete benchmark coverage")
            require(independent["failures"] == [], "Independent benchmark checks failed")
            benchmark = {"status": "PASS_REPRODUCED_AND_INDEPENDENTLY_RECOMPUTED",
                "input_sha256": digest(archive), "numpy": required_numpy,
                "coverage": independent["coverage"],
                "independent_results_sha256": digest(output / "independent_results.json"),
                "analysis_source_sha256": digest(ROOT / "analyze_vowel_summaries.py"),
                "independent_source_sha256": digest(ROOT / "independent_decimal_audit.py"),
                "table_checks_sha256": digest(output / "reproduced_tables" / "artifact_checks.json")}
            print(json.dumps({"stage": "benchmark_pass", **benchmark["coverage"]}), flush=True)
        if args.figures:
            for key in ("analysis_requirement", "figure_requirement"):
                name, version = settings["python"][key].split("==", 1)
                require(importlib.metadata.version(name) == version, "Figure dependency pin mismatch: " + name)
            figure_command = [sys.executable, str(ROOT / "generate_vowel_figure.py"),
                "--results", str(ROOT / "expected" / "raw_hz" / "results.json"),
                "--output-dir", str(output / "figures")]
            if args.anonymous_figures:
                figure_command.append("--anonymous")
            run("figure_exports", figure_command, cwd=ROOT)
            for suffix in ("pdf", "png", "jpg", "eps", "svg"):
                require((output / "figures" / ("vowel_intervals." + suffix)).stat().st_size > 0,
                        "Empty figure export: " + suffix)
            require(digest(output / "figures" / "vowel_intervals.csv") ==
                    digest(ROOT / "expected" / "tables" / "vowel_intervals.csv"), "Figure CSV differs from reviewed data")
            figures = {"status": "PASS_FIVE_FORMAT_EXPORT_AND_EXACT_CSV_MATCH",
                "source": "reviewed recorded raw_hz aggregates; separate from archive-dependent rerun",
                "manifest_sha256": digest(output / "figures" / "figure_exports.json"),
                "csv_sha256": digest(output / "figures" / "vowel_intervals.csv"),
                "visual_review": "Not performed by this command; requires separate page/figure inspection."}

        lake_path = run("lake_search_path", [lake, "env", "printenv", "LEAN_PATH"]).strip()
        compile_env = env | {"LEAN_PATH": str(output)+os.pathsep+lake_path}
        declarations = []
        for module, info in modules.items():
            source = ROOT / info["source"]
            require(digest(source) == info["sha256"], f"Frozen proof source mismatch: {module}")
            source_text = source.read_text()
            require(not re.search(r"\b(sorry|admit|sorryAx|native_decide)\b|^\s*(axiom|constant)\b", source_text, re.M),
                    f"Forbidden proof placeholder or axiom token in {module}")
            local = re.findall(r"^(?:noncomputable )?(?:def|theorem) ([A-Za-z_][A-Za-z_0-9']*)", source_text, re.M)
            names = [info["namespace"]+"."+name for name in local]
            require(names == info["declarations"], f"Declaration map mismatch: {module}")
            declarations.extend(names)
            text = run("build_"+module, [lean, "-R", str(ROOT), "-o", str(output / f"{module}.olean"), str(source)],
                       run_env=compile_env)
            require("warning:" not in text and "error:" not in text, f"Build diagnostics in {module}")
            artifacts[module] = {"source_sha256": digest(source), "olean_sha256": digest(output / f"{module}.olean")}
            print(json.dumps({"stage": "clean_module_pass", "module": module}), flush=True)

        require(len(declarations) == theorem_map["total_declarations"] == len(set(declarations)), "Declaration count mismatch")
        audit = output / "AxiomAudit.lean"
        audit.write_text("import "+theorem_map["top_module"]+"\nset_option pp.universes false\n"+
            "\n".join(f"#check @{name}\n#print axioms {name}" for name in declarations)+"\n")
        text = run("statements_and_axioms", [lean, str(audit)], run_env=compile_env)
        require("warning:" not in text and "error:" not in text, "Audit diagnostics")
        axioms = {name: [x.strip() for x in body.split(",") if x.strip()] for name, body in
            re.findall(r"^'(.+)' depends on axioms: \[([^\]]*)\]", text, re.M)}
        for name in re.findall(r"^'(.+)' does not depend on any axioms", text, re.M):
            axioms[name] = []
        require(set(axioms) == set(declarations), "Incomplete axiom audit")
        allowed = {"propext", "Classical.choice", "Quot.sound"}
        require(set(theorem_map["allowed_axioms"]) == allowed, "Allowed-axiom map mismatch")
        require(all(set(items) <= allowed for items in axioms.values()), "Disallowed transitive axiom")
        print(json.dumps({"stage": "all_axioms_pass", "declarations": len(declarations)}), flush=True)
        run("kernel_replay_fresh", [checker, "--fresh", "--verbose", theorem_map["top_module"]], run_env=compile_env)
        for module, info in modules.items():
            require(digest(ROOT / info["source"]) == info["sha256"], f"Proof changed during verification: {module}")
        require(all(digest(ROOT / name) == info["sha256"] for name, info in inventory.items()),
                "Repository source changed during verification")

        report = {
            "status": "PASS_FORMAL_AND_BENCHMARK_VERIFICATION" if args.benchmark_archive is not None
                      else "PASS_FORMAL_VERIFICATION_BENCHMARK_NOT_RUN",
            "created_utc": datetime.now(timezone.utc).isoformat(),
            "python": platform.python_version(), "lean": lean_version, "lake": lake_version,
            "lean_commit": settings["lean_commit"], "mathlib_commit": settings["mathlib"]["commit"],
            "sources": artifacts, "transitive_axioms": axioms, "declaration_count": len(declarations),
            "exact_results_sha256": digest(output / "exact_results.json"),
            "verifier_sha256": digest(Path(__file__)),
            "environment_sha256": digest(ROOT / "environment.json"),
            "theorem_map_sha256": digest(ROOT / "theorem_map.json"),
            "repository_manifest_sha256": digest(ROOT / "repository_manifest.json"),
            "recorded_aggregate_checks": "PASS; consistency only, distinct from archive-dependent rerun",
            "benchmark": benchmark,
            "figures": figures,
            "commands": runs,
            "limits": ["Official same-kernel fresh replay, not an independent kernel implementation.",
                "Formalized objective is the explicit real matrix-square-root trace plus squared mean difference.",
                "No measure-theoretic Gaussian Wasserstein or Python-to-Lean translation is formalized.",
                "Finite exact synthetic and Decimal checks are not unbounded proofs or certified interval arithmetic.",
                "The optional benchmark is a finite-dataset Gaussian-moment reporting audit, not a perception test or population inference.",
                "Completion witnesses need not preserve normalized-data row identities or the observed reference covariance.",
                "No external empirical input is needed for the proof; omitting the archive explicitly leaves its benchmark rerun NOT_RUN.",
                "CI configuration is not evidence of hosted execution."]
        }
        (output / "verification.json").write_text(json.dumps(report, indent=2)+"\n")
        print(json.dumps({"status": report["status"], "report": str(output / "verification.json"),
                          "sha256": digest(output / "verification.json")}), flush=True)
    except Exception as error:
        (output / "failure.json").write_text(json.dumps({"status": "FAIL", "error": str(error), "commands": runs}, indent=2)+"\n")
        raise


if __name__ == "__main__":
    main()
