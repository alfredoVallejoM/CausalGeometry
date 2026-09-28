#!/usr/bin/env python3
"""Directed CX-I1 gate. Reuses the repository source audit; never mocks Lean.

Exit 0: the requested Lean scope typechecked (not full campaign accreditation).
Exit 1: a required check failed. Exit 3: Lean verification remains pending.
--non-kernel runs only independent tests and ALWAYS exits 3 on success.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import resource
import re
import shutil
import signal
import subprocess
import sys
import time
import uuid

ROOT = Path(__file__).resolve().parents[1]
TEST = [sys.executable, "-m", "unittest", "discover", "-s", "tests", "-p", "test_cx_i1.py", "-v"]
COMMANDS = [
    TEST,
    [sys.executable, "tools/source_audit.py", "--all"],
    ["lake", "build", "+CausalGeometry.Exchange.Variational",
     "+CausalGeometry.Models.ExchangeThreeEvents",
     "+CausalGeometry.Variational.QuasiNoether",
     "+CausalGeometry.Variational.CausalMomentumMap"],
    ["lake", "env", "lean", "verification/cx-i1/KernelAudit.lean"],
]


def git(*args):
    p = subprocess.run(["git", *args], cwd=ROOT, text=True, capture_output=True)
    return p.stdout.strip() if p.returncode == 0 else None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", action="store_true")
    parser.add_argument("--non-kernel", action="store_true")
    parser.add_argument("--timeout", type=int, default=900, help="seconds per command")
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    commands = [TEST] if args.non_kernel else COMMANDS
    if args.plan:
        print(json.dumps({"scope": "CX-I1", "commands": commands,
                          "not_full_campaign": True}, indent=2))
        return 0

    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    out = ROOT / "verification" / "local-runner" / "cx-i1" / (stamp + "-" + uuid.uuid4().hex[:8])
    out.mkdir(parents=True, exist_ok=False)
    affinity = None
    if hasattr(os, "sched_getaffinity"):
        affinity = sorted(os.sched_getaffinity(0))[:2]
        os.sched_setaffinity(0, affinity)
    env = dict(os.environ)
    env.update({"OMP_NUM_THREADS": "1", "OPENBLAS_NUM_THREADS": "1", "MKL_NUM_THREADS": "1"})
    receipt = {
        "schema": 1, "scope": "CX-I1", "started_at": stamp,
        "source_sha": git("rev-parse", "HEAD"), "git_status_before": git("status", "--short"),
        "cpu_affinity": affinity, "python": sys.version, "results": [],
        "lean_typecheck": "NOT_RUN", "campaign_accredited": False,
        "limitations": ["directed scope only", "no independent review claimed"],
    }
    manifest = ROOT / "verification/cx-i1/manifest.json"
    if manifest.is_file():
        receipt["increment_manifest_sha256"] = hashlib.sha256(manifest.read_bytes()).hexdigest()
    code = 3
    try:
        if manifest.is_file():
            expected = json.loads(manifest.read_text())["files"]
            mismatches = [path for path, data in expected.items()
                          if not (ROOT / path).is_file()
                          or hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != data["sha256"]]
            if mismatches:
                receipt["status"] = "INCREMENT_SOURCE_MISMATCH"
                receipt["mismatched_files"] = mismatches
                return 1
        if not args.non_kernel:
            missing = [exe for exe in ("git", "lean", "lake") if shutil.which(exe) is None]
            if missing:
                receipt["status"] = "BLOCKED_MISSING_TOOLCHAIN"
                receipt["missing"] = missing
                return 3
            if receipt["source_sha"] is None:
                receipt["status"] = "BLOCKED_NOT_A_GIT_CHECKOUT"
                return 3
            for exe in ("lean", "lake"):
                p = subprocess.run([exe, "--version"], cwd=ROOT, env=env, text=True,
                                   capture_output=True, timeout=args.timeout)
                receipt[exe + "_version"] = p.stdout.strip()
                if p.returncode:
                    receipt["status"] = "TOOLCHAIN_VERSION_FAILED"
                    return 1
            receipt["lean_toolchain_pin"] = (ROOT / "lean-toolchain").read_text().strip()
            expected_version = receipt["lean_toolchain_pin"].rsplit(":v", 1)[-1]
            found = re.search(r"version ([0-9]+\.[0-9]+\.[0-9]+)", receipt["lean_version"])
            if found is None or found.group(1) != expected_version:
                receipt["status"] = "LEAN_VERSION_MISMATCH"
                return 1
            receipt["mathlib_resolved_sha_before"] = git("-C", ".lake/packages/mathlib", "rev-parse", "HEAD")
        for index, argv in enumerate(commands):
            path = out / f"{index:02d}.log"
            started = time.monotonic()
            print("+", " ".join(argv), flush=True)
            with path.open("wb") as log:
                proc = subprocess.Popen(argv, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT,
                                        start_new_session=True)
                try:
                    result = proc.wait(timeout=args.timeout)
                    status = "PASS" if result == 0 else "FAIL"
                except subprocess.TimeoutExpired:
                    os.killpg(proc.pid, signal.SIGKILL)
                    proc.wait()
                    result, status = 124, "TIMEOUT"
            receipt["results"].append({
                "argv": argv, "exit_code": result, "status": status,
                "wall_seconds": time.monotonic()-started,
                "log": str(path.relative_to(ROOT)),
                "log_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                "peak_rss_children_cumulative_kib": resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
            })
            print(path.read_text(errors="replace"), end="")
            if argv[:3] == ["lake", "env", "lean"] and "sorryAx" in path.read_text(errors="replace"):
                receipt["status"] = "UNSAFE_AXIOM_IN_KERNEL_OUTPUT"
                receipt["lean_typecheck"] = "REJECTED_AXIOMS"
                return 1
            if result:
                receipt["status"] = "REQUIRED_CHECK_FAILED"
                if argv[0] == "lake":
                    receipt["lean_typecheck"] = status
                return 1
        if args.non_kernel:
            receipt["status"] = "NON_KERNEL_PASS_TYPECHECK_PENDING"
        else:
            packages = json.loads((ROOT / "lake-manifest.json").read_text())["packages"]
            entry = next(p for p in packages if p["name"] == "mathlib")
            resolved = git("-C", ".lake/packages/mathlib", "rev-parse", "HEAD")
            receipt["mathlib_manifest_rev"] = entry["rev"]
            receipt["mathlib_resolved_sha_after"] = resolved
            if resolved != entry["rev"]:
                receipt["status"] = "MATHLIB_RESOLUTION_MISMATCH"
                return 1
            receipt["status"] = "SCOPE_TYPECHECK_PASS_NOT_CAMPAIGN_ACCREDITED"
            receipt["lean_typecheck"] = "PASS"
            code = 0
        return code
    except (OSError, subprocess.SubprocessError, KeyError, ValueError, StopIteration) as error:
        receipt["status"] = "EXECUTION_ERROR"
        receipt["error"] = str(error)
        return 1
    finally:
        receipt["finished_at"] = dt.datetime.now(dt.timezone.utc).isoformat()
        (out / "receipt.json").write_text(json.dumps(receipt, indent=2, ensure_ascii=False)+"\n")
        print("Receipt:", out / "receipt.json")


if __name__ == "__main__":
    raise SystemExit(main())
