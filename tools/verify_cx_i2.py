#!/usr/bin/env python3
"""CX-I2 directed gate; no simulated compiler or implicit campaign accreditation.

Exit 0: actual directed kernel scope passed. Exit 1: required check failed.
Exit 3: kernel checks remain pending, including successful --non-kernel runs.
The historical I1 manifest stays immutable; I2 checks its append-only migration.
"""
from __future__ import annotations
import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import shutil
import signal
import subprocess
import sys
import time
import uuid

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT/"verification/cx-i2/manifest.json"
TEST = [sys.executable, "-m", "unittest", "discover", "-s", "tests", "-p", "test_cx_i2.py", "-v"]
COMMANDS = [
    TEST,
    [sys.executable, "tools/source_audit.py", "--all"],
    ["lake", "build", "+CausalGeometry.Models.ExchangeCoherenceControls",
     "+CausalGeometry.Exchange.Variational", "+CausalGeometry.Variational.QuasiNoether",
     "+CausalGeometry.Variational.CausalMomentumMap"],
    ["lake", "env", "lean", "verification/cx-i1/KernelAudit.lean"],
    ["lake", "env", "lean", "verification/cx-i2/KernelAudit.lean"],
]


def git(*args):
    if shutil.which("git") is None:
        return None
    p = subprocess.run(["git", *args], cwd=ROOT, text=True, capture_output=True, timeout=30)
    return p.stdout.strip() if p.returncode == 0 else None


def audit_axiom_output(text, expected):
    """Count actual outputs and reject dependencies outside the native whitelist."""
    groups = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", text, flags=re.S)
    empty = len(re.findall(r"does not depend on any axioms", text))
    used = {a.strip() for group in groups for a in group.split(",") if a.strip()}
    extra = used - {"propext", "Classical.choice", "Quot.sound"}
    return {"outputs": len(groups)+empty, "expected": expected,
            "axioms": sorted(used), "unexpected": sorted(extra),
            "pass": len(groups)+empty == expected and not extra and "sorryAx" not in text}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", action="store_true")
    parser.add_argument("--non-kernel", action="store_true")
    parser.add_argument("--timeout", type=int, default=900, help="seconds per command")
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("timeout must be positive")
    commands = [TEST] if args.non_kernel else COMMANDS
    if args.plan:
        print(json.dumps({"scope": "CX-I2", "commands": commands,
                          "not_full_workspace": True}, indent=2))
        return 0
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    out = ROOT/"verification/local-runner/cx-i2"/(stamp+"-"+uuid.uuid4().hex[:8])
    out.mkdir(parents=True, exist_ok=False)
    receipt = {"schema": 1, "scope": "CX-I2", "started_at": stamp, "results": [],
               "kernel_status": "NOT_RUN", "campaign_accredited": False,
               "limitations": ["directed scope, not full workspace", "no independent review claimed"]}
    try:
        receipt["source_sha"] = git("rev-parse", "HEAD")
        receipt["git_status_before"] = git("status", "--short")
        if not MANIFEST.is_file():
            receipt["status"] = "MISSING_INCREMENT_MANIFEST"
            return 1
        data = json.loads(MANIFEST.read_text())
        receipt["manifest_sha256"] = hashlib.sha256(MANIFEST.read_bytes()).hexdigest()
        bad = [p for p, digest in data["files_sha256"].items()
               if not (ROOT/p).is_file() or hashlib.sha256((ROOT/p).read_bytes()).hexdigest() != digest]
        if bad:
            receipt["status"], receipt["mismatches"] = "SOURCE_HASH_MISMATCH", bad
            return 1
        affinity = None
        if hasattr(os, "sched_getaffinity"):
            affinity = sorted(os.sched_getaffinity(0))[:2]
            os.sched_setaffinity(0, affinity)
        receipt["cpu_affinity"] = affinity
        receipt["python_version"] = sys.version
        env = dict(os.environ, OMP_NUM_THREADS="1", OPENBLAS_NUM_THREADS="1", MKL_NUM_THREADS="1")
        if not args.non_kernel:
            missing = [x for x in ("lean", "lake") if shutil.which(x) is None]
            if missing:
                receipt["status"], receipt["missing"] = "BLOCKED_MISSING_TOOLCHAIN", missing
                return 3
            if receipt["source_sha"] is None:
                receipt["status"] = "BLOCKED_NOT_A_GIT_CHECKOUT"
                return 3
            for name in ("lean", "lake"):
                p = subprocess.run([name, "--version"], cwd=ROOT, env=env,
                                   text=True, capture_output=True, timeout=args.timeout)
                receipt[name+"_version"] = {"stdout": p.stdout, "stderr": p.stderr, "exit_code": p.returncode}
                if p.returncode:
                    receipt["status"] = "TOOLCHAIN_VERSION_FAILED"
                    return 1
            pin = (ROOT/"lean-toolchain").read_text().strip()
            version = re.search(r"version ([0-9]+\.[0-9]+\.[0-9]+)", receipt["lean_version"]["stdout"])
            if version is None or version.group(1) != pin.rsplit(":v", 1)[-1]:
                receipt["status"] = "LEAN_VERSION_MISMATCH"
                return 1
            receipt["lean_toolchain_pin"] = pin
        for i, argv in enumerate(commands):
            log = out/f"{i:02d}.log"
            started = time.monotonic()
            print("+", " ".join(argv), flush=True)
            with log.open("wb") as stream:
                p = subprocess.Popen(argv, cwd=ROOT, env=env, stdout=stream,
                                     stderr=subprocess.STDOUT, start_new_session=True)
                try:
                    code = p.wait(timeout=args.timeout)
                except subprocess.TimeoutExpired:
                    os.killpg(p.pid, signal.SIGKILL)
                    p.wait()
                    code = 124
            text = log.read_text(errors="replace")
            row = {"argv": argv, "exit_code": code,
                   "status": "PASS" if code == 0 else "TIMEOUT" if code == 124 else "FAIL",
                   "wall_seconds": time.monotonic()-started,
                   "log": str(log.relative_to(ROOT)),
                   "log_sha256": hashlib.sha256(log.read_bytes()).hexdigest(),
                   "peak_rss_children_cumulative_kib": resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss}
            receipt["results"].append(row)
            print(text, end="")
            if code:
                receipt["status"] = "REQUIRED_CHECK_FAILED"
                return 1
            if argv[:3] == ["lake", "env", "lean"]:
                expected = 22 if "cx-i1" in argv[-1] else 36
                row["axiom_audit"] = audit_axiom_output(text, expected)
                if not row["axiom_audit"]["pass"]:
                    receipt["status"] = "KERNEL_AXIOM_AUDIT_FAILED"
                    return 1
        if args.non_kernel:
            receipt["status"] = "NON_KERNEL_PASS_TYPECHECK_PENDING"
            return 3
        packages = json.loads((ROOT/"lake-manifest.json").read_text())["packages"]
        mathlib = next(p for p in packages if p["name"] == "mathlib")
        resolved = git("-C", ".lake/packages/mathlib", "rev-parse", "HEAD")
        receipt["mathlib"] = {"manifest": mathlib, "resolved_sha": resolved}
        if resolved != mathlib["rev"] or mathlib.get("inputRev") != "v4.32.1":
            receipt["status"] = "MATHLIB_PIN_MISMATCH"
            return 1
        receipt["status"] = "DIRECTED_KERNEL_PASS_NOT_CAMPAIGN_ACCREDITED"
        receipt["kernel_status"] = "PASS"
        return 0
    except (OSError, ValueError, KeyError, StopIteration, subprocess.SubprocessError) as error:
        receipt["status"], receipt["error"] = "EXECUTION_ERROR", str(error)
        return 1
    finally:
        receipt["finished_at"] = dt.datetime.now(dt.timezone.utc).isoformat()
        (out/"receipt.json").write_text(json.dumps(receipt, indent=2, ensure_ascii=False)+"\n")
        print("Receipt:", out/"receipt.json")


if __name__ == "__main__":
    raise SystemExit(main())
