#!/usr/bin/env python3
"""CX-I7 directed verification. Never substitutes finite tests for the kernel.

Returns 0 only after the declared real Lean scope; 1 for a failed requirement;
3 for pending kernel verification, including successful --non-kernel runs.
Reuses the I2 axiom-output checker and the I4 directed-gate strategy.
The I7 loader verifies the exact historical root before replaying old tests.
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
from verify_cx_i2 import audit_axiom_output

ROOT = Path(__file__).resolve().parents[1]


def git(*args):
    if shutil.which("git") is None:
        return None
    p = subprocess.run(["git", *args], cwd=ROOT, text=True, capture_output=True, timeout=30)
    return p.stdout.strip() if p.returncode == 0 else None


def commands(manifest, non_kernel):
    result = [([sys.executable, "-m", "unittest", "discover", "-s", "tests", "-p", "test_cx_i7.py", "-v"], None)]
    if not non_kernel:
        result += [([sys.executable, "tools/source_audit.py", "--all"], None),
                   (["lake", "build", *["+"+x for x in manifest["kernel_targets"]]], None)]
        result += [(["lake", "env", "lean", path], count) for path, count in manifest["kernel_audits"].items()]
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", action="store_true")
    parser.add_argument("--non-kernel", action="store_true")
    parser.add_argument("--timeout", type=int, default=900)
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    manifest_path = ROOT/"verification/cx-i7/manifest.json"
    if args.plan:
        m = json.loads(manifest_path.read_text())
        print(json.dumps({"scope": "CX-I7", "commands": commands(m, args.non_kernel),
                          "not_full_workspace": True, "no_new_accreditation": True}, indent=2))
        return 0
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    out = ROOT/"verification/local-runner/cx-i7"/(stamp+"-"+uuid.uuid4().hex[:8])
    out.mkdir(parents=True, exist_ok=False)
    receipt = {"schema": 1, "scope": "CX-I7", "results": [], "started_at": stamp,
               "kernel_status": "NOT_RUN", "campaign_accredited": False,
               "limitations": ["directed scope only", "no independent review claimed"]}
    try:
        receipt.update(source_sha=git("rev-parse", "HEAD"), git_status_before=git("status", "--short"),
                       python_version=sys.version)
        if not manifest_path.is_file():
            receipt["status"] = "MISSING_MANIFEST"
            return 1
        m = json.loads(manifest_path.read_text())
        receipt["manifest_sha256"] = hashlib.sha256(manifest_path.read_bytes()).hexdigest()
        bad = [p for p, h in m["files_sha256"].items()
               if not (ROOT/p).is_file() or hashlib.sha256((ROOT/p).read_bytes()).hexdigest() != h]
        if bad:
            receipt.update(status="SOURCE_HASH_MISMATCH", mismatches=bad)
            return 1
        receipt["cpu_affinity"] = None
        if hasattr(os, "sched_getaffinity"):
            cpus = sorted(os.sched_getaffinity(0))[:2]
            os.sched_setaffinity(0, cpus)
            receipt["cpu_affinity"] = cpus
        env = dict(os.environ, OMP_NUM_THREADS="1", OPENBLAS_NUM_THREADS="1", MKL_NUM_THREADS="1")
        if not args.non_kernel:
            missing = [x for x in ("lean", "lake") if shutil.which(x) is None]
            if missing:
                receipt.update(status="BLOCKED_MISSING_TOOLCHAIN", missing=missing)
                return 3
            if receipt["source_sha"] is None:
                receipt["status"] = "BLOCKED_NOT_A_GIT_CHECKOUT"
                return 3
            for name in ("lean", "lake"):
                p = subprocess.run([name, "--version"], cwd=ROOT, env=env, text=True,
                                   capture_output=True, timeout=args.timeout)
                receipt[name+"_version"] = {"stdout": p.stdout, "stderr": p.stderr, "exit_code": p.returncode}
                if p.returncode:
                    receipt["status"] = "TOOLCHAIN_VERSION_FAILED"
                    return 1
            pin = (ROOT/"lean-toolchain").read_text().strip()
            found = re.search(r"version ([0-9]+\.[0-9]+\.[0-9]+)", receipt["lean_version"]["stdout"])
            if found is None or found.group(1) != pin.rsplit(":v", 1)[-1]:
                receipt["status"] = "LEAN_VERSION_MISMATCH"
                return 1
            receipt["lean_toolchain_pin"] = pin
        for index, (argv, axiom_count) in enumerate(commands(m, args.non_kernel)):
            log = out/f"{index:02d}.log"
            started = time.monotonic()
            print("+", " ".join(argv), flush=True)
            with log.open("wb") as stream:
                p = subprocess.Popen(argv, cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT,
                                     start_new_session=True)
                try:
                    code = p.wait(timeout=args.timeout)
                except subprocess.TimeoutExpired:
                    os.killpg(p.pid, signal.SIGKILL)
                    p.wait()
                    code = 124
            text = log.read_text(errors="replace")
            row = {"argv": argv, "exit_code": code, "wall_seconds": time.monotonic()-started,
                   "status": "PASS" if code == 0 else "TIMEOUT" if code == 124 else "FAIL",
                   "log": str(log.relative_to(ROOT)), "log_sha256": hashlib.sha256(log.read_bytes()).hexdigest(),
                   "peak_rss_children_cumulative_kib": resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss}
            receipt["results"].append(row)
            print(text, end="")
            if code:
                receipt["status"] = "REQUIRED_CHECK_FAILED"
                return 1
            if axiom_count is not None:
                row["axiom_audit"] = audit_axiom_output(text, axiom_count)
                if not row["axiom_audit"]["pass"]:
                    receipt["status"] = "KERNEL_AXIOM_AUDIT_FAILED"
                    return 1
        changed = [path for path, digest in m["files_sha256"].items()
                   if not (ROOT/path).is_file()
                   or hashlib.sha256((ROOT/path).read_bytes()).hexdigest() != digest]
        if changed:
            receipt.update(status="SOURCE_CHANGED_DURING_RUN", changed=changed)
            return 1
        if args.non_kernel:
            receipt["status"] = "NON_KERNEL_PASS_TYPECHECK_PENDING"
            return 3
        packages = json.loads((ROOT/"lake-manifest.json").read_text())["packages"]
        mathlib = next(p for p in packages if p["name"] == "mathlib")
        resolved = git("-C", ".lake/packages/mathlib", "rev-parse", "HEAD")
        receipt["mathlib"] = {"manifest": mathlib, "resolved_sha": resolved}
        if resolved != mathlib["rev"] or mathlib.get("inputRev") != m["mathlib_pin"]:
            receipt["status"] = "MATHLIB_PIN_MISMATCH"
            return 1
        receipt.update(status="DIRECTED_KERNEL_PASS_NOT_CAMPAIGN_ACCREDITED", kernel_status="PASS")
        return 0
    except (OSError, ValueError, KeyError, StopIteration, subprocess.SubprocessError) as error:
        receipt.update(status="EXECUTION_ERROR", error=str(error))
        return 1
    finally:
        receipt["finished_at"] = dt.datetime.now(dt.timezone.utc).isoformat()
        (out/"receipt.json").write_text(json.dumps(receipt, indent=2, ensure_ascii=False)+"\n")
        print("Receipt:", out/"receipt.json")


if __name__ == "__main__":
    raise SystemExit(main())
