#!/usr/bin/env python3
"""Directed CA-24 Tamagawa gate with exact-SHA receipts.

Exit 0: selected Lean build and kernel axiom audit passed.
Exit 1: a required source or kernel check failed.
Exit 3: non-kernel checks passed but Lean/Lake are unavailable or kernel work
        was explicitly skipped.

This runner is local-only. It does not use GitHub Actions and it does not
accredit unrelated CA/CX campaign rows.
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

SOURCE_FILES = [
    "CausalGeometry/Realization/ECIATamagawaContract.lean",
    "CausalGeometry/Realization/IndexedFamily.lean",
    "CausalGeometry/Realization/TamagawaIndexedFamily.lean",
    "CausalGeometry/Models/TamagawaControls.lean",
    "CausalGeometry/Models/IndexedFamilyControls.lean",
    "CausalGeometry/Models/CommonSourceControls.lean",
    "verification/tamagawa/KernelAudit.lean",
]

SOURCE_AUDIT = [sys.executable, "tools/source_audit.py", "--proof-hygiene"]
BUILD = [
    "lake", "build",
    "+CausalGeometry.Realization.ECIATamagawaContract",
    "+CausalGeometry.Realization.IndexedFamily",
    "+CausalGeometry.Realization.TamagawaIndexedFamily",
    "+CausalGeometry.Models.TamagawaControls",
    "+CausalGeometry.Models.IndexedFamilyControls",
    "+CausalGeometry.Models.CommonSourceControls",
]
KERNEL = ["lake", "env", "lean", "verification/tamagawa/KernelAudit.lean"]


def git(*args: str) -> str | None:
    if shutil.which("git") is None:
        return None
    proc = subprocess.run(
        ["git", *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
        timeout=30,
    )
    return proc.stdout.strip() if proc.returncode == 0 else None


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audit_axiom_output(text: str, expected: int) -> dict[str, object]:
    groups = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", text, flags=re.S)
    empty = len(re.findall(r"does not depend on any axioms", text))
    used = {
        axiom.strip()
        for group in groups
        for axiom in group.split(",")
        if axiom.strip()
    }
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    unexpected = sorted(used - allowed)
    outputs = len(groups) + empty
    return {
        "outputs": outputs,
        "expected": expected,
        "axioms": sorted(used),
        "unexpected": unexpected,
        "pass": outputs == expected and not unexpected and "sorryAx" not in text,
    }


def run_command(
    argv: list[str],
    out_dir: Path,
    index: int,
    timeout_seconds: int,
    env: dict[str, str],
) -> tuple[dict[str, object], str]:
    log = out_dir / f"{index:02d}.log"
    started = time.monotonic()
    print("+", " ".join(argv), flush=True)
    with log.open("wb") as stream:
        proc = subprocess.Popen(
            argv,
            cwd=ROOT,
            env=env,
            stdout=stream,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )
        try:
            code = proc.wait(timeout=timeout_seconds)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait()
            code = 124
    text = log.read_text(errors="replace")
    row: dict[str, object] = {
        "argv": argv,
        "exit_code": code,
        "status": "PASS" if code == 0 else "TIMEOUT" if code == 124 else "FAIL",
        "wall_seconds": time.monotonic() - started,
        "log": str(log.relative_to(ROOT)),
        "log_sha256": sha256(log),
        "peak_rss_children_cumulative_kib":
            resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
    }
    print(text, end="")
    return row, text


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", action="store_true")
    parser.add_argument("--non-kernel", action="store_true")
    parser.add_argument("--timeout", type=int, default=900)
    args = parser.parse_args()

    if args.timeout <= 0:
        parser.error("timeout must be positive")

    commands = [SOURCE_AUDIT] if args.non_kernel else [SOURCE_AUDIT, BUILD, KERNEL]

    if args.plan:
        print(json.dumps({
            "scope": "CA24-TAMAGAWA",
            "commands": commands,
            "source_files": SOURCE_FILES,
            "not_full_workspace": True,
            "github_actions": False,
        }, indent=2))
        return 0

    missing_sources = [path for path in SOURCE_FILES if not (ROOT / path).is_file()]
    if missing_sources:
        print("missing Tamagawa source files:", *missing_sources, sep="\n- ", file=sys.stderr)
        return 1

    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    out_dir = ROOT / "verification/local-runner/tamagawa" / (
        stamp + "-" + uuid.uuid4().hex[:8]
    )
    out_dir.mkdir(parents=True, exist_ok=False)

    receipt: dict[str, object] = {
        "schema": 1,
        "scope": "CA24-TAMAGAWA",
        "started_at": stamp,
        "source_sha": git("rev-parse", "HEAD"),
        "git_status_before": git("status", "--short"),
        "source_files_sha256": {
            path: sha256(ROOT / path)
            for path in SOURCE_FILES
        },
        "results": [],
        "kernel_status": "NOT_RUN",
        "campaign_accredited": False,
        "limitations": [
            "directed Tamagawa scope, not full workspace",
            "does not close CA-24.39 or T152 by itself",
            "no independent review claimed",
        ],
    }

    affinity: list[int] | None = None
    if hasattr(os, "sched_getaffinity"):
        available = sorted(os.sched_getaffinity(0))
        affinity = available[:2]
        if affinity:
            os.sched_setaffinity(0, affinity)
    receipt["cpu_affinity"] = affinity

    env = dict(
        os.environ,
        OMP_NUM_THREADS="1",
        OPENBLAS_NUM_THREADS="1",
        MKL_NUM_THREADS="1",
    )

    try:
        if not args.non_kernel:
            missing_tools = [
                name for name in ("lean", "lake")
                if shutil.which(name) is None
            ]
            if missing_tools:
                row, _ = run_command(
                    SOURCE_AUDIT, out_dir, 0, args.timeout, env
                )
                receipt["results"].append(row)
                if row["exit_code"] != 0:
                    receipt["status"] = "SOURCE_AUDIT_FAILED"
                    return 1
                receipt["status"] = "BLOCKED_MISSING_TOOLCHAIN"
                receipt["missing"] = missing_tools
                return 3

        for index, argv in enumerate(commands):
            row, output = run_command(
                argv, out_dir, index, args.timeout, env
            )
            if argv == KERNEL:
                row["axiom_audit"] = audit_axiom_output(output, 10)
            receipt["results"].append(row)
            if row["exit_code"] != 0:
                receipt["status"] = "REQUIRED_CHECK_FAILED"
                return 1
            if argv == KERNEL and not row["axiom_audit"]["pass"]:
                receipt["status"] = "KERNEL_AXIOM_AUDIT_FAILED"
                return 1

        if args.non_kernel:
            receipt["status"] = "NON_KERNEL_PASS_TYPECHECK_PENDING"
            return 3

        receipt["kernel_status"] = "PASS"
        receipt["status"] = "DIRECTED_KERNEL_PASS_NOT_CAMPAIGN_ACCREDITED"
        return 0
    except (OSError, subprocess.SubprocessError, ValueError) as error:
        receipt["status"] = "EXECUTION_ERROR"
        receipt["error"] = str(error)
        return 1
    finally:
        receipt["finished_at"] = dt.datetime.now(dt.timezone.utc).isoformat()
        receipt["git_status_after"] = git("status", "--short")
        (out_dir / "receipt.json").write_text(
            json.dumps(receipt, indent=2, ensure_ascii=False) + "\n",
            encoding="utf-8",
        )
        print("Receipt:", out_dir / "receipt.json")


if __name__ == "__main__":
    raise SystemExit(main())
