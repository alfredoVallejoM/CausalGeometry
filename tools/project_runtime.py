#!/usr/bin/env python3
from __future__ import annotations

import argparse
import datetime as dt
import json
from pathlib import Path
import shutil
import subprocess
import sys
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
PROFILE_PATH = ROOT / "runtime-profile.json"
LEVELS = ["source", "execution", "regression", "adversarial", "performance", "release"]


def load_profile() -> dict[str, Any]:
    data = json.loads(PROFILE_PATH.read_text(encoding="utf-8"))
    if data.get("schema") != 1:
        raise SystemExit(f"unsupported runtime profile schema: {data.get('schema')!r}")
    return data


def git(*args: str) -> str:
    proc = subprocess.run(
        ["git", *args],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    return proc.stdout.strip() if proc.returncode == 0 else ""


def context() -> dict[str, str]:
    return {
        "root": str(ROOT),
        "python": sys.executable,
    }


def evidence_root() -> Path:
    head = git("rev-parse", "HEAD") or "unknown"
    path = ROOT / "verification" / "local-runner" / "by-sha" / head
    path.mkdir(parents=True, exist_ok=True)
    return path


def run(command: str) -> subprocess.CompletedProcess[str]:
    print(f"+ {command}", flush=True)
    return subprocess.run(command, cwd=ROOT, shell=True, text=True)


def doctor(profile: dict[str, Any]) -> int:
    failures = 0
    if profile.get("toolchains", {}).get("lean"):
        for command in ("lake", "lean"):
            path = shutil.which(command)
            print(f"[{'OK' if path else 'MISSING'}] {command}: {path or command}")
            failures += int(path is None)
    return 1 if failures else 0


def expand(command: str) -> str:
    return command.format(**context())


def verify(profile: dict[str, Any], level: str) -> int:
    selected = [
        ob for ob in profile.get("obligations", [])
        if level == "all" or ob.get("level") == level
    ]
    started = dt.datetime.now(dt.timezone.utc)
    evidence: dict[str, Any] = {
        "schema": 1,
        "project": profile["project"],
        "git_head": git("rev-parse", "HEAD") or None,
        "git_status": git("status", "--short"),
        "requested_level": level,
        "started_at": started.isoformat(),
        "results": [],
    }

    failed = False
    manual_pending = False
    for ob in selected:
        oid = ob["id"]
        required = bool(ob.get("required", True))
        kind = ob.get("kind", "command")

        if kind == "manual":
            print(f"[PENDING_MANUAL] {oid}: {ob.get('description', '')}")
            evidence["results"].append({
                "id": oid,
                "kind": kind,
                "required": required,
                "status": "PENDING_MANUAL",
            })
            manual_pending |= required
            continue

        command = expand(ob["command"])
        proc = run(command)
        status = "PASS" if proc.returncode == 0 else "FAIL"
        print(f"[{status}] {oid}")
        evidence["results"].append({
            "id": oid,
            "kind": kind,
            "required": required,
            "command": command,
            "returncode": proc.returncode,
            "status": status,
        })
        if required and proc.returncode != 0:
            failed = True
            if not ob.get("continue_on_failure", False):
                break

    evidence["finished_at"] = dt.datetime.now(dt.timezone.utc).isoformat()
    evidence["manual_pending"] = manual_pending
    evidence["failed"] = failed

    root = evidence_root()
    stamp = started.strftime("%Y%m%dT%H%M%SZ")
    path = root / f"{stamp}-{level}.json"
    path.write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    latest = root / f"latest-{level}.json"
    latest.write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[evidence] {path.relative_to(ROOT)}")

    if failed:
        return 1
    if manual_pending:
        print("[INCOMPLETE] required manual obligations remain pending")
        return 3
    return 0


def plan(profile: dict[str, Any]) -> None:
    for level in LEVELS:
        rows = [o for o in profile.get("obligations", []) if o.get("level") == level]
        if not rows:
            continue
        print(f"\n{level.upper()}")
        for row in rows:
            kind = row.get("kind", "command")
            req = "required" if row.get("required", True) else "optional"
            print(f"  {row['id']}: {kind}, {req} - {row.get('description', '')}")


def main() -> int:
    parser = argparse.ArgumentParser(description="CausalGeometry local verification runner")
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("doctor")
    verify_p = sub.add_parser("verify")
    verify_p.add_argument("level", nargs="?", default="all", choices=[*LEVELS, "all"])
    sub.add_parser("plan")
    sub.add_parser("quick")
    sub.add_parser("full")
    args = parser.parse_args()
    profile = load_profile()

    if args.command == "doctor":
        return doctor(profile)
    if args.command == "plan":
        plan(profile)
        return 0
    if args.command == "verify":
        return verify(profile, args.level)
    if args.command == "quick":
        if doctor(profile):
            return 1
        for level in ("source", "execution", "regression"):
            code = verify(profile, level)
            if code not in (0, 3):
                return code
        return 0
    if args.command == "full":
        if doctor(profile):
            return 1
        return verify(profile, "all")
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
