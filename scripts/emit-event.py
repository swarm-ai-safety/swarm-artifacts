#!/usr/bin/env python3
"""
Emit a SWARM event to the Inngest pipeline.

Reads run.yaml from a completed run and sends the appropriate event
(swarm/run.completed, swarm/sweep.completed, swarm/redteam.completed,
or swarm/run.failed) to the Inngest HTTP endpoint.

Usage:
    python scripts/emit-event.py <run_id>                    # auto-detect event type
    python scripts/emit-event.py <run_id> --event swarm/run.failed --error "OOM"
    python scripts/emit-event.py <run_id> --dry-run          # print event without sending

Environment:
    INNGEST_URL  — Inngest event API URL (default: http://localhost:8288/e/*)
"""

import argparse
import json
import os
import sys
from datetime import datetime, timezone
from pathlib import Path
from urllib.request import Request, urlopen
from urllib.error import URLError

import yaml


ROOT = Path(__file__).parent.parent
RUNS_DIR = ROOT / "runs"

INNGEST_URL = os.environ.get("INNGEST_URL", "http://localhost:8288/e/swarm-research-os")

# Map experiment types to completion event names
TYPE_EVENT_MAP = {
    "sweep": "swarm/sweep.completed",
    "redteam": "swarm/redteam.completed",
    "single": "swarm/run.completed",
    "study": "swarm/run.completed",
    "calibration": "swarm/run.completed",
}


def read_yaml(path: Path) -> dict:
    with open(path) as f:
        return yaml.safe_load(f) or {}


def read_json_safe(path: Path) -> dict:
    try:
        with open(path) as f:
            return json.load(f)
    except (json.JSONDecodeError, FileNotFoundError):
        return {}


def build_event(run_id: str, event_name: str | None = None, error: str | None = None) -> dict:
    """Build an Inngest event from a run's metadata."""
    run_path = RUNS_DIR / run_id
    if not run_path.exists():
        print(f"Error: {run_path} does not exist", file=sys.stderr)
        sys.exit(1)

    run_yaml_path = run_path / "run.yaml"
    if not run_yaml_path.exists():
        print(f"Error: {run_id} has no run.yaml", file=sys.stderr)
        sys.exit(1)

    run_data = read_yaml(run_yaml_path)
    exp = run_data.get("experiment", {})
    exp_type = exp.get("type", "single")
    results = run_data.get("results", {})
    artifacts = run_data.get("artifacts", {})
    tags = run_data.get("tags", [])
    provenance = run_data.get("provenance", {})

    # Determine event name
    if error:
        name = "swarm/run.failed"
    elif event_name:
        name = event_name
    else:
        status = results.get("status", "completed")
        if status == "failed":
            name = "swarm/run.failed"
        else:
            name = TYPE_EVENT_MAP.get(exp_type, "swarm/run.completed")

    # Build event data
    data = {
        "run_id": run_id,
        "experiment_type": exp_type,
        "status": results.get("status", "completed"),
        "run_yaml_path": f"runs/{run_id}/run.yaml",
        "tags": tags,
    }

    # Add type-specific fields
    if name == "swarm/run.failed":
        data["error"] = error or results.get("error", "unknown")
        data["status"] = "failed"

    elif name == "swarm/sweep.completed":
        data["swept_parameters"] = exp.get("swept_parameters", {})
        data["total_runs"] = exp.get("total_runs", 0)

        # Read summary for hypothesis counts
        summary_rel = artifacts.get("summary", "summary.json")
        summary = read_json_safe(run_path / summary_rel)
        data["total_hypotheses"] = summary.get("total_hypotheses", 0)
        data["bonferroni_significant"] = summary.get("n_bonferroni_significant", 0)

        if artifacts.get("summary"):
            data["summary_path"] = f"runs/{run_id}/{artifacts['summary']}"
        if artifacts.get("sweep_csv"):
            data["sweep_csv_path"] = f"runs/{run_id}/{artifacts['sweep_csv']}"

        p_audit = summary.get("p_hacking_audit", {})
        if p_audit:
            data["p_hacking_audit"] = p_audit

    elif name == "swarm/redteam.completed":
        report_rel = artifacts.get("summary", "report.json")
        report = read_json_safe(run_path / report_rel)
        robustness = report.get("robustness", report)
        data["attacks_tested"] = robustness.get("attacks_tested", 0)
        data["attacks_successful"] = robustness.get("attacks_successful", 0)
        data["robustness_score"] = robustness.get("robustness_score")
        data["grade"] = robustness.get("grade")
        data["critical_vulnerabilities"] = len([
            v for v in robustness.get("vulnerabilities", [])
            if v.get("severity") == "critical"
        ])
        data["report_path"] = f"runs/{run_id}/{report_rel}"

    else:  # swarm/run.completed
        if artifacts.get("summary"):
            data["summary_path"] = f"runs/{run_id}/{artifacts['summary']}"
        data["artifacts"] = {k: v for k, v in artifacts.items() if v}

        # Add primary metric if available
        primary = results.get("primary_metric")
        if primary:
            data["primary_metric"] = primary
        findings = results.get("significant_findings")
        if findings:
            data["significant_findings"] = findings

    return {
        "name": name,
        "data": data,
        "ts": int(datetime.now(timezone.utc).timestamp() * 1000),
    }


def send_event(event: dict) -> bool:
    """Send an event to the Inngest API."""
    payload = json.dumps(event).encode("utf-8")

    req = Request(
        INNGEST_URL,
        data=payload,
        headers={"Content-Type": "application/json"},
        method="POST",
    )

    try:
        with urlopen(req, timeout=10) as resp:
            status = resp.status
            body = resp.read().decode("utf-8")
            if status >= 200 and status < 300:
                return True
            else:
                print(f"Inngest returned {status}: {body}", file=sys.stderr)
                return False
    except URLError as e:
        print(f"Failed to reach Inngest at {INNGEST_URL}: {e}", file=sys.stderr)
        return False


def main():
    parser = argparse.ArgumentParser(
        description="Emit a SWARM event to Inngest"
    )
    parser.add_argument("run_id", help="Run ID to emit event for")
    parser.add_argument("--event", type=str, help="Override event name")
    parser.add_argument("--error", type=str, help="Error message (implies swarm/run.failed)")
    parser.add_argument("--dry-run", action="store_true", help="Print event without sending")
    parser.add_argument("--url", type=str, help="Override Inngest URL")
    args = parser.parse_args()

    global INNGEST_URL
    if args.url:
        INNGEST_URL = args.url

    event = build_event(args.run_id, event_name=args.event, error=args.error)

    if args.dry_run:
        print(json.dumps(event, indent=2, default=str))
        return

    print(f"Emitting {event['name']} for {args.run_id} → {INNGEST_URL}")
    if send_event(event):
        print("Event sent successfully")
    else:
        print("Failed to send event", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
