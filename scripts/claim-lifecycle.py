#!/usr/bin/env python3
"""
Claim lifecycle auditor — detect when new evidence should update claim statuses.

Scans runs/ for uncited relevant evidence and recommends status/confidence
changes for claims in vault/claims/.

Usage:
    python scripts/claim-lifecycle.py                  # report all claims
    python scripts/claim-lifecycle.py --claim <id>     # report one claim
    python scripts/claim-lifecycle.py --json           # JSON output
    python scripts/claim-lifecycle.py --auto-update    # update claim frontmatter
"""

import argparse
import json
import re
import sys
from datetime import date
from pathlib import Path

import yaml

ROOT = Path(__file__).parent.parent
RUNS_DIR = ROOT / "runs"
VAULT_DIR = ROOT / "vault"
CLAIMS_DIR = VAULT_DIR / "claims"

# ---------------------------------------------------------------------------
# Parsing helpers
# ---------------------------------------------------------------------------

def parse_frontmatter(path: Path) -> dict | None:
    """Extract YAML frontmatter from a markdown file."""
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return None
    match = re.match(r"^---\n(.+?)\n---", text, re.DOTALL)
    if not match:
        return None
    try:
        data = yaml.safe_load(match.group(1))
    except yaml.YAMLError:
        return None
    if not isinstance(data, dict):
        return None
    # Normalize date objects to strings
    from datetime import date as _date, datetime as _datetime
    for key in ("created", "updated"):
        if key in data and isinstance(data[key], (_date, _datetime)):
            data[key] = data[key].isoformat()
    return data


def extract_topics(path: Path) -> list[str]:
    """Extract topics from the <!-- topics: ... --> footer of a claim."""
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return []
    m = re.search(r"<!--\s*topics:\s*(.+?)\s*-->", text)
    if m:
        return [t.strip() for t in m.group(1).split(",") if t.strip()]
    # Fallback: visible Topics: line
    m = re.search(r"^Topics:\s*(.+)", text, re.MULTILINE)
    if m:
        return [t.strip() for t in m.group(1).split(",") if t.strip()]
    return []


def load_run_yaml(run_dir: Path) -> dict | None:
    """Load run.yaml from a run directory."""
    run_yaml = run_dir / "run.yaml"
    if not run_yaml.exists():
        return None
    try:
        with open(run_yaml) as f:
            return yaml.safe_load(f)
    except (yaml.YAMLError, OSError):
        return None


def cited_run_ids(claim_fm: dict) -> set[str]:
    """Return set of run IDs already cited in a claim's evidence."""
    ids = set()
    evidence = claim_fm.get("evidence", {})
    if not isinstance(evidence, dict):
        return ids
    for entry in evidence.get("supporting", []) or []:
        if isinstance(entry, dict) and entry.get("run"):
            ids.add(str(entry["run"]))
    for entry in evidence.get("weakening", []) or []:
        if isinstance(entry, dict) and entry.get("run"):
            ids.add(str(entry["run"]))
    return ids


def claim_metrics(claim_fm: dict) -> set[str]:
    """Return set of metric names referenced in the claim's evidence."""
    metrics = set()
    evidence = claim_fm.get("evidence", {})
    if not isinstance(evidence, dict):
        return metrics
    for entry in (evidence.get("supporting", []) or []) + (evidence.get("weakening", []) or []):
        if isinstance(entry, dict) and entry.get("metric"):
            metrics.add(entry["metric"])
    return metrics


def tag_overlap(claim_topics: list[str], run_tags: list[str]) -> int:
    """Count tag overlap between claim topics and run tags."""
    topic_set = {t.lower().replace("_", "-") for t in claim_topics}
    tag_set = {t.lower().replace("_", "-") for t in run_tags}
    return len(topic_set & tag_set)


# ---------------------------------------------------------------------------
# Summary readers — extract significant results from different run types
# ---------------------------------------------------------------------------

def _load_json(path: Path) -> dict | list | None:
    if not path.exists():
        return None
    try:
        with open(path) as f:
            return json.load(f)
    except (json.JSONDecodeError, OSError):
        return None


def extract_sweep_results(run_dir: Path) -> list[dict]:
    """Extract Bonferroni-significant results from a sweep summary."""
    data = _load_json(run_dir / "summary.json")
    if not isinstance(data, dict):
        return []
    results = data.get("results", [])
    if not isinstance(results, list):
        return []
    significant = []
    for r in results:
        if not isinstance(r, dict):
            continue
        if r.get("bonferroni_sig"):
            significant.append({
                "metric": r.get("metric", "unknown"),
                "parameter": r.get("parameter", "unknown"),
                "effect_size": r.get("cohens_d", 0),
                "mean_1": r.get("mean_1"),
                "mean_2": r.get("mean_2"),
                "bonferroni_sig": True,
            })
    return significant


def extract_study_results(run_dir: Path) -> list[dict]:
    """Extract significant results from a study analysis/summary.json or summary.json."""
    # Try analysis/summary.json first, then summary.json
    for rel in ["analysis/summary.json", "summary.json"]:
        data = _load_json(run_dir / rel)
        if not isinstance(data, dict):
            continue
        # Look for pairwise_tests in the data or nested under analysis_summary
        tests = data.get("pairwise_tests", [])
        if not tests and "analysis_summary" in data:
            tests = data["analysis_summary"].get("pairwise_tests", [])
        if not isinstance(tests, list):
            continue
        significant = []
        for t in tests:
            if not isinstance(t, dict):
                continue
            is_sig = t.get("bonferroni_sig") or t.get("significant_bonferroni")
            if is_sig:
                significant.append({
                    "metric": t.get("metric", "unknown"),
                    "parameter": t.get("parameter", t.get("comparison", "unknown")),
                    "effect_size": t.get("cohens_d", t.get("effect_size", 0)),
                    "mean_1": t.get("mean_1"),
                    "mean_2": t.get("mean_2"),
                    "bonferroni_sig": True,
                })
        if significant:
            return significant
    return []


def extract_redteam_results(run_dir: Path) -> list[dict]:
    """Extract vulnerability findings from a redteam run."""
    for fname in ["report.json", "summary.json"]:
        data = _load_json(run_dir / fname)
        if not isinstance(data, dict):
            continue
        # Data may be nested under config names (e.g. "minimal_governance")
        configs = data if not any(isinstance(v, dict) and "robustness" in v for v in data.values()) else data
        vulns = []
        for key, val in configs.items():
            if not isinstance(val, dict):
                continue
            rob = val.get("robustness", {})
            if not isinstance(rob, dict):
                continue
            for v in rob.get("vulnerabilities", []):
                if isinstance(v, dict):
                    vulns.append({
                        "metric": "robustness",
                        "vulnerability": v.get("vulnerability_id", "unknown"),
                        "severity": v.get("severity", "unknown"),
                        "description": v.get("description", ""),
                        "damage": v.get("potential_damage", 0),
                    })
        if vulns:
            return vulns
    return []


def extract_single_results(run_dir: Path) -> list[dict]:
    """Extract metrics from a single run (summary.json or history.json)."""
    for fname in ["summary.json", "history.json"]:
        data = _load_json(run_dir / fname)
        if data is not None:
            # Single runs generally lack statistical tests; just note they exist
            return [{"metric": "single_run", "has_data": True}]
    return []


def extract_run_results(run_dir: Path, experiment_type: str) -> list[dict]:
    """Dispatch to the right extractor based on experiment type."""
    if experiment_type == "sweep":
        return extract_sweep_results(run_dir)
    elif experiment_type == "study":
        return extract_study_results(run_dir)
    elif experiment_type == "redteam":
        return extract_redteam_results(run_dir)
    elif experiment_type == "single":
        return extract_single_results(run_dir)
    else:
        # Try sweep first, then study, then redteam, then single
        for extractor in [extract_sweep_results, extract_study_results,
                          extract_redteam_results, extract_single_results]:
            results = extractor(run_dir)
            if results:
                return results
        return []


# ---------------------------------------------------------------------------
# Evidence detection logic
# ---------------------------------------------------------------------------

def detect_direction(claim_fm: dict) -> str | None:
    """Infer the expected effect direction from supporting evidence detail text.

    Returns 'positive', 'negative', or None if ambiguous.
    """
    evidence = claim_fm.get("evidence", {})
    if not isinstance(evidence, dict):
        return None
    for entry in evidence.get("supporting", []) or []:
        if not isinstance(entry, dict):
            continue
        detail = str(entry.get("detail", ""))
        # Look for explicit effect size direction
        d_match = re.search(r"d\s*=\s*(-?[\d.]+)", detail)
        if d_match:
            d_val = float(d_match.group(1))
            return "positive" if d_val > 0 else "negative"
    return None


def is_contradictory(claim_direction: str | None, result: dict) -> bool:
    """Check if a result contradicts the claim's expected direction."""
    if claim_direction is None:
        return False
    effect = result.get("effect_size", 0)
    if effect is None:
        return False
    try:
        effect = float(effect)
    except (TypeError, ValueError):
        return False
    if claim_direction == "positive" and effect < -0.2:
        return True
    if claim_direction == "negative" and effect > 0.2:
        return True
    return False


def analyze_claim(claim_path: Path, all_runs: dict[str, dict]) -> dict | None:
    """Analyze a single claim against all runs. Returns a report dict or None."""
    fm = parse_frontmatter(claim_path)
    if fm is None:
        return None

    claim_id = claim_path.stem
    topics = extract_topics(claim_path)
    cited = cited_run_ids(fm)
    metrics = claim_metrics(fm)
    direction = detect_direction(fm)

    status = fm.get("status", "unknown")
    confidence = fm.get("confidence", "unknown")

    uncited_relevant = []
    strengthening = []
    weakening = []

    for run_id, run_info in all_runs.items():
        if run_id in cited:
            continue

        run_tags = run_info.get("tags", [])
        overlap = tag_overlap(topics, run_tags)
        if overlap < 2:
            continue

        run_dir = RUNS_DIR / run_id
        exp_type = run_info.get("experiment", {}).get("type", "unknown")
        results = extract_run_results(run_dir, exp_type)

        entry = {
            "run_id": run_id,
            "tag_overlap": overlap,
            "experiment_type": exp_type,
            "overlapping_tags": sorted(
                {t.lower().replace("_", "-") for t in topics}
                & {t.lower().replace("_", "-") for t in run_tags}
            ),
        }
        uncited_relevant.append(entry)

        # Check each significant result
        for r in results:
            r_metric = r.get("metric", "")
            # Match if the run has a Bonferroni-significant result for a metric the claim references
            metric_match = r_metric in metrics or any(
                r_metric.lower() in m.lower() or m.lower() in r_metric.lower()
                for m in metrics
            )

            if r.get("bonferroni_sig"):
                if metric_match:
                    if is_contradictory(direction, r):
                        weakening.append({**entry, "result": r, "reason": "contradicts_direction"})
                    else:
                        strengthening.append({**entry, "result": r, "reason": "bonferroni_significant"})
                else:
                    # Significant result but for a different metric — note it
                    strengthening.append({
                        **entry, "result": r,
                        "reason": "bonferroni_significant_different_metric",
                    })

            elif r.get("vulnerability"):
                # Redteam vulnerabilities may weaken claims about robustness
                if "robustness" in metrics or any(
                    kw in fm.get("description", "").lower()
                    for kw in ["robust", "prevent", "protect", "defend"]
                ):
                    weakening.append({**entry, "result": r, "reason": "vulnerability_found"})

    if not uncited_relevant:
        return None

    # Build recommendations
    recommendations = []

    # Count total supporting runs (cited + new strengthening)
    supporting_cited = len(fm.get("evidence", {}).get("supporting", []) or [])
    supporting_total = supporting_cited + len([
        s for s in strengthening
        if s.get("reason") == "bonferroni_significant"
    ])

    weakening_cited = len(fm.get("evidence", {}).get("weakening", []) or [])
    weakening_total = weakening_cited + len(weakening)

    # Detect replication — recommend confidence upgrade
    if confidence in ("medium", "low") and supporting_total >= 2:
        bonf_supporting = supporting_cited + len([
            s for s in strengthening if s.get("reason") == "bonferroni_significant"
        ])
        if bonf_supporting >= 2:
            next_level = "high" if confidence == "medium" else "medium"
            recommendations.append({
                "action": "upgrade",
                "field": "confidence",
                "from": confidence,
                "to": next_level,
                "reason": f"{bonf_supporting} independent Bonferroni-significant supporting runs",
            })

    # Detect contested status
    if supporting_total >= 1 and weakening_total >= 1 and confidence != "contested":
        recommendations.append({
            "action": "contest",
            "field": "confidence",
            "from": confidence,
            "to": "contested",
            "reason": f"{supporting_total} supporting vs {weakening_total} weakening from independent runs",
        })

    # Flag strengthening evidence to add
    if strengthening:
        recommendations.append({
            "action": "strengthen",
            "detail": f"{len(strengthening)} uncited run(s) with significant results",
            "runs": [s["run_id"] for s in strengthening],
        })

    # Flag weakening evidence to add
    if weakening:
        recommendations.append({
            "action": "weaken",
            "detail": f"{len(weakening)} uncited run(s) with contradictory or vulnerability results",
            "runs": [w["run_id"] for w in weakening],
        })
        if status == "active" and not any(r["action"] == "contest" for r in recommendations):
            recommendations.append({
                "action": "weaken_status",
                "field": "status",
                "from": status,
                "to": "weakened",
                "reason": "new weakening evidence found",
            })

    # If uncited relevant runs exist but no strong signal, flag for review
    if not recommendations:
        recommendations.append({
            "action": "review_needed",
            "detail": f"{len(uncited_relevant)} uncited relevant run(s) found but no clear signal",
        })

    return {
        "claim_id": claim_id,
        "claim_path": str(claim_path),
        "status": status,
        "confidence": confidence,
        "topics": topics,
        "uncited_relevant_runs": uncited_relevant,
        "strengthening": strengthening,
        "weakening": weakening,
        "recommendations": recommendations,
    }


# ---------------------------------------------------------------------------
# Auto-update logic
# ---------------------------------------------------------------------------

def auto_update_claim(claim_path: Path, report: dict) -> list[str]:
    """Apply recommended changes to a claim file. Returns list of changes made."""
    changes = []
    text = claim_path.read_text(encoding="utf-8")
    fm_match = re.match(r"^---\n(.+?)\n---", text, re.DOTALL)
    if not fm_match:
        return ["ERROR: could not parse frontmatter"]

    fm_raw = fm_match.group(1)
    fm = yaml.safe_load(fm_raw)
    if not isinstance(fm, dict):
        return ["ERROR: frontmatter is not a dict"]

    body = text[fm_match.end():]

    # Ensure evidence structure exists
    if "evidence" not in fm or not isinstance(fm["evidence"], dict):
        fm["evidence"] = {"supporting": [], "weakening": []}
    if fm["evidence"].get("supporting") is None:
        fm["evidence"]["supporting"] = []
    if fm["evidence"].get("weakening") is None:
        fm["evidence"]["weakening"] = []

    # Add strengthening evidence
    for s in report.get("strengthening", []):
        if s.get("reason") not in ("bonferroni_significant", "bonferroni_significant_different_metric"):
            continue
        run_id = s["run_id"]
        result = s.get("result", {})
        detail_parts = []
        if result.get("metric"):
            detail_parts.append(f"metric={result['metric']}")
        if result.get("effect_size") is not None:
            detail_parts.append(f"d={result['effect_size']:.2f}")
        if result.get("parameter"):
            detail_parts.append(f"parameter={result['parameter']}")
        detail = ", ".join(detail_parts) if detail_parts else "Bonferroni-significant"
        entry = {"run": run_id, "metric": result.get("metric", "unknown"), "detail": detail}
        fm["evidence"]["supporting"].append(entry)
        changes.append(f"Added supporting evidence from {run_id}")

    # Add weakening evidence
    for w in report.get("weakening", []):
        run_id = w["run_id"]
        result = w.get("result", {})
        reason = w.get("reason", "")
        if reason == "contradicts_direction":
            detail = f"Contradicts claim direction: d={result.get('effect_size', 0):.2f}"
        elif reason == "vulnerability_found":
            detail = f"Vulnerability: {result.get('description', 'unknown')}"
        else:
            detail = "Weakening evidence"
        metric = result.get("metric", "unknown")
        entry = {"run": run_id, "metric": metric, "detail": detail}
        fm["evidence"]["weakening"].append(entry)
        changes.append(f"Added weakening evidence from {run_id}")

    # Apply status/confidence changes
    for rec in report.get("recommendations", []):
        action = rec.get("action")
        if action == "upgrade" and rec.get("field") == "confidence":
            old = fm.get("confidence")
            fm["confidence"] = rec["to"]
            changes.append(f"Upgraded confidence: {old} -> {rec['to']}")
        elif action == "contest" and rec.get("field") == "confidence":
            old = fm.get("confidence")
            fm["confidence"] = "contested"
            changes.append(f"Changed confidence: {old} -> contested")
        elif action == "weaken_status" and rec.get("field") == "status":
            old = fm.get("status")
            fm["status"] = "weakened"
            changes.append(f"Changed status: {old} -> weakened")

    if not changes:
        return []

    # Update the 'updated' field
    fm["updated"] = date.today().isoformat()

    # Reconstruct the file
    # Use block style for readability
    new_fm = yaml.dump(fm, default_flow_style=False, sort_keys=False, allow_unicode=True)
    # Remove trailing newline from dump before wrapping in ---
    new_fm = new_fm.rstrip("\n")

    # Append lifecycle audit section
    today = date.today().isoformat()
    audit_section = f"\n\n## Lifecycle audit\n\n**{today}** — automated claim-lifecycle audit:\n"
    for c in changes:
        audit_section += f"- {c}\n"

    new_text = f"---\n{new_fm}\n---{body}"
    # Append audit section before the topics footer if possible
    topics_match = re.search(r"\n(<!-- topics:.*-->)\s*$", new_text)
    if topics_match:
        insert_pos = topics_match.start()
        new_text = new_text[:insert_pos] + audit_section + new_text[insert_pos:]
    else:
        new_text = new_text.rstrip("\n") + audit_section + "\n"

    claim_path.write_text(new_text, encoding="utf-8")
    return changes


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------

def format_report_text(reports: list[dict]) -> str:
    """Format reports as human-readable text."""
    if not reports:
        return "No claims have uncited relevant evidence.\n"

    lines = []
    lines.append("=" * 72)
    lines.append("CLAIM LIFECYCLE AUDIT")
    lines.append("=" * 72)

    for r in reports:
        lines.append("")
        lines.append(f"Claim: {r['claim_id']}")
        lines.append(f"  Status: {r['status']}  |  Confidence: {r['confidence']}")
        lines.append(f"  Topics: {', '.join(r['topics'])}")
        lines.append("")

        lines.append(f"  Uncited relevant runs ({len(r['uncited_relevant_runs'])}):")
        for u in r["uncited_relevant_runs"]:
            lines.append(
                f"    - {u['run_id']}  (overlap: {u['tag_overlap']} tags: "
                f"{', '.join(u['overlapping_tags'])})"
            )

        if r["strengthening"]:
            lines.append(f"  Strengthening evidence ({len(r['strengthening'])}):")
            for s in r["strengthening"]:
                result = s.get("result", {})
                metric = result.get("metric", "?")
                d = result.get("effect_size", "?")
                lines.append(f"    + {s['run_id']}  metric={metric}  d={d}  [{s['reason']}]")

        if r["weakening"]:
            lines.append(f"  Weakening evidence ({len(r['weakening'])}):")
            for w in r["weakening"]:
                result = w.get("result", {})
                desc = result.get("description", result.get("metric", "?"))
                lines.append(f"    - {w['run_id']}  {desc}  [{w['reason']}]")

        lines.append("")
        lines.append("  Recommendations:")
        for rec in r["recommendations"]:
            action = rec["action"]
            if action in ("upgrade", "contest", "weaken_status"):
                lines.append(
                    f"    >> {action.upper()}: {rec.get('field', '')} "
                    f"{rec.get('from', '')} -> {rec.get('to', '')}  "
                    f"({rec.get('reason', '')})"
                )
            elif action in ("strengthen", "weaken"):
                lines.append(f"    >> {action.upper()}: {rec.get('detail', '')}")
            elif action == "review_needed":
                lines.append(f"    >> REVIEW NEEDED: {rec.get('detail', '')}")
        lines.append("-" * 72)

    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def load_all_runs() -> dict[str, dict]:
    """Load all run.yaml files from runs/."""
    runs = {}
    if not RUNS_DIR.exists():
        return runs
    for run_dir in sorted(RUNS_DIR.iterdir()):
        if not run_dir.is_dir() or run_dir.name.startswith("_"):
            continue
        run_info = load_run_yaml(run_dir)
        if run_info is not None:
            run_id = run_info.get("run_id", run_dir.name)
            runs[str(run_id)] = run_info
    return runs


def main():
    parser = argparse.ArgumentParser(
        description="Claim lifecycle auditor — detect when new evidence should update claim statuses"
    )
    parser.add_argument(
        "--claim", type=str, default=None,
        help="Audit a single claim (stem name, e.g. claim-tax-phase-transition)"
    )
    parser.add_argument(
        "--json", action="store_true", dest="json_output",
        help="Output results as JSON"
    )
    parser.add_argument(
        "--auto-update", action="store_true", dest="auto_update",
        help="Actually update claim frontmatter with new evidence and status changes"
    )
    args = parser.parse_args()

    if not CLAIMS_DIR.exists():
        print(f"ERROR: Claims directory not found: {CLAIMS_DIR}", file=sys.stderr)
        sys.exit(1)

    # Determine which claims to audit
    if args.claim:
        claim_name = args.claim
        if not claim_name.endswith(".md"):
            claim_name += ".md"
        claim_path = CLAIMS_DIR / claim_name
        if not claim_path.exists():
            print(f"ERROR: Claim not found: {claim_path}", file=sys.stderr)
            sys.exit(1)
        claim_paths = [claim_path]
    else:
        claim_paths = sorted(CLAIMS_DIR.glob("claim-*.md"))

    if not claim_paths:
        print("No claim files found.", file=sys.stderr)
        sys.exit(1)

    # Load all runs once
    all_runs = load_all_runs()

    # Analyze each claim
    reports = []
    for cp in claim_paths:
        report = analyze_claim(cp, all_runs)
        if report is not None:
            reports.append(report)

    # Auto-update if requested
    if args.auto_update:
        for report in reports:
            claim_path = Path(report["claim_path"])
            changes = auto_update_claim(claim_path, report)
            if changes:
                report["changes_applied"] = changes
            else:
                report["changes_applied"] = ["No changes needed"]

    # Output
    if args.json_output:
        print(json.dumps(reports, indent=2, default=str))
    else:
        print(format_report_text(reports))
        if args.auto_update:
            updated = [r for r in reports if r.get("changes_applied") and
                       r["changes_applied"] != ["No changes needed"]]
            if updated:
                print(f"\nAuto-updated {len(updated)} claim(s):")
                for r in updated:
                    print(f"  {r['claim_id']}:")
                    for c in r["changes_applied"]:
                        print(f"    - {c}")
            else:
                print("\nNo claims were modified.")


if __name__ == "__main__":
    main()
