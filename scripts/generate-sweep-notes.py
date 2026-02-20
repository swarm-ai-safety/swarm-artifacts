#!/usr/bin/env python3
"""
Generate sweep summary notes in vault/sweeps/.

Groups runs that sweep the same parameter and generates cross-run
aggregation notes showing convergence across sweeps.

Usage:
    python scripts/generate-sweep-notes.py              # generate all
    python scripts/generate-sweep-notes.py --dry-run    # preview
    python scripts/generate-sweep-notes.py --force      # overwrite existing
"""

import argparse
import json
import re
import sys
from collections import defaultdict
from datetime import date
from pathlib import Path

import yaml


ROOT = Path(__file__).parent.parent
RUNS_DIR = ROOT / "runs"
VAULT_DIR = ROOT / "vault"
SWEEPS_DIR = VAULT_DIR / "sweeps"


def read_yaml_safe(path: Path) -> dict:
    try:
        with open(path) as f:
            return yaml.safe_load(f) or {}
    except (FileNotFoundError, yaml.YAMLError):
        return {}


def read_json_safe(path: Path) -> dict:
    try:
        with open(path) as f:
            data = json.load(f)
            return data if isinstance(data, dict) else {}
    except (FileNotFoundError, json.JSONDecodeError):
        return {}


def slugify(text: str) -> str:
    text = text.lower().strip()
    text = re.sub(r"[^a-z0-9\s._\-]", "", text)
    text = re.sub(r"[\s._]+", "-", text)
    return text[:80]


def discover_sweep_series() -> dict[str, list[dict]]:
    """Group sweep/study runs by their primary swept parameter."""
    series = defaultdict(list)

    for run_path in sorted(RUNS_DIR.iterdir()):
        if not run_path.is_dir() or run_path.name.startswith("_"):
            continue

        run_yaml = read_yaml_safe(run_path / "run.yaml")
        exp = run_yaml.get("experiment", {})
        exp_type = exp.get("type", "single")

        if exp_type not in ("sweep", "study"):
            continue

        swept = exp.get("swept_parameters", {})
        if not swept:
            continue

        # swept_parameters can be a dict or a list of param names
        if isinstance(swept, list):
            primary_param = swept[0] if swept else None
            swept = {p: [] for p in swept}
        else:
            primary_param = list(swept.keys())[0]

        if not primary_param:
            continue

        # Read summary for result counts
        summary_rel = run_yaml.get("artifacts", {}).get("summary", "summary.json")
        summary = read_json_safe(run_path / summary_rel)
        if not summary and exp_type == "study":
            summary = read_json_safe(run_path / "analysis" / "summary.json")

        series[primary_param].append({
            "run_id": run_yaml.get("run_id", run_path.name),
            "slug": run_yaml.get("slug", ""),
            "created_utc": run_yaml.get("created_utc", ""),
            "type": exp_type,
            "swept_parameters": swept,
            "total_runs": exp.get("total_runs") or summary.get("total_runs", "?"),
            "seeds": exp.get("seeds", []),
            "values": swept.get(primary_param, []),
            "n_bonferroni": summary.get("n_bonferroni_significant", 0),
            "n_hypotheses": summary.get("total_hypotheses", 0),
            "tags": run_yaml.get("tags", []),
        })

    return dict(series)


def generate_sweep_note(param: str, runs: list[dict], force: bool = False) -> bool:
    """Generate a sweep summary note. Returns True if note was created."""
    if len(runs) < 1:
        return False

    note_name = f"sweep-{slugify(param)}"
    note_path = SWEEPS_DIR / f"{note_name}.md"

    if note_path.exists() and not force:
        return False

    # Sort runs by date
    runs_sorted = sorted(runs, key=lambda r: r.get("created_utc", ""))

    # Build runs table
    run_rows = []
    for r in runs_sorted:
        created = str(r["created_utc"])[:10] if r["created_utc"] else "?"
        n_values = len(r["values"]) if isinstance(r["values"], list) else "?"
        n_seeds = len(r["seeds"]) if isinstance(r["seeds"], list) else "?"
        bonf = r.get("n_bonferroni", 0)
        run_rows.append(
            f"| {r['run_id']} | {created} | {r['type']} | "
            f"{n_seeds} | {n_values} | {r['total_runs']} | {bonf} |"
        )
    runs_table = (
        "| Run ID | Date | Type | Seeds | Levels | Total Runs | Bonferroni Sig |\n"
        "|--------|------|------|-------|--------|------------|----------------|\n"
        + "\n".join(run_rows)
    )

    # Values tested across all runs
    all_values = set()
    for r in runs:
        vals = r.get("values", [])
        if isinstance(vals, list):
            for v in vals:
                all_values.add(str(v))
    values_str = ", ".join(sorted(all_values, key=lambda x: float(x) if x.replace(".", "").replace("-", "").isdigit() else 0))

    # Convergence analysis
    total_runs_sum = sum(r["total_runs"] for r in runs if isinstance(r["total_runs"], (int, float)))
    max_bonf = max((r.get("n_bonferroni", 0) for r in runs), default=0)

    # Collect all tags
    all_tags = set()
    for r in runs:
        all_tags.update(r.get("tags", []))

    # Description
    param_short = param.split(".")[-1].replace("_", " ")
    description = f"Sweep series for {param_short}: {len(runs)} runs, {total_runs_sum} total configurations"
    if len(description) > 200:
        description = description[:197] + "..."

    # Frontmatter
    fm = {
        "description": description,
        "type": "sweep-summary",
        "status": "active",
        "parameter": param,
        "values_tested": sorted(all_values) if all_values else [],
        "created": runs_sorted[0].get("created_utc", "")[:10] if runs_sorted else str(date.today()),
        "updated": str(date.today()),
    }

    fm_yaml = yaml.dump(fm, default_flow_style=False, sort_keys=False).strip()
    topic_tags = ", ".join(sorted(all_tags)) if all_tags else "sweep"

    note = f"""\
---
{fm_yaml}
---

# {param_short} sweep series shows {"significant" if max_bonf > 0 else "no significant"} effects across {len(runs)} independent runs

## Runs in this sweep

{runs_table}

## Values tested

`{param}`: {values_str}

## Convergence

{len(runs)} runs have explored this parameter with a combined {total_runs_sum} configurations.
{"Effect is robust: Bonferroni-significant findings replicated across runs." if max_bonf > 0 else "No Bonferroni-significant findings yet. More power may be needed."}

## Open questions

- Has the parameter space been fully covered?
- Are there interaction effects with other parameters?
- Do results generalize across topologies?

---

Topics:
- [[_index]]

<!-- topics: {topic_tags} -->
"""

    SWEEPS_DIR.mkdir(parents=True, exist_ok=True)
    note_path.write_text(note, encoding="utf-8")
    return True


def main():
    parser = argparse.ArgumentParser(description="Generate sweep summary notes")
    parser.add_argument("--dry-run", action="store_true", help="Preview without writing")
    parser.add_argument("--force", action="store_true", help="Overwrite existing notes")
    args = parser.parse_args()

    series = discover_sweep_series()

    if not series:
        print("No sweep series found")
        return

    print(f"Discovered {len(series)} sweep series:\n")

    created = 0
    skipped = 0

    for param, runs in sorted(series.items()):
        print(f"  {param}: {len(runs)} runs")
        for r in runs:
            print(f"    - {r['run_id']} ({r['total_runs']} configs)")

        if args.dry_run:
            continue

        if generate_sweep_note(param, runs, force=args.force):
            note_name = f"sweep-{slugify(param)}"
            print(f"    → CREATED: vault/sweeps/{note_name}.md")
            created += 1
        else:
            print(f"    → skipped (already exists)")
            skipped += 1

    print(f"\nDone: {created} created, {skipped} skipped")


if __name__ == "__main__":
    main()
