#!/usr/bin/env python3
"""Detect and visualize run lineage chains across the experiment archive.

Scans runs/<run_id>/run.yaml files, groups them by base concept, and reports
version progressions, seed series, reproduction chains, and temporal ordering.

Usage:
    python scripts/run-provenance.py                    # human-readable report
    python scripts/run-provenance.py --format mermaid   # Mermaid timeline
    python scripts/run-provenance.py --format json      # JSON lineage data
    python scripts/run-provenance.py --chain <concept>  # focus on one chain
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from datetime import datetime
from pathlib import Path
from typing import Any

try:
    import yaml
except ImportError:
    sys.exit("pyyaml is required: pip install pyyaml")

ROOT = Path(__file__).parent.parent
RUNS_DIR = ROOT / "runs"

# ---------------------------------------------------------------------------
# Slug normalisation
# ---------------------------------------------------------------------------

# Matches a leading date-time prefix like 20260210-211721_
DATE_PREFIX_RE = re.compile(r"^\d{8}-\d{6}_")
# Matches trailing _seed<N>
SEED_SUFFIX_RE = re.compile(r"_seed\d+$")
# Matches trailing version markers: _v2, _v3, _v4_code (captures version num)
VERSION_RE = re.compile(r"_v(\d+)(?:_[a-z]+)?$")
# Matches reproduce_ prefix and its id
REPRODUCE_RE = re.compile(r"^reproduce_(.+)$")
# Matches _optimized / _tuned / _fast suffixes before version/seed
VARIANT_SUFFIX_RE = re.compile(r"_(optimized|tuned|fast|strict|relaxed)(?=_|$)")


def parse_run_yaml(path: Path) -> dict[str, Any] | None:
    """Load a run.yaml, returning None on any parse error."""
    try:
        with open(path) as fh:
            return yaml.safe_load(fh)
    except Exception:
        return None


def extract_seed(slug: str) -> int | None:
    """Return the seed number from a slug, or None."""
    m = SEED_SUFFIX_RE.search(slug)
    return int(m.group(0).replace("_seed", "")) if m else None


def extract_version(slug: str) -> int | None:
    """Return the version number from a slug, or None.
    Strip seed suffix first so 'foo_v2_seed42' is detected as v2."""
    deseed = SEED_SUFFIX_RE.sub("", slug)
    m = VERSION_RE.search(deseed)
    return int(m.group(1)) if m else None


def strip_to_base(slug: str) -> str:
    """Strip seed suffix, version suffix, and variant modifiers to get the
    base concept.  E.g. 'adversarial_redteam_optimized_seed42' -> 'adversarial_redteam'."""
    s = slug
    s = SEED_SUFFIX_RE.sub("", s)
    s = VERSION_RE.sub("", s)
    s = VARIANT_SUFFIX_RE.sub("", s)
    return s


def classify_run(slug: str) -> str:
    """Return a short label: 'reproduce', 'seed-variant', 'version', or 'base'."""
    if REPRODUCE_RE.match(slug):
        return "reproduce"
    has_ver = extract_version(slug) is not None
    has_seed = extract_seed(slug) is not None
    if has_ver and has_seed:
        return "version+seed"
    if has_ver:
        return "version"
    if has_seed:
        return "seed-variant"
    return "base"


# ---------------------------------------------------------------------------
# Run record
# ---------------------------------------------------------------------------

class RunRecord:
    """Thin wrapper around a parsed run.yaml with derived fields."""

    def __init__(self, data: dict[str, Any], run_dir: str):
        self.data = data
        self.run_id: str = data.get("run_id", run_dir)
        self.slug: str = data.get("slug", run_dir)
        self.created: datetime | None = self._parse_date(data.get("created_utc"))
        self.seed = extract_seed(self.slug)
        self.version = extract_version(self.slug)
        self.base_concept = strip_to_base(self.slug)
        self.kind = classify_run(self.slug)
        self.exp_type: str = (data.get("experiment") or {}).get("type", "unknown")
        self.seeds: list[int] = (data.get("experiment") or {}).get("seeds", [])
        self.status: str = (data.get("results") or {}).get("status", "unknown")
        self.tags: list[str] = data.get("tags", [])
        self.based_on: str | None = data.get("based_on") or data.get("prior_run")
        self.parent_runs: list[str] = ((data.get("links") or {}).get("parent_runs") or [])

    @staticmethod
    def _parse_date(raw: str | None) -> datetime | None:
        if not raw:
            return None
        try:
            return datetime.fromisoformat(str(raw))
        except (ValueError, TypeError):
            return None

    @property
    def date_str(self) -> str:
        return self.created.strftime("%Y-%m-%d %H:%M") if self.created else "unknown"

    def param_summary(self) -> dict[str, Any]:
        """Return experiment-level params useful for diffing."""
        exp = self.data.get("experiment") or {}
        out: dict[str, Any] = {}
        for key in ("type", "scenario_ref", "seeds", "total_runs"):
            if key in exp:
                out[key] = exp[key]
        if "scenario_sha256" in exp:
            out["scenario_sha256"] = exp["scenario_sha256"]
        return out


# ---------------------------------------------------------------------------
# Chain builder
# ---------------------------------------------------------------------------

class LineageChain:
    """A group of runs sharing the same base concept."""

    def __init__(self, base_concept: str):
        self.base_concept = base_concept
        self.runs: list[RunRecord] = []

    def add(self, rec: RunRecord) -> None:
        self.runs.append(rec)

    def sort(self) -> None:
        self.runs.sort(key=lambda r: (r.created or datetime.min, r.version or 0))

    @property
    def seed_coverage(self) -> list[int]:
        seeds: set[int] = set()
        for r in self.runs:
            if r.seed is not None:
                seeds.add(r.seed)
            seeds.update(r.seeds)
        return sorted(seeds)

    @property
    def version_range(self) -> str:
        versions = sorted(v for r in self.runs if (v := r.version) is not None)
        if not versions:
            return ""
        return f"v{versions[0]}..v{versions[-1]}"

    def param_diffs(self) -> list[str]:
        """Return human-readable diffs between consecutive versioned runs."""
        versioned = [r for r in self.runs if r.version is not None]
        versioned.sort(key=lambda r: r.version or 0)
        diffs: list[str] = []
        for i in range(1, len(versioned)):
            prev, curr = versioned[i - 1], versioned[i]
            pp, cp = prev.param_summary(), curr.param_summary()
            changes: list[str] = []
            all_keys = sorted(set(pp) | set(cp))
            for k in all_keys:
                if pp.get(k) != cp.get(k):
                    changes.append(f"  {k}: {pp.get(k)!r} -> {cp.get(k)!r}")
            if changes:
                label = f"v{prev.version} -> v{curr.version}"
                diffs.append(f"{label}:\n" + "\n".join(changes))
        return diffs


def load_all_runs() -> list[RunRecord]:
    """Scan RUNS_DIR and load every run.yaml found."""
    records: list[RunRecord] = []
    if not RUNS_DIR.is_dir():
        return records
    for entry in sorted(RUNS_DIR.iterdir()):
        if not entry.is_dir() or entry.name.startswith("_"):
            continue
        run_yaml = entry / "run.yaml"
        if not run_yaml.exists():
            continue
        data = parse_run_yaml(run_yaml)
        if data is None:
            continue
        records.append(RunRecord(data, entry.name))
    return records


def build_chains(records: list[RunRecord]) -> dict[str, LineageChain]:
    """Group runs into lineage chains by base concept."""
    chains: dict[str, LineageChain] = {}
    reproduce_map: dict[str, RunRecord] = {}

    for rec in records:
        # Handle reproduce runs — try to link them to a known concept
        m = REPRODUCE_RE.match(rec.slug)
        if m:
            reproduce_map[rec.run_id] = rec

        concept = rec.base_concept
        if concept not in chains:
            chains[concept] = LineageChain(concept)
        chains[concept].add(rec)

    # Also check explicit references (based_on / prior_run / parent_runs)
    id_to_rec = {r.run_id: r for r in records}
    for rec in records:
        refs = []
        if rec.based_on:
            refs.append(rec.based_on)
        refs.extend(rec.parent_runs)
        for ref in refs:
            parent = id_to_rec.get(ref)
            if parent and parent.base_concept != rec.base_concept:
                # Cross-link: ensure parent chain also lists this run
                concept = parent.base_concept
                if concept not in chains:
                    chains[concept] = LineageChain(concept)
                if rec not in chains[concept].runs:
                    chains[concept].add(rec)

    for chain in chains.values():
        chain.sort()

    # Filter out singleton chains with no interesting lineage
    return {k: v for k, v in chains.items() if len(v.runs) > 1}


# ---------------------------------------------------------------------------
# Output formatters
# ---------------------------------------------------------------------------

def format_text(chains: dict[str, LineageChain], focus: str | None) -> str:
    """Human-readable report."""
    selected = _select(chains, focus)
    lines: list[str] = []
    lines.append(f"Run Provenance Report  ({len(selected)} chain(s))\n{'=' * 60}")

    for concept, chain in sorted(selected.items()):
        lines.append(f"\n--- {concept} ---")
        vr = chain.version_range
        sc = chain.seed_coverage
        lines.append(f"  Runs: {len(chain.runs)}  |  Versions: {vr or 'none'}  |  Seeds: {sc or 'none'}")
        for r in chain.runs:
            seed_part = f"  seed={r.seed}" if r.seed is not None else ""
            ver_part = f"  v{r.version}" if r.version is not None else ""
            lines.append(
                f"  [{r.date_str}]  {r.run_id}  ({r.kind}{ver_part}{seed_part})  [{r.status}]"
            )
        diffs = chain.param_diffs()
        if diffs:
            lines.append("  Parameter changes:")
            for d in diffs:
                for dl in d.split("\n"):
                    lines.append(f"    {dl}")
    return "\n".join(lines)


def format_mermaid(chains: dict[str, LineageChain], focus: str | None) -> str:
    """Mermaid timeline diagram."""
    selected = _select(chains, focus)
    lines: list[str] = ["timeline", "  title Run Lineage"]

    for concept, chain in sorted(selected.items()):
        lines.append(f"  section {concept}")
        for r in chain.runs:
            label = r.slug
            if r.version is not None:
                label += f" (v{r.version})"
            if r.seed is not None:
                label += f" [s{r.seed}]"
            date = r.created.strftime("%Y-%m-%d") if r.created else "unknown"
            lines.append(f"    {date} : {label}")
    return "\n".join(lines)


def format_json(chains: dict[str, LineageChain], focus: str | None) -> str:
    """JSON lineage data."""
    selected = _select(chains, focus)
    out: dict[str, Any] = {}
    for concept, chain in sorted(selected.items()):
        out[concept] = {
            "run_count": len(chain.runs),
            "version_range": chain.version_range or None,
            "seed_coverage": chain.seed_coverage,
            "param_diffs": chain.param_diffs(),
            "runs": [
                {
                    "run_id": r.run_id,
                    "slug": r.slug,
                    "created_utc": r.date_str,
                    "kind": r.kind,
                    "version": r.version,
                    "seed": r.seed,
                    "status": r.status,
                    "experiment_type": r.exp_type,
                    "tags": r.tags,
                }
                for r in chain.runs
            ],
        }
    return json.dumps(out, indent=2)


def _select(chains: dict[str, LineageChain], focus: str | None) -> dict[str, LineageChain]:
    if focus is None:
        return chains
    # Exact match first, then substring
    if focus in chains:
        return {focus: chains[focus]}
    matches = {k: v for k, v in chains.items() if focus in k}
    if matches:
        return matches
    print(f"Warning: no chain matching '{focus}'. Showing all.", file=sys.stderr)
    return chains


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Detect and visualize run lineage chains."
    )
    parser.add_argument(
        "--format",
        choices=["text", "mermaid", "json"],
        default="text",
        help="Output format (default: text)",
    )
    parser.add_argument(
        "--chain",
        metavar="CONCEPT",
        default=None,
        help="Focus on a single base concept (substring match supported)",
    )
    args = parser.parse_args()

    records = load_all_runs()
    if not records:
        print("No runs found in", RUNS_DIR, file=sys.stderr)
        sys.exit(1)

    chains = build_chains(records)
    if not chains:
        print("No lineage chains detected (all runs are singletons).", file=sys.stderr)
        sys.exit(0)

    formatters = {
        "text": format_text,
        "mermaid": format_mermaid,
        "json": format_json,
    }
    print(formatters[args.format](chains, args.chain))


if __name__ == "__main__":
    main()
