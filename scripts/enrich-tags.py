#!/usr/bin/env python3
"""
Enrich run tags by mining content from summary data, scenario files,
and folder names.

Many runs only have 1-2 tags from the folder name. This script reads
the actual data to add semantic tags, improving claim-matching overlap.

Usage:
    python scripts/enrich-tags.py              # enrich all runs
    python scripts/enrich-tags.py --run-id <id> # enrich a specific run
    python scripts/enrich-tags.py --dry-run     # preview without writing
"""

import argparse
import json
import re
import sys
from pathlib import Path

import yaml


ROOT = Path(__file__).parent.parent
RUNS_DIR = ROOT / "runs"

# ── Tag inference rules ──────────────────────────────────────────────────

# Governance parameter → tag
GOVERNANCE_TAGS = {
    "transaction_tax_rate": "transaction-tax",
    "circuit_breaker_enabled": "circuit-breaker",
    "audit_enabled": "audit",
    "audit_probability": "audit",
    "staking_enabled": "staking",
    "collusion_detection_enabled": "collusion-detection",
    "reputation_decay_rate": "reputation",
    "freeze_threshold": "circuit-breaker",
    "freeze_duration": "circuit-breaker",
}

# Metric keywords → tag
METRIC_TAGS = {
    "welfare": "welfare",
    "toxicity": "toxicity",
    "acceptance": "acceptance",
    "quality_gap": "quality",
    "collusion": "collusion",
    "reputation": "reputation",
    "payoff": "payoff",
    "robustness": "robustness",
    "evasion": "evasion",
    "damage": "damage",
    "cooperation": "cooperation",
}

# Topology keywords
TOPOLOGY_TAGS = {
    "small_world": "small-world",
    "ring": "ring",
    "random": "random-graph",
    "complete": "complete-graph",
    "scale_free": "scale-free",
}

# Agent type tags
AGENT_TAGS = {
    "honest": "honest-agents",
    "adversarial": "adversarial-agents",
    "adaptive_adversary": "adaptive-adversary",
    "adaptive": "adaptive-adversary",
}


def read_yaml_safe(path: Path) -> dict:
    try:
        with open(path) as f:
            return yaml.safe_load(f) or {}
    except (FileNotFoundError, yaml.YAMLError):
        return {}


def read_json_safe(path: Path) -> dict | list:
    try:
        with open(path) as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        return {}


def enrich_from_swept_parameters(swept: dict | list) -> set[str]:
    """Extract tags from swept parameter names."""
    tags = set()
    if isinstance(swept, list):
        swept = {p: [] for p in swept}
    for param in swept.keys():
        param_lower = param.lower()
        for keyword, tag in GOVERNANCE_TAGS.items():
            if keyword in param_lower:
                tags.add(tag)
        # Generic: extract the leaf parameter name
        leaf = param.split(".")[-1]
        if leaf not in ("enabled", "rate"):
            tags.add(leaf.replace("_", "-"))
    return tags


def enrich_from_scenario(scenario: dict) -> set[str]:
    """Extract tags from scenario content."""
    tags = set()

    # Governance parameters
    gov = scenario.get("governance", {})
    for param, val in gov.items():
        param_lower = param.lower()
        for keyword, tag in GOVERNANCE_TAGS.items():
            if keyword in param_lower:
                # Only tag if the governance mechanism is active
                if isinstance(val, bool) and val:
                    tags.add(tag)
                elif isinstance(val, (int, float)) and val > 0:
                    tags.add(tag)
                break

    # Network topology
    network = scenario.get("network", {})
    topo = network.get("topology", "")
    if topo in TOPOLOGY_TAGS:
        tags.add(TOPOLOGY_TAGS[topo])
    if network.get("dynamic"):
        tags.add("dynamic-network")

    # Agent types
    for agent in scenario.get("agents", []):
        agent_type = agent.get("type", "").lower()
        if agent_type in AGENT_TAGS:
            tags.add(AGENT_TAGS[agent_type])

    # Motif
    motif = scenario.get("motif", "").lower()
    if "red-team" in motif or "redteam" in motif:
        tags.add("redteam")
    if "governance" in motif:
        tags.add("governance")

    return tags


def enrich_from_summary(summary: dict, exp_type: str) -> set[str]:
    """Extract tags from summary content."""
    tags = set()

    if exp_type == "sweep":
        # Tag metrics that appear in significant results
        results = summary.get("results", [])
        for r in results:
            if r.get("bonferroni_sig") or r.get("bh_sig"):
                metric = r.get("metric", "").lower()
                for keyword, tag in METRIC_TAGS.items():
                    if keyword in metric:
                        tags.add(tag)
                # Tag the parameter being swept
                param = r.get("parameter", "")
                for keyword, tag in GOVERNANCE_TAGS.items():
                    if keyword in param.lower():
                        tags.add(tag)

    elif exp_type == "redteam":
        robustness = summary.get("robustness", summary)
        vulns = robustness.get("vulnerabilities", [])
        for v in vulns:
            vector = v.get("attack_vector", "").lower()
            if vector:
                tags.add(f"attack-{vector}")
            lever = v.get("affected_lever", "").lower()
            for keyword, tag in GOVERNANCE_TAGS.items():
                if keyword in lever:
                    tags.add(tag)

    elif exp_type == "study":
        # Tag the studied parameter
        param = summary.get("parameter")
        if param:
            tags.add(param.replace("_", "-"))

        # Tag significant metrics
        pairwise = summary.get("pairwise_tests", [])
        for p in pairwise:
            if p.get("bonferroni_sig") or p.get("significant_bonferroni"):
                metric = p.get("metric", "").lower()
                for keyword, tag in METRIC_TAGS.items():
                    if keyword in metric:
                        tags.add(tag)

    return tags


def enrich_from_folder_name(slug: str) -> set[str]:
    """Extract additional tags from folder name patterns."""
    tags = set()
    slug_lower = slug.lower()

    # Domain-specific keywords
    domain_keywords = {
        "welfare": "welfare",
        "toxicity": "toxicity",
        "circuit_breaker": "circuit-breaker",
        "circuit-breaker": "circuit-breaker",
        "tax": "transaction-tax",
        "audit": "audit",
        "staking": "staking",
        "reputation": "reputation",
        "freeze": "circuit-breaker",
        "memory": "memory",
        "recursive": "recursive-reasoning",
        "acausality": "acausal-reasoning",
        "acausal": "acausal-reasoning",
        "decision_theory": "decision-theory",
        "decision-theory": "decision-theory",
        "large_pop": "population-scaling",
        "large-pop": "population-scaling",
    }

    for keyword, tag in domain_keywords.items():
        if keyword in slug_lower:
            tags.add(tag)

    return tags


def enrich_run(run_path: Path, dry_run: bool = False) -> tuple[int, list[str]]:
    """Enrich tags for a single run. Returns (new_tag_count, new_tags)."""
    run_yaml_path = run_path / "run.yaml"
    if not run_yaml_path.exists():
        return 0, []

    run_data = read_yaml_safe(run_yaml_path)
    existing_tags = set(run_data.get("tags", []))
    exp_type = run_data.get("experiment", {}).get("type", "single")
    slug = run_data.get("slug", run_path.name)

    new_tags = set()

    # 1. Enrich from swept parameters
    swept = run_data.get("experiment", {}).get("swept_parameters", {})
    if swept:
        new_tags |= enrich_from_swept_parameters(swept)

    # 2. Enrich from scenario.yaml
    scenario_path = run_path / "scenario.yaml"
    if scenario_path.exists():
        scenario = read_yaml_safe(scenario_path)
        new_tags |= enrich_from_scenario(scenario)

    # 3. Enrich from summary data
    summary_rel = run_data.get("artifacts", {}).get("summary")
    if summary_rel:
        summary = read_json_safe(run_path / summary_rel)
        if isinstance(summary, dict):
            new_tags |= enrich_from_summary(summary, exp_type)

    # Also check analysis/summary.json for studies
    if exp_type == "study":
        analysis_summary = read_json_safe(run_path / "analysis" / "summary.json")
        if isinstance(analysis_summary, dict):
            new_tags |= enrich_from_summary(analysis_summary, exp_type)

    # 4. Enrich from folder name
    new_tags |= enrich_from_folder_name(slug)

    # 5. Add experiment type as tag
    new_tags.add(exp_type)

    # Filter out tags we already have
    actually_new = new_tags - existing_tags
    # Filter out empty or very short tags
    actually_new = {t for t in actually_new if len(t) >= 2}

    if actually_new and not dry_run:
        all_tags = sorted(existing_tags | actually_new)
        run_data["tags"] = all_tags
        with open(run_yaml_path, "w") as f:
            yaml.dump(run_data, f, default_flow_style=False, sort_keys=False)

    return len(actually_new), sorted(actually_new)


def main():
    parser = argparse.ArgumentParser(description="Enrich run tags from content")
    parser.add_argument("--run-id", type=str, help="Enrich a specific run")
    parser.add_argument("--dry-run", action="store_true", help="Preview without writing")
    args = parser.parse_args()

    if args.run_id:
        targets = [RUNS_DIR / args.run_id]
    else:
        targets = sorted(p for p in RUNS_DIR.iterdir() if p.is_dir() and not p.name.startswith("_"))

    total_enriched = 0
    total_new_tags = 0

    for run_path in targets:
        count, new_tags = enrich_run(run_path, dry_run=args.dry_run)
        if count > 0:
            prefix = "WOULD ADD" if args.dry_run else "ENRICHED"
            print(f"  {prefix}: {run_path.name} (+{count}): {', '.join(new_tags)}")
            total_enriched += 1
            total_new_tags += count

    print(f"\nDone: {total_enriched} runs enriched, {total_new_tags} new tags added")


if __name__ == "__main__":
    main()
