#!/usr/bin/env python3
"""
Generate a vault experiment note from a SWARM run.

Reads run.yaml and the appropriate summary file, then writes a Markdown
experiment note to vault/experiments/<run_id>.md following the template
conventions.

Usage:
    python scripts/generate-note.py <run_id>
    python scripts/generate-note.py --all          # all unsynthesized runs
    python scripts/generate-note.py --batch 5      # 5 most recent unsynthesized
    python scripts/generate-note.py <run_id> --force  # overwrite existing note
"""

import argparse
import json
import re
import sys
from datetime import date
from pathlib import Path
from textwrap import dedent

import yaml


ROOT = Path(__file__).parent.parent
RUNS_DIR = ROOT / "runs"
VAULT_DIR = ROOT / "vault"
EXPERIMENTS_DIR = VAULT_DIR / "experiments"
CLAIMS_DIR = VAULT_DIR / "claims"


# ── Helpers ──────────────────────────────────────────────────────────────


def read_yaml(path: Path) -> dict:
    with open(path) as f:
        return yaml.safe_load(f) or {}


def read_json(path: Path) -> dict:
    with open(path) as f:
        return json.load(f)


def parse_frontmatter(path: Path) -> dict | None:
    """Extract YAML frontmatter from a markdown file."""
    text = path.read_text(encoding="utf-8")
    match = re.match(r"^---\n(.+?)\n---", text, re.DOTALL)
    if not match:
        return None
    return yaml.safe_load(match.group(1))


def extract_topics(path: Path) -> list[str]:
    """Extract topics from footer comment or visible Topics: section."""
    text = path.read_text(encoding="utf-8")
    # HTML comment style: <!-- topics: a, b, c -->
    m = re.search(r"<!--\s*topics:\s*(.+?)\s*-->", text)
    if m:
        return [t.strip() for t in m.group(1).split(",")]
    # Visible style: Topics:\n- [[x]]
    topics = re.findall(r"\[\[([^\]]+)\]\]", text)
    return topics


def slugify(text: str) -> str:
    """Convert text to kebab-case slug."""
    text = text.lower().strip()
    text = re.sub(r"[^a-z0-9\s-]", "", text)
    text = re.sub(r"[\s_]+", "-", text)
    return text[:80]


def fmt_pvalue(p: float) -> str:
    """Format p-value for display."""
    if p < 1e-14:
        return "p<1e-14"
    elif p < 0.001:
        return f"p<0.001"
    elif p < 0.01:
        return f"p={p:.4f}"
    else:
        return f"p={p:.3f}"


def fmt_effect(d: float) -> str:
    """Classify effect size."""
    ad = abs(d)
    if ad >= 0.8:
        return "large"
    elif ad >= 0.5:
        return "medium"
    else:
        return "small"


# ── Summary readers (per experiment type) ────────────────────────────────


def read_sweep_summary(run_path: Path, run_data: dict) -> dict:
    """Read sweep summary.json and extract key information."""
    summary_rel = run_data.get("artifacts", {}).get("summary", "summary.json")
    summary_path = run_path / summary_rel
    if not summary_path.exists():
        return {}
    data = read_json(summary_path)

    # Top results by effect size
    results = data.get("results", [])
    top_results = sorted(
        [r for r in results if r.get("bonferroni_sig")],
        key=lambda r: abs(r.get("cohens_d", 0)),
        reverse=True,
    )[:5]

    return {
        "total_runs": data.get("total_runs"),
        "total_hypotheses": data.get("total_hypotheses"),
        "n_bonferroni_significant": data.get("n_bonferroni_significant", 0),
        "n_bh_significant": data.get("n_bh_significant", 0),
        "swept_parameters": data.get("swept_parameters", {}),
        "top_results": top_results,
        "p_hacking_audit": data.get("p_hacking_audit", {}),
        "improvements": data.get("improvements_over_v1", []),
    }


def read_redteam_summary(run_path: Path, run_data: dict) -> dict:
    """Read redteam report.json."""
    summary_rel = run_data.get("artifacts", {}).get("summary", "report.json")
    summary_path = run_path / summary_rel
    if not summary_path.exists():
        return {}
    data = read_json(summary_path)

    # Handle nested robustness key
    robustness = data.get("robustness", data)

    vulns = robustness.get("vulnerabilities", [])
    critical = [v for v in vulns if v.get("severity") == "critical"]
    high = [v for v in vulns if v.get("severity") == "high"]

    return {
        "attacks_tested": robustness.get("attacks_tested", 0),
        "attacks_successful": robustness.get("attacks_successful", 0),
        "attacks_prevented": robustness.get("attacks_prevented", 0),
        "robustness_score": robustness.get("robustness_score"),
        "grade": robustness.get("grade"),
        "evasion_rate": robustness.get("overall_evasion_rate"),
        "total_damage": robustness.get("total_damage_allowed"),
        "critical_vulns": critical,
        "high_vulns": high,
        "all_vulns": vulns,
        "governance_config": robustness.get("governance_config", {}),
    }


def read_study_summary(run_path: Path, run_data: dict) -> dict:
    """Read study analysis/summary.json."""
    summary_rel = run_data.get("artifacts", {}).get("summary", "analysis/summary.json")
    summary_path = run_path / summary_rel
    if not summary_path.exists():
        # Fallback: try summary.json directly
        summary_path = run_path / "summary.json"
        if not summary_path.exists():
            return {}
    data = read_json(summary_path)

    # Extract significant pairwise comparisons
    # Handle both field naming conventions
    pairwise = data.get("pairwise_tests", [])
    significant = [
        p for p in pairwise
        if p.get("bonferroni_sig") or p.get("significant_bonferroni")
    ]

    # Normalize pairwise entries to a common format
    for p in pairwise:
        # Ensure "comparison" field exists
        if "comparison" not in p and "group_1" in p and "group_2" in p:
            p["comparison"] = f"{p['group_1']} vs {p['group_2']}"
        # Normalize bonferroni_sig
        if "bonferroni_sig" not in p and "significant_bonferroni" in p:
            p["bonferroni_sig"] = p["significant_bonferroni"]
        # Normalize p_value
        if "p_value" not in p and "t_p" in p:
            p["p_value"] = p["t_p"]

    # Handle both "descriptive" and "descriptive_stats" keys
    descriptive = data.get("descriptive") or data.get("descriptive_stats") or {}

    # If descriptive is a list (e.g. memori study), convert to dict keyed by index
    if isinstance(descriptive, list):
        desc_dict = {}
        for i, entry in enumerate(descriptive):
            # Try to build a meaningful key from the entry
            key_parts = []
            for k in ("tax_rate", "circuit_breaker", "label", "config", "group"):
                if k in entry:
                    key_parts.append(str(entry[k]))
            key = "|".join(key_parts) if key_parts else str(i)
            desc_dict[key] = entry
        descriptive = desc_dict

    return {
        "scenario": data.get("scenario"),
        "parameter": data.get("parameter"),
        "values": data.get("values", []),
        "seeds_per_config": data.get("seeds_per_config"),
        "total_runs": data.get("total_runs"),
        "descriptive": descriptive,
        "pairwise_tests": pairwise,
        "significant_pairwise": significant,
    }


def read_single_summary(run_path: Path, run_data: dict) -> dict:
    """Read single run history.json for final-epoch metrics."""
    history_path = run_path / "history.json"
    if not history_path.exists():
        return {}
    data = read_json(history_path)

    # Handle list-format history (e.g. concordia sweeps: list of run dicts)
    if isinstance(data, list):
        return {
            "simulation_id": data[0].get("label", "unknown") if data else "unknown",
            "n_runs": len(data),
            "final_welfare": data[-1].get("mean_welfare") if data else None,
            "final_toxicity": data[-1].get("mean_toxicity") if data else None,
        }

    # Standard dict-format history
    snapshots = data.get("epoch_snapshots", [])
    final = snapshots[-1] if snapshots else {}

    return {
        "simulation_id": data.get("simulation_id"),
        "n_epochs": data.get("n_epochs"),
        "steps_per_epoch": data.get("steps_per_epoch"),
        "n_agents": data.get("n_agents"),
        "seed": data.get("seed"),
        "final_welfare": final.get("total_welfare"),
        "final_toxicity": final.get("toxicity_rate"),
        "final_acceptance": final.get("accepted_interactions", 0)
            / max(final.get("total_interactions", 1), 1)
            if final.get("total_interactions") else None,
        "final_quality_gap": final.get("quality_gap"),
    }


def read_calibration_summary(run_path: Path, run_data: dict) -> dict:
    """Read calibration summary.json and recommendation.json."""
    result = {}
    summary_path = run_path / "summary.json"
    if summary_path.exists():
        result["summary"] = read_json(summary_path)

    rec_path = run_path / "recommendation.json"
    if rec_path.exists():
        result["recommendation"] = read_json(rec_path)

    return result


# ── Claim matching ───────────────────────────────────────────────────────


def find_related_claims(run_tags: list[str]) -> list[dict]:
    """Find claims whose topics overlap with run tags (>=2 tag overlap)."""
    if not CLAIMS_DIR.exists():
        return []

    related = []
    run_tag_set = set(t.lower() for t in run_tags)

    for claim_path in sorted(CLAIMS_DIR.glob("*.md")):
        fm = parse_frontmatter(claim_path)
        if fm is None:
            continue

        topics = extract_topics(claim_path)
        # Also use domain as a topic
        domain = fm.get("domain", "")
        topic_set = set(t.lower() for t in topics) | {domain.lower()}

        overlap = run_tag_set & topic_set
        if len(overlap) >= 2:
            related.append({
                "claim_id": claim_path.stem,
                "description": fm.get("description", ""),
                "confidence": fm.get("confidence", ""),
                "overlap": sorted(overlap),
            })

    return related


# ── Title generation ─────────────────────────────────────────────────────


def generate_title(run_data: dict, summary: dict, exp_type: str) -> str:
    """Generate a prose-as-title for the experiment note."""
    slug = run_data.get("slug", "unknown")
    hypothesis = run_data.get("experiment", {}).get("hypothesis", "")

    if exp_type == "sweep":
        swept = run_data.get("experiment", {}).get("swept_parameters", {})
        params = ", ".join(k.split(".")[-1] for k in swept.keys()) if swept else slug
        n_sig = summary.get("n_bonferroni_significant", 0)
        total = summary.get("total_runs", "?")
        return f"{slug.replace('_', ' ')} sweep ({total} runs) finds {n_sig} Bonferroni-significant effects across {params}"

    elif exp_type == "redteam":
        grade = summary.get("grade", "?")
        score = summary.get("robustness_score")
        score_str = f"{score:.0%}" if score is not None else "?"
        return f"red-team evaluation scores {score_str} ({grade}) against baseline governance"

    elif exp_type == "study":
        param = summary.get("parameter") or slug
        n_sig = len(summary.get("significant_pairwise", []))
        total = summary.get("total_runs", "?")
        return f"{param.replace('_', ' ')} study ({total} runs) finds {n_sig} significant pairwise differences"

    elif exp_type == "single":
        welfare = summary.get("final_welfare")
        w_str = f" with welfare={welfare:.1f}" if welfare is not None else ""
        return f"single-run baseline{w_str} ({slug.replace('_', ' ')})"

    elif exp_type == "calibration":
        return f"calibration of {slug.replace('_', ' ')}"

    return f"experiment: {slug.replace('_', ' ')}"


# ── Description generation ──────────────────────────────────────────────


def generate_description(run_data: dict, summary: dict, exp_type: str) -> str:
    """Generate a description (<=200 chars, no trailing period)."""
    slug = run_data.get("slug", "unknown")
    total = summary.get("total_runs") or run_data.get("experiment", {}).get("total_runs")

    if exp_type == "sweep":
        n_sig = summary.get("n_bonferroni_significant", 0)
        swept = run_data.get("experiment", {}).get("swept_parameters", {})
        params = ", ".join(k.split(".")[-1] for k in swept.keys()) if swept else "parameters"
        desc = f"{slug}: {total}-run sweep of {params}, {n_sig} Bonferroni-significant findings"

    elif exp_type == "redteam":
        grade = summary.get("grade", "?")
        attacks = summary.get("attacks_tested", "?")
        desc = f"Red-team evaluation: {attacks} attacks tested, grade {grade}"

    elif exp_type == "study":
        param = summary.get("parameter") or slug
        values = summary.get("values", [])
        desc = f"Multi-condition study of {param} ({len(values)} levels, {total} total runs)"

    elif exp_type == "single":
        welfare = summary.get("final_welfare")
        desc = f"Single baseline run of {slug}"
        if welfare is not None:
            desc += f", final welfare={welfare:.1f}"

    elif exp_type == "calibration":
        desc = f"Calibration run for {slug}"

    else:
        desc = f"Experiment: {slug}"

    # Enforce 200-char limit, no trailing period
    desc = desc.rstrip(".")
    if len(desc) > 200:
        desc = desc[:197] + "..."
    return desc


# ── Note generation (per type) ───────────────────────────────────────────


def generate_sweep_note(run_id: str, run_data: dict, summary: dict, claims: list[dict]) -> str:
    """Generate experiment note for a sweep."""
    exp = run_data.get("experiment", {})
    results = run_data.get("results", {})
    provenance = run_data.get("provenance", {})
    artifacts = run_data.get("artifacts", {})
    tags = run_data.get("tags", [])

    # Swept parameters section
    swept = exp.get("swept_parameters", {})
    swept_lines = []
    for param, values in swept.items():
        if isinstance(values, list) and len(values) <= 10:
            swept_lines.append(f"- `{param}`: {values}")
        elif isinstance(values, list):
            swept_lines.append(f"- `{param}`: {len(values)} levels")
        else:
            swept_lines.append(f"- `{param}`: {values}")
    swept_section = "\n".join(swept_lines) if swept_lines else "- Not recorded"

    # Top results
    top_results = summary.get("top_results", [])
    results_lines = []
    for r in top_results:
        param = r.get("parameter", "?").split(".")[-1]
        metric = r.get("metric", "?")
        d = r.get("cohens_d", 0)
        p = r.get("t_p", 1)
        v1, v2 = r.get("value_1", "?"), r.get("value_2", "?")
        m1, m2 = r.get("mean_1", 0), r.get("mean_2", 0)
        results_lines.append(
            f"- **{param}** ({v1} vs {v2}) on {metric}: "
            f"mean {m1:.2f} vs {m2:.2f}, d={d:.2f} ({fmt_effect(d)}), "
            f"{fmt_pvalue(p)}, Bonferroni-corrected"
        )

    if not results_lines:
        results_lines = ["- No Bonferroni-significant results found"]

    # P-hacking audit
    audit = summary.get("p_hacking_audit", {})
    audit_section = ""
    if audit:
        audit_section = dedent(f"""\

        ### Statistical audit

        - Total hypotheses tested: {audit.get('total_hypotheses', '?')}
        - Pre-registered: {audit.get('pre_registered', 'unknown')}
        - Nominally significant: {audit.get('nominally_significant', '?')}
        - Bonferroni-significant: {audit.get('bonferroni_significant', '?')}
        - Holm-Bonferroni significant: {audit.get('holm_bonferroni_significant', '?')}
        """)

    # Claims section
    claims_section = "No claims with >=2 tag overlap found."
    if claims:
        claims_lines = []
        for c in claims:
            claims_lines.append(f"- [[{c['claim_id']}]] ({c['confidence']}) — overlapping tags: {', '.join(c['overlap'])}")
        claims_section = "\n".join(claims_lines)

    # Artifacts
    artifact_lines = []
    if artifacts.get("summary"):
        artifact_lines.append(f"- Summary: `runs/{run_id}/{artifacts['summary']}`")
    if artifacts.get("sweep_csv"):
        artifact_lines.append(f"- Sweep CSV: `runs/{run_id}/{artifacts['sweep_csv']}`")
    for script in artifacts.get("scripts", []):
        artifact_lines.append(f"- Script: `runs/{run_id}/{script}`")
    artifact_section = "\n".join(artifact_lines) if artifact_lines else "- No artifacts recorded"

    body = f"""\
## Design

- **Hypothesis**: {exp.get('hypothesis', 'Not recorded')}
- **Type**: Parameter sweep
- **Parameters swept**:
{swept_section}
- **Seeds**: {len(exp.get('seeds', []))} seeds
- **Total runs**: {exp.get('total_runs', '?')}
- **SWARM version**: {provenance.get('swarm_version', 'unknown')} @ `{provenance.get('git_sha', 'unknown')}`

## Key results

{chr(10).join(results_lines)}
{audit_section}
## Claims affected

{claims_section}

## Artifacts

{artifact_section}

## Reproduction

```bash
python -m swarm sweep {exp.get('scenario_ref', '<scenario>')} --seeds {len(exp.get('seeds', []))}
```"""

    return body


def generate_redteam_note(run_id: str, run_data: dict, summary: dict, claims: list[dict]) -> str:
    """Generate experiment note for a redteam."""
    provenance = run_data.get("provenance", {})
    artifacts = run_data.get("artifacts", {})
    gov = summary.get("governance_config", {})

    # Governance config table
    gov_lines = []
    for k, v in gov.items():
        gov_lines.append(f"| `{k}` | `{v}` |")
    gov_section = "| Parameter | Value |\n|-----------|-------|\n" + "\n".join(gov_lines) if gov_lines else "Not recorded"

    # Vulnerability table
    vulns = summary.get("all_vulns", [])
    vuln_rows = []
    for v in vulns:
        vuln_rows.append(
            f"| {v.get('vulnerability_id', '?')} | {v.get('severity', '?')} | "
            f"{v.get('attack_vector', '?')} | {v.get('potential_damage', '?')} | "
            f"{v.get('affected_lever', '?')} |"
        )
    vuln_table = (
        "| Vulnerability | Severity | Vector | Damage | Affected Lever |\n"
        "|---------------|----------|--------|--------|----------------|\n"
        + "\n".join(vuln_rows)
    ) if vuln_rows else "No vulnerabilities recorded"

    # Claims section
    claims_section = "No claims with >=2 tag overlap found."
    if claims:
        claims_lines = [f"- [[{c['claim_id']}]] ({c['confidence']}) — {', '.join(c['overlap'])}" for c in claims]
        claims_section = "\n".join(claims_lines)

    body = f"""\
## Design

- **Type**: Red-team adversarial evaluation
- **Attacks tested**: {summary.get('attacks_tested', '?')}
- **SWARM version**: {provenance.get('swarm_version', 'unknown')} @ `{provenance.get('git_sha', 'unknown')}`

### Governance configuration

{gov_section}

## Key results

- **Robustness score**: {summary.get('robustness_score', '?')}
- **Grade**: {summary.get('grade', '?')}
- **Attacks successful**: {summary.get('attacks_successful', '?')}/{summary.get('attacks_tested', '?')}
- **Evasion rate**: {summary.get('evasion_rate', '?')}
- **Total damage allowed**: {summary.get('total_damage', '?')}

### Vulnerabilities

{vuln_table}

## Claims affected

{claims_section}

## Artifacts

- Report: `runs/{run_id}/{artifacts.get('summary', 'report.json')}`

## Reproduction

```bash
python -m swarm redteam {run_data.get('experiment', {}).get('scenario_ref', '<scenario>')}
```"""

    return body


def generate_study_note(run_id: str, run_data: dict, summary: dict, claims: list[dict]) -> str:
    """Generate experiment note for a study."""
    exp = run_data.get("experiment", {})
    provenance = run_data.get("provenance", {})
    artifacts = run_data.get("artifacts", {})

    param = summary.get("parameter") or "unknown"
    values = summary.get("values", [])
    descriptive = summary.get("descriptive", {})

    # Descriptive stats table
    desc_rows = []
    metrics = ["welfare_mean", "welfare_std", "toxicity_mean", "toxicity_std", "acceptance_mean"]
    if descriptive:
        header_vals = list(descriptive.keys())
        # Truncate headers if too many columns
        if len(header_vals) > 8:
            header_vals = header_vals[:8]
        desc_rows.append("| Metric | " + " | ".join(str(v)[:20] for v in header_vals) + " |")
        desc_rows.append("|--------|" + "|".join("-----" for _ in header_vals) + "|")
        for metric in metrics:
            row = f"| {metric} |"
            for val in header_vals:
                entry = descriptive.get(str(val), {})
                if isinstance(entry, dict):
                    cell = entry.get(metric, "—")
                else:
                    cell = "—"
                if isinstance(cell, float):
                    row += f" {cell:.3f} |"
                else:
                    row += f" {cell} |"
            desc_rows.append(row)
    desc_table = "\n".join(desc_rows) if desc_rows else "No descriptive statistics available"

    # Pairwise tests
    pairwise = summary.get("pairwise_tests", [])
    pw_rows = []
    for pw in pairwise:
        d = pw.get("cohens_d", 0)
        p = pw.get("p_value", 1)
        sig = "**yes**" if pw.get("bonferroni_sig") else "no"
        pw_rows.append(
            f"| {pw.get('comparison', '?')} | {pw.get('metric', '?')} | "
            f"d={d:.3f} | {fmt_pvalue(p)} | {sig} |"
        )
    pw_table = (
        "| Comparison | Metric | Effect size | p-value | Bonferroni sig |\n"
        "|------------|--------|-------------|---------|----------------|\n"
        + "\n".join(pw_rows)
    ) if pw_rows else "No pairwise tests available"

    # Claims section
    claims_section = "No claims with >=2 tag overlap found."
    if claims:
        claims_lines = [f"- [[{c['claim_id']}]] ({c['confidence']}) — {', '.join(c['overlap'])}" for c in claims]
        claims_section = "\n".join(claims_lines)

    body = f"""\
## Design

- **Type**: Multi-condition study
- **Parameter**: `{param}`
- **Levels**: {values}
- **Seeds per config**: {summary.get('seeds_per_config', '?')}
- **Total runs**: {summary.get('total_runs', '?')}
- **SWARM version**: {provenance.get('swarm_version', 'unknown')} @ `{provenance.get('git_sha', 'unknown')}`

## Key results

### Descriptive statistics

{desc_table}

### Pairwise comparisons

{pw_table}

## Claims affected

{claims_section}

## Artifacts

- Summary: `runs/{run_id}/{artifacts.get('summary', 'analysis/summary.json')}`
- Sweep CSV: `runs/{run_id}/{artifacts.get('sweep_csv', 'sweep_results.csv')}`

## Reproduction

```bash
python -m swarm study {exp.get('scenario_ref', '<scenario>')} --seeds {summary.get('seeds_per_config', '?')}
```"""

    return body


def generate_single_note(run_id: str, run_data: dict, summary: dict, claims: list[dict]) -> str:
    """Generate experiment note for a single run."""
    exp = run_data.get("experiment", {})
    provenance = run_data.get("provenance", {})
    artifacts = run_data.get("artifacts", {})

    # Metrics summary
    metrics_lines = []
    for key, label in [
        ("final_welfare", "Welfare"),
        ("final_toxicity", "Toxicity rate"),
        ("final_acceptance", "Acceptance rate"),
        ("final_quality_gap", "Quality gap"),
    ]:
        val = summary.get(key)
        if val is not None:
            metrics_lines.append(f"- **{label}**: {val:.3f}")
    metrics_section = "\n".join(metrics_lines) if metrics_lines else "- No final-epoch metrics available"

    # Claims section
    claims_section = "No claims with >=2 tag overlap found."
    if claims:
        claims_lines = [f"- [[{c['claim_id']}]] ({c['confidence']}) — {', '.join(c['overlap'])}" for c in claims]
        claims_section = "\n".join(claims_lines)

    # Artifacts
    artifact_lines = []
    if artifacts.get("epoch_csvs"):
        for csv_path in artifacts["epoch_csvs"]:
            artifact_lines.append(f"- CSV: `runs/{run_id}/{csv_path}`")
    for plot in artifacts.get("plots", []):
        p = plot.get("path", plot) if isinstance(plot, dict) else plot
        artifact_lines.append(f"- Plot: `runs/{run_id}/{p}`")
    artifact_section = "\n".join(artifact_lines) if artifact_lines else "- No artifacts recorded"

    seed = summary.get("seed") or (exp.get("seeds", [0])[0] if exp.get("seeds") else "?")

    body = f"""\
## Design

- **Type**: Single run
- **Scenario**: {exp.get('scenario_ref', 'unknown')}
- **Seed**: {seed}
- **Epochs**: {summary.get('n_epochs', '?')}
- **Steps per epoch**: {summary.get('steps_per_epoch', '?')}
- **Agents**: {summary.get('n_agents', '?')}
- **SWARM version**: {provenance.get('swarm_version', 'unknown')} @ `{provenance.get('git_sha', 'unknown')}`

## Key results

{metrics_section}

## Claims affected

{claims_section}

## Artifacts

{artifact_section}

## Reproduction

```bash
python -m swarm run {exp.get('scenario_ref', '<scenario>')} --seed {seed}
```"""

    return body


def generate_calibration_note(run_id: str, run_data: dict, summary: dict, claims: list[dict]) -> str:
    """Generate experiment note for a calibration run."""
    exp = run_data.get("experiment", {})
    provenance = run_data.get("provenance", {})

    rec = summary.get("recommendation", {})
    rec_lines = []
    if rec:
        for k, v in rec.items():
            rec_lines.append(f"- `{k}`: {v}")
    rec_section = "\n".join(rec_lines) if rec_lines else "- No recommendation available"

    body = f"""\
## Design

- **Type**: Calibration
- **Scenario**: {exp.get('scenario_ref', 'unknown')}
- **SWARM version**: {provenance.get('swarm_version', 'unknown')} @ `{provenance.get('git_sha', 'unknown')}`

## Key results

### Recommended configuration

{rec_section}

## Claims affected

No claims typically affected by calibration runs.

## Reproduction

```bash
python -m swarm calibrate {exp.get('scenario_ref', '<scenario>')}
```"""

    return body


# ── Main synthesis ───────────────────────────────────────────────────────


def synthesize_run(run_id: str, force: bool = False) -> bool:
    """Synthesize a single run into a vault experiment note. Returns True if note was created."""
    run_path = RUNS_DIR / run_id
    if not run_path.exists():
        print(f"  ERROR: {run_path} does not exist")
        return False

    run_yaml_path = run_path / "run.yaml"
    if not run_yaml_path.exists():
        print(f"  ERROR: {run_id} has no run.yaml (run backfill-run-yaml.py first)")
        return False

    output_path = EXPERIMENTS_DIR / f"{run_id}.md"
    if output_path.exists() and not force:
        print(f"  SKIP: {run_id} already synthesized")
        return False

    # Read run metadata
    run_data = read_yaml(run_yaml_path)
    exp_type = run_data.get("experiment", {}).get("type", "single")
    tags = run_data.get("tags", [])

    # Read type-specific summary
    SUMMARY_READERS = {
        "sweep": read_sweep_summary,
        "redteam": read_redteam_summary,
        "study": read_study_summary,
        "single": read_single_summary,
        "calibration": read_calibration_summary,
    }
    reader = SUMMARY_READERS.get(exp_type, read_single_summary)
    summary = reader(run_path, run_data)

    # Find related claims
    claims = find_related_claims(tags)

    # Generate title and description
    title = generate_title(run_data, summary, exp_type)
    description = generate_description(run_data, summary, exp_type)

    # Generate type-specific body
    NOTE_GENERATORS = {
        "sweep": generate_sweep_note,
        "redteam": generate_redteam_note,
        "study": generate_study_note,
        "single": generate_single_note,
        "calibration": generate_calibration_note,
    }
    generator = NOTE_GENERATORS.get(exp_type, generate_single_note)
    body = generator(run_id, run_data, summary, claims)

    # Extract created date
    created_utc = run_data.get("created_utc", "")
    if created_utc and created_utc != "unknown":
        created_date = created_utc[:10]  # YYYY-MM-DD
    else:
        created_date = str(date.today())

    # Build frontmatter
    frontmatter = {
        "description": description,
        "type": "experiment",
        "status": run_data.get("results", {}).get("status", "completed"),
        "run_id": run_id,
        "experiment_type": exp_type,
        "created": created_date,
    }

    # Add optional provenance
    prov = run_data.get("provenance", {})
    if prov.get("swarm_version") and prov["swarm_version"] != "unknown":
        frontmatter["swarm_version"] = prov["swarm_version"]
    if prov.get("git_sha") and prov["git_sha"] != "unknown":
        frontmatter["git_sha"] = prov["git_sha"]

    hypothesis = run_data.get("experiment", {}).get("hypothesis")
    if hypothesis:
        frontmatter["hypothesis"] = hypothesis

    # Build full note
    fm_yaml = yaml.dump(frontmatter, default_flow_style=False, sort_keys=False).strip()
    topic_tags = ", ".join(tags) if tags else "untagged"

    note = f"""\
---
{fm_yaml}
---

# {title}

{body}

---

Topics:
- [[_index]]

<!-- topics: {topic_tags} -->
"""

    # Write
    EXPERIMENTS_DIR.mkdir(parents=True, exist_ok=True)
    output_path.write_text(note, encoding="utf-8")
    print(f"  CREATED: {output_path}")
    return True


# ── CLI ──────────────────────────────────────────────────────────────────


def get_unsynthesized_runs() -> list[str]:
    """Find runs that have run.yaml but no experiment note."""
    synthesized = set()
    if EXPERIMENTS_DIR.exists():
        synthesized = {p.stem for p in EXPERIMENTS_DIR.glob("*.md")}

    unsynthesized = []
    for run_path in sorted(RUNS_DIR.iterdir(), reverse=True):
        if not run_path.is_dir():
            continue
        if run_path.name.startswith("_"):
            continue
        if (run_path / "run.yaml").exists() and run_path.name not in synthesized:
            unsynthesized.append(run_path.name)

    return unsynthesized


def main():
    parser = argparse.ArgumentParser(
        description="Generate vault experiment notes from SWARM runs"
    )
    parser.add_argument("run_id", nargs="?", help="Run ID to synthesize")
    parser.add_argument("--all", action="store_true", help="Synthesize all unsynthesized runs")
    parser.add_argument("--batch", type=int, help="Synthesize N most recent unsynthesized runs")
    parser.add_argument("--force", action="store_true", help="Overwrite existing notes")
    parser.add_argument("--dry-run", action="store_true", help="List what would be synthesized")
    args = parser.parse_args()

    if not args.run_id and not args.all and args.batch is None:
        # Show unsynthesized runs
        unsynthesized = get_unsynthesized_runs()
        if unsynthesized:
            print(f"{len(unsynthesized)} unsynthesized runs:")
            for run_id in unsynthesized[:20]:
                print(f"  {run_id}")
            if len(unsynthesized) > 20:
                print(f"  ... and {len(unsynthesized) - 20} more")
            print(f"\nUsage: python scripts/generate-note.py <run_id>")
            print(f"       python scripts/generate-note.py --all")
        else:
            print("All runs are synthesized.")
        return

    # Determine targets
    if args.run_id:
        targets = [args.run_id]
    else:
        targets = get_unsynthesized_runs()
        if args.batch:
            targets = targets[:args.batch]

    if args.dry_run:
        print(f"Would synthesize {len(targets)} runs:")
        for t in targets:
            print(f"  {t}")
        return

    # Synthesize
    created = 0
    skipped = 0
    errors = 0

    for run_id in targets:
        try:
            if synthesize_run(run_id, force=args.force):
                created += 1
            else:
                skipped += 1
        except Exception as e:
            print(f"  ERROR: {run_id}: {e}")
            errors += 1

    print(f"\nDone: {created} created, {skipped} skipped, {errors} errors")


if __name__ == "__main__":
    main()
