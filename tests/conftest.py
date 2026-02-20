"""Shared fixtures for SWARM Research OS tests."""

import json
import sys
from pathlib import Path

import pytest
import yaml

# Allow importing scripts as modules
SCRIPTS_DIR = Path(__file__).parent.parent / "scripts"
sys.path.insert(0, str(SCRIPTS_DIR))


# ---------------------------------------------------------------------------
# Vault structure
# ---------------------------------------------------------------------------

VAULT_SUBDIRS = [
    "claims",
    "experiments",
    "sweeps",
    "governance",
    "topologies",
    "failures",
    "methods",
    "templates",
]


@pytest.fixture()
def tmp_vault(tmp_path):
    """Create a temporary vault directory with the standard subdirectory structure."""
    vault = tmp_path / "vault"
    vault.mkdir()
    for sub in VAULT_SUBDIRS:
        (vault / sub).mkdir()
    return vault


# ---------------------------------------------------------------------------
# Runs structure
# ---------------------------------------------------------------------------


def _make_run(runs_dir: Path, run_id: str, run_yaml: dict, summary: dict) -> Path:
    """Helper: write a mock run directory with run.yaml and summary.json."""
    run_dir = runs_dir / run_id
    run_dir.mkdir(parents=True, exist_ok=True)
    with open(run_dir / "run.yaml", "w") as f:
        yaml.dump(run_yaml, f, default_flow_style=False)
    with open(run_dir / "summary.json", "w") as f:
        json.dump(summary, f)
    return run_dir


@pytest.fixture()
def tmp_runs(tmp_path):
    """Create a temp runs/ directory with 3 mock run directories."""
    runs = tmp_path / "runs"
    runs.mkdir()

    # Run 1 -- sweep with Bonferroni-significant result
    _make_run(
        runs,
        "sweep-tax-001",
        {
            "run_id": "sweep-tax-001",
            "slug": "tax_rate_sweep",
            "tags": ["governance", "transaction-tax", "welfare", "market"],
            "experiment": {
                "type": "sweep",
                "hypothesis": "Higher tax rates reduce welfare",
                "swept_parameters": {"governance.tax_rate": [0.01, 0.05, 0.10]},
                "seeds": [42, 43, 44],
                "total_runs": 9,
            },
            "results": {"status": "completed"},
            "provenance": {"swarm_version": "0.4.0", "git_sha": "abc123"},
            "artifacts": {"summary": "summary.json"},
            "created_utc": "2026-01-15T12:00:00Z",
        },
        {
            "total_runs": 9,
            "total_hypotheses": 6,
            "n_bonferroni_significant": 2,
            "n_bh_significant": 3,
            "swept_parameters": {"governance.tax_rate": [0.01, 0.05, 0.10]},
            "results": [
                {
                    "metric": "welfare_mean",
                    "parameter": "governance.tax_rate",
                    "value_1": 0.01,
                    "value_2": 0.10,
                    "mean_1": 85.3,
                    "mean_2": 72.1,
                    "cohens_d": -1.42,
                    "t_p": 0.0001,
                    "bonferroni_sig": True,
                },
                {
                    "metric": "toxicity_mean",
                    "parameter": "governance.tax_rate",
                    "value_1": 0.01,
                    "value_2": 0.10,
                    "mean_1": 0.12,
                    "mean_2": 0.08,
                    "cohens_d": 0.65,
                    "t_p": 0.03,
                    "bonferroni_sig": False,
                },
            ],
        },
    )

    # Run 2 -- study
    _make_run(
        runs,
        "study-topology-002",
        {
            "run_id": "study-topology-002",
            "slug": "topology_study",
            "tags": ["topology", "small-world", "welfare"],
            "experiment": {
                "type": "study",
                "hypothesis": "Small-world topology improves welfare",
                "total_runs": 12,
            },
            "results": {"status": "completed"},
            "provenance": {"swarm_version": "0.4.0", "git_sha": "def456"},
            "artifacts": {"summary": "summary.json"},
            "created_utc": "2026-01-20T08:00:00Z",
        },
        {
            "scenario": "baseline",
            "parameter": "topology",
            "values": ["ring", "small-world", "complete"],
            "seeds_per_config": 4,
            "total_runs": 12,
            "pairwise_tests": [
                {
                    "comparison": "ring vs small-world",
                    "metric": "welfare_mean",
                    "cohens_d": 0.91,
                    "p_value": 0.002,
                    "bonferroni_sig": True,
                    "mean_1": 70.0,
                    "mean_2": 82.0,
                },
            ],
            "descriptive_stats": [
                {"label": "ring", "welfare_mean": 70.0, "welfare_std": 5.1},
                {"label": "small-world", "welfare_mean": 82.0, "welfare_std": 4.3},
                {"label": "complete", "welfare_mean": 78.0, "welfare_std": 6.0},
            ],
        },
    )

    # Run 3 -- single run, low overlap tags
    _make_run(
        runs,
        "single-baseline-003",
        {
            "run_id": "single-baseline-003",
            "slug": "baseline_single",
            "tags": ["baseline", "calibration"],
            "experiment": {"type": "single", "total_runs": 1},
            "results": {"status": "completed"},
            "provenance": {"swarm_version": "0.4.0", "git_sha": "ghi789"},
            "artifacts": {},
            "created_utc": "2026-02-01T10:00:00Z",
        },
        {"final_welfare": 75.0},
    )

    return runs


# ---------------------------------------------------------------------------
# Mock claim card
# ---------------------------------------------------------------------------

MOCK_CLAIM_FM = {
    "description": "Transaction taxes above 5% cause a welfare phase-transition",
    "type": "claim",
    "status": "active",
    "confidence": "medium",
    "domain": "governance",
    "evidence": {
        "supporting": [
            {
                "run": "sweep-tax-000",
                "metric": "welfare_mean",
                "detail": "d=-1.20, Bonferroni p<0.001, N=27",
            }
        ],
    },
    "created": "2026-01-10",
}

MOCK_CLAIM_BODY = """\
# Transaction taxes above 5% cause a welfare phase-transition

Evidence from the initial tax-rate sweep shows a sharp welfare drop
when the transaction tax exceeds 5%.

<!-- topics: governance, transaction-tax, welfare, market -->
"""


def _write_claim(claims_dir: Path, name: str, fm: dict, body: str) -> Path:
    """Write a claim markdown file with frontmatter."""
    fm_yaml = yaml.dump(fm, default_flow_style=False, sort_keys=False)
    text = f"---\n{fm_yaml}---\n\n{body}"
    path = claims_dir / f"{name}.md"
    path.write_text(text, encoding="utf-8")
    return path


@pytest.fixture()
def mock_claim(tmp_vault, tmp_runs):
    """Write a valid mock claim card into tmp_vault/claims/ and return its Path.

    Also creates the referenced run directory (sweep-tax-000) so that evidence
    provenance checks pass.
    """
    # Create the run directory referenced by the claim's supporting evidence
    ref_run = tmp_runs / "sweep-tax-000"
    ref_run.mkdir(exist_ok=True)
    (ref_run / "run.yaml").write_text("run_id: sweep-tax-000\n")

    return _write_claim(
        tmp_vault / "claims",
        "claim-tax-phase-transition",
        MOCK_CLAIM_FM,
        MOCK_CLAIM_BODY,
    )


# ---------------------------------------------------------------------------
# Mock experiment note
# ---------------------------------------------------------------------------

MOCK_EXPERIMENT_FM = {
    "description": "Tax-rate sweep finds 2 Bonferroni-significant effects",
    "type": "experiment",
    "status": "completed",
    "run_id": "sweep-tax-001",
    "experiment_type": "sweep",
    "created": "2026-01-15",
}

MOCK_EXPERIMENT_BODY = """\
# tax rate sweep (9 runs) finds 2 Bonferroni-significant effects across tax_rate

## Design

- **Type**: Parameter sweep
- **Total runs**: 9

<!-- topics: governance, transaction-tax, welfare -->
"""


@pytest.fixture()
def mock_experiment(tmp_vault, tmp_runs):
    """Write a mock experiment note into tmp_vault/experiments/ and return its Path."""
    fm_yaml = yaml.dump(MOCK_EXPERIMENT_FM, default_flow_style=False, sort_keys=False)
    text = f"---\n{fm_yaml}---\n\n{MOCK_EXPERIMENT_BODY}"
    path = tmp_vault / "experiments" / "sweep-tax-001.md"
    path.write_text(text, encoding="utf-8")
    return path


# ---------------------------------------------------------------------------
# Helper to write a claim (reusable in tests)
# ---------------------------------------------------------------------------

@pytest.fixture()
def write_claim(tmp_vault):
    """Return a factory function for writing claim cards."""
    def _factory(name: str, fm: dict, body: str) -> Path:
        return _write_claim(tmp_vault / "claims", name, fm, body)
    return _factory
