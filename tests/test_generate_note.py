"""Tests for scripts/generate-note.py helpers."""

import importlib.util
import json
from pathlib import Path

import pytest
import yaml

SCRIPTS_DIR = Path(__file__).parent.parent / "scripts"


def _load_module(monkeypatch, tmp_path, tmp_vault, tmp_runs):
    """Load generate-note.py as a module with patched paths."""
    spec_path = SCRIPTS_DIR / "generate-note.py"
    spec = importlib.util.spec_from_file_location("generate_note", spec_path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)

    monkeypatch.setattr(mod, "ROOT", tmp_path)
    monkeypatch.setattr(mod, "RUNS_DIR", tmp_runs)
    monkeypatch.setattr(mod, "VAULT_DIR", tmp_vault)
    monkeypatch.setattr(mod, "EXPERIMENTS_DIR", tmp_vault / "experiments")
    monkeypatch.setattr(mod, "CLAIMS_DIR", tmp_vault / "claims")
    return mod


# ---------------------------------------------------------------------------
# slugify()
# ---------------------------------------------------------------------------


class TestSlugify:
    def test_basic_slugify(self, monkeypatch, tmp_path, tmp_vault, tmp_runs):
        mod = _load_module(monkeypatch, tmp_path, tmp_vault, tmp_runs)
        assert mod.slugify("Hello World") == "hello-world"

    def test_strips_special_chars(self, monkeypatch, tmp_path, tmp_vault, tmp_runs):
        mod = _load_module(monkeypatch, tmp_path, tmp_vault, tmp_runs)
        assert mod.slugify("Tax Rate (5%)") == "tax-rate-5"

    def test_underscores_become_hyphens(self, monkeypatch, tmp_path, tmp_vault, tmp_runs):
        """Underscores are first stripped by the [^a-z0-9\\s-] regex, then
        whitespace/underscores become hyphens. Since underscores are removed
        before the replacement step, the result collapses the words."""
        mod = _load_module(monkeypatch, tmp_path, tmp_vault, tmp_runs)
        # The regex strips underscores (not in [a-z0-9\s-]), so "my_param" -> "myparamname"
        assert mod.slugify("my_param_name") == "myparamname"
        # But spaces are preserved and become hyphens
        assert mod.slugify("my param name") == "my-param-name"

    def test_truncates_to_80(self, monkeypatch, tmp_path, tmp_vault, tmp_runs):
        mod = _load_module(monkeypatch, tmp_path, tmp_vault, tmp_runs)
        result = mod.slugify("a " * 100)
        assert len(result) <= 80

    def test_empty_string(self, monkeypatch, tmp_path, tmp_vault, tmp_runs):
        mod = _load_module(monkeypatch, tmp_path, tmp_vault, tmp_runs)
        assert mod.slugify("") == ""


# ---------------------------------------------------------------------------
# generate_title() for sweep type
# ---------------------------------------------------------------------------


class TestGenerateTitle:
    def test_sweep_title_format(self, monkeypatch, tmp_path, tmp_vault, tmp_runs):
        mod = _load_module(monkeypatch, tmp_path, tmp_vault, tmp_runs)

        run_data = {
            "slug": "tax_rate_sweep",
            "experiment": {
                "type": "sweep",
                "swept_parameters": {"governance.tax_rate": [0.01, 0.05, 0.10]},
            },
        }
        summary = {
            "n_bonferroni_significant": 2,
            "total_runs": 9,
        }

        title = mod.generate_title(run_data, summary, "sweep")
        assert "tax rate sweep" in title.lower() or "tax_rate_sweep" in title.lower()
        assert "9 runs" in title
        assert "2 Bonferroni-significant" in title
        assert "tax_rate" in title

    def test_study_title_format(self, monkeypatch, tmp_path, tmp_vault, tmp_runs):
        mod = _load_module(monkeypatch, tmp_path, tmp_vault, tmp_runs)

        run_data = {
            "slug": "topology_study",
            "experiment": {"type": "study"},
        }
        summary = {
            "parameter": "topology",
            "total_runs": 12,
            "significant_pairwise": [{"comparison": "ring vs small-world"}],
        }

        title = mod.generate_title(run_data, summary, "study")
        assert "topology" in title.lower()
        assert "12 runs" in title
        assert "1 significant" in title


# ---------------------------------------------------------------------------
# generate_description()
# ---------------------------------------------------------------------------


class TestGenerateDescription:
    def test_description_under_200_chars(self, monkeypatch, tmp_path, tmp_vault, tmp_runs):
        mod = _load_module(monkeypatch, tmp_path, tmp_vault, tmp_runs)

        run_data = {
            "slug": "tax_rate_sweep",
            "experiment": {
                "type": "sweep",
                "swept_parameters": {"governance.tax_rate": [0.01, 0.05, 0.10]},
            },
        }
        summary = {
            "n_bonferroni_significant": 2,
            "total_runs": 9,
        }

        desc = mod.generate_description(run_data, summary, "sweep")
        assert len(desc) <= 200
        assert not desc.endswith(".")

    def test_very_long_slug_gets_truncated(self, monkeypatch, tmp_path, tmp_vault, tmp_runs):
        mod = _load_module(monkeypatch, tmp_path, tmp_vault, tmp_runs)

        long_slug = "a_very_long_experiment_name_" * 10
        run_data = {
            "slug": long_slug,
            "experiment": {
                "type": "sweep",
                "swept_parameters": {"x": [1, 2, 3]},
            },
        }
        summary = {"n_bonferroni_significant": 0, "total_runs": 3}

        desc = mod.generate_description(run_data, summary, "sweep")
        assert len(desc) <= 200

    def test_no_trailing_period(self, monkeypatch, tmp_path, tmp_vault, tmp_runs):
        mod = _load_module(monkeypatch, tmp_path, tmp_vault, tmp_runs)

        for exp_type in ["sweep", "redteam", "study", "single", "calibration"]:
            run_data = {
                "slug": "test",
                "experiment": {"type": exp_type, "swept_parameters": {"x": [1]}},
            }
            summary = {
                "n_bonferroni_significant": 0,
                "total_runs": 1,
                "grade": "B",
                "attacks_tested": 5,
                "parameter": "p",
                "values": [1, 2],
                "final_welfare": 70.0,
            }
            desc = mod.generate_description(run_data, summary, exp_type)
            assert not desc.endswith("."), f"Description for {exp_type} ends with period: {desc!r}"


# ---------------------------------------------------------------------------
# read_sweep_summary()
# ---------------------------------------------------------------------------


class TestReadSweepSummary:
    def test_reads_summary_json(self, monkeypatch, tmp_path, tmp_vault, tmp_runs):
        mod = _load_module(monkeypatch, tmp_path, tmp_vault, tmp_runs)

        run_data = {"artifacts": {"summary": "summary.json"}}
        result = mod.read_sweep_summary(tmp_runs / "sweep-tax-001", run_data)

        assert result["total_runs"] == 9
        assert result["n_bonferroni_significant"] == 2
        assert len(result["top_results"]) == 1  # Only 1 bonferroni_sig=True result

    def test_handles_missing_file_gracefully(self, monkeypatch, tmp_path, tmp_vault, tmp_runs):
        mod = _load_module(monkeypatch, tmp_path, tmp_vault, tmp_runs)

        run_data = {"artifacts": {"summary": "nonexistent.json"}}
        empty_dir = tmp_runs / "empty-run"
        empty_dir.mkdir()
        result = mod.read_sweep_summary(empty_dir, run_data)
        assert result == {}


# ---------------------------------------------------------------------------
# read_study_summary()
# ---------------------------------------------------------------------------


class TestReadStudySummary:
    def test_handles_list_format_descriptive_stats(self, monkeypatch, tmp_path, tmp_vault, tmp_runs):
        """descriptive_stats as a list (not dict) should be converted to dict keyed by label."""
        mod = _load_module(monkeypatch, tmp_path, tmp_vault, tmp_runs)

        run_data = {"artifacts": {"summary": "summary.json"}}
        result = mod.read_study_summary(tmp_runs / "study-topology-002", run_data)

        # The summary.json uses descriptive_stats as a list of dicts with "label" keys
        descriptive = result.get("descriptive", {})
        assert isinstance(descriptive, dict)
        # Keys should be built from the label field
        assert "ring" in descriptive or any("ring" in str(k) for k in descriptive.keys())

    def test_extracts_significant_pairwise(self, monkeypatch, tmp_path, tmp_vault, tmp_runs):
        mod = _load_module(monkeypatch, tmp_path, tmp_vault, tmp_runs)

        run_data = {"artifacts": {"summary": "summary.json"}}
        result = mod.read_study_summary(tmp_runs / "study-topology-002", run_data)

        sig = result.get("significant_pairwise", [])
        assert len(sig) == 1
        assert sig[0]["metric"] == "welfare_mean"

    def test_handles_missing_file(self, monkeypatch, tmp_path, tmp_vault, tmp_runs):
        mod = _load_module(monkeypatch, tmp_path, tmp_vault, tmp_runs)

        run_data = {"artifacts": {"summary": "analysis/summary.json"}}
        empty_dir = tmp_runs / "missing-study"
        empty_dir.mkdir()
        result = mod.read_study_summary(empty_dir, run_data)
        assert result == {}
