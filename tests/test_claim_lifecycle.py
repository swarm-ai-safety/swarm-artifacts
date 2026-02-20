"""Tests for scripts/claim-lifecycle.py logic."""

import importlib.util
import json
import sys
from pathlib import Path

import pytest
import yaml

SCRIPTS_DIR = Path(__file__).parent.parent / "scripts"


def _load_module(monkeypatch, tmp_path, tmp_vault, tmp_runs):
    """Load claim-lifecycle.py as a module with patched paths."""
    spec_path = SCRIPTS_DIR / "claim-lifecycle.py"
    spec = importlib.util.spec_from_file_location("claim_lifecycle", spec_path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)

    monkeypatch.setattr(mod, "ROOT", tmp_path)
    monkeypatch.setattr(mod, "RUNS_DIR", tmp_runs)
    monkeypatch.setattr(mod, "VAULT_DIR", tmp_vault)
    monkeypatch.setattr(mod, "CLAIMS_DIR", tmp_vault / "claims")
    return mod


# ---------------------------------------------------------------------------
# Tag overlap
# ---------------------------------------------------------------------------


class TestTagOverlap:
    def test_exact_overlap(self, monkeypatch, tmp_path, tmp_vault, tmp_runs):
        mod = _load_module(monkeypatch, tmp_path, tmp_vault, tmp_runs)
        assert mod.tag_overlap(["governance", "welfare"], ["governance", "welfare"]) == 2

    def test_underscore_hyphen_normalization(self, monkeypatch, tmp_path, tmp_vault, tmp_runs):
        mod = _load_module(monkeypatch, tmp_path, tmp_vault, tmp_runs)
        assert mod.tag_overlap(["transaction_tax"], ["transaction-tax"]) == 1

    def test_case_insensitive(self, monkeypatch, tmp_path, tmp_vault, tmp_runs):
        mod = _load_module(monkeypatch, tmp_path, tmp_vault, tmp_runs)
        assert mod.tag_overlap(["Governance"], ["governance"]) == 1

    def test_no_overlap(self, monkeypatch, tmp_path, tmp_vault, tmp_runs):
        mod = _load_module(monkeypatch, tmp_path, tmp_vault, tmp_runs)
        assert mod.tag_overlap(["governance", "welfare"], ["topology", "memory"]) == 0


# ---------------------------------------------------------------------------
# Uncited relevant run detection
# ---------------------------------------------------------------------------


class TestAnalyzeClaim:
    """Tests for analyze_claim() — the core lifecycle analysis."""

    def test_finds_uncited_relevant_runs(self, monkeypatch, tmp_path, tmp_vault, tmp_runs, mock_claim):
        """A run with >=2 tag overlap that is not cited should be detected."""
        mod = _load_module(monkeypatch, tmp_path, tmp_vault, tmp_runs)

        # Load all runs the way the module does
        all_runs = mod.load_all_runs()
        report = mod.analyze_claim(mock_claim, all_runs)

        assert report is not None
        uncited_ids = [u["run_id"] for u in report["uncited_relevant_runs"]]
        # sweep-tax-001 has tags [governance, transaction-tax, welfare, market]
        # claim topics are [governance, transaction-tax, welfare, market] -> overlap >= 2
        assert "sweep-tax-001" in uncited_ids

    def test_does_not_match_low_overlap_runs(self, monkeypatch, tmp_path, tmp_vault, tmp_runs, mock_claim):
        """A run with <2 tag overlap should NOT appear in uncited_relevant_runs."""
        mod = _load_module(monkeypatch, tmp_path, tmp_vault, tmp_runs)

        all_runs = mod.load_all_runs()
        report = mod.analyze_claim(mock_claim, all_runs)

        assert report is not None
        uncited_ids = [u["run_id"] for u in report["uncited_relevant_runs"]]
        # single-baseline-003 has tags [baseline, calibration] -> overlap 0
        assert "single-baseline-003" not in uncited_ids

    def test_detects_strengthening_evidence(self, monkeypatch, tmp_path, tmp_vault, tmp_runs, mock_claim):
        """A Bonferroni-significant result on a matching metric should be flagged as strengthening."""
        mod = _load_module(monkeypatch, tmp_path, tmp_vault, tmp_runs)

        all_runs = mod.load_all_runs()
        report = mod.analyze_claim(mock_claim, all_runs)

        assert report is not None
        # sweep-tax-001 has bonferroni_sig=True on welfare_mean, which the claim references
        strengthening_ids = [s["run_id"] for s in report["strengthening"]]
        assert "sweep-tax-001" in strengthening_ids

        # Check at least one has the bonferroni_significant reason
        reasons = [s["reason"] for s in report["strengthening"]]
        assert "bonferroni_significant" in reasons or "bonferroni_significant_different_metric" in reasons

    def test_recommends_upgrade_with_supporting_runs(
        self, monkeypatch, tmp_path, tmp_vault, tmp_runs, write_claim
    ):
        """A medium-confidence claim with >=2 Bonferroni-supporting runs should get an upgrade recommendation."""
        mod = _load_module(monkeypatch, tmp_path, tmp_vault, tmp_runs)

        # Create a claim that already has 1 cited supporting run with bonferroni sig,
        # and the uncited sweep-tax-001 will add another.
        fm = {
            "description": "Tax above 5% causes welfare phase-transition",
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
        body = "# Tax above 5% causes welfare phase-transition\n\n<!-- topics: governance, transaction-tax, welfare, market -->\n"
        claim_path = write_claim("claim-tax-upgrade", fm, body)

        all_runs = mod.load_all_runs()
        report = mod.analyze_claim(claim_path, all_runs)

        assert report is not None
        actions = [r["action"] for r in report["recommendations"]]
        assert "upgrade" in actions

        upgrade_rec = [r for r in report["recommendations"] if r["action"] == "upgrade"][0]
        assert upgrade_rec["from"] == "medium"
        assert upgrade_rec["to"] == "high"


# ---------------------------------------------------------------------------
# cited_run_ids helper
# ---------------------------------------------------------------------------


class TestCitedRunIds:
    def test_extracts_supporting_and_weakening(self, monkeypatch, tmp_path, tmp_vault, tmp_runs):
        mod = _load_module(monkeypatch, tmp_path, tmp_vault, tmp_runs)

        fm = {
            "evidence": {
                "supporting": [{"run": "run-a"}, {"run": "run-b"}],
                "weakening": [{"run": "run-c"}],
            }
        }
        assert mod.cited_run_ids(fm) == {"run-a", "run-b", "run-c"}

    def test_empty_evidence(self, monkeypatch, tmp_path, tmp_vault, tmp_runs):
        mod = _load_module(monkeypatch, tmp_path, tmp_vault, tmp_runs)
        assert mod.cited_run_ids({}) == set()
        assert mod.cited_run_ids({"evidence": {}}) == set()


# ---------------------------------------------------------------------------
# extract_sweep_results
# ---------------------------------------------------------------------------


class TestExtractSweepResults:
    def test_extracts_bonferroni_significant(self, monkeypatch, tmp_path, tmp_vault, tmp_runs):
        mod = _load_module(monkeypatch, tmp_path, tmp_vault, tmp_runs)

        results = mod.extract_sweep_results(tmp_runs / "sweep-tax-001")
        assert len(results) == 1  # Only the one with bonferroni_sig=True
        assert results[0]["metric"] == "welfare_mean"
        assert results[0]["bonferroni_sig"] is True

    def test_handles_missing_summary(self, monkeypatch, tmp_path, tmp_vault, tmp_runs):
        mod = _load_module(monkeypatch, tmp_path, tmp_vault, tmp_runs)

        empty_dir = tmp_runs / "nonexistent"
        empty_dir.mkdir()
        results = mod.extract_sweep_results(empty_dir)
        assert results == []
