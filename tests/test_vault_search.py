"""Tests for scripts/vault-search.py logic."""

import importlib.util
from pathlib import Path

import pytest
import yaml

SCRIPTS_DIR = Path(__file__).parent.parent / "scripts"


def _load_module(monkeypatch, tmp_vault):
    """Load vault-search.py as a module with patched VAULT_DIR."""
    spec_path = SCRIPTS_DIR / "vault-search.py"
    spec = importlib.util.spec_from_file_location("vault_search", spec_path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)

    monkeypatch.setattr(mod, "VAULT_DIR", tmp_vault)
    return mod


def _write_note(vault: Path, subdir: str, name: str, fm: dict, body: str) -> Path:
    """Write a markdown note with frontmatter into vault/<subdir>/<name>.md."""
    fm_yaml = yaml.dump(fm, default_flow_style=False, sort_keys=False)
    text = f"---\n{fm_yaml}---\n\n{body}"
    path = vault / subdir / f"{name}.md"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    return path


@pytest.fixture()
def populated_vault(tmp_vault):
    """Populate the vault with several notes for search testing."""
    # Claim 1 — governance, high confidence
    _write_note(
        tmp_vault,
        "claims",
        "claim-tax-welfare",
        {
            "description": "Transaction taxes reduce welfare above a threshold",
            "type": "claim",
            "status": "active",
            "confidence": "high",
            "tags": ["governance", "transaction-tax"],
        },
        "# Transaction taxes reduce welfare above a threshold\n\n"
        "Evidence shows a clear welfare drop.\n\n"
        "<!-- topics: governance, transaction-tax, welfare -->\n",
    )

    # Claim 2 — topology, medium confidence
    _write_note(
        tmp_vault,
        "claims",
        "claim-small-world",
        {
            "description": "Small-world topology improves information flow",
            "type": "claim",
            "status": "active",
            "confidence": "medium",
            "tags": ["topology", "small-world"],
        },
        "# Small-world topology improves information flow\n\n"
        "Agents on a small-world network converge faster.\n\n"
        "<!-- topics: topology, small-world -->\n",
    )

    # Method note
    _write_note(
        tmp_vault,
        "methods",
        "method-bonferroni",
        {
            "description": "Bonferroni correction for multiple hypothesis testing",
            "type": "method",
            "status": "active",
            "tags": ["methodology", "statistics"],
        },
        "# Bonferroni correction for multiple hypothesis testing\n\n"
        "Standard correction that divides alpha by number of tests.\n\n"
        "<!-- topics: methodology, statistics -->\n",
    )

    # Governance note — contains keyword 'welfare' in body only
    _write_note(
        tmp_vault,
        "governance",
        "circuit-breaker-v1",
        {
            "description": "Circuit breaker halts trading during extreme events",
            "type": "governance",
            "status": "active",
            "tags": ["governance"],
        },
        "# Circuit breaker halts trading during extreme events\n\n"
        "When welfare drops below a critical threshold the circuit breaker activates.\n\n"
        "<!-- topics: governance, circuit-breaker -->\n",
    )

    return tmp_vault


# ---------------------------------------------------------------------------
# Keyword search
# ---------------------------------------------------------------------------


class TestKeywordSearch:
    def test_matches_title(self, monkeypatch, populated_vault):
        mod = _load_module(monkeypatch, populated_vault)
        records = mod.build_index()
        results = mod.search(records, query="small-world")
        assert len(results) >= 1
        paths = [r["path"] for r in results]
        assert any("claim-small-world" in p for p in paths)

    def test_matches_description(self, monkeypatch, populated_vault):
        mod = _load_module(monkeypatch, populated_vault)
        records = mod.build_index()
        results = mod.search(records, query="multiple hypothesis testing")
        assert len(results) >= 1
        paths = [r["path"] for r in results]
        assert any("method-bonferroni" in p for p in paths)

    def test_body_match_included(self, monkeypatch, populated_vault):
        """A keyword appearing only in the body should still return results."""
        mod = _load_module(monkeypatch, populated_vault)
        records = mod.build_index()
        # "circuit breaker activates" is only in the body of circuit-breaker-v1
        results = mod.search(records, query="activates")
        assert len(results) >= 1
        paths = [r["path"] for r in results]
        assert any("circuit-breaker-v1" in p for p in paths)


# ---------------------------------------------------------------------------
# Filters
# ---------------------------------------------------------------------------


class TestFilters:
    def test_tag_filter(self, monkeypatch, populated_vault):
        mod = _load_module(monkeypatch, populated_vault)
        records = mod.build_index()
        results = mod.search(records, tag="topology")
        # Only claim-small-world has the topology tag
        assert len(results) >= 1
        for r in results:
            assert any("topology" in t.lower() for t in r["tags"])

    def test_type_filter(self, monkeypatch, populated_vault):
        mod = _load_module(monkeypatch, populated_vault)
        records = mod.build_index()
        results = mod.search(records, note_type="method")
        assert len(results) >= 1
        for r in results:
            assert r["type"] == "method"

    def test_confidence_filter(self, monkeypatch, populated_vault):
        mod = _load_module(monkeypatch, populated_vault)
        records = mod.build_index()
        results = mod.search(records, confidence="high")
        assert len(results) >= 1
        for r in results:
            assert r["confidence"] == "high"

    def test_combined_type_and_query(self, monkeypatch, populated_vault):
        """Combining type filter with keyword narrows results correctly."""
        mod = _load_module(monkeypatch, populated_vault)
        records = mod.build_index()
        results = mod.search(records, query="welfare", note_type="claim")
        for r in results:
            assert r["type"] == "claim"


# ---------------------------------------------------------------------------
# Ranking
# ---------------------------------------------------------------------------


class TestRanking:
    def test_tag_match_scores_higher_than_body_match(self, monkeypatch, populated_vault):
        """A note where the query matches a tag should rank above a body-only match."""
        mod = _load_module(monkeypatch, populated_vault)
        records = mod.build_index()

        # "governance" appears as a tag on claim-tax-welfare and circuit-breaker-v1
        # but also in the body. The ones with tag matches get +10 per tag match.
        results = mod.search(records, query="governance")
        assert len(results) >= 2

        # The top results should have "governance" in their tags
        top = results[0]
        assert any("governance" in t.lower() for t in top["tags"])
        assert top["_score"] >= 10  # tag match alone is worth 10

    def test_confidence_boosts_score(self, monkeypatch, populated_vault):
        """Notes with higher confidence should get a score boost."""
        mod = _load_module(monkeypatch, populated_vault)

        rec_high = {
            "tags": ["test"],
            "title": "test note",
            "description": "",
            "body": "",
            "confidence": "high",
        }
        rec_low = {
            "tags": ["test"],
            "title": "test note",
            "description": "",
            "body": "",
            "confidence": "low",
        }

        score_high = mod.score_record(rec_high, "test")
        score_low = mod.score_record(rec_low, "test")
        assert score_high > score_low
