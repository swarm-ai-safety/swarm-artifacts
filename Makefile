# SWARM Research OS — Makefile
# Common workflows for managing the knowledge vault.

.PHONY: validate synthesize audit search stats digest test release clean help

# ── Validation ──────────────────────────────────────────────────────────

validate: validate-runs validate-vault  ## Run all validations

validate-runs:  ## Validate all run.yaml schemas
	python scripts/validate-run.py --all

validate-vault:  ## Validate all vault notes
	python scripts/validate-vault.py --all

health:  ## Run comprehensive vault health audit
	python scripts/vault-health.py

# ── Synthesis ───────────────────────────────────────────────────────────

synthesize:  ## Synthesize all unsynthesized experiment notes
	python scripts/generate-note.py --all
	python scripts/generate-sweep-notes.py

synthesize-run:  ## Synthesize a single run (usage: make synthesize-run RUN=<run_id>)
	python scripts/generate-note.py $(RUN)

# ── Enrichment ──────────────────────────────────────────────────────────

enrich:  ## Enrich tags and Obsidian metadata
	python scripts/enrich-tags.py
	python scripts/obsidian-metadata.py

# ── Analysis ────────────────────────────────────────────────────────────

audit:  ## Full audit: validate + health + claim lifecycle
	python scripts/validate-run.py --all --quiet
	python scripts/validate-vault.py --all
	python scripts/vault-health.py
	python scripts/claim-lifecycle.py

lifecycle:  ## Audit claim evidence and status
	python scripts/claim-lifecycle.py

correlate:  ## Detect parameter interactions across sweeps
	python scripts/cross-correlate.py

provenance:  ## Show run lineage chains
	python scripts/run-provenance.py

graph:  ## Generate claim dependency graph
	python scripts/claim-graph.py --output vault/methods/claim-graph.md --include-runs

# ── Search & Reporting ──────────────────────────────────────────────────

search:  ## Search vault (usage: make search Q="transaction tax")
	python scripts/vault-search.py "$(Q)"

stats:  ## Show vault statistics
	python scripts/vault-stats.py

digest:  ## Show recent vault changes
	python scripts/vault-digest.py HEAD~5..HEAD

# ── Indexing ────────────────────────────────────────────────────────────

index:  ## Rebuild run index
	python scripts/index-runs.py

backfill:  ## Generate run.yaml for existing runs
	python scripts/backfill-run-yaml.py

# ── Testing ─────────────────────────────────────────────────────────────

test:  ## Run pytest test suite
	python -m pytest tests/ -v

test-quick:  ## Run tests (short output)
	python -m pytest tests/ -q

# ── Release ─────────────────────────────────────────────────────────────

release:  ## Generate release notes from last tag
	@LAST_TAG=$$(git describe --tags --abbrev=0 2>/dev/null || echo ""); \
	if [ -z "$$LAST_TAG" ]; then \
		echo "No previous release tag found"; \
	else \
		python scripts/vault-digest.py "$$LAST_TAG..HEAD"; \
	fi

# ── Pipeline (full workflow) ────────────────────────────────────────────

pipeline: validate synthesize enrich index audit stats  ## Run full pipeline

# ── Clean ───────────────────────────────────────────────────────────────

clean:  ## Remove Python caches
	find . -type d -name __pycache__ -exec rm -rf {} + 2>/dev/null || true
	find . -type f -name "*.pyc" -delete 2>/dev/null || true
	rm -rf .pytest_cache

# ── Help ────────────────────────────────────────────────────────────────

help:  ## Show this help
	@grep -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | sort | awk 'BEGIN {FS = ":.*?## "}; {printf "\033[36m%-16s\033[0m %s\n", $$1, $$2}'

.DEFAULT_GOAL := help
