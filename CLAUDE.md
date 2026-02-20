# SWARM Research OS — Project Instructions

This repo is the artifact store and knowledge vault for the SWARM multi-agent simulation framework. It uses arscontexta conventions for knowledge management.

## Repo structure

```
runs/           # One folder per experiment run (run.yaml + data)
vault/          # arscontexta knowledge vault
  claims/       # Claim cards — atoms of scientific memory
  experiments/  # Auto-generated experiment notes (one per run)
  governance/   # Governance mechanism notes
  topologies/   # Network topology notes
  failures/     # Named failure/vulnerability patterns
  sweeps/       # Cross-run sweep aggregations
  methods/      # Methodology notes
  templates/    # Schema-enforced templates for all note types
  _index.md     # Master index (MOC)
schemas/        # JSON Schema for run.yaml, claims, sweeps
scripts/        # Python automation (validation, synthesis, indexing)
inngest/        # Durable orchestration pipeline (TypeScript)
scenarios/      # SWARM scenario definitions (benchmarks, sweeps)
skills/         # arscontexta plugin skills (vault-init, synthesize, claim, verify)
```

## Kernel invariants

These rules apply to ALL vault notes. Never violate them:

1. **Prose-as-title.** Every H1 heading is a complete proposition, not a label. Test: "This note argues that [title]"
2. **description ≤200 chars.** No trailing period. Must add info beyond the title.
3. **Topics footer mandatory.** Every note ends with `<!-- topics: tag1, tag2 -->` or a visible `Topics:` section linking to `[[_index]]`.
4. **Wiki-links inline as prose.** Example: "This replicates [[baseline governance v2 sweep]]"
5. **Evidence provenance mandatory.** Every evidence entry must reference a real run_id in `runs/`.
6. **Effect sizes with correction methods.** Never report raw p-values without Bonferroni/Holm/BH.

## Claim confidence criteria

| Level | Criteria |
|-------|----------|
| **high** | Bonferroni-significant AND replicated across ≥2 independent runs/seeds |
| **medium** | Nominally significant OR single-sweep support with BH correction |
| **low** | Suggestive but underpowered (<20 seeds) or unreplicated |
| **contested** | Conflicting evidence from different runs |

## Experiment types

| Type | Description |
|------|-------------|
| `single` | One scenario, one seed → `history.json` |
| `sweep` | Parameter grid, multiple seeds → `summary.json`, `sweep_results.csv` |
| `redteam` | Adversarial evaluation → `report.json` |
| `study` | Multi-factor analysis → `analysis/summary.json` |
| `calibration` | Hyperparameter tuning → `recommendation.json` |

## Key scripts

```bash
# Validation
python scripts/validate-run.py --all          # Validate run schemas
python scripts/validate-vault.py --all        # Validate vault notes
python scripts/vault-health.py                # Comprehensive vault audit

# Synthesis
python scripts/backfill-run-yaml.py           # Generate run.yaml for existing runs
python scripts/generate-note.py --all         # Synthesize experiment notes
python scripts/generate-sweep-notes.py        # Generate sweep summaries

# Enrichment
python scripts/enrich-tags.py                 # Mine semantic tags from run content
python scripts/obsidian-metadata.py           # Add Obsidian graph metadata

# Analysis
python scripts/claim-lifecycle.py             # Audit claim evidence and status
python scripts/cross-correlate.py             # Detect parameter interactions
python scripts/diff-runs.py <a> <b>           # Compare two runs
python scripts/claim-graph.py                 # Generate claim dependency graph
python scripts/run-provenance.py              # Detect run lineage chains

# Search & reporting
python scripts/vault-search.py "query"        # Search vault by keyword/tag/type
python scripts/vault-stats.py                 # Vault statistics summary
python scripts/vault-digest.py HEAD~5..HEAD   # Changelog between commits

# Indexing & events
python scripts/index-runs.py                  # Rebuild run-index.yaml
python scripts/emit-event.py <run_id>         # Emit Inngest event
```

## Working with claims

- Never auto-edit claim cards without human judgment
- Claim filenames use `claim-` prefix + kebab-case proposition
- Status flow: `active → weakened → superseded → retracted`
- Every status change must be visible and explained

## Inngest pipeline

```bash
cd inngest && npm ci && npx tsc --noEmit   # Typecheck
docker compose up                           # Run locally
```

## Skills

Available slash commands: `/vault-init`, `/synthesize`, `/claim`, `/verify`

## Python dependencies

```bash
pip install pyyaml jsonschema
```
