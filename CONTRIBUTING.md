# Contributing to SWARM Research OS

This guide covers the practical workflows for adding runs, creating claims, synthesizing notes, and running analysis pipelines.

---

## 1. Adding new runs

Each run lives in `runs/<YYYYMMDD-HHMMSS>_<slug>/` and must contain a `run.yaml` metadata envelope.

```bash
# If run.yaml doesn't exist yet (e.g., legacy runs):
python scripts/backfill-run-yaml.py

# Validate the run against schemas:
python scripts/validate-run.py runs/<run_id>

# Update the run index:
python scripts/index-runs.py

# Add semantic tags:
python scripts/enrich-tags.py --run-id <run_id>
```

The `run.yaml` file is the single source of truth for what happened, when, with what code, and where to find artifacts. See `schemas/run.schema.yaml` for the full contract.

---

## 2. Creating claims

Claims are atoms of scientific memory. **Never auto-generate them** -- every claim requires human judgment.

**Filename:** `vault/claims/claim-<kebab-case-proposition>.md`

**Template:** Follow `vault/templates/claim-card.md` exactly.

**Required frontmatter fields:**

| Field | Constraint |
|-------|-----------|
| `description` | <=200 chars, no trailing period |
| `type` | `claim` |
| `status` | `active` (initial) |
| `confidence` | `high`, `medium`, or `low` |
| `evidence` | List with real `run_id` references |

**Confidence criteria:**

| Level | Criteria |
|-------|---------|
| **high** | Bonferroni-significant AND replicated across >=2 independent runs/seeds |
| **medium** | Nominally significant OR single-sweep with BH correction |
| **low** | Suggestive but underpowered (<20 seeds) or unreplicated |

**Status flow:** `active` -> `weakened` -> `superseded` -> `retracted`

Every status change must be visible and explained in the note.

```bash
# Validate after creating or editing claims:
python scripts/validate-vault.py --all
```

---

## 3. Synthesizing experiment notes

Experiment notes in `vault/experiments/` are **auto-generated** from run data. Do not manually edit them.

```bash
# Generate a note for one run:
python scripts/generate-note.py <run_id>

# Generate notes for all runs:
python scripts/generate-note.py --all
```

If a generated note is wrong, fix the underlying `run.yaml` or the generation script -- never patch the note by hand.

---

## 4. Running the analysis pipeline

```bash
# Audit claim evidence and status transitions:
python scripts/claim-lifecycle.py

# Detect parameter interactions across runs:
python scripts/cross-correlate.py

# See what changed in recent commits:
python scripts/vault-digest.py HEAD~5..HEAD
```

---

## 5. Vault conventions (kernel invariants)

These rules apply to **all** vault notes. Never violate them.

1. **Prose-as-title.** Every H1 is a complete proposition, not a label. Test: "This note argues that [title]."
2. **Description <=200 chars.** No trailing period. Must add information beyond the title.
3. **Topics footer mandatory.** Every note ends with `<!-- topics: tag1, tag2 -->`.
4. **Wiki-links inline as prose.** Write `This replicates [[baseline governance v2 sweep]]`, not bare link dumps.
5. **Evidence provenance mandatory.** Every evidence entry must reference a real `run_id` from `runs/`.
6. **Effect sizes with correction methods.** Never report raw p-values without Bonferroni/Holm/BH correction.

---

## 6. Pre-commit hook

Install the hook to validate vault notes and run schemas before every commit:

```bash
ln -sf ../../scripts/pre-commit-hook.sh .git/hooks/pre-commit
```

The hook runs `validate-run.py` and `validate-vault.py` and blocks the commit on failure.

---

## 7. Running tests

```bash
pip install pytest
pytest
```

Run from the repo root.

---

## 8. Obsidian integration

The `vault/` directory is designed to work as an Obsidian vault:

1. Open `vault/` as a vault in Obsidian.
2. Install the **Dataview** community plugin (required for claim queries and sweep tables).
3. Enable the `swarm-graph` CSS snippet for graph-view styling.

Wiki-links, frontmatter, and the `_index.md` MOC all follow Obsidian conventions out of the box.
