# SWARM Research OS — Setup Guide

## Prerequisites

- Python 3.10+
- Node.js 20+ (for Inngest pipeline)
- Docker + Docker Compose (optional, for local Inngest dev server)

## Python dependencies

```bash
pip install -r requirements.txt
```

Required packages: `pyyaml>=6.0`, `jsonschema>=4.0`

## Git hooks

Install the pre-commit hook to validate vault notes and run schemas before each commit:

```bash
# Symlink (recommended — stays in sync with repo)
ln -sf ../../scripts/pre-commit-hook.sh .git/hooks/pre-commit

# Or copy
cp scripts/pre-commit-hook.sh .git/hooks/pre-commit && chmod +x .git/hooks/pre-commit
```

The hook validates vault notes, run schemas, and checks run-index freshness only when relevant files are staged.

## Inngest pipeline (local)

```bash
cd inngest && npm ci
docker compose up          # Starts Inngest dev server + app
```

The app listens on `http://localhost:3000` and the Inngest dev server on `http://localhost:8288`.

To emit events manually:

```bash
python scripts/emit-event.py <run_id>                    # Send to local Inngest
INNGEST_URL=https://... python scripts/emit-event.py <run_id>  # Send to production
```

## GitHub Actions

The CI/CD workflows in `.github/workflows/` require these repository settings:

### Required secrets

| Secret | Purpose | Where to get it |
|--------|---------|-----------------|
| `INNGEST_URL` | Production Inngest event endpoint | Inngest dashboard → Events → Event Key |
| `INNGEST_SIGNING_KEY` | Inngest function signing | Inngest dashboard → Signing Key |

Set these in: **Settings → Secrets and variables → Actions → New repository secret**

### Required permissions

The `synthesize.yml` workflow creates PRs automatically. It needs:

- **Settings → Actions → General → Workflow permissions** → "Read and write permissions"
- Enable "Allow GitHub Actions to create and approve pull requests"

### Workflow overview

| Workflow | Trigger | Purpose |
|----------|---------|---------|
| `ci.yml` | PR + push to main | Typecheck Inngest, validate runs + vault, check index |
| `synthesize.yml` | Push to main (runs/) | Auto-synthesize new experiment notes, open PR |
| `nightly-regression.yml` | Cron 4 AM UTC + manual | Run canary scenarios, detect drift, create issue |
| `vault-health.yml` | Weekly Mon 6 AM + PR (vault/) | Audit claims, evidence, wiki-links, create issue |
| `post-merge-benchmark.yml` | Push to main (scenarios/) | Benchmark new/modified scenarios |

### Environment variables

| Variable | Default | Purpose |
|----------|---------|---------|
| `INNGEST_URL` | `http://localhost:8288/e/swarm-research-os` | Inngest event endpoint |
| `SWARM_ENGINE_PATH` | (none) | Path to SWARM simulation engine (for nightly regression) |

## Obsidian integration

The vault is designed to be opened as an Obsidian vault. After running the metadata enrichment:

```bash
python scripts/obsidian-metadata.py
```

Notes will have Obsidian-compatible frontmatter: `aliases`, `cssclasses`, `tags`, and `graph-group` fields for optimal graph view rendering.

### Recommended Obsidian settings

1. Open `vault/` as the Obsidian vault root
2. Enable "Detect all file extensions" in Settings → Files & Links
3. In Graph View, group nodes by the `graph-group` property:
   - `claim` → red
   - `experiment` → blue
   - `sweep-summary` → green
   - `governance` → orange
   - `topology` → purple
   - `failure` → yellow
   - `method` → gray

## Key scripts

```bash
# Validation
python scripts/validate-run.py --all          # Validate run schemas
python scripts/validate-vault.py --all        # Validate vault notes
python scripts/vault-health.py                # Comprehensive vault audit

# Synthesis
python scripts/generate-note.py --all         # Generate experiment notes
python scripts/generate-sweep-notes.py        # Generate sweep summaries

# Enrichment
python scripts/enrich-tags.py                 # Mine semantic tags from run content
python scripts/obsidian-metadata.py           # Add Obsidian graph metadata

# Analysis
python scripts/claim-lifecycle.py             # Audit claim evidence and status
python scripts/cross-correlate.py             # Detect parameter interactions
python scripts/diff-runs.py <run_a> <run_b>   # Compare two runs

# Indexing
python scripts/index-runs.py                  # Rebuild run-index.yaml
python scripts/backfill-run-yaml.py           # Generate run.yaml for existing runs

# Events
python scripts/emit-event.py <run_id>         # Emit Inngest event for a run
```
