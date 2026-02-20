# SWARM Research OS

Continuous integration for multi-agent science. This repo is the artifact store and knowledge vault for the [SWARM](https://github.com/swarm-ai-safety/swarm) multi-agent simulation framework.

## Vault statistics

| Category | Count |
|----------|-------|
| Claims | 12 (8 high, 2 medium, 2 low confidence) |
| Experiment notes | 110 |
| Runs indexed | 110 |
| Failure patterns | 8 (2 critical, 4 high, 2 medium) |
| Governance mechanisms | 6 |
| Statistical methods | 7 |
| Sweep summaries | 7 |
| Network topologies | 5 |
| **Total vault notes** | **155** |

## Architecture

```
┌─────────────────────────────────────────────────────────┐
│                    GitHub Actions CI                      │
│  ci.yml │ synthesize.yml │ nightly.yml │ vault-health.yml │
└────┬────────────┬──────────────┬──────────────┬──────────┘
     │            │              │              │
     ▼            ▼              ▼              ▼
┌─────────┐ ┌──────────┐ ┌───────────┐ ┌────────────┐
│ Validate │ │Synthesize│ │ Regression│ │ Health     │
│ schemas  │ │ notes    │ │ canaries  │ │ audit      │
└─────────┘ └────┬─────┘ └───────────┘ └────────────┘
                  │
                  ▼
┌─────────────────────────────────────────────────────────┐
│                   Knowledge Vault                        │
│                                                          │
│  claims/     12 findings with evidence chains            │
│  experiments/ 110 auto-synthesized experiment notes      │
│  governance/  6 mechanism profiles                       │
│  failures/    8 attack patterns from red-team            │
│  methods/     7 statistical method references            │
│  sweeps/      7 cross-run parameter aggregations         │
│  topologies/  5 network structure notes                  │
│  _index.md    Master index (MOC)                         │
│                                                          │
└──────────────────────┬──────────────────────────────────┘
                       │
                       ▼
┌─────────────────────────────────────────────────────────┐
│                    Inngest Pipeline                       │
│  swarm/run.completed → validate → synthesize → index     │
│  swarm/sweep.completed → analyze → claim-match → notify  │
│  swarm/redteam.completed → grade → failure-extract       │
└─────────────────────────────────────────────────────────┘
```

## Quickstart

```bash
# Install dependencies
pip install -r requirements.txt

# Validate everything
python scripts/validate-run.py --all
python scripts/validate-vault.py --all
python scripts/vault-health.py

# Search the vault
python scripts/vault-search.py "transaction tax"
python scripts/vault-search.py --type claim --confidence high

# View statistics
python scripts/vault-stats.py

# Synthesize new experiment notes
python scripts/generate-note.py --all

# Audit claim evidence
python scripts/claim-lifecycle.py

# Generate changelog
python scripts/vault-digest.py HEAD~5..HEAD
```

## Key findings

The vault contains 12 active claims. Highlights:

| Claim | Confidence | Key result |
|-------|------------|------------|
| Circuit breakers dominate | High | CB-only: +81% welfare, -11% toxicity vs baseline (d=1.64) |
| Tax-welfare tradeoff | High | Tax >5% significantly reduces welfare (d=1.18) |
| Tax phase transition | High | Non-linear welfare decline with S-curve at 5-10% |
| Smarter agents earn less | High | Depth-5 RLM agents earn 2.3-2.8x less than honest agents |
| Collusion wealth destruction | High | 137x wealth gap under behavioral monitoring (d=3.51) |
| Sybil attacks universal | Critical | 100% success rate across all governance configurations |

## Scripts

### Validation
| Script | Purpose |
|--------|---------|
| `validate-run.py --all` | Validate run.yaml schemas |
| `validate-vault.py --all` | Validate vault note conventions |
| `vault-health.py` | Comprehensive audit (evidence, wiki-links, index) |

### Synthesis
| Script | Purpose |
|--------|---------|
| `generate-note.py --all` | Synthesize experiment notes from runs |
| `generate-sweep-notes.py` | Generate cross-run sweep summaries |
| `backfill-run-yaml.py` | Generate run.yaml for existing run dirs |

### Enrichment
| Script | Purpose |
|--------|---------|
| `enrich-tags.py` | Mine semantic tags from run content |
| `obsidian-metadata.py` | Add Obsidian graph metadata to vault notes |

### Analysis
| Script | Purpose |
|--------|---------|
| `claim-lifecycle.py` | Audit claim evidence and recommend status changes |
| `cross-correlate.py` | Detect parameter interactions across sweeps |
| `diff-runs.py <a> <b>` | Compare two runs side-by-side |
| `claim-graph.py` | Generate claim dependency graph (Mermaid/DOT) |
| `run-provenance.py` | Detect run lineage chains |

### Search & Reporting
| Script | Purpose |
|--------|---------|
| `vault-search.py "query"` | Search vault by keyword, tag, or type |
| `vault-stats.py` | Vault statistics summary |
| `vault-digest.py HEAD~5..HEAD` | Git-based vault changelog |

### Indexing & Events
| Script | Purpose |
|--------|---------|
| `index-runs.py` | Rebuild run-index.yaml |
| `emit-event.py <run_id>` | Emit Inngest event for a run |

## GitHub Actions workflows

| Workflow | Trigger | Purpose |
|----------|---------|---------|
| `ci.yml` | PR + push to main | Typecheck, validate runs + vault, check index |
| `synthesize.yml` | Push to main (runs/) | Auto-synthesize experiment notes, open PR |
| `nightly-regression.yml` | Cron 4 AM UTC | Run canary scenarios, detect drift |
| `vault-health.yml` | Weekly Mon 6 AM | Audit claims, evidence, wiki-links |
| `post-merge-benchmark.yml` | Push to main (scenarios/) | Benchmark new scenarios |
| `release.yml` | Push to main (vault/) | Milestone-based releases with auto notes |

## Obsidian integration

The `vault/` directory is designed to be opened as an Obsidian vault:

1. Open `vault/` as the Obsidian vault root
2. Install the [Dataview](https://github.com/blacksmithgu/obsidian-dataview) plugin
3. Enable the `swarm-graph` CSS snippet in Settings > Appearance
4. Open Graph View — nodes are color-coded by type:
   - **Red**: Claims (darker = higher confidence)
   - **Blue**: Experiments (by type)
   - **Green**: Sweep summaries
   - **Orange**: Governance mechanisms
   - **Purple**: Topologies
   - **Yellow/Red border**: Failure patterns
   - **Gray**: Methods

7 interactive dashboards are available from the index:
- Claims, Experiments, Sweeps, Failures, Governance, Evidence Trail, Stats

## Conventions

This vault follows [arscontexta](https://github.com/arscontexta) knowledge management conventions:

1. **Prose-as-title**: Every H1 is a complete proposition
2. **Description ≤200 chars**: No trailing period
3. **Topics footer**: Every note ends with `<!-- topics: tag1, tag2 -->`
4. **Evidence provenance**: Every evidence entry references a real run_id
5. **Effect sizes with correction**: Never raw p-values without Bonferroni/Holm/BH

## Reproducing runs

Runs can be regenerated from the main repo:

```bash
python -m swarm run scenarios/baseline.yaml --seed 42 --epochs 10 --steps 10
```

## Setup

See [docs/setup.md](docs/setup.md) for detailed setup instructions including GitHub Actions secrets, Inngest deployment, and pre-commit hooks.
