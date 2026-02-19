# SWARM Research OS: Repo Layout & Artifact Schema

*Spec v0.1 — 2026-02-18*

This document formalizes the artifact contracts for SWARM Research OS.
It is designed to be **backwards-compatible** with the ~90 existing runs
in `runs/` while adding the structure needed for automated synthesis,
claim tracking, and reproducibility.

---

## 1. Repo Layout

```
swarm-research-os/
│
├── scenarios/                     # INPUT: experiment definitions
│   ├── benchmarks/                #   standard benchmark suite (canaries)
│   ├── sweeps/                    #   parameter sweep specs
│   └── hypotheses/                #   hypothesis-driven experiments
│
├── runs/                          # OUTPUT: one folder per run (heavy, .gitignore traces)
│   └── <run-id>/                  #   naming: YYYYMMDD-HHMMSS_<slug>
│       ├── run.yaml               #   ← NEW: standardized metadata envelope
│       ├── scenario.yaml          #   fully-resolved scenario (frozen copy)
│       ├── summary.json           #   aggregate metrics
│       ├── csv/                   #   tabular data (epochs, sweeps)
│       ├── traces/                #   interaction-level data (gitignored)
│       └── plots/                 #   generated visualizations
│
├── vault/                         # KNOWLEDGE: arscontexta-managed research memory
│   ├── experiments/               #   one note per experiment (auto-generated)
│   ├── claims/                    #   claim cards with evidence pointers
│   ├── governance/                #   governance mechanism notes
│   ├── topologies/                #   topology behavior notes
│   ├── failures/                  #   named failure patterns
│   ├── methods/                   #   methodology notes
│   ├── sweeps/                    #   sweep summary notes
│   └── _index.md                  #   MOC: master index
│
├── schemas/                       # CONTRACTS: JSON Schema for all artifact types
│   ├── run.schema.yaml            #   run metadata envelope
│   ├── scenario.schema.yaml       #   scenario input spec
│   ├── summary.schema.yaml        #   summary output spec
│   ├── claim.schema.yaml          #   claim card spec
│   └── sweep.schema.yaml          #   sweep aggregation spec
│
├── scripts/                       # TOOLING: automation
│   ├── validate-run.py            #   validate a run folder against schemas
│   ├── generate-note.py           #   run → vault experiment note
│   ├── index-runs.py              #   rebuild run index
│   └── diff-runs.py               #   compare two runs
│
├── .gitignore                     #   ignore traces/, large CSVs
├── run-index.yaml                 #   auto-generated index of all runs
└── RESEARCH_OS_SPEC.md            #   this file
```

### What goes in git vs. what doesn't

| In git | NOT in git (gitignored) |
|--------|------------------------|
| `run.yaml` (metadata envelope) | `traces/*.parquet` / `traces/*.jsonl` |
| `scenario.yaml` (frozen config) | Raw CSV > 10MB |
| `summary.json` (aggregate metrics) | `plots/*.png` (regenerable) |
| `csv/*.csv` (epoch summaries, sweep results) | Intermediate analysis artifacts |
| `vault/**/*.md` (all knowledge notes) | |
| `schemas/**` | |

Large artifacts get content-addressed via SHA-256 in `run.yaml` so they
can be stored in releases / object storage and still verified.

---

## 2. Artifact Schemas

### 2.1 `run.yaml` — The Metadata Envelope

Every run folder MUST contain a `run.yaml`. This is the single source of
truth for what happened, when, with what code, and where to find everything.

```yaml
# -- identity --
run_id: "20260213-202050_baseline_governance_v2"
slug: "baseline_governance_v2"
created_utc: "2026-02-13T20:20:50Z"

# -- provenance --
provenance:
  swarm_version: "0.14.2"
  git_sha: "a1b2c3d"
  git_dirty: false
  python_version: "3.11.7"
  platform: "darwin-arm64"
  command: "python -m swarm sweep scenarios/sweeps/baseline_governance.yaml --seeds 50"

# -- experiment design --
experiment:
  type: "sweep"                    # one of: single | sweep | redteam | study | calibration
  hypothesis: >
    Transaction tax > 0.05 reduces welfare; circuit breakers compensate.
  scenario_ref: "scenarios/sweeps/baseline_governance.yaml"
  scenario_sha256: "e3b0c44..."
  swept_parameters:
    governance.transaction_tax_rate: [0.0, 0.025, 0.05, 0.075, 0.1, 0.125, 0.15]
    governance.circuit_breaker_enabled: [false, true]
  seeds: [1, 2, 3, "...", 50]
  total_runs: 700
  epochs_per_run: 10
  steps_per_epoch: 10

# -- results summary --
results:
  status: "completed"              # completed | failed | partial
  wall_time_seconds: 1847
  primary_metric: "welfare"
  primary_result: "tax > 0.075 significantly reduces welfare (d=1.18, p<1e-14)"
  significant_findings: 18
  total_hypotheses_tested: 132
  p_hacking_audit:
    pre_registered: true
    bonferroni_significant: 18
    holm_bonferroni_significant: 22

# -- artifacts manifest --
artifacts:
  summary: "summary.json"
  sweep_csv: "sweep_results.csv"
  epoch_csvs: []                   # empty for sweeps; populated for single runs
  traces: []                       # paths to trace files (may be external)
  plots:
    - path: "plots/welfare_vs_tax.png"
      description: "Welfare as a function of transaction tax rate"
  scripts:
    - "analyze.py"
    - "generate_plots.py"
    - "run_sweep.py"
  external:                        # large files stored outside git
    - path: "traces/interactions.parquet"
      sha256: "abc123..."
      size_bytes: 52428800
      storage: "gh-release:v0.14.2-runs"

# -- links --
links:
  parent_runs: []                  # run_ids this builds on
  child_runs: []                   # run_ids that extend this
  claims: ["claim-circuit-breakers-dominate", "claim-tax-welfare-tradeoff"]
  paper: "research/papers/baseline_governance.tex"
  pr: null                         # GitHub PR number if applicable
  issue: null                      # GitHub issue number if applicable

# -- tags --
tags: ["governance", "sweep", "circuit-breaker", "transaction-tax", "welfare"]
```

#### Field definitions

| Field | Required | Type | Description |
|-------|----------|------|-------------|
| `run_id` | yes | string | Folder name. Format: `YYYYMMDD-HHMMSS_<slug>` |
| `slug` | yes | string | Human-readable short name |
| `created_utc` | yes | datetime | When the run started |
| `provenance.swarm_version` | yes | string | Semver of SWARM |
| `provenance.git_sha` | yes | string | Commit hash of SWARM repo |
| `provenance.git_dirty` | yes | bool | Whether the working tree had uncommitted changes |
| `experiment.type` | yes | enum | `single`, `sweep`, `redteam`, `study`, `calibration` |
| `experiment.hypothesis` | no | string | What the experiment tests (free text) |
| `experiment.scenario_ref` | yes | string | Path to scenario YAML |
| `experiment.scenario_sha256` | yes | string | SHA-256 of the scenario file |
| `experiment.seeds` | yes | list[int] | All seeds used |
| `results.status` | yes | enum | `completed`, `failed`, `partial` |
| `results.primary_metric` | no | string | The metric the experiment is about |
| `results.primary_result` | no | string | One-sentence finding |
| `artifacts.*` | yes | object | Manifest of all files in the run folder |
| `links.claims` | no | list[string] | Claim IDs this run supports/weakens |
| `tags` | yes | list[string] | Searchable tags |

### 2.2 `scenario.yaml` — Experiment Input

Already well-defined by SWARM. The frozen copy in each run folder is the
**fully-resolved** version (all defaults filled, no template references).

Existing format is preserved. Key sections:

```yaml
scenario_id: string               # unique identifier
description: string               # what this scenario tests
motif: string                     # research theme

agents:                            # agent composition
  - type: enum                     # honest | adversarial | adaptive_adversary | ...
    count: int

governance:                        # governance knobs
  transaction_tax_rate: float
  circuit_breaker_enabled: bool
  # ... (all governance parameters)

network:                           # topology
  topology: enum                   # ring | random | small_world | complete | ...
  params: object
  dynamic: bool

simulation:                        # execution parameters
  n_epochs: int
  steps_per_epoch: int
  seed: int

payoff:                            # payoff function parameters
  s_plus: float
  s_minus: float
  h: float
  theta: float
  w_rep: float

success_criteria:                  # pass/fail thresholds
  max_avg_toxicity: float
  min_total_welfare: float
  # ...
```

### 2.3 `summary.json` — Run Output

Three variants depending on `experiment.type`:

#### 2.3.1 Single run summary

```jsonc
{
  "simulation_id": "string",
  "seed": 42,
  "n_epochs": 10,
  "steps_per_epoch": 10,
  "n_agents": 8,

  // aggregate metrics (final epoch or whole-run)
  "welfare": 125.07,
  "toxicity_rate": 0.336,
  "acceptance_rate": 0.897,
  "quality_gap": 0.162,
  "gini_coefficient": 0.15,

  // per-agent-type breakdown
  "agent_type_metrics": {
    "honest": { "avg_payoff": 21.39, "avg_reputation": 0.82 },
    "adversarial": { "avg_payoff": 3.26, "avg_reputation": 0.12 }
  },

  // governance telemetry
  "governance_events": {
    "freezes": 3,
    "audits": 12,
    "collusion_flags": 1,
    "tax_collected": 45.2
  },

  // network state
  "network_final": {
    "n_edges": 24,
    "avg_degree": 3.0,
    "avg_clustering": 0.42,
    "n_components": 1
  }
}
```

#### 2.3.2 Sweep summary

```jsonc
{
  "total_runs": 700,
  "total_hypotheses": 132,
  "swept_parameters": { /* param: [values] */ },

  "results": [
    {
      "parameter": "governance.transaction_tax_rate",
      "metric": "welfare",
      "value_1": 0.025,
      "value_2": 0.15,
      "n_1": 100,
      "n_2": 100,
      "mean_1": 59.07,
      "mean_2": 50.96,
      "sd_1": 7.28,
      "sd_2": 6.41,
      "t_stat": 8.36,
      "t_p": 1.2e-14,
      "u_stat": 7916.0,
      "u_p": 1.05e-12,
      "cohens_d": 1.18,
      "effect_class": "large",          // small | medium | large
      "bootstrap_diff_lo": 6.21,
      "bootstrap_diff_hi": 10.01,
      "bonferroni_sig": true,
      "bh_sig": true
    }
    // ... more comparisons
  ],

  "p_hacking_audit": {
    "total_hypotheses": 132,
    "pre_registered": true,
    "nominally_significant": 35,
    "bonferroni_significant": 18,
    "holm_bonferroni_significant": 22
  }
}
```

#### 2.3.3 Redteam summary

```jsonc
{
  "governance_config": { /* snapshot */ },
  "evaluated_at": "2026-02-12T23:11:33Z",
  "attacks_tested": 8,
  "attacks_successful": 6,
  "attacks_prevented": 2,
  "overall_evasion_rate": 0.42,
  "overall_detection_latency": 13.9,
  "total_damage_allowed": 455.7,
  "robustness_score": 0.40,
  "grade": "F",                    // A | B | C | D | F

  "vulnerabilities": [
    {
      "vulnerability_id": "string",
      "severity": "critical",      // critical | high | medium | low
      "description": "string",
      "attack_vector": "string",   // exploitation | coordination | evasion | ...
      "affected_lever": "string",  // which governance lever is weak
      "exploitation_difficulty": "string",
      "potential_damage": 97.2,
      "mitigation": "string"
    }
  ]
}
```

### 2.4 Claim Card — `vault/claims/<claim-id>.md`

Claims are the **atoms of scientific memory**. Each claim is a Markdown
file in the vault with structured frontmatter.

```yaml
---
description: "Transaction tax above 5% significantly reduces welfare with large effect size"
type: claim
status: active                     # active | weakened | superseded | retracted
confidence: high                   # high | medium | low | contested
domain: governance

# evidence
evidence:
  supporting:
    - run: "20260213-202050_baseline_governance_v2"
      metric: "welfare"
      detail: "d=1.18, p<1e-14, N=700, Bonferroni-corrected"
    - run: "20260213-173805_baseline_governance"
      metric: "welfare"
      detail: "d=0.95, p<0.001, N=280"
  weakening: []
  boundary_conditions:
    - "Effect measured in small-world topology with 8 agents"
    - "Tax range tested: 0-15%"
    - "Does not account for redistribution effects"

# sensitivity
sensitivity:
  topology: "untested beyond small_world"
  agent_count: "untested beyond 8"
  governance_interaction: "circuit breakers partially compensate (see claim-cb-compensation)"

# genealogy
supersedes: []
superseded_by: []
related_claims:
  - "claim-circuit-breakers-dominate"
  - "claim-smarter-agents-earn-less"

created: 2026-02-13
updated: 2026-02-18
---

Transaction tax above 5% significantly reduces aggregate welfare.

## Evidence summary

The baseline governance v2 sweep (700 runs, 50 seeds per config, 7 tax levels x 2 circuit-breaker states) shows that increasing `transaction_tax_rate` from 0.025 to 0.15 reduces mean welfare from 59.1 to 51.0 (Cohen's d = 1.18, Bonferroni-corrected p < 1e-14).

This replicates the v1 finding (280 runs, d = 0.95) with finer granularity and stronger statistical controls.

## Boundary conditions

- Topology: small_world (k=4, p=0.15). Ring and random topologies untested.
- Agent count: 8 (4 honest, 2 adversarial, 2 adaptive). Population scaling untested.
- The interaction with circuit breakers is significant: enabling circuit breakers at tax >= 0.075 partially recovers welfare. See [[claim-circuit-breakers-dominate]].

## Open questions

- Does the effect hold in ring topology where information flow is constrained?
- Is there a tax level where governance benefit (reduced adversarial payoff) outweighs welfare cost?
- How does agent heterogeneity (mixed strategies) change the threshold?

<!-- topics: governance, transaction-tax, welfare, sweep-result -->
```

### 2.5 Experiment Note — `vault/experiments/<run-id>.md`

Auto-generated from `run.yaml` + `summary.json`. One note per run.

```yaml
---
description: "Baseline governance v2: 700-run sweep of tax rate and circuit breakers"
type: experiment
status: completed
run_id: "20260213-202050_baseline_governance_v2"
experiment_type: sweep
created: 2026-02-13
---

## Design

- **Hypothesis**: Transaction tax > 0.05 reduces welfare; circuit breakers compensate.
- **Type**: Parameter sweep
- **Parameters swept**: `transaction_tax_rate` (7 levels), `circuit_breaker_enabled` (2 levels)
- **Seeds**: 50 per config
- **Total runs**: 700
- **SWARM version**: 0.14.2 @ `a1b2c3d`

## Key results

- 18 Bonferroni-significant findings out of 132 hypotheses tested
- Primary: tax 0.025→0.15 reduces welfare by 8.1 units (d=1.18, p<1e-14)
- Circuit breaker interaction: enables partial welfare recovery at high tax

## Claims affected

- Supports: [[claim-tax-welfare-tradeoff]]
- Supports: [[claim-circuit-breakers-dominate]]

## Artifacts

- Summary: `runs/20260213-202050_baseline_governance_v2/summary.json`
- Sweep CSV: `runs/20260213-202050_baseline_governance_v2/sweep_results.csv`
- Scripts: `analyze.py`, `generate_plots.py`, `run_sweep.py`

## Reproduction

```bash
python -m swarm sweep scenarios/sweeps/baseline_governance.yaml --seeds 50
```

<!-- topics: governance, sweep, circuit-breaker, transaction-tax -->
```

### 2.6 Sweep Note — `vault/sweeps/<sweep-name>.md`

Cross-run aggregation for a parameter sweep series.

```yaml
---
description: "All runs exploring transaction tax sensitivity across governance configs"
type: sweep-summary
status: active
parameter: "governance.transaction_tax_rate"
created: 2026-02-10
updated: 2026-02-18
---

## Runs in this sweep

| Run ID | Date | Seeds | Tax levels | CB states | Key finding |
|--------|------|-------|------------|-----------|-------------|
| 20260213-173805 | Feb 13 | 10 | 4 | 2 | d=0.95, sig |
| 20260213-202050 | Feb 13 | 50 | 7 | 2 | d=1.18, sig |

## Convergence

The effect is robust across both runs. Increasing seed count from 10→50
narrowed confidence intervals without changing direction or significance.

## Phase transition surface

Tax threshold for significant welfare loss: ~0.05 (below this, effect is negligible).
Circuit breaker partially compensates above 0.075.

<!-- topics: governance, transaction-tax, sweep-series -->
```

---

## 3. Run Index — `run-index.yaml`

Auto-generated. Provides a searchable catalog of all runs without
having to traverse the filesystem.

```yaml
# Auto-generated by scripts/index-runs.py
# Do not edit manually.
generated_utc: "2026-02-18T00:00:00Z"
total_runs: 93

runs:
  - id: "20260208-214018_baseline_seed42"
    type: single
    tags: [baseline]
    date: "2026-02-08"
    status: completed

  - id: "20260213-202050_baseline_governance_v2"
    type: sweep
    tags: [governance, sweep, circuit-breaker, transaction-tax]
    date: "2026-02-13"
    status: completed
    total_configs: 14
    total_runs: 700

  # ... etc
```

---

## 4. Experiment Types — Taxonomy

| Type | Description | Key outputs | Example |
|------|-------------|-------------|---------|
| `single` | One scenario, one seed | `history.json`, `csv/<name>_epochs.csv`, `plots/` | `baseline_seed42` |
| `sweep` | Parameter grid, multiple seeds | `sweep_results.csv`, `summary.json` | `baseline_governance_v2` |
| `redteam` | Adversarial evaluation | `report.json`, `report.txt` | `redteam_strict_governance` |
| `study` | Multi-factor analysis | `sweep_results.csv`, `analysis/summary.json` | `ldt_acausality_study` |
| `calibration` | Hyperparameter tuning | `runs.csv`, `recommendation.json`, `summary.json` | `tau_k_calibration` |

---

## 5. Migration Path

The ~90 existing runs in `runs/` predate this spec. Migration strategy:

### Phase 1: Generate `run.yaml` for existing runs (automated)

For each existing run folder:
1. Parse folder name → `run_id`, `created_utc`, `slug`
2. Detect `experiment.type` from contents:
   - Has `sweep_results.csv` → `sweep`
   - Has `report.json` with `attacks_tested` → `redteam`
   - Has `analysis/summary.json` → `study`
   - Has `recommendation.json` → `calibration`
   - Has `history.json` + `csv/` → `single`
3. Read `scenario.yaml` if present → `experiment.scenario_ref`
4. Read `summary.json` if present → `results.*`
5. Inventory all files → `artifacts.*`
6. Set `provenance.git_sha` to "unknown" (retroactive)
7. Set `tags` from folder name heuristics

### Phase 2: Generate vault notes (automated)

For each `run.yaml`:
1. Generate `vault/experiments/<run-id>.md` from template
2. Identify related runs by tag overlap → link them
3. Populate `vault/sweeps/` for runs sharing swept parameters

### Phase 3: Manual claim extraction

Claims require human judgment. Seed the process by:
1. Mining existing posts in `research/posts/` for claims
2. Mining paper abstracts in `research/papers/` for findings
3. Creating stub claim cards with evidence pointers

---

## 6. Validation

### Run validation rules

A valid run folder MUST have:
- `run.yaml` with all required fields
- `scenario.yaml` OR `experiment.scenario_ref` pointing to a committed scenario
- At least one of: `summary.json`, `csv/`, `report.json`

A valid run folder SHOULD have:
- `results.status == "completed"`
- `provenance.git_dirty == false`
- All files listed in `artifacts.*` actually present

### Claim validation rules

A valid claim card MUST have:
- `status` is one of: `active`, `weakened`, `superseded`, `retracted`
- At least one entry in `evidence.supporting` with a valid `run` reference
- `confidence` consistent with evidence (high requires Bonferroni-significant result)

### Schema enforcement

JSON Schema files in `schemas/` can be used with any validator.
The `scripts/validate-run.py` script checks a run folder against all
applicable schemas and reports violations.

---

## 7. Content-Addressing Convention

For artifacts too large for git, reference them by SHA-256:

```yaml
artifacts:
  external:
    - path: "traces/interactions.parquet"
      sha256: "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
      size_bytes: 52428800
      storage: "gh-release:v0.14.2-runs"
```

Verification: `sha256sum traces/interactions.parquet` must match.

This ensures that even when large files live outside git, every reference
is verifiable and every experiment remains reproducible.
