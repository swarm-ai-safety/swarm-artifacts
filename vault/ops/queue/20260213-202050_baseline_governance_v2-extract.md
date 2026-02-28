---
type: extract
run_id: 20260213-202050_baseline_governance_v2
run_path: runs/20260213-202050_baseline_governance_v2/
next_claim_start: 16
status: pending
created: 2026-02-20
---

# Extract task: 20260213-202050_baseline_governance_v2

Run: runs/20260213-202050_baseline_governance_v2

## Run metadata

Type: sweep
Swept parameters: governance.transaction_tax_rate (0.0, 0.025, 0.05, 0.075, 0.1, 0.125, 0.15), governance.circuit_breaker_enabled (false, true)
Total runs: 700
Total hypotheses tested: 132
Significant findings: 18
Artifacts: summary.json, sweep_results.csv, council_review.json, council_review_heterogeneous.json

## Notes for extraction

Expanded v2 of baseline governance sweep with finer tax rate grid (7 levels vs 4). 700 runs gives strong statistical power. 18 significant findings from 132 hypotheses — rich extraction target. Check for replication of v1 findings and new discoveries from finer granularity. Heterogeneous council review may contain additional governance mechanism insights.
