---
type: extract
run_id: 20260213-221500_collusion_tax_effect
run_path: runs/20260213-221500_collusion_tax_effect/
next_claim_start: 21
status: pending
created: 2026-02-20
---

# Extract task: 20260213-221500_collusion_tax_effect

Run: runs/20260213-221500_collusion_tax_effect

## Run metadata

Type: sweep
Swept parameters: governance.transaction_tax_rate (0.0, 0.02, 0.05, 0.1), governance.collusion_penalty_multiplier (0.5, 1.0, 1.5, 2.0)
Total runs: 160
Total hypotheses tested: 60
Significant findings: 21
Artifacts: summary.json, sweep_results.csv

## Notes for extraction

Tax-collusion interaction sweep. High finding density (21/60 significant). Look for interaction effects between tax rate and collusion penalty — does tax substitute for or complement direct collusion penalties? Check for nonlinear thresholds. Connects to existing claims on tax phase transitions and collusion penalties.
