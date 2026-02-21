---
description: Full governance red-team replicates with-collusion results exactly; D grade, sybil remains critical vulnerability
type: experiment
status: completed
run_id: 20260221-082443_redteam_contract_screening_full
experiment_type: redteam
created: '2026-02-21'
aliases:
- 20260221-082443_redteam_contract_screening_full
cssclasses:
- experiment
- experiment-redteam
tags:
- redteam
- contract-screening
- adversarial
- full-governance
graph-group: experiment
---

# full governance contract screening red-team replicates D grade with identical attack outcomes

## Design

- **Type**: Red-team adversarial evaluation
- **Attacks tested**: 8
- **Seeds**: [0]
- **Parent run**: [[20260221-081106_redteam_contract_screening_no_collusion]]
- **SWARM version**: unknown @ `unknown`

### Governance configuration

Identical to [[20260221-081953_redteam_contract_screening_with_collusion]] — full governance stack with collusion detection enabled.

## Key results

- **Robustness score**: 0.607 (identical to with-collusion run)
- **Grade**: D
- **Attacks successful**: 4/8
- **Overall evasion rate**: 0.268
- **Total damage allowed**: 299.79

All 8 attack results are numerically identical to [[20260221-081953_redteam_contract_screening_with_collusion]], confirming deterministic evaluation with seed=0. This serves as a replication run.

### Replication confirmation

| Metric | With-Collusion Run | Full Run | Delta |
|--------|--------------------|----------|-------|
| Robustness score | 0.607 | 0.607 | 0 |
| Total damage | 299.79 | 299.79 | 0 |
| Evasion rate | 0.268 | 0.268 | 0 |
| Sybil damage | 105.84 | 105.84 | 0 |
| Collusion ring damage | 21.43 | 21.43 | 0 |

The identical results confirm that the "full" governance configuration is equivalent to "with collusion" — the full stack adds no additional mechanisms beyond what was already enabled.

## Claims affected

- Supports: [[claim-sybil-attacks-resist-full-governance-stack]] — sybil at 106 damage, replication
- Supports: [[claim-collusion-detection-is-binding-constraint-on-robustness]] — replication of D grade
- Supports: [[claim-full-governance-stack-prevents-most-attack-types]] — 4/8 prevented

## Artifacts

- Report: `runs/20260221-082443_redteam_contract_screening_full/report.json`

## Reproduction

```bash
python -m swarm redteam contract_screening --full-governance --seed 0
```

---

Topics:
- [[_index]]
- [[governance-dashboard]]
- [[failures-dashboard]]

<!-- topics: redteam, contract-screening, adversarial, full-governance -->
