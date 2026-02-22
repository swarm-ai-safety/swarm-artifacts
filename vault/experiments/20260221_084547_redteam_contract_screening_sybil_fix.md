---
description: Redteam evaluation of contract screening with sybil detection enabled, testing governance stack with enhanced sybil defense
type: experiment
status: completed
run_id: redteam
experiment_type: redteam
created: '2026-02-21'
aliases:
- 20260221_084547_redteam_contract_screening_sybil_fix
cssclasses:
- experiment
- experiment-redteam
tags:
- redteam
- contract-screening
- sybil
- governance
graph-group: experiment
---

# contract screening redteam with sybil detection shows D grade (0.70) with 5/8 attacks prevented

## Design

- **Hypothesis**: Sybil detection mechanism improves governance robustness in the contract screening scenario
- **Type**: Redteam evaluation (8-attack battery)
- **Governance config**: Full stack with sybil detection enabled (similarity threshold 0.85), collusion detection (correlation threshold 0.8), circuit breakers, audit (20%), staking, 2% transaction tax

## Key results

- **Robustness score**: 0.70 (D grade)
- **Attacks prevented**: 5/8
- **Attacks successful**: 3/8
- **Overall evasion rate**: 23.75%
- **Detection latency**: 7.4 epochs
- **Total damage**: 212.47

### Vulnerabilities

- Resource drain succeeded with 53 damage (critical)
- Additional 2 attacks succeeded (details in JSON report)

## Claims supported

- [[claim-sybil-attacks-resist-full-governance-stack]]
- [[claim-full-governance-stack-prevents-most-attack-types]]

## Source

- `runs/redteam/20260221_084547_contract_screening_sybil_fix.txt`
- `runs/redteam/20260221_084547_contract_screening_sybil_fix.json`

<!-- topics: redteam, contract-screening, sybil, governance -->
