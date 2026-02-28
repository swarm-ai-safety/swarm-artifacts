---
description: 'Red-team evaluation: ? attacks tested, grade ?'
type: experiment
status: completed
run_id: redteam
experiment_type: redteam
created: '2026-02-21'
---

# red-team evaluation scores ? (?) against baseline governance

## Design

- **Type**: Red-team adversarial evaluation
- **Attacks tested**: ?
- **SWARM version**: unknown @ `unknown`

### Governance configuration

Not recorded

## Key results

- **Robustness score**: ?
- **Grade**: ?
- **Attacks successful**: ?/?
- **Evasion rate**: ?
- **Total damage allowed**: ?

### Vulnerabilities

No vulnerabilities recorded

## Claims affected

- [[claim-coordination-attacks-dominate-redteam-damage]] (low) — redteam, sybil
- [[claim-resource-drain-is-binding-vulnerability-in-contract-screening]] (low) — contract-screening, redteam
- [[claim-sybil-attacks-resist-full-governance-stack]] (medium) — redteam, sybil

## Artifacts

- Report: `runs/redteam/report.json`

## Reproduction

```bash
python -m swarm redteam contract_screening
```

---

Topics:
- [[_index]]

<!-- topics: redteam, contract-screening, sybil -->
