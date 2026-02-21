---
name: stats
description: Show SWARM vault metrics — claim counts by confidence, experiment coverage, failure pattern status, sweep series, pipeline queue state. Triggers on "/stats", "vault stats", "how many claims", "what's in the vault".
user-invocable: true
allowed-tools: Read, Glob, Grep, Bash
context: fork
---

## EXECUTE NOW

Gather and display vault metrics.

---

# Stats

```bash
# Claim counts
echo "=== Claims ==="
total=$(ls vault/claims/*.md 2>/dev/null | wc -l | tr -d ' ')
high=$(rg '^confidence: high' vault/claims/*.md 2>/dev/null | wc -l | tr -d ' ')
medium=$(rg '^confidence: medium' vault/claims/*.md 2>/dev/null | wc -l | tr -d ' ')
low=$(rg '^confidence: low' vault/claims/*.md 2>/dev/null | wc -l | tr -d ' ')
contested=$(rg '^confidence: contested' vault/claims/*.md 2>/dev/null | wc -l | tr -d ' ')
echo "Total: $total | High: $high | Medium: $medium | Low: $low | Contested: $contested"

echo ""
echo "=== Experiments ==="
exp=$(ls vault/experiments/*.md 2>/dev/null | wc -l | tr -d ' ')
echo "Experiment notes: $exp"

echo ""
echo "=== Failures ==="
fail=$(ls vault/failures/*.md 2>/dev/null | wc -l | tr -d ' ')
echo "Failure patterns: $fail"

echo ""
echo "=== Governance ==="
gov=$(ls vault/governance/*.md 2>/dev/null | wc -l | tr -d ' ')
echo "Governance mechanisms: $gov"

echo ""
echo "=== Sweeps ==="
sw=$(ls vault/sweeps/*.md 2>/dev/null | wc -l | tr -d ' ')
echo "Sweep series: $sw"

echo ""
echo "=== Runs ==="
runs=$(ls -d runs/*/ 2>/dev/null | wc -l | tr -d ' ')
echo "Experiment runs: $runs"

echo ""
echo "=== Pipeline ==="
pending_obs=$(ls vault/ops/observations/*.md 2>/dev/null | wc -l | tr -d ' ')
pending_ten=$(ls vault/ops/tensions/*.md 2>/dev/null | wc -l | tr -d ' ')
echo "Pending observations: $pending_obs (threshold: 10)"
echo "Pending tensions: $pending_ten (threshold: 5)"
```

## Output Format

```
SWARM Research OS — Vault Stats

Claims: N total
  High confidence:  N
  Medium:           N
  Low:              N
  Contested:        N

Coverage:
  Experiments: N notes
  Failures:    N patterns
  Governance:  N mechanisms
  Sweeps:      N series
  Runs:        N raw runs

Pipeline:
  Queue tasks pending: N
  Observations pending: N / 10
  Tensions pending:     N / 5
```
