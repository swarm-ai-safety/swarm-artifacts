---
description: One sentence naming the failure pattern and its consequence (~150 chars)
type: failure
status: active | mitigated | resolved
severity: critical | high | medium | low
attack_vector: exploitation | coordination | evasion | resource-exhaustion | information-asymmetry
affected_lever: circuit-breaker | transaction-tax | staking | reputation-decay | audit | collusion-detection | vote-normalization
source_run: "run_id"

created: YYYY-MM-DD
updated: YYYY-MM-DD

_schema:
  required: [description, type, status, severity, attack_vector, affected_lever, source_run, created]
  optional: [updated]
  enums:
    type: [failure]
    status: [active, mitigated, resolved]
    severity: [critical, high, medium, low]
    attack_vector: [exploitation, coordination, evasion, resource-exhaustion, information-asymmetry]
    affected_lever: [circuit-breaker, transaction-tax, staking, reputation-decay, audit, collusion-detection, vote-normalization]
  constraints:
    description: "max 200 chars, names the pattern, no trailing period"
    source_run: "must reference a valid run_id"
---

# prose-as-title naming the failure as a pattern

## Description

What happens? What conditions trigger this failure?
Show the attack chain or failure sequence.

## Impact

- **Potential damage**: quantified where possible
- **Exploitation difficulty**: trivial / moderate / advanced / expert
- **Detection latency**: how long before the system notices

## Reproduction

Which run first exposed this failure? What scenario and parameters?

- Source: [[experiment-run-id]]
- Scenario: `scenarios/<name>.yaml`
- Seed: specific seed if relevant

## Mitigation

What governance changes reduce or eliminate this failure?
Reference claims about effective mitigations.

- [[claim-id]] — mitigation evidence
- [[governance-mechanism]] — the lever that helps

## Related patterns

Other failure modes that share the same attack vector or affected lever.

---

Topics:
- [[_index]]
