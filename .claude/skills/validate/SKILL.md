---
name: validate
description: Validate provenance and schema for SWARM claims. Verifies run_id links, effect sizes, correction methods, confidence criteria, and _schema compliance. Triggers on "/validate", "/validate [claim]", "validate provenance", "check this claim".
user-invocable: true
allowed-tools: Read, Write, Edit, Grep, Glob, Bash
context: fork
---

## Runtime Configuration (Step 0)

Read `vault/ops/derivation-manifest.md` and `vault/ops/config.yaml`.

---

## EXECUTE NOW

**Target: $ARGUMENTS**

- If target is a claim path: validate that claim fully
- If target is empty: validate all claims lacking full provenance
- If target is "all": batch validate entire vault/claims/ directory

**Execute these steps:**

1. Read the target claim
2. Run all six validation gates
3. Report PASS/FAIL per gate with specific failures
4. For failures: provide exact remediation (what run_id to add, what effect size to compute)

---

# Validate Provenance

Combined quality verification gate for SWARM claims.

## Six Validation Gates

### Gate 1: Run Provenance
Every `evidence.supporting` entry must have:
- `run:` pointing to a folder in `runs/` that actually exists
- `metric:` a named metric
- `detail:` effect size, p-value, N — not just a description

```bash
# Check run exists
ls runs/[run_id] 2>/dev/null && echo "EXISTS" || echo "MISSING"
```

### Gate 2: Statistical Rigor
For high or medium confidence claims:
- Effect size (Cohen's d) must be reported
- Correction method must be one of: Bonferroni, Holm-Bonferroni, Benjamini-Hochberg
- Raw p-values alone are INSUFFICIENT — must pair with correction method
- N (number of seeds/runs) must be stated

### Gate 3: Confidence Criteria Match
Confidence level must match evidence strength:
- `high`: Bonferroni-significant AND replicated across ≥2 independent runs/seeds
- `medium`: Nominally significant OR single-sweep support with BH correction
- `low`: Suggestive but underpowered (<20 seeds) or unreplicated
- `contested`: Conflicting evidence from different runs

### Gate 4: Schema Compliance
Check against `vault/templates/claim-card.md` _schema block:
- Required fields present: description, type, status, confidence, domain, evidence, created
- Enums valid: status ∈ [active, weakened, superseded, retracted], confidence ∈ [high, medium, low, contested]
- Description ≤200 chars, no trailing period, adds info beyond title

### Gate 5: Boundary Conditions
Claims without boundary_conditions are incomplete:
- What topology was tested? (small-world, random, scale-free, ring, complete)
- What agent count? (8, 14, custom)
- What adversarial fraction? (0%, 10%, 25%, 30%)
- What time horizon? (epochs, steps)

### Gate 6: Prose-as-Title Test
Run the claim test: "this claim argues that [title]"
- Must make grammatical sense
- Must be something you could agree or disagree with
- Must be lowercase with spaces, no filesystem-breaking punctuation

## Output Format

```
Validation: vault/claims/[claim-name].md

Gate 1 — Run Provenance: PASS / FAIL
  [if FAIL: which run_id is missing, which entry is incomplete]

Gate 2 — Statistical Rigor: PASS / FAIL
  [if FAIL: which effect size is missing, which correction method is absent]

Gate 3 — Confidence Criteria: PASS / FAIL
  [if FAIL: what evidence level was found vs what confidence claims]

Gate 4 — Schema Compliance: PASS / FAIL
  [if FAIL: which required fields are absent, which enums are invalid]

Gate 5 — Boundary Conditions: PASS / FAIL
  [if FAIL: which dimensions are undocumented]

Gate 6 — Prose-as-Title: PASS / FAIL
  [if FAIL: why the title fails the claim test]

OVERALL: PASS (6/6) / NEEDS WORK ([N] gates failed)
```

If all gates pass, task is complete. If any fail, remediation must be completed before the claim is marked active.
