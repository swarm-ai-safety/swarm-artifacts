---
name: extract
description: Extract structured claims from SWARM experiment runs, sweep results, and red-team reports. Comprehensive extraction is the default — every governance finding, adversarial pattern, and parameter sensitivity result gets extracted. Zero extraction from a domain-relevant run is a BUG. Triggers on "/extract", "/extract [file]", "extract findings", "mine this run", "process this experiment".
version: "1.0"
generated_from: "arscontexta-v0.8.0"
user-invocable: true
allowed-tools: Read, Write, Grep, Glob, mcp__qmd__vector_search
context: fork
---

## Runtime Configuration (Step 0 — before any processing)

Read these files to configure domain-specific behavior:

1. **`vault/ops/derivation-manifest.md`** — vocabulary mapping, extraction categories, platform hints
2. **`vault/ops/config.yaml`** — processing depth, pipeline chaining, selectivity

If these files don't exist, use SWARM defaults:
- depth: standard
- chaining: suggested
- selectivity: moderate
- notes folder: `vault/claims/`
- inbox folder: `runs/`

---

## EXECUTE NOW

**Target: $ARGUMENTS**

Parse immediately:
- If target contains a file path: extract findings from that experiment/run/report
- If target contains `--handoff`: output RALPH HANDOFF block + task entries at end
- If target is empty: scan `runs/` for unprocessed experiment folders, pick newest
- If target is "all": process all unprocessed runs sequentially

**Execute these steps:**

1. Read the source fully — understand what experiment/run/report it contains
2. **Source size check:** If source exceeds 2500 lines, chunk into 350-1200 line segments
3. Hunt for SWARM findings using extraction categories below
4. For each candidate: run semantic duplicate check, classify as OPEN or CLOSED
5. Output extraction report with titles, classifications, rationale
6. Wait for user approval before creating files
7. If `--handoff`: create per-claim task files, update queue.json

**START NOW.** Reference below explains methodology.

---

# Extract Findings

Extract composable claims from SWARM experiment runs and reports into vault/claims/.

## Extraction Categories for SWARM Research

| Category | What to Find | Output Type |
|----------|--------------|-------------|
| Governance claims | Causal assertions about mechanism effects with Cohen's d, p-value, N, correction method | claim |
| Adversarial patterns | Named attack patterns with success rates, damage ranges, evasion rates | claim or failure note |
| Parameter sensitivity | Phase transitions, threshold effects, welfare cliffs from parameter sweeps | claim |
| Mechanism interactions | Synergistic or antagonistic combinations between governance levers | claim |
| Open questions | Unresolved research directions, next decisive experiments | claim (open) |
| Method validations | Statistical approach justifications, correction method rationale | method note |
| Failure modes | Vulnerability patterns with severity, evasion rates, and mitigations | failure note |

Every extracted claim MUST include:
- `run:` pointing to a real run_id in runs/
- `metric:` the measured outcome
- `detail:` effect size, p-value, N, correction method
- `boundary_conditions:` known limits of generalizability

**Zero extraction from a domain-relevant run is a BUG.**

## Claim Title Rules

Title IS the claim as a testable proposition:
- Good: "circuit breakers reduce toxicity more than transaction taxes at equivalent cost"
- Good: "collusion penalty multipliers above 1.5x paradoxically increase toxicity"
- Bad: "governance findings" (label, not claim)
- Test: "this claim argues that [title]" — must make sense

## Output Format

```
Extraction scan complete.

SUMMARY:
- governance claims: N
- adversarial patterns: N
- parameter sensitivity: N
- mechanism interactions: N
- open questions: N
- method notes: N
- failure modes: N
- enrichment tasks: N
- skipped: N
- TOTAL OUTPUTS: N

---

GOVERNANCE CLAIMS:
1. [claim as proposition] (Cohen's d=X, p=Y, N=Z, Bonferroni)
   Evidence: run/[run_id], metric: [metric], boundary: [topology, agent_count, adversarial_fraction]
   Connects to: [[existing-claim]]

...

SKIPPED:
- [description] — why nothing extractable
```

Wait for user approval before creating files.

## Pipeline Chaining

After extraction completes:
- **suggested (default):** Output "Next: /cross-link [created claims]" and add to queue
- **manual:** Output next step, user decides
- **automatic:** Queue advanced, cross-linking proceeds immediately

See `vault/ops/config.yaml` pipeline.chaining.
