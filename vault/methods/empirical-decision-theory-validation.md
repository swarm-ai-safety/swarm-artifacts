---
description: "SWARM's LDT composition study contributes one of the first large-scale empirical tests of decision theory in multi-agent simulation"
type: method
status: active
category: simulation
created: 2026-02-22
cssclasses:
- method
tags:
- decision-theory
- empirical-validation
- ldt
- methodology
graph-group: method
---

# large-scale empirical validation of decision theory predictions is a methodological contribution of SWARM

Decision theory — including functional decision theory (FDT), updateless decision theory (UDT), superrationality, and program equilibrium — has a rich theoretical literature but surprisingly little large-scale empirical validation. SWARM's LDT composition study provides one of the first empirical tests of decision-theoretic predictions at scale, making it a methodological contribution independent of the specific findings.

## What it does

Empirical decision theory validation uses multi-agent simulation to test predictions derived from formal decision theory. Rather than proving theorems about idealized agents, this approach instantiates decision-theoretic agents (e.g., LDT agents with varying acausality depth) in realistic market environments and measures whether the predicted behavioral patterns emerge.

SWARM's implementation tested LDT agent welfare stability across composition ratios (0-100% LDT agents) with d=2.89, N=160 runs, Bonferroni-corrected. This produced two key findings: [[claim-ldt-agents-provide-welfare-stability-at-intermediate-composition|LDT agents maintain +48% welfare at 40-70% composition]], and [[claim-acausality-depth-does-not-affect-cooperation-outcomes|acausality depth does not affect cooperation outcomes]].

## Why it matters

The gap between decision theory and empirical validation is a significant methodological concern. Theoretical results about FDT, UDT, and superrationality make strong predictions about cooperation, coordination, and welfare in multi-agent settings, but these predictions have been tested almost exclusively through toy examples (prisoner's dilemma, Newcomb's problem) or analytical models. SWARM's market environment — with heterogeneous agents, governance mechanisms, and realistic interaction structures — provides a much richer testbed.

The finding that acausality depth does not affect outcomes is particularly methodologically significant: it suggests that the theoretical distinction between different levels of "logical updatelessness" may not matter in practice, at least in the market settings tested.

## How to apply it

1. Define the decision-theoretic prediction to test (e.g., "LDT agents should cooperate more at intermediate composition ratios")
2. Design a SWARM sweep varying the relevant parameters (e.g., LDT composition from 0% to 100%)
3. Run with sufficient seeds for statistical power (N >= 10 seeds per condition, ideally 20+)
4. Analyze with appropriate multiple-comparison correction ([[bonferroni-correction]] or [[benjamini-hochberg]])
5. Report effect sizes with [[cohens-d]] alongside significance tests

```bash
# Example: LDT composition sweep
python scripts/validate-run.py runs/ldt-composition-sweep/
python scripts/generate-note.py runs/ldt-composition-sweep/
```

## Assumptions and limitations

- LLM agents are not ideal decision-theoretic reasoners — they approximate decision theories through prompt engineering and architecture, not formal implementation
- The mapping between theoretical decision theories (FDT, UDT) and LLM agent implementations is imperfect
- Results may be sensitive to the specific market mechanism (SWARM's knowledge market) and may not generalize to other domains
- Short-horizon simulations may not capture long-run equilibrium behavior predicted by decision theory

## Evidence of effectiveness

- [[claim-ldt-agents-provide-welfare-stability-at-intermediate-composition]] — d=2.89, N=160, Bonferroni-corrected. One of the largest effect sizes in the SWARM corpus, providing strong empirical evidence for LDT welfare stability predictions
- [[claim-acausality-depth-does-not-affect-cooperation-outcomes]] — High confidence null result challenging theoretical predictions about depth-dependent cooperation

---

Topics:
- [[_index]]

<!-- topics: decision-theory, empirical-validation, ldt, methodology -->
