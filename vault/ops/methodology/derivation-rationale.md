---
description: Why each configuration dimension was chosen for the SWARM Research OS vault
category: derivation-rationale
created: 2026-02-20
status: active
---

# derivation rationale for SWARM Research OS

## Domain

Distributional safety in multi-agent AI systems. The vault stores scientific claims, experiment notes, failure patterns, governance mechanism analyses, parameter sweep results, topology studies, and statistical methods — all evidence-linked and provenance-tracked.

## Preset

Research (with SWARM-specific extensions). The vocabulary.yaml in vault/ pre-mapped all universal Ars Contexta terms to SWARM domain language before this setup ran.

## Dimension Choices

**Atomic granularity (High confidence)**
The vault enforces one claim per file. The existing naming convention (`claim-*`) and templates confirmed this signal explicitly. Atomic granularity maximizes composability — a claim about circuit breakers can be invoked from a topology study without dragging in governance cost data.

**Flat organization (High confidence)**
The vault uses typed subfolders (claims/, experiments/, failures/, governance/, methods/, sweeps/, topologies/) without hierarchy within each folder. This is the flat-associative pattern. Navigation is handled by dashboards (domain MOCs) and semantic search, not by folder nesting.

**Explicit+Implicit linking (High confidence)**
Wiki-links are used inline as prose throughout existing claims. Dataview queries provide implicit cross-references. Evidence provenance chains (run_id → claim → sweep) are explicit link chains.

**Heavy processing (High confidence)**
The existing Inngest durable pipeline and Python automation scripts confirmed full-pipeline processing: extract findings → cross-link evidence → validate provenance → update prior claims. The Bonferroni correction requirement, effect size mandates, and evidence provenance rules all signal heavy processing discipline.

**3-tier navigation (High confidence)**
_index.md (hub) → domain dashboards (claims-dashboard, experiments-dashboard, failures-dashboard, governance-dashboard, sweeps-dashboard) → individual notes. This is exactly the 3-tier pattern.

**Dense schema (High confidence)**
Existing claim-card.md template has 15+ YAML fields including confidence, domain, status, evidence (supporting/weakening), boundary_conditions, sensitivity, supersedes, superseded_by, related_claims — plus a full _schema block with enums and constraints.

**Full automation (High confidence)**
Inngest durable pipeline, Python validation/synthesis/indexing scripts, the arscontexta skills directory, and the Inngest TypeScript pipeline all confirm full automation intent.

**Condition-based maintenance (High confidence)**
The claim lifecycle (active → weakened → superseded → retracted) is a condition-based maintenance system. Validation scripts trigger on batch completion.

## Coherence

No hard constraint violations. The atomic+flat+dense combination is compensated by:
- Python scripts for batch navigation at scale
- Dashboards acting as domain MOCs (compensates for flat structure at 100+ note scale)
- Full automation handling maintenance burden of dense schema

## Failure Mode Risks

Active mitigations in place:
- **Collector's Fallacy**: `python scripts/claim-lifecycle.py` audits claim evidence and status
- **Orphan Drift**: `python scripts/vault-health.py` detects orphan notes
- **Verbatim Risk**: "Prose-as-title" kernel invariant enforces transformation over reproduction
- **MOC Sprawl**: Dashboards use Dataview queries not manual curation — they stay disciplined automatically

---

Topics:
- [[methodology]]
