---
description: How this knowledge system was derived — enables architect and reseed commands
created: 2026-02-20
engine_version: "0.8.0"
---

# System Derivation — SWARM Research OS

## Configuration Dimensions

| Dimension | Position | Conversation Signal | Confidence |
|-----------|----------|--------------------|--------------------|
| Granularity | Atomic | "claim-" prefix naming, "one claim per note", existing templates enforce single-proposition files | High |
| Organization | Flat | Typed subfolders (claims/, experiments/, failures/) without hierarchy, all within vault/ | High |
| Linking | Explicit+Implicit | Wiki-links used inline as prose, Dataview cross-references, evidence provenance chains | High |
| Processing | Heavy | Full pipeline: extract findings → cross-link evidence → validate provenance → update prior claims | High |
| Navigation | 3-tier | _index.md hub → domain dashboards → individual claims and experiment notes | High |
| Maintenance | Condition-based | Claim lifecycle (active → weakened → superseded → retracted), validation scripts trigger on accumulation | High |
| Schema | Dense | Extensive YAML frontmatter: confidence, domain, status, evidence provenance, effect sizes, sensitivity, boundary conditions | High |
| Automation | Full | Inngest durable pipeline, Python validation scripts, auto-generation scripts, hooks | High |

## Personality Dimensions

| Dimension | Position | Signal |
|-----------|----------|--------|
| Warmth | clinical | Research domain, existing CLAUDE.md is professional and precise |
| Opinionatedness | opinionated | Explicit confidence criteria, "never report raw p-values", "never auto-edit claim cards" |
| Formality | formal | Effect sizes required, Bonferroni correction mandated, structured evidence format |
| Emotional Awareness | task-focused | Scientific rigor domain, quantitative outputs |

## Vocabulary Mapping

| Universal Term | Domain Term | Category |
|---------------|-------------|----------|
| notes | claims | folder concept |
| notes/ | vault/ (and subdirs: vault/claims, vault/experiments, etc.) | folder |
| inbox | new runs (runs/) | folder |
| archive | processed runs | folder |
| note (type) | claim | note type |
| note_plural | claims | note type plural |
| reduce | extract findings | process phase |
| reflect | cross-link evidence | process phase |
| reweave | update prior claims | process phase |
| verify | validate provenance | process phase |
| validate | audit schema | process phase |
| rethink | rethink | process phase (universal) |
| MOC | topic map | navigation |
| description | claim summary | schema field (value only, field name stays) |
| topics | research areas | schema field (value only) |
| relevant_notes | related claims | schema field (value only) |
| inbox | new runs | capture zone |
| pipeline | synthesis pipeline | process |
| orient | load run context | session phase |
| persist | commit to vault | session phase |
| cmd_reduce | /extract | skill command |
| cmd_reflect | /cross-link | skill command |
| cmd_reweave | /update | skill command |
| cmd_verify | /validate | skill command |
| cmd_rethink | /rethink | skill command |

## Platform

- Tier: Claude Code
- Automation level: full (Inngest pipeline, Python scripts, hooks)
- Base path: /Users/raelisavitt/swarm-artifacts/
- Vault path: vault/

## Active Feature Blocks

- [x] wiki-links — always included (kernel)
- [x] processing-pipeline — always included
- [x] schema — always included (dense schema, _schema blocks in templates)
- [x] maintenance — always included (claim lifecycle, condition-based)
- [x] self-evolution — always included
- [x] session-rhythm — always included
- [x] templates — always included (7 domain templates existing)
- [x] ethical-guardrails — always included
- [x] helper-functions — always included
- [x] graph-analysis — always included (Python scripts + claim-graph.py)
- [x] atomic-notes — included (one claim per file enforced)
- [x] mocs — included (_index.md + dashboards)
- [x] semantic-search — conditional (qmd if installed)
- [ ] personality — excluded (neutral-analytical default)
- [ ] self-space — excluded for research preset (identity in ops/)
- [ ] multi-domain — excluded (single research domain)

## Coherence Validation Results

- Hard constraints checked: 3. Violations: none
- Soft constraints checked: 5. Auto-adjusted: none. User-confirmed: none
- Compensating mechanisms active:
  - Atomic + flat organization → Python scripts compensate for navigation at scale
  - Dense schema + heavy processing → existing automation handles maintenance burden
  - High volume (110+ experiments) → 3-tier navigation (dashboards act as domain MOCs)

## Failure Mode Risks

HIGH risk for this configuration:
- **Collector's Fallacy**: 1000+ runs available, temptation to absorb without synthesis
- **Orphan Drift**: High experiment creation volume — scripts mitigate but vigilance needed
- **Verbatim Risk**: Experiment data tempts reproduction over transformation into claims
- **MOC Sprawl**: Multiple domain dashboards could proliferate without discipline

## Extraction Categories (SWARM-specific)

1. **Governance claims** — causal assertions about mechanism effects (effect size required)
2. **Adversarial patterns** — named attack patterns with success rates and damage ranges
3. **Parameter sensitivity findings** — phase transitions, threshold effects, welfare cliffs
4. **Mechanism interactions** — synergistic or antagonistic combinations between governance levers
5. **Open questions** — unresolved research directions, next decisive experiments
6. **Method validations** — statistical approach justifications (Bonferroni, Holm-Bonferroni, BH)
7. **Failure modes** — vulnerability patterns with severity, evasion rates, mitigations

## Generation Parameters

- Folder names: vault/claims, vault/experiments, vault/failures, vault/governance, vault/methods, vault/sweeps, vault/topologies
- Ars Contexta ops path: vault/ops/
- Agent self path: vault/self/
- Skills location: .claude/skills/
- Hooks location: .claude/hooks/
- Notes collection name: vault
- Existing templates preserved (7 domain templates in vault/templates/)
- Augmented CLAUDE.md (not replaced)
