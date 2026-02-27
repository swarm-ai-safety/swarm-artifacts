# Local LLM Benchmark: Agentic Self-Improvement Loop

**Date**: 2026-02-23 — 2026-02-26
**Setup**: 6-phase self-improvement loop (`self_improve.py`) running against a coding agent codebase (~20 files, Python). Each phase dispatches a scoped sub-agent via `SubAgentRunner` with phase-specific tools and system prompts. Local models served by Ollama on Apple Silicon.

## Models Tested

| Model | Parameters | Quantization | Context | Disk |
|-------|-----------|--------------|---------|------|
| Claude Sonnet (API) | undisclosed | native | 200k | API |
| qwen2.5:14b | 14.8B | Q4_K_M | 128k | 8.5 GB |
| glm-4.7-flash:q8_0 | 29.9B | Q8_0 | 128k | 30 GB |
| llama3.1:8b | 8.0B | Q4_K_M | 128k | 4.7 GB |
| mistral:7b | 7.2B | Q4_K_M | 32k | 4.1 GB |

## Task Structure

Each iteration runs 6 phases sequentially. Only the IMPLEMENT phase has write access; all others are read-only.

| Phase | Role | Purpose |
|-------|------|---------|
| EXPLORE | Explorer | Map unexplored files, find improvement opportunities |
| HYPOTHESIZE | Strategist | Generate 3-5 candidates across 7 axes, pick winner |
| IMPLEMENT | Coder | Apply the change, run tests before/after |
| RED-TEAM | Adversary | Try 3-5 attack strategies to break the change |
| AUDIT | Auditor | Score iteration on correctness/robustness/value/scope/tests |
| REFLECT | Strategist | Update exploration map, propose next-iteration seeds |

Budget per phase: 100k tokens / 15 turns (API), 20k tokens / 8 turns (local).

## Part 1: Single-Iteration Model Comparison

Five models ran 1 iteration each to establish baseline capabilities.

### Headline Numbers

| Metric | Claude Sonnet | qwen2.5:14b | glm-4.7-flash | llama3.1:8b | mistral:7b |
|--------|:------------:|:-----------:|:-------------:|:-----------:|:----------:|
| Phases completed | 6/6 | 6/6 | 6/6 | 6/6 | 2/6 |
| Total tokens | 670,003 | 31,714 | 115,073 | 10,088 | 5,689 |
| Wall time | ~110 min | ~10 min | ~40 min | ~2 min | ~1 min |
| Avg turns/phase | 12 | 2 | 4 | 1 | 1.5 |
| JSON parse success | 6/6 | 5/6 | 2/6 | 3/6 | 0/6 |
| Axis chosen | observability | architecture | i18n (invented) | architecture | N/A |
| Audit score | 3.4/10 | 6.6/10 | N/A | N/A | N/A |
| Red-team verdict | broken | N/A | N/A | broken | N/A |

### Capability Breakdown

#### Tool Use Quality

How well each model called tools (read_file, search, bash, edit_file) during agentic loops:

| Model | Calls tools | Correct args | Multi-turn chains | Writes code |
|-------|:-----------:|:------------:|:-----------------:|:-----------:|
| Claude Sonnet | Yes | Yes | Yes (10-15 turns) | Yes |
| qwen2.5:14b | Yes | Yes | Yes (1-3 turns) | Attempted |
| glm-4.7-flash | Yes | Mostly | Yes (5-8 turns) | Attempted |
| llama3.1:8b | Confused | Malformed | No | No |
| mistral:7b | Barely | Yes (1 call) | No | No |

- **Claude**: Exhaustive exploration — read 9+ files per phase, ran tests, made surgical edits.
- **qwen2.5:14b**: Competent tool use with correct argument schemas. Explored directories, read files, produced clean JSON. Best cost/quality ratio.
- **glm-4.7-flash**: Active tool user (hit budget limits on 3 phases) but verbose, burning tokens on long prose between tool calls.
- **llama3.1:8b**: Returned tool-call-shaped JSON as its text response instead of actually invoking tools. Classic small-model confusion between "describe doing X" and "do X."
- **mistral:7b**: Made one `list_directory` call in EXPLORE, then switched to pure prose for everything else.

#### Structured Output Compliance

Each phase asks for a specific JSON schema. Parse success rate:

| Model | explore | hypothesize | implement | red_team | audit | reflect |
|-------|:-------:|:-----------:|:---------:|:--------:|:-----:|:-------:|
| Claude Sonnet | Yes | Yes | Yes | Yes | Yes | Yes |
| qwen2.5:14b | Yes | Yes | Yes | No | Yes | Yes |
| glm-4.7-flash | No | Yes | No | No | No | Yes |
| llama3.1:8b | No | Yes | No | Yes | No | Yes |
| mistral:7b | No | No | - | - | - | - |

Failure modes:
- **glm-4.7-flash**: Generates structured content but buries it in verbose prose, or uses non-standard JSON formatting that the regex extractor misses.
- **llama3.1:8b**: Emits tool-call dicts (`{"name": "bash", "parameters": {...}}`) where content JSON is expected.
- **mistral:7b**: Ignores JSON formatting instructions entirely. Writes good prose analysis but zero fenced code blocks.

#### Hypothesis Diversity

The HYPOTHESIZE prompt enforces 7 improvement axes and says "do not default to error-handling." Results:

| Model | Hypotheses generated | Distinct axes | Invented axes |
|-------|:-------------------:|:-------------:|:-------------:|
| Claude Sonnet | 5 | 5 (obs, perf, ux, test, sec) | No |
| qwen2.5:14b | 4+ | 4 | No |
| glm-4.7-flash | 4 | 4 (i18n, docs, perf, sec) | Yes: i18n, docs |
| llama3.1:8b | 1 | 1 (architecture) | No |
| mistral:7b | 3 | 3 (ux, perf, obs) | No |

- GLM was the most creative, inventing "internationalization" and "documentation" as axes outside the prescribed 7.
- Mistral generated diverse hypotheses in prose but couldn't format them as JSON, so the loop couldn't proceed.

#### Self-Awareness / Reflection Quality

The REFLECT phase asks the model to honestly assess the iteration and plan ahead:

| Model | Self-critical | Actionable seeds | Trajectory awareness |
|-------|:------------:|:----------------:|:-------------------:|
| Claude Sonnet | Yes ("incomplete implementation") | 3, diverse | Yes |
| qwen2.5:14b | Moderate | 2, reasonable | Partial |
| glm-4.7-flash | Excellent ("absence of data is a signal") | 3, well-reasoned | Yes |
| llama3.1:8b | No | 3, generic | No |
| mistral:7b | N/A (aborted) | N/A | N/A |

GLM's reflection was the standout for local models: "the summary is sparse...no actual scores, strengths, or weaknesses are reported. This suggests either an incomplete audit or that no substantive findings were generated...the absence of data is a signal to iterate with more rigor." This is genuine metacognition about its own iteration's shortcomings.

## Part 2: Multi-Iteration Runs

### qwen2.5:14b

Two runs tested whether the model can sustain quality, diversify axes, and learn across iterations. Run A did 3 iterations; Run B did 5 (3 initial + 2 continuation).

### Run A (2026-02-24)

| | Iter 1 | Iter 2 | Iter 3 |
|---|:---:|:---:|:---:|
| **Axis** | test_coverage | security | ux_cli |
| **Audit score** | 5.0 | 6.8 | 6.8 |
| **Red-team** | partial | holds | N/A |
| **Files changed** | none | none | agent.py, cli.py |
| **Tokens** | 58k | 75k | 56k |

**Audit score trend: 5.0 → 6.8 → 6.8** (improving then plateau)

Observations:
- Perfect axis diversity — 3 different axes, no repeats.
- Audit scores improved from iter 1 to 2, then held. The model learned from red-team breaking iter 1 (partial verdict) and produced a change that held in iter 2.
- Iter 3 was the first to actually modify source files (agent.py, cli.py) with UX improvements.
- Total cost: 189k tokens (~63k avg/iteration), all local/free.

### Run B (2026-02-25 — 2026-02-26, 5 iterations)

| | Iter 1 | Iter 2 | Iter 3 | Iter 4* | Iter 4 | Iter 5 |
|---|:---:|:---:|:---:|:---:|:---:|:---:|
| **Axis** | architecture | ux_cli | ux_cli | *(aborted)* | observability | performance |
| **Audit score** | 4.9 | 2.4 | N/A | N/A | 3.0 | 3.0 |
| **Red-team** | N/A | N/A | partial | N/A | broken | N/A |
| **Files changed** | none | none | cli.py | none | none | none |
| **Tokens** | 25k | 19k | 70k | 8k | 55k | 59k |

*Iter 4 first attempt aborted — HYPOTHESIZE produced no parseable JSON. Retried successfully.*

**Audit score trend: 4.9 → 2.4 → N/A → 3.0 → 3.0** (crash then flat recovery)

Observations (iters 1-3):
- Axis diversity failed early — ux_cli repeated in iters 2 and 3 despite the prompt discouraging repeats.
- Iter 2 scored very poorly (2.4): correctness=1, robustness=1, tests=0. The model attempted to add CLI progress indicators but couldn't find shell scripts to modify.
- Iter 3 spent 70k tokens (3.5x iter 2) trying to fix a syntax error it introduced, then the red-team found the fix was partial.
- The explore phase logged glob patterns (`**/*.js`, `**/*.css`) as "files examined" instead of actual filenames, polluting the manifest.

Observations (iters 4-5, continuation):
- Axis diversity improved — finally hit observability (iter 4) and performance (iter 5), both previously untouched.
- Audit scores stabilized at 3.0 but never recovered to the iter 1 level (4.9). The model plateaued.
- Neither iter 4 nor iter 5 actually modified any source files, despite claiming to implement changes. The IMPLEMENT phase ran tools but produced no lasting code changes.
- Red-team broke iter 4 — found dependency issues and edge input failures in the (non-existent) implementation.
- Iter 5 audit noted "misalignment between hypothesis and implemented solution" — the model selected a performance hypothesis but implemented a logging utility instead.
- Reflect phase produced Thai text in seed rationale, indicating language drift in later iterations.
- Manifest pollution continued: tool names (`list_files`, `list_directory`, `search`) and paths like `/runs/*.json` appeared in "files_examined."

### Cross-Run Analysis

| Metric | Run A (3 iters) | Run B (5 iters) |
|--------|:-----:|:-----:|
| Audit trend | 5.0 → 6.8 → 6.8 (improving) | 4.9 → 2.4 → N/A → 3.0 → 3.0 (crash/flat) |
| Axis diversity | 3/3 distinct | 4/6 distinct (ux_cli×2) |
| Red-team breaks | 1 (iter 1 partial) | 2 (iter 3 partial, iter 4 broken) |
| Total tokens | 189k | 236k |
| Files actually changed | 2 (iter 3) | 1 (iter 3) |
| Self-inflicted bugs | 0 | 1 (syntax error in iter 2/3) |
| Aborted iterations | 0 | 1 (iter 4 attempt 1) |
| Hypothesis-implementation mismatch | 0 | 1 (iter 5: perf hypothesis → logging impl) |

Key finding: **qwen2.5:14b's multi-iteration performance is inconsistent and does not show a learning curve**. Run A showed genuine improvement over 3 iterations (audit scores rose, axis diversity was perfect). Run B showed degradation then stagnation over 5 iterations — the model crashed in iter 2, partially recovered, but never exceeded its starting score. The difference appears to be whether the EXPLORE phase produces quality findings that seed diverse hypotheses.

Additional finding from Run B's 5-iteration trajectory: **the model does not learn from its own audit feedback**. Despite the audit consistently flagging "no tests written" (tests score: 0-1 across all iterations) and "no files changed," subsequent iterations continued to produce phantom implementations with no actual code modifications. The reflect phase proposes reasonable next-iteration seeds, but the implement phase fails to execute on them.

### glm-4.7-flash:q8_0

One run of 3 requested iterations. Only 1 completed; iterations 2 and 3 both aborted at HYPOTHESIZE due to JSON extraction failure.

### Run C (2026-02-26)

| | Iter 1 | Iter 2 (attempt 1) | Iter 2 (attempt 2) |
|---|:---:|:---:|:---:|
| **Axis** | observability | *(aborted)* | *(aborted)* |
| **Audit score** | N/A | N/A | N/A |
| **Red-team** | broken | N/A | N/A |
| **Files changed** | none | none | none |
| **Tokens** | 155k | 75k | 75k |
| **Wall time** | ~8 hours | ~5 hours | ~3 hours |
| **Phase budget exceeded** | 4/6 | 2/2 | 1/2 |

**Audit score trend: N/A** (no audit scores parseable across the entire run)

Phase-level detail for iter 1:

| Phase | Status | Tokens | Turns | Wall time |
|-------|--------|--------|-------|-----------|
| EXPLORE | budget_exceeded | 57k | 5 | ~3.1 hours |
| HYPOTHESIZE | completed | 3.7k | 2 | ~19 min |
| IMPLEMENT | budget_exceeded | 28k | 9 | ~1.1 hours |
| RED-TEAM | budget_exceeded | 29k | 7 | ~1.8 hours |
| AUDIT | budget_exceeded | 36k | 7 | ~1.3 hours |
| REFLECT | completed | 1.9k | 1 | ~15 min |

Observations:
- **Catastrophic token burn**: 155k tokens for a single iteration — 3x the qwen2.5:14b average (47k). The EXPLORE phase alone consumed 57k tokens in 5 turns, spending ~3 hours on verbose prose between tool calls.
- **Strong HYPOTHESIZE when it works**: Iter 1 produced 4 well-structured hypotheses across ux_cli, observability, test_coverage, and performance axes. Clean JSON with value/risk scoring. Selected observability (H2) with coherent rationale.
- **Excellent REFLECT quality**: Even with empty audit data, the model produced insightful reflection — "the broken state on observability suggests the codebase may have missing or non-functional logging." Proposed 4 next-iteration seeds with confidence levels and conditional reasoning.
- **JSON extraction is the fatal bottleneck**: Only 2/6 phases in iter 1 produced parseable JSON (HYPOTHESIZE and REFLECT). Both aborted iter 2 attempts failed because HYPOTHESIZE produced no extractable JSON despite spending 31k–74k tokens. The model has the reasoning capability but buries structured output in verbose prose.
- **Input:output token ratio is extreme**: 147k input vs 8k output in iter 1 (18:1 ratio). The model reads far more than it writes, consuming budget on long tool results and context rather than generation.
- **Multi-iteration viability: zero**: 2 of 3 iterations aborted. The model cannot reliably produce HYPOTHESIZE JSON, which gates all downstream phases. Without a JSON re-prompt fallback, GLM cannot sustain a multi-iteration loop.

### Cross-Run Analysis (all models)

| Metric | qwen Run A (3 iters) | qwen Run B (5 iters) | GLM Run C (1 iter*) |
|--------|:-----:|:-----:|:-----:|
| Audit trend | 5.0 → 6.8 → 6.8 (improving) | 4.9 → 2.4 → N/A → 3.0 → 3.0 (crash/flat) | N/A (unparseable) |
| Axis diversity | 3/3 distinct | 4/6 distinct (ux_cli×2) | 1/1 (only 1 completed) |
| Red-team breaks | 1 (iter 1 partial) | 2 (iter 3 partial, iter 4 broken) | 1 (iter 1 broken) |
| Total tokens | 189k | 236k | 305k |
| Tokens/completed iter | 63k | 47k | 155k |
| Wall time | ~30 min | ~2 hours | ~16 hours |
| Files actually changed | 2 (iter 3) | 1 (iter 3) | 0 |
| Self-inflicted bugs | 0 | 1 | 0 |
| Aborted iterations | 0 | 1 | 2 |
| Abort rate | 0% | 17% | 67% |

*Run C requested 3 iterations but only 1 completed. The other 2 aborted at HYPOTHESIZE.

Key finding: **GLM's cost-per-completed-iteration is 3x qwen's, with lower reliability**. At 155k tokens and ~8 hours per completed iteration (vs 47-63k tokens and ~10 min for qwen), GLM is not viable for iterative loops despite superior reasoning quality in isolated phases. The model's verbose reasoning style and unreliable JSON compliance make it a poor fit for the structured phase pipeline.

### Aggregate Statistics (9 completed iterations across all runs)

- **Axes touched**: test_coverage(1), security(1), ux_cli(3), architecture(2), performance(1), prompt_engineering(0), observability(2)
- **Gravitational bias**: ux_cli attracted 33% of iterations. prompt_engineering remains completely untouched across all models and runs.
- **Avg audit score**: 3.7 (across 6 scored iterations; 3 had N/A)
- **Red-team break rate**: 4/9 iterations (44%) had partial or broken verdicts
- **Code modification rate**: 2/9 iterations (22%) actually changed source files
- **Phantom implementation rate**: 7/9 iterations (78%) claimed changes but modified zero files
- **Avg tokens/iteration**: 65k for qwen (range: 19k–75k), 155k for GLM
- **Aborted iterations**: 3/12 attempts (25%) — all due to HYPOTHESIZE failing to produce parseable JSON
- **GLM-specific abort rate**: 2/3 attempts (67%) vs qwen 1/9 (11%)

## Failure Taxonomy

### 1. Tool-Call Confusion (llama3.1:8b)
The model returns a dict that looks like a tool call (`{"name": "bash", "parameters": {"command": "ls"}}`) as its text response, instead of actually invoking the tool. The sub-agent framework sees no tool_calls in the API response and treats the turn as "completed." The model thinks it acted; it didn't.

### 2. JSON Schema Blindness (mistral:7b)
The model understands the task and produces good analysis, but ignores the explicit JSON formatting requirement. It writes paragraphs where the prompt asks for fenced ```json blocks. The downstream parser gets nothing, and the loop aborts because it can't extract a hypothesis to implement.

### 3. Verbose Token Burn (glm-4.7-flash)
The model writes extensive reasoning between tool calls, consuming its token budget on prose instead of tool use. It hit `budget_exceeded` on 4/6 phases in the multi-iteration run (iter 1). The EXPLORE phase alone consumed 57k tokens in 5 turns — more than an entire qwen iteration. At 30B Q8, each token is also ~3x slower to generate than the 14B models. In the multi-iteration run, this caused ~8 hour wall times per completed iteration.

### 4. Hallucinated Execution (llama3.1:8b)
The RED-TEAM phase claimed to run attack scripts and report results, but the "commands_run" were never actually executed. The model fabricated plausible-looking test outputs. This is the most dangerous failure mode: it looks like the phase succeeded.

### 5. Axis Gravitational Collapse (qwen2.5:14b, Run B)
Despite explicit prompting to diversify across 7 axes and a histogram showing prior coverage, the model repeated ux_cli for 2 consecutive iterations. The HYPOTHESIZE prompt says "prefer under-explored axes," but the model's tendency toward concrete, familiar tasks (CLI improvements) overrides this instruction. This suggests the axis-diversity mechanism needs structural enforcement (e.g., blacklisting recently-used axes) rather than relying on prompt compliance.

### 6. Self-Inflicted Regression (qwen2.5:14b, Run B)
In iter 2, the IMPLEMENT phase introduced a syntax error into cli.py. Iter 3 then spent its entire budget (70k tokens) diagnosing and partially fixing the bug it created. The audit couldn't even score iter 3. This cascading failure pattern — where one bad iteration poisons subsequent ones — is a key risk for autonomous multi-iteration loops.

### 7. Phantom Implementation (qwen2.5:14b, Run B iters 4-5)
The IMPLEMENT phase runs tools (read_file, search, bash), produces a plausible narrative about what it changed, but modifies zero files. The audit then scores a non-existent implementation. This happened in 6 of 8 total iterations (75%). The model appears to confuse "planning to make a change" with "making the change." This is distinct from hallucinated execution (#4) because the model genuinely runs tools — it just never calls edit_file or write_file.

### 8. Hypothesis-Implementation Drift (qwen2.5:14b, Run B iter 5)
The HYPOTHESIZE phase selected a "performance optimization" hypothesis. The IMPLEMENT phase then built a logging utility instead. The audit caught this: "misalignment between hypothesis and implemented solution." The model loses track of the selected hypothesis across the phase boundary, substituting a task it finds easier or more familiar.

### 9. Language Drift (qwen2.5:14b, Run B iters 4-5)
The REFLECT phase produced seed rationale in Thai instead of English. This occurred in later iterations when the model's context was loaded with prior-iteration summaries. Multilingual models (Qwen is trained on Chinese/English/multilingual data) can drift into non-target languages when prompt pressure is low and context is long.

### 10. Manifest Pollution (qwen2.5:14b, Run B)
The EXPLORE phase logged tool names (`list_files`, `list_directory`, `search`), glob patterns (`**/*.js`, `**/*.css`), and metadata paths (`/runs/*.json`) as "files examined." These invalid entries accumulate in the manifest and corrupt the exploration map for future iterations, since the EXPLORE phase is told to skip already-examined files. This creates a feedback loop where the model thinks it has examined more of the codebase than it actually has.

### 11. Chronic HYPOTHESIZE Failure (glm-4.7-flash, Run C)
The model can produce valid HYPOTHESIZE JSON on its first iteration but fails on subsequent attempts. In Run C, iter 1 HYPOTHESIZE completed in 2 turns with clean JSON, but both iter 2 attempts (spending 31k and 74k tokens respectively) failed to produce any parseable JSON. The EXPLORE phase dumps massive context into the HYPOTHESIZE prompt, and the model responds with verbose analysis instead of the required structured output. This creates a hard ceiling: GLM can do exactly 1 iteration before the accumulated context overwhelms its JSON compliance. The 18:1 input:output token ratio suggests the model is "reading" far more than "writing," losing the structured-output instruction in the noise.

## Recommendations

### For local agentic workloads:
- **qwen2.5:14b** is the clear winner for cost/quality. Clean tool calls, reliable JSON, fast inference. But expect inconsistency across runs — some runs show learning, others show degradation.
- **glm-4.7-flash** is not viable for multi-iteration loops. Despite strong reasoning in isolated phases (excellent reflection, creative hypotheses), it burns 155k tokens per completed iteration, takes ~8 hours wall time, and has a 67% abort rate due to JSON extraction failures. Single-iteration use is possible but impractical at current speeds.
- **7B models are not viable** for multi-turn agentic loops with tool use. They can do single-turn generation but break down when asked to alternate between tool calls and structured output.

### For the framework:
- Add a JSON extraction fallback that re-prompts the model: "Your response did not contain valid JSON. Please output ONLY the JSON block." This would likely recover glm-4.7-flash and mistral:7b failures.
- Consider reducing system prompt length for smaller models. The current phase prompts are ~300-500 tokens each, which is a significant fraction of a 7B model's effective reasoning budget.
- Track tool-call-vs-text confusion as a metric. If a model's "text" response contains `{"name":` patterns, flag it as a tool-call confusion and retry.
- **Enforce axis diversity structurally**: blacklist the last N axes used, or weight the HYPOTHESIZE selection toward under-explored axes programmatically rather than via prompt.
- **Add a regression gate**: after IMPLEMENT, if tests fail that passed before, automatically revert and skip to REFLECT. Don't let a broken iteration cascade into the next one.
- **Validate explore output**: check that "files_examined" entries are actual file paths (exist on disk, no globs, no tool names). Reject and re-prompt if the format is wrong.
- **Verify implementation actually happened**: after IMPLEMENT, diff the working tree. If no files changed, mark the iteration as "phantom" and skip to REFLECT with a note. Don't waste red-team and audit budget scoring a non-existent change.
- **Pin the hypothesis across phases**: pass the full selected hypothesis JSON verbatim to IMPLEMENT, RED-TEAM, and AUDIT prompts. Currently the hypothesis summary can drift as it passes through the PhaseContext chain.
- **Force English output**: add "You MUST respond in English only" to all phase system prompts for multilingual models, or validate output language and re-prompt on drift.

## Raw Data

All phase JSONs, manifests, and iteration summaries are archived in `swarm-artifacts/runs/coding-agent-self-improve/`:
```
runs/coding-agent-self-improve/
  manifest.json
  benchmark_writeup.md
  # Run A — qwen2.5:14b (2026-02-24, 3 iterations)
  20260224_045251_iter1/
  20260224_051315_iter2/
  20260224_060054_iter3/
  # Run B — qwen2.5:14b (2026-02-25 — 2026-02-26, 5 iterations + 1 aborted)
  20260225_003123_iter1/
  20260225_005905_iter2/
  20260225_012204_iter3/
  20260226_040125_iter4/    # aborted (no hypotheses)
  20260226_040507_iter4/    # retry, completed
  20260226_041913_iter5/
  # Run C — glm-4.7-flash:q8_0 (2026-02-26, 1 completed + 2 aborted)
  20260226_045243_iter1/    # completed, 155k tokens, ~8 hours
  20260226_124726_iter2/    # aborted (no hypotheses), 75k tokens
  20260226_174017_iter2/    # aborted retry (no hypotheses), 75k tokens
```

Each iteration directory contains:
```
  explore.json         # Phase 1 output
  hypotheses.json      # Phase 2 output
  implement.json       # Phase 3 output
  red_team.json        # Phase 4 output
  audit.json           # Phase 5 output
  reflect.json         # Phase 6 output
  iteration_summary.json  # Rolled-up scores
```
