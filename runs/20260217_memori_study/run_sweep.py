#!/usr/bin/env python
"""Parameter sweep for Memori study — LLM agents with semantic memory."""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent.parent))

from swarm.analysis import SweepConfig, SweepParameter, SweepRunner
from swarm.scenarios import load_scenario

RUN_DIR = Path(__file__).parent
SCENARIO = Path(__file__).parent.parent.parent / "scenarios" / "llm_memori_openrouter.yaml"
OUTPUT = RUN_DIR / "sweep_results.csv"


def progress(current: int, total: int, params: dict) -> None:
    param_str = ", ".join(f"{k}={v}" for k, v in params.items())
    print(f"  [{current}/{total}] {param_str}", flush=True)


def main():
    print("=" * 60)
    print("Memori Study — Parameter Sweep")
    print("=" * 60)

    base_scenario = load_scenario(SCENARIO)
    base_scenario.orchestrator_config.n_epochs = 2
    base_scenario.orchestrator_config.steps_per_epoch = 5

    sweep_config = SweepConfig(
        base_scenario=base_scenario,
        parameters=[
            SweepParameter(
                name="governance.transaction_tax_rate",
                values=[0.0, 0.05, 0.10],
            ),
            SweepParameter(
                name="governance.circuit_breaker_enabled",
                values=[False, True],
            ),
        ],
        runs_per_config=5,
        seed_base=42,
    )

    print(f"  Parameters: {len(sweep_config.parameters)}")
    for p in sweep_config.parameters:
        print(f"    - {p.name}: {p.values}")
    print(f"  Runs per config: {sweep_config.runs_per_config}")
    print(f"  Total runs: {sweep_config.total_runs()}")
    print()
    print("Running sweep (this involves LLM API calls)...")
    print()

    runner = SweepRunner(sweep_config, progress_callback=progress)
    runner.run()

    print()
    print("=" * 60)
    print("Results Summary")
    print("=" * 60)

    summary = runner.summary()
    print(f"\nTotal runs: {summary['total_runs']}")
    print(f"Parameter combinations: {summary['param_combinations']}")
    print()

    print(
        f"{'Tax Rate':<10} {'Circuit':<10} {'Welfare':<12} {'Toxicity':<12} "
        f"{'Frozen':<8} {'Honest':<12} {'Adversarial':<12}"
    )
    print("-" * 86)

    for s in summary["summaries"]:
        tax = s.get("governance.transaction_tax_rate", 0)
        circuit = s.get("governance.circuit_breaker_enabled", False)
        print(
            f"{tax:<10.2f} "
            f"{'Yes' if circuit else 'No':<10} "
            f"{s['mean_welfare']:<12.2f} "
            f"{s['mean_toxicity']:<12.4f} "
            f"{s['mean_frozen']:<8.1f} "
            f"{s['mean_honest_payoff']:<12.2f} "
            f"{s['mean_adversarial_payoff']:<12.2f}"
        )

    print(f"\nExporting results to: {OUTPUT}")
    runner.to_csv(OUTPUT)
    print("Done.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
