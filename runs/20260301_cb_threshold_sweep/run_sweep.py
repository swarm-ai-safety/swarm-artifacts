#!/usr/bin/env python
"""CB threshold sweep: 4x4x3x3 full factorial = 1,440 runs.

Tests claim-cb-null-may-reflect-design-limitation by varying
freeze_threshold_toxicity, freeze_threshold_violations,
freeze_duration_epochs, and transaction_tax_rate.

Directional prediction: freeze_threshold_toxicity 0.3-0.5
maximizes welfare (claim-optimal-cb-threshold-predicted-in-03-05-range).
"""

import json
import os
import sys
import time
from pathlib import Path

os.environ.setdefault("MPLBACKEND", "Agg")

sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent))

from swarm.analysis import SweepConfig, SweepParameter, SweepRunner  # noqa: E402
from swarm.scenarios import load_scenario  # noqa: E402

RUN_DIR = Path(__file__).resolve().parent
SCENARIO = (
    Path(__file__).resolve().parent.parent.parent
    / "scenarios"
    / "hypotheses"
    / "cb_threshold_sweep.yaml"
)
SEEDS = 10
SEED_BASE = 42


def progress(current: int, total: int, params: dict) -> None:
    param_str = ", ".join(f"{k.split('.')[-1]}={v}" for k, v in params.items())
    print(f"  [{current}/{total}] {param_str}")


def main() -> int:
    print("=" * 60)
    print("CB Threshold Sweep — Full Factorial")
    print("=" * 60)

    base_scenario = load_scenario(SCENARIO)

    sweep_config = SweepConfig(
        base_scenario=base_scenario,
        parameters=[
            SweepParameter(
                name="governance.freeze_threshold_toxicity",
                values=[0.3, 0.5, 0.7, 0.9],
            ),
            SweepParameter(
                name="governance.freeze_threshold_violations",
                values=[1, 3, 5, 8],
            ),
            SweepParameter(
                name="governance.freeze_duration_epochs",
                values=[1, 3, 5],
            ),
            SweepParameter(
                name="governance.transaction_tax_rate",
                values=[0.0, 0.05, 0.10],
            ),
        ],
        runs_per_config=SEEDS,
        seed_base=SEED_BASE,
    )

    n_configs = 4 * 4 * 3 * 3
    total_runs = n_configs * SEEDS
    print(f"\nParameters:")
    for p in sweep_config.parameters:
        print(f"  - {p.name}: {p.values}")
    print(f"Configurations: {n_configs}")
    print(f"Seeds per config: {SEEDS}")
    print(f"Total runs: {total_runs}\n")

    t0 = time.time()
    runner = SweepRunner(sweep_config, progress_callback=progress)
    runner.run()
    elapsed = time.time() - t0

    # Export results
    csv_path = RUN_DIR / "sweep_results.csv"
    runner.to_csv(csv_path)
    print(f"\nResults written to: {csv_path}")

    try:
        runner.to_parquet(csv_path.with_suffix(".parquet"))
        print(f"Parquet written to: {csv_path.with_suffix('.parquet')}")
    except Exception:
        pass

    # Summary
    summary = runner.summary()
    summary["elapsed_seconds"] = round(elapsed, 1)
    summary_path = RUN_DIR / "summary.json"
    with open(summary_path, "w") as f:
        json.dump(summary, f, indent=2)
    print(f"Summary written to: {summary_path}")

    print(f"\n{'=' * 60}")
    print(f"Completed {summary['total_runs']} runs in {elapsed:.0f}s")
    print(f"Parameter combinations: {summary['param_combinations']}")
    print(f"{'=' * 60}")

    # Quick summary table
    print("\nTop 5 configs by welfare:")
    sorted_configs = sorted(
        summary["summaries"], key=lambda x: x.get("mean_welfare", 0), reverse=True
    )
    for i, cfg in enumerate(sorted_configs[:5]):
        thr = cfg.get("governance.freeze_threshold_toxicity", "?")
        viol = cfg.get("governance.freeze_threshold_violations", "?")
        dur = cfg.get("governance.freeze_duration_epochs", "?")
        tax = cfg.get("governance.transaction_tax_rate", "?")
        w = cfg.get("mean_welfare", 0)
        tox = cfg.get("mean_toxicity", 0)
        print(f"  {i+1}. thr={thr} viol={viol} dur={dur} tax={tax} → welfare={w:.1f} toxicity={tox:.3f}")

    print("\nBottom 5 configs by welfare:")
    for i, cfg in enumerate(sorted_configs[-5:]):
        thr = cfg.get("governance.freeze_threshold_toxicity", "?")
        viol = cfg.get("governance.freeze_threshold_violations", "?")
        dur = cfg.get("governance.freeze_duration_epochs", "?")
        tax = cfg.get("governance.transaction_tax_rate", "?")
        w = cfg.get("mean_welfare", 0)
        tox = cfg.get("mean_toxicity", 0)
        print(f"  {i+1}. thr={thr} viol={viol} dur={dur} tax={tax} → welfare={w:.1f} toxicity={tox:.3f}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
