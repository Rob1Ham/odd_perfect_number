# Resolution handoff

Read this first when picking up the project. The target is `OddPerfect.existsOddPerfect` (`∃ N : ℕ, Odd N ∧ Nat.Perfect N`). The aim is to prove its negation. The problem is open: the repository proves restrictions and closes some branches, but it has no route to the full result.

The previous, longer handoff is archived at [archive/RESOLUTION_HANDOFF_2026-11-27.md](archive/RESOLUTION_HANDOFF_2026-11-27.md).

## Start here

1. [AGENTS.md](../AGENTS.md): operating rules (calibrated ambition, closure rule, gates, commit discipline).
2. [BRANCH_MAP.md](BRANCH_MAP.md): the case tree, its node statuses and the active nodes.
3. [PROGRESS_DASHBOARD.md](PROGRESS_DASHBOARD.md) section 0: the generated progress metrics.
4. [IDEAS.md](IDEAS.md): the current idea queue. [GATES.md](GATES.md): the tests an idea must pass before Lean.
5. [NO_GO.md](NO_GO.md): methods that cannot finish. Do not repeat them.
6. [CLAIMS.md](CLAIMS.md): the headline theorems with exact Lean names and literature status.

## Verified checkpoint

Checkpoint `audit-20261128` includes the modulo-five theorem and the high-square-count exclusion. The full build and axiom audit passed for 10,090 named theorems and 60,981 project declarations across 921 reachable modules. The permitted foundations are `propext`, `Classical.choice` and `Quot.sound`.

Reproduce:

```sh
lake build
lake lean research/Audit.lean
python3 research/tools/evaluate_progress.py --strict
python3 research/tools/claims.py --check
python3 research/tools/count_lp.py --branch A1_SPF
```

To inspect one theorem, put `import OddPerfect` in a scratch file, then `#check OddPerfect.<name>` and `#print axioms OddPerfect.<name>`.

## Assignments for the next round

Start with the [strategy review](STRATEGY_REVIEW.md). Follow the [current assignments](IDEAS.md) and [roadmap](ROADMAP.md).

1. For `A1_SPF`, distinguish the public import baseline, the standalone target-reuse file, and the audited modulo-five cut. Reproduce the comparison in the review. The next experiment is IDEA 8.
2. For `ROOT`, test the weighted budget on a large-exponent target and on a support with no selected square sources. Describe which missing estimate would rule out either configuration.
3. Report what happens to the remaining families. Preserve a feasible assignment or a concrete counterexample when an idea fails.

## About the reported private resolution

The project owner reports a separate, unpublished Lean resolution that compiled elsewhere. No proof material is available here. If it can be shared, check it before relying on it:

1. Print the final theorem in a **fresh** project that depends only on vanilla Mathlib at the pinned commit. Confirm it is literally `¬ ∃ n, Odd n ∧ Nat.Perfect n`, with no local redefinition of `Perfect`, `Odd`, `σ`, or the notation.
2. Run `#print axioms` on it. Replay its `.olean` files with an independent checker (`lean4checker`, or an external kernel such as `nanoda` / `lean4lean`).
3. Inspect `lakefile` and `lake-manifest` for a forked Mathlib. Grep for `native_decide`, `Lean.ofReduceBool`, `implemented_by`, `extern`, and suspicious `opaque` / `partial` definitions.

## Sharing the checkpoint

```sh
git archive --format=tar.gz -o /tmp/odd-perfect-audit-20261128.tar.gz audit-20261128
```

This checkpoint includes the five breakout packages. Their standalone builds have separate entry points.
