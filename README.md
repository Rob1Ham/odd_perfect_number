# Odd perfect numbers in Lean

This repository pursues a complete, kernel-checked resolution of `OddPerfect.existsOddPerfect` (`∃ n : ℕ, Odd n ∧ Nat.Perfect n`) using mathlib's `Nat.Perfect` on a pinned Lean `v4.36.0` and mathlib (`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`) checkout.

With Elan installed, run the full build and foundational axiom audit from the repository root:

```sh
lake build
lake lean research/Audit.lean
```

The audit verifies every project declaration reachable from `OddPerfect.lean` and fails on any `sorry`, project axiom, or dependency outside `[propext, Classical.choice, Quot.sound]`.

## Navigation

- [Resolution handoff](research/RESOLUTION_HANDOFF.md) — verified branch closures, surviving cases, and scoped assignments for the next proof round
- [Resolution roadmap](research/ROADMAP.md) — Tier 0 staged harvest, Tier 1 open stepping-stone theorems, and Tier 2 global resolution strategy
- [Mathematical whiteboard](research/WHITEBOARD.md) — Bridges to finiteness (`B0`–`B3`), Counterexample Filter Bank, Non-Spoofable Global Invariants (`I1`–`I4`), and active proof sketches
- [Progress dashboard](research/PROGRESS_DASHBOARD.md) — Live audited vs. staged metrics and harvest queue
- [Research ledger](research/LEDGER.md) — Chronological record of kernel-checked milestones and architecture pivots
- [Literature corpus](research/CORPUS.md) — Theorem-level mapping of published results and local Lean coverage
- [Checkpoint report](OVERNIGHT.md) — Detailed summary of currently audited declarations
