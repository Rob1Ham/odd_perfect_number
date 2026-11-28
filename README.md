# Odd perfect numbers in Lean

This repository pursues a kernel-checked resolution of `OddPerfect.existsOddPerfect` (`∃ n : ℕ, Odd n ∧ Nat.Perfect n`), using Mathlib's `Nat.Perfect` on a pinned Lean `v4.36.0` and Mathlib (`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`) checkout.

**Status.** The conjecture remains open. The repository is a verified library of restrictions on hypothetical odd perfect numbers. It includes formal replays of classical results and closes several sub-branches of an explicit case tree.

With Elan installed, run the full build and the foundational axiom audit from the repository root:

```sh
lake build
lake lean research/Audit.lean
```

The audit checks every project declaration reachable from `OddPerfect.lean`. It fails on any `sorry`, any project axiom, or any dependency outside `[propext, Classical.choice, Quot.sound]`.

## Navigation

- [Operating rules](AGENTS.md): research premise, roles, gates and invariants
- [Case tree](research/BRANCH_MAP.md): the unit of progress; node statuses and the active nodes
- [Roadmap](research/ROADMAP.md): active program, terminating deliverables, frozen methods
- [Progress dashboard](research/PROGRESS_DASHBOARD.md): generated progress metrics and library health
- [Headline claims](research/CLAIMS.md): exact Lean names, statements and literature status
- [Idea queue](research/IDEAS.md) · [Pre-dispatch gates](research/GATES.md) · [No-go record](research/NO_GO.md) · [Floor/ceiling register](research/FLOOR_CEILING.md)
- [Whiteboard](research/WHITEBOARD.md): the closed equation, non-spoofable properties, counterexample filter bank
- [Resolution handoff](research/RESOLUTION_HANDOFF.md): start here when picking up the work
- [Research ledger](research/LEDGER.md): chronological record of audited rounds
- [Literature corpus](research/CORPUS.md): published results and their local Lean coverage

Tools: `research/tools/evaluate_progress.py` (dashboard), `research/tools/claims.py` (claims registry), `research/tools/count_lp.py` (count-polyhedron gate), `research/tools/mathlib_kb.py` (Mathlib search).
