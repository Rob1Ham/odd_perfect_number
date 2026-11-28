# Resolution handoff

Read this first when picking up the project. The target is `OddPerfect.existsOddPerfect` (`∃ N : ℕ, Odd N ∧ Nat.Perfect N`). The aim is to prove its negation. The problem is open: the repository proves restrictions and closes some branches, but it has no route to the full result.

The previous, longer handoff is archived at [archive/RESOLUTION_HANDOFF_2026-11-27.md](archive/RESOLUTION_HANDOFF_2026-11-27.md).

## Start here

1. [AGENTS.md](../AGENTS.md): operating rules (calibrated ambition, closure rule, gates, commit discipline).
2. [BRANCH_MAP.md](BRANCH_MAP.md): the case tree, its node statuses and the 3 active nodes.
3. [PROGRESS_DASHBOARD.md](PROGRESS_DASHBOARD.md) section 0: the generated progress metrics.
4. [IDEAS.md](IDEAS.md): the current idea queue. [GATES.md](GATES.md): the tests an idea must pass before Lean.
5. [NO_GO.md](NO_GO.md): methods that cannot finish. Do not repeat them.
6. [CLAIMS.md](CLAIMS.md): the headline theorems with exact Lean names and literature status.

## Verified checkpoint

Tag `audit-20261127`: `lake build` plus `lake lean research/Audit.lean` passed, with 10,083 named theorems and 60,946 project declarations, all depending only on `propext`, `Classical.choice` and `Quot.sound`.

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

Take one active node and follow `.agents/skills/carbon-reevaluation-loop/SKILL.md`. Phases 2–3 (informal sketch, gates, Skeptic) come **before** any Lean.

| Node | First experiment | Done when |
| --- | --- | --- |
| `A1_SPF` | IDEAS #1: list the Φ₃/Φ₅ root-class and size constraints on targets. Encode any resulting linear consequence with `count_lp.py --add` | The LP ray is cut, or the idea is KILLED with a reason |
| `IQ_PRIME_POWER_EVEN` | IDEAS #3: attempt a Dickson-type gap bound u ≤ g(p, ω(s)) on paper | A ceiling is stated and passes the Skeptic, or the node is frozen with a NO_GO entry |
| `A1_G1` | IDEAS #4: search for a descent on u² = Wσ(h²), σ(u²) = W(2h² − 1). First test whether spoof "solutions" exist | A strictly smaller family is defined, or the idea is KILLED |
| Background | ROADMAP §3: the Fletcher–Nielsen–Ochem least-prime replay, or Bang–Zsigmondy to Mathlib | Audited theorem or merged PR |

Close every assignment with: the exact Lean statement or the KILL evidence, the gate record, the branch impact, and the axiom output. The Strategist owns `OddPerfect.lean` and the research documents.

## About the reported private resolution

The project owner reports a separate, unpublished Lean resolution that compiled elsewhere. No proof material is available here. If it can be shared, check it before relying on it:

1. Print the final theorem in a **fresh** project that depends only on vanilla Mathlib at the pinned commit. Confirm it is literally `¬ ∃ n, Odd n ∧ Nat.Perfect n`, with no local redefinition of `Perfect`, `Odd`, `σ`, or the notation.
2. Run `#print axioms` on it. Replay its `.olean` files with an independent checker (`lean4checker`, or an external kernel such as `nanoda` / `lean4lean`).
3. Inspect `lakefile` and `lake-manifest` for a forked Mathlib. Grep for `native_decide`, `Lean.ofReduceBool`, `implemented_by`, `extern`, and suspicious `opaque` / `partial` definitions.

## Sharing the checkpoint

```sh
git archive --format=tar.gz -o /tmp/odd-perfect-audit-20261127.tar.gz audit-20261127
```

The four `*-breakout/` package directories are not yet tracked by git. Commit them separately if they should travel with the checkpoint.
