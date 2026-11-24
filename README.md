# Odd perfect numbers in Lean

This project studies whether `∃ n : ℕ, Odd n ∧ Nat.Perfect n`. The definition of perfection comes from mathlib. The Lean toolchain and mathlib commit are pinned in this repository.

With Elan installed, run the following from the checkout.

```sh
lake build
lake env lean research/Audit.lean
```

The audit prints the type and foundation axioms of every named project theorem imported by `OddPerfect`. It fails on a project axiom or on any declaration depending on an axiom outside the allowed three. The research ledger tracks branch coverage, and the corpus links published results to their local verification status. [Research ledger](research/LEDGER.md) · [Literature corpus](research/CORPUS.md) · [Overnight report](OVERNIGHT.md)
