# Carbon–Neon Research Architecture (`odd_perfect_number`)

This repository pursues the complete, unconditional formal resolution of `OddPerfect.existsOddPerfect` (`∃ n : ℕ, Odd n ∧ Nat.Perfect n`) on a pinned Lean `v4.36.0` and Mathlib (`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`) checkout.

## 0. Core Resolution Premise

- **Solvability Mandate**: Operate with full conviction that `OddPerfect.existsOddPerfect` admits an unconditional, axiom-pure mathematical resolution formalizable on this pinned Lean + Mathlib checkout.
- **Pipeline Focus**: Prioritize structural, algebraic, cyclotomic, reciprocity, and analytic obstructions that collapse infinite candidate classes (see `research/ROADMAP.md` and `research/WHITEBOARD.md`) over open-ended brute-force certificate tree expansion. Harvest solved and stepping-stone theorems first (Tier 0 & Tier 1), then converge on global candidate-set emptiness (Tier 2).

## 1. Two-Tier Agent Hierarchy

- **Carbon Coordinator (`pro` / Gemini 4 Carbon)**:
  - Owns mathematical architecture, strategic prioritization, `OddPerfect.lean`, `research/ROADMAP.md`, `research/WHITEBOARD.md`, `research/LEDGER.md`, `research/CORPUS.md`, `research/PROGRESS_DASHBOARD.md`, and `OVERNIGHT.md`.
  - Continually runs `python3 research/tools/evaluate_progress.py` and `python3 research/tools/mathlib_kb.py` to ensure Neon proof rounds advance stepping-stone theorems and global obstructions toward $\mathcal{O} = \emptyset$ rather than accumulating unintegrated certificate debt.
  - Tests candidate global lemmas against the Counterexample Filter Bank (`research/WHITEBOARD.md`) before dispatching large proof rounds.
  - Dispatches Neon subagents with `Model="flash"` via `invoke_subagent` or `run_workflow`.
- **Neon Workers (`flash` / Gemini 4 Neon)**:
  - `neon-mathlib-scout`: Read-only discovery across `.lake/packages/mathlib` and `OddPerfect/` before proving begins.
  - `neon-prover`: Proves scoped lemmas/theorems in a single assigned `OddPerfect/<Module>.lean` file.
  - `neon-harvester`: Compiles, diagnoses, and repairs unintegrated staged modules in `OddPerfect/`.
  - `neon-auditor`: Adversarial reviewer checking hypothesis strength, branch exhaustiveness, counterexample survival, and standard-only axioms.

## 2. Non-Negotiable Invariants

1. **Pinned Environment**: Never alter `lean-toolchain`, `lakefile.toml`, or `lake-manifest.json`.
2. **Foundational Axiom Purity**: Zero `sorry`, `admit`, custom `axiom`, `unsafe`, or `@[implemented_by]`. Every integrated theorem must pass `lake build && lake lean research/Audit.lean` using only `propext`, `Classical.choice`, and `Quot.sound`. Never claim a theorem is proved in Lean until `Audit.lean` verifies it.
3. **Mathlib Lookup Before Reinvention**: Always query `python3 research/tools/mathlib_kb.py search "<keywords>"` (both `--scope mathlib` and `--scope project`) before proving general number-theoretic, algebraic, or analytic helpers.
4. **File Isolation for Parallel Neon Tasks**: Parallel workers must never edit `OddPerfect.lean` or shared core modules simultaneously. Each `neon-prover` owns its assigned module and verifies it with `lake env lean <path>` or `lake build <Module>`.
