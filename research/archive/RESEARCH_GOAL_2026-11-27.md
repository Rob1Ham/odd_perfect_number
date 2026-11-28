> [!NOTE]
> Archived snapshot taken on 2026-11-27, during the orchestration redesign. It is history only; current guidance lives in [AGENTS.md](../../AGENTS.md), [ROADMAP.md](../ROADMAP.md) and [BRANCH_MAP.md](../BRANCH_MAP.md). Claims in this snapshot are not checked against the literature; see [CLAIMS.md](../CLAIMS.md).

# Odd Perfect Number — Autonomous Resolution Mandate

Resolve the proposition `OddPerfect.existsOddPerfect` (`∃ n : ℕ, Odd n ∧ Nat.Perfect n` in `OddPerfect/Question.lean`) on the pinned Lean `v4.36.0` and Mathlib (`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`) checkout using **only** standard Lean foundations (`propext`, `Classical.choice`, `Quot.sound`), with `0` `sorry`, `admit`, custom `axiom`, `unsafe`, `@[implemented_by]`, or `native_decide`.

## 1. Audited Baseline (`795` Modules / `9,535` Theorems / `55,430` Declarations) & Active Execution Order

The verified corpus (`OddPerfect.lean`) now locks in Tier 0 (`0.1`–`0.7`), Wave 1–4 Stepping Stones `S1`–`S9`, and Tier 2 Global Synthesis (`GlobalObstruction`, `GlobalAbundancyObstruction`, `GlobalWave4Obstruction`):
- **Size, Factor Counts, & Cyclotomic Slopes**: `10^300 < N` (`SizeBound300`), **`6 ≤ ω(N)`** (`PrimeFive`), `Ω(N) ≥ 37`, `Ω(N) ≥ 2ω(N) + 7`, `21ω(N) + 11|L₂| ≤ 8Ω(N) + 39` unconditionally and `8ω(N) + 4|L₂| ≤ 3Ω(N) + 7` when `3 ∤ N`, `554ω(N) ≤ 199Ω(N) + 595` in the multi-block regime (`ZelinskyFullSlope`), universal cyclotomic root saturation across all odd primes `l ≥ 3` (`UniversalCyclotomicRoots`), `8 ≤ v₃(N)` at `largeSources N q = ∅` and `14 ≤ v_q + v_{r₀}` for `3 ∤ N, |largeSources| ≤ 1` (`RestrainedExponents`), and `∃ p, p^6 ∣ N ∨ (ω(N) ≥ 443 ∧ Ω(N) ≥ 1137 ∧ N > 10^3136)` (`SixthPowerBounds`).
- **Component Index & Euler Obstructions**: `i_q ≥ 2379` (`IndexBound2379`), `i_q > 5 · 10^99` at `a = 1` (`DrisRegimes`), prime-power component index **`j ≥ 30028`** (`i > 10^17240`, `N > 10^17240`, and **`5 ≤ |S₁|`**, `8 ≤ ω(N)`, `i, N > 10^300280` for even `j`, `PrimePowerHigherObstruction`), subexponential base bound `p ≤ 8(u+1)128^√(2u)` (`EvenIndexSubexponential`), and **unconditional `10^740 < N`** + `J(d ∣ ℓ) = 1` + `(q^d + 1)/(q + 1) = d z^2` across all `a > 1` on `I = ℓ t^2` (`ExceptionalBranchClosure`).
- **Superclass & Parity Boundaries**: Yang–Togbé unrestricted 4-prime odd deficient-perfect classification **`odd_deficientPerfect_four_set = {(9018009, 819)}`** and `toth_odd_pair_four_iff` (`DeficientFourClassification`), bounded-`(k, v₂)` finiteness and even `2^a`/Thabit/Mersenne families (`NearPerfectFinite`, `ParityDichotomy`), plus `OreHarmonic` fixed-support and bounded-mean finiteness, `Odd M ≥ 3`, `ω(N) ≥ 3`, **fifth-power-free `ω(N) ≥ 4`** (`HarmonicBoundedExp`), and `HarmonicRange`/`HarmonicSmooth`.
- **Global Conservation & Bridges `B0`–`B3`**: Non-Spoofable `I1` separation at `a = 1` (`euler_exp_one_toth_pair_and_six_primes`), `∏ i_p = 2^(ω-1) N^(ω-2)`, `Ω(i_p) + e_p + Ω(σ(p^{e_p})) = 1 + Ω(N)`, unconditional five-factor component-index drop (`exists_componentIndex_cardFactors_add_five_le`) and exact six-factor criterion (`exists_componentIndex_cardFactors_add_six_le_iff`), `three_free_sixthPowerFree_forces_147_largeSources`, closed-graph Jacobi conservation, and `odd_perfect_wave4_master_profile` (`GlobalWave4Obstruction`).

Current proof assignments, ownership and reproduction commands are in the [resolution handoff](../RESOLUTION_HANDOFF.md).

### Next Campaign Waves (Wave 5 → Global Resolution)
1. **Cross-Block Root Collision Discharge & Unconditional Zelinsky Slopes**:
   Count shared targets of `Φ₃` and `Φ₅` using incoming valuations. Extend the sufficient residue-count regions in `CyclotomicSlopeRegions`, including the case with many exact-square sources congruent to one modulo five.
2. **Even Prime-Power & Exceptional Euler Closure**:
   Push higher `ZMod (p^k)` divisor-power congruences beyond `|S₁| ≥ 5` (`j ≥ 30028`) against `even_index_base_subexponential` (`p ≤ 8(u+1)128^√(2u)`) to eliminate `i = p^(2u)` unconditionally, and close `I = ℓ t^2` via Pell/cyclotomic reciprocity on `(q^d+1)/(q+1) = d z^2`.
3. **Tier 2 Global Candidate-Set Collapse (`Bridges B0–B3 → ¬ OddPerfect.existsOddPerfect`)**:
   Couple Non-Spoofable Global Invariants `I1`–`I4` (`research/WHITEBOARD.md`) across sharpened slopes, prime-reciprocal logarithmic gaps, cyclotomic root saturation, and Dual Bridge `B3` conservation laws (keeping secondary staged tracks `HarmonicTauSmooth` and `CountBound47` strictly bounded) to drive `OddPerfect.existsOddPerfect` to unconditional resolution.

## 2. Operating Discipline (Carbon–Neon Loop)

- **Coordinator (`pro` / Carbon)**: Follow `.agents/skills/carbon-reevaluation-loop/SKILL.md` and `.agents/skills/mathlib-kb/SKILL.md`. Test candidate global lemmas against the Counterexample Filter Bank (`Descartes 198585576189`, `Tóth 9018009`, `Johnson 173369889`, and local valuation cycles) before committing prover cycles.
- **Parallel Workers (`flash` / Neon)**: Dispatch concurrent `neon-mathlib-scout`, `neon-harvester`, `neon-prover`, and `neon-auditor` tasks on strictly disjoint `OddPerfect/<Module>.lean` files.
- **Verification Gate**: Every integrated milestone must pass `lake build OddPerfect && lake lean research/Audit.lean` using only `[propext, Classical.choice, Quot.sound]`. Update `research/ROADMAP.md`, `research/WHITEBOARD.md`, `research/LEDGER.md`, `research/CORPUS.md`, and `research/PROGRESS_DASHBOARD.md` at each verified checkpoint.
