# Analytical Exclusion of Three-Free Restrained Odd Perfect Numbers — Standalone Breakout

Self-contained Lean `v4.36.0` + Mathlib (`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`) package giving a **purely analytical exclusion of three-free restrained odd perfect numbers** ($\neg 3 \mid N \implies |\text{largeSources } N\; q| \ge 2$, where $\text{largeSources } N\; q$ is the set of non-$3$, non-Euler prime divisors with exponent $\ge 4$), extending the smooth-quadratic growth method to **two** large non-Euler exponents, and proving $81 \mid N$ whenever $|\text{largeSources } N\; q| \le 1$ and $q \equiv 2 \pmod 3$.

## Key Files

| File | Description |
| :--- | :--- |
| [`RestrainedOPN.lean`](RestrainedOPN.lean) | Public entry point packaging the smooth-quadratic growth inequality, `¬ 3 ∣ N → 2 ≤ |largeSources|`, two-large-sources congruence forcing, and `3`-adic restrained exponent bounds |
| [`OddPerfect/ThreeFreeRestrainedClosure.lean`](OddPerfect/ThreeFreeRestrainedClosure.lean) | Pigeonhole median step `5 * u₀ + 3 ≤ 2 * u₂` on `{q, r₀}`-smooth `u² + u + 1` values and unconditional closure of `¬ 3 ∣ N ∧ |largeSources| ≤ 1` |
| [`OddPerfect/ThreeFreeTwoLargeSources.lean`](OddPerfect/ThreeFreeTwoLargeSources.lean) | Extension to `|largeSources| = 2` (`r ≡ 1 [MOD 3]` for both large bases, or `7 ≤ |largeSources|` if none is `1 [MOD 3]`) |
| [`OddPerfect/RestrainedThreeSquareObstruction.lean`](OddPerfect/RestrainedThreeSquareObstruction.lean) | Exclusion of `v₃(N) = 2` (`81 ∣ N`) across all restrained candidates with `q ≡ 2 [MOD 3]` |
| [`OddPerfect/RestrainedSquareSourcesOneObstruction.lean`](OddPerfect/RestrainedSquareSourcesOneObstruction.lean) | Confinement `q % 12 = 1 ∧ 13 ≤ q ∧ 1 ≤ |squareSourcesOne N| ≤ 2` at `v₃(N) = 2` |
| [`Audit.lean`](Audit.lean) | Standalone kernel axiom verifier (`[propext, Classical.choice, Quot.sound]` only) |
| [`paper/main.tex`](paper/main.tex) | Companion `amsart` LaTeX manuscript (*"An Elementary Exclusion of Three-Free Restrained Odd Perfect Numbers and Extensions to Two Large Exponents"*) |

## Paper-to-Lean Theorem Mapping (`paper/main.tex`)

| Paper Item | Lean Declaration(s) | Location |
| :--- | :--- | :--- |
| Theorem 1 (`¬ 3 ∣ N → 2 ≤ |largeSources N q|`) | `three_free_restrained_excluded` | [`RestrainedOPN.lean:63`](RestrainedOPN.lean#L63) |
| Theorem 2 (Two-large-sources congruence & 7-source jump) | `three_free_two_large_sources_congruence` | [`RestrainedOPN.lean:76`](RestrainedOPN.lean#L76) |
| Theorem 3 (`3`-adic exponent bounds & `v₃(N) = 2` profile) | `restrained_three_divisibility_and_exponent_profile` | [`RestrainedOPN.lean:95`](RestrainedOPN.lean#L95) |
| Lemma 4 & Corollary 5 (Common prime-power & `5u² < v` gap) | `zelinsky_twoModThree_prime_pow_common_divisor_le`, `sq_add_self_add_one_prime_pow_gap` | [`OddPerfect/ThreeFreeRestrainedClosure.lean:107`](OddPerfect/ThreeFreeRestrainedClosure.lean#L107), [`OddPerfect/RestrainedThreeFreeObstruction.lean:104`](OddPerfect/RestrainedThreeFreeObstruction.lean#L104) |
| Lemma 6 (`{q, r₀}`-smooth `5 u₀ + 3 ≤ 2 u₂` growth) | `smooth_quadratic_three_step_growth` | [`RestrainedOPN.lean:46`](RestrainedOPN.lean#L46) |

Audited totals (`Audit.lean`): **`108` modules (`0` size-tree certificate chunks), `507` named theorems, `4,193` declarations** on `[propext, Classical.choice, Quot.sound]`.

## Building & Auditing Standalone

```sh
lake exe cache get   # if building outside the parent checkout
lake build
lake lean Audit.lean
```
