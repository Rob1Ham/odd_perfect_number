# Unconditional `p`-adic and Repunit Obstructions to Prime-Power Component Indices — Standalone Breakout

Self-contained Lean `v4.36.0` + Mathlib (`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`) package establishing unconditional obstructions to prime-power component indices $i_r = \sigma(N/r^{v_r(N)})/r^{v_r(N)} = p^j$ ($p$ prime, $j \ge 1$) of hypothetical odd perfect numbers—without assuming the Nagell–Ljunggren or Goormaghtigh conjectures.

## Key Files

| File | Description |
| :--- | :--- |
| [`PrimePowerIndex.lean`](PrimePowerIndex.lean) | Public entry point packaging non-Euler elimination (`r = q`), non-Fermat base restriction, 13-repunit Goormaghtigh forcing, subexponential base cap, primorial confinement `min S₁ ∈ {3,5,7,11,13}`, Gauss-sum reciprocity, and `ℤ_[p]` Hensel root distance |
| [`OddPerfect/ComponentIndexMatrix.lean`](OddPerfect/ComponentIndexMatrix.lean) | Global `2`-adic component-index dichotomy (`v₂(i_q) = 0` vs. `v₂(i_r) = 1` for `r ≠ q`) |
| [`OddPerfect/PrimePowerHigherObstruction.lean`](OddPerfect/PrimePowerHigherObstruction.lean) | Mod-`p²` and mod-`p³` divisor-power congruences (building on `PrimePowerObstruction`, `TripleRepunitObstruction`, and `QuadrupleRepunitObstruction` to eliminate `|S₁| ≤ 4` and prove `30028 ≤ j`) |
| [`OddPerfect/TridecupleRepunitObstruction.lean`](OddPerfect/TridecupleRepunitObstruction.lean) | Elimination of `|S₁| ≤ 12`, forcing `HasThirteenOddPrimeRepunits p`, `16 ≤ ω(N)`, `13082761331670028 ≤ j`, and `10 ^ 353234555955090756 < N` |
| [`OddPerfect/EvenIndexPrimorialObstruction.lean`](OddPerfect/EvenIndexPrimorialObstruction.lean) | All-`k` symbolic primorial bound confining `min S₁ ∈ {3, 5, 7, 11, 13}` |
| [`OddPerfect/PadicEvenIndexObstruction.lean`](OddPerfect/PadicEvenIndexObstruction.lean) | Universal mod-`p⁴` cofactor congruence and `p`-adic Hensel root distance `‖s - σ_p‖_p = p^(-(2u+1))` |
| [`OddPerfect/GaussSumCyclotomicForms.lean`](OddPerfect/GaussSumCyclotomicForms.lean) | Quadratic Gauss-sum cyclotomic reciprocity `IsSquare ((-1)^(l/2) * l : ZMod p)` |
| [`Audit.lean`](Audit.lean) | Standalone kernel axiom verifier (`[propext, Classical.choice, Quot.sound]` only) |
| [`paper/main.tex`](paper/main.tex) | Companion `amsart` LaTeX manuscript |

## Paper-to-Lean Theorem Mapping (`paper/main.tex`)

| Paper Item | Lean Declaration(s) | Location |
| :--- | :--- | :--- |
| Theorem 1 (Euler-only confinement & non-Fermat base) | `componentIndex_two_valuation_dichotomy`, `prime_power_index_euler_only_and_nonfermat` | [`OddPerfect/ComponentIndexMatrix.lean:99`](OddPerfect/ComponentIndexMatrix.lean#L99), [`PrimePowerIndex.lean:47`](PrimePowerIndex.lean#L47) |
| Theorem 2 (Mod-`p` harmonic, mod-`p^4`, & `ℤ_[p]` Hensel root) | `even_index_mod_p_sq_second_order_congruence`, `even_prime_power_primorial_padic_and_gauss_reciprocity` | [`OddPerfect/PrimePowerHigherObstruction.lean:373`](OddPerfect/PrimePowerHigherObstruction.lean#L373), [`PrimePowerIndex.lean:135`](PrimePowerIndex.lean#L135) |
| Theorem 3 (13 Goormaghtigh repunits, primorial & size bounds) | `even_prime_power_tridecuple_repunit_and_size_bounds`, `even_prime_power_primorial_padic_and_gauss_reciprocity` | [`PrimePowerIndex.lean:105`](PrimePowerIndex.lean#L105), [`PrimePowerIndex.lean:135`](PrimePowerIndex.lean#L135) |

Audited totals (`Audit.lean`): **`172` structural modules (`0` size-tree certificate chunks), `723` named theorems, `6,271` declarations** on `[propext, Classical.choice, Quot.sound]`.

## Building & Auditing Standalone

```sh
lake exe cache get   # if building outside the parent checkout
lake build
lake lean Audit.lean
```
