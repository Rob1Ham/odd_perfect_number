# Euler Index Bounds, Non-Fermat Support, & `ℤ√2` Descent — Standalone Breakout

Self-contained Lean `v4.36.0` + Mathlib (`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`) package sharpening the unconditional Euler component index lower bound from $315$ (Broughan, Delbourgo, and Zhou 2013) to **$2{,}379$**, proving every Euler index has a non-Fermat prime divisor, and establishing $N > 10^{740}$, a $148$-class modular Fermat sieve, and reduced $\mathbb{Z}[\sqrt{2}]$ Frobenius descent on Hirakawa's (2024) prime-times-square Euler-index branch $I = \ell t^2$ ($a > 1$).

## Key Files

| File | Description |
| :--- | :--- |
| [`EulerIndexBounds.lean`](EulerIndexBounds.lean) | Public entry point packaging `2379 ≤ σ(m²)/q^a`, non-Fermat prime support, `10^740 < N`, the 148-class modular Fermat sieve, and `ℤ√2` Frobenius descent |
| [`OddPerfect/IndexBound2379.lean`](OddPerfect/IndexBound2379.lean) | Two-base cyclotomic residual GCD sieve proving `2379 * q^a < 2 * m²` and `2379 ≤ σ(m²)/q^a` |
| [`OddPerfect/FermatIndexObstruction.lean`](OddPerfect/FermatIndexObstruction.lean) | Proof that every odd component index has a prime factor `p` with `p - 1` not a power of two |
| [`OddPerfect/ExceptionalBranchClosure.lean`](OddPerfect/ExceptionalBranchClosure.lean) | Unconditional `10^740 < N` across all `a > 1` on `σ(m²)/q^a = l * t²` (closing `d = 17` via `15 ∣ w`) |
| [`OddPerfect/HirakawaClosure.lean`](OddPerfect/HirakawaClosure.lean) | Fundamental Pell solutions in `ℤ[√(2q)]` and `ℤ[√(q(q+1))]` on Hirakawa's block equations |
| [`OddPerfect/ExceptionalFermatHigherSieve.lean`](OddPerfect/ExceptionalFermatHigherSieve.lean) | Mod-8-refined 148-class modular Fermat obstruction (`q % 5 ≠ 3`, `d ≥ 241` for `3, 5 ∤ N`) |
| [`OddPerfect/ZsqrtTwoFermatDescent.lean`](OddPerfect/ZsqrtTwoFermatDescent.lean) | `EuclideanDomain (ℤ√2)`, unit group `±(1+√2)^ℤ`, `k ≠ 0` power descent, and mod-`d` Frobenius congruence |
| [`Audit.lean`](Audit.lean) | Standalone kernel axiom verifier (`[propext, Classical.choice, Quot.sound]` only) |
| [`paper/main.tex`](paper/main.tex) | Companion `amsart` LaTeX manuscript |

## Paper-to-Lean Theorem Mapping (`paper/main.tex`)

| Paper Item | Lean Declaration(s) | Location |
| :--- | :--- | :--- |
| Theorem 1 (Euler index threshold `2,379`) | `euler_index_ge_2379` | [`EulerIndexBounds.lean:44`](EulerIndexBounds.lean#L44) |
| Theorem 2 (Non-Fermat support & predecessor escape) | `odd_component_index_has_nonfermat_prime`, `euler_index_odd_valuation_escape` | [`EulerIndexBounds.lean:53`](EulerIndexBounds.lean#L53), [`EulerIndexBounds.lean:62`](EulerIndexBounds.lean#L62) |
| Theorem 3 (`10^740` bound, Pell minimality, & 148-class sieve) | `hirakawa_second_block_pell_fundamental`, `hirakawa_exceptional_branch_size_and_sieve` | [`EulerIndexBounds.lean:71`](EulerIndexBounds.lean#L71), [`EulerIndexBounds.lean:81`](EulerIndexBounds.lean#L81) |
| Theorem 4 (`ℤ√2` Euclidean domain & Frobenius descent) | `instEuclideanDomainZsqrtTwo`, `hirakawa_zsqrtTwo_frobenius_descent` | [`OddPerfect/ZsqrtTwoFermatDescent.lean:135`](OddPerfect/ZsqrtTwoFermatDescent.lean#L135), [`EulerIndexBounds.lean:107`](EulerIndexBounds.lean#L107) |

Audited totals (`Audit.lean`): **`156` modules (`0` size-tree certificate chunks), `629` named theorems, `4,454` declarations** on `[propext, Classical.choice, Quot.sound]`.

## Building & Auditing Standalone

```sh
lake exe cache get   # if building outside the parent checkout
lake build
lake lean Audit.lean
```
