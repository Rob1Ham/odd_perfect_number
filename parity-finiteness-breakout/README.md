# Parity Dichotomy & Fixed-Rank Finiteness — Standalone Breakout

Self-contained Lean `v4.36.0` + Mathlib (`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`) package proving the **unrestricted-parity $(k, v_2)$-finiteness dichotomy** for deficient-perfect numbers ($\sigma(n) + d = 2n$, $d \mid n$, $d < n$) and near-perfect numbers ($\sigma(n) = 2n + d$, $d \mid n$, $d < n$), resolving **Dutta and Saikia's Conjecture 3.2 (2020)** and answering **Yang and Togbé's §6 question (2023)** across all parities with explicit computable bounds and **zero** case-enumeration certificate files (`28` structural modules total).

## Key Files

| File | Description |
| :--- | :--- |
| [`ParityFiniteness.lean`](ParityFiniteness.lean) | Public entry point packaging the even infinite/conditional families, weighted prefix-gap bounds, `(k, v₂)`-finiteness for deficient-perfect and near-perfect pairs, and explicit odd `(4(k+1))^(4^(k+1))` bounds |
| [`OddPerfect/ParityDichotomy.lean`](OddPerfect/ParityDichotomy.lean) | Core weighted product-gap recurrence `weightedLabelBound` and unrestricted-parity `(k, A)`-finiteness proofs |
| [`OddPerfect/DeficientFiniteness.lean`](OddPerfect/DeficientFiniteness.lean) | Odd deficient-perfect explicit size bound (`TothPair.radical_size_upper`) and Dutta–Saikia Conjecture 3.2 proof |
| [`OddPerfect/NearPerfectFinite.lean`](OddPerfect/NearPerfectFinite.lean) | Odd near-perfect fixed-rank component bound and finiteness theorem |
| [`Audit.lean`](Audit.lean) | Standalone kernel axiom verifier (`[propext, Classical.choice, Quot.sound]` only) |
| [`paper/main.tex`](paper/main.tex) | Companion `amsart` LaTeX manuscript (*"On the Parity Dichotomy and Fixed-Rank Finiteness of Deficient-Perfect and Near-Perfect Numbers"*) |

## Paper-to-Lean Theorem Mapping (`paper/main.tex`)

| Paper Item | Lean Declaration(s) | Location |
| :--- | :--- | :--- |
| Proposition 2(1)–(4) (Even families & perfect multiples) | `even_pow_two_deficientPerfect`, `even_thabit_deficientPerfect`, `even_mersenne_nearPerfect_families`, `not_deficientPerfect_of_perfect_dvd` | [`ParityFiniteness.lean:32–52`](ParityFiniteness.lean#L32-L52) |
| Theorem 3 (Unrestricted-parity `(k, A)`-finiteness & bounds) | `deficientPerfect_le_of_bounded_rank_two_val`, `nearPerfect_le_of_bounded_rank_two_val`, `finite_deficient_and_nearPerfect_of_bounded_rank_two_val` | [`ParityFiniteness.lean:55–75`](ParityFiniteness.lean#L55-L75) |
| Theorem 4 (Explicit odd bound & Dutta–Saikia Conj. 3.2) | `odd_deficientPerfect_explicit_bound_and_finiteness`, `odd_nearPerfect_finiteness` | [`ParityFiniteness.lean:81–94`](ParityFiniteness.lean#L81-L94) |
| Lemma 5 & Proposition 6 (Weighted prefix product-gap engine) | `exists_small_label_of_weighted_prod_eq`, `labels_bounded_of_weighted_no_balanced_prefix` | [`OddPerfect/ParityDichotomy.lean:94`](OddPerfect/ParityDichotomy.lean#L94), [`OddPerfect/ParityDichotomy.lean:181`](OddPerfect/ParityDichotomy.lean#L181) |

Audited totals (`Audit.lean`): **`28` structural modules (`0` certificate chunks), `158` named theorems, `446` declarations** on `[propext, Classical.choice, Quot.sound]`.

## Building & Auditing Standalone

```sh
lake exe cache get   # if building outside the parent checkout
lake build
lake lean Audit.lean
```
