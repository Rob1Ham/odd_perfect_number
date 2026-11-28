# Tóth's Theorem & General Analytical Proof — Standalone Breakout

This directory is a self-contained Lean `v4.36.0` + Mathlib (`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`) Lake package extracted from the parent repository, isolating **only** Tóth's theorem (L. Tóth, *"On the Density of Spoof Odd Perfect Numbers"*, *CMST* 27, 2021, Theorem 1) and the **general analytical proofs** for unbounded Tóth pairs $\sigma(n)(x+1) = 2nx$ and deficient-perfect cofactors $\sigma(n) + d = 2n$.

Every theorem compiles with `0` `sorry`, `0` custom axioms, and depends solely on Lean's standard foundations (`propext`, `Classical.choice`, `Quot.sound`).

---

## Entry Points

| Entry Module | Scope | Certificate Chunks Imported |
| :--- | :--- | :--- |
| [`TothAnalytic.lean`](TothAnalytic.lean) | **Pure General Analytical Proof** (unbounded $n$ and $x$, rational abundancy/multiplier cuts, explicit rank-$k$ size bounds & finiteness, coprime Tóth splits, linear-Euler $N = qm^2$ source isolation) | **0** (`35` small structural modules only) |
| [`TothTheorem.lean`](TothTheorem.lean) | **Tóth (2021), Theorem 1** ($n \le 10^{12} \implies (n,x) = (9018009, 22021)$, hence $m > 10^{12}$ for every other odd Descartes factorization $mw$) | `38` leaf modules (`OddPerfect/TothTrillion/Part01.lean`–`Part38.lean`) |
| [`Audit.lean`](Audit.lean) | **Kernel Axiom Audit** across both entry points and all transitive local declarations | Verifies `[propext, Classical.choice, Quot.sound]` |
| [`paper/main.tex`](paper/main.tex) | **Companion `amsart` LaTeX Manuscript** (*"An Elementary Reduction of Tóth's Bound for Descartes Numbers, and an Extension to $10^{18}$"*) | — |

---

## 1. General Analytical Proof (`TothAnalytic.lean`)

All analytical arguments operate without the $n \le 10^{12}$ hypothesis and without importing `OddPerfect/TothTrillion/Part*.lean`:

1. **Square-Cofactor & Deficient-Divisor Bijection** ([`OddPerfect/TothCandidates.lean`](OddPerfect/TothCandidates.lean), [`OddPerfect/DeficientPerfect.lean`](OddPerfect/DeficientPerfect.lean)):
   - `TothBreakout.Analytic.odd_toth_square_and_deficient_iff`: For odd $n$, $\sigma(n)(x+1) = 2nx$ with odd $x > 1$ forces $n = m^2$ and $x \equiv 1 \pmod 4$, and bijects via $d = 2n - \sigma(n) = \sigma(n)/x$ and $x = 2(n/d) - 1$ with proper deficient divisors $\sigma(n) + d = 2n$.
   - `OddPerfect.tothPair_of_linear_euler` & `OddPerfect.toth_coprime_perfect_iff_prime`: Every Euler-exponent-one odd perfect candidate $N = q m^2$ produces a coprime Tóth pair $(m^2, q)$; conversely, for coprime $(n, x)$ with $x > 1$, $nx$ is genuinely perfect iff $x$ is prime.

2. **Rational Abundancy Ceiling & Unbounded-Multiplier Monotonicity Cut** ([`OddPerfect/TothAbundancy.lean`](OddPerfect/TothAbundancy.lean), [`OddPerfect/TothSplit.lean`](OddPerfect/TothSplit.lean)):
   - `TothBreakout.Analytic.suffix_abundancy_strict_ceiling` (`Toth.suffix_strict_limit`): When every prime divisor of $m > 1$ is $\ge a$ and $m < a^{k+1}$, $\omega(m) \le k$ and
     $$\frac{\sigma(m^2)}{m^2} < \left(\frac{a}{a - 1}\right)^k.$$
   - `OddPerfect.Toth.nextMultiplier_le`: Prefix deficiency $S = \sigma(D^2) < 2D^2$ bounds the a priori unbounded multiplier $x \equiv 1 \pmod 4$ from below by $t = \text{nextMultiplier}(D, S)$.
   - `TothBreakout.Analytic.analytic_interval_cut` (`Toth.closed_interval`): Combines $\frac{S}{2D^2}\left(\frac{a}{a-1}\right)^k \le \frac{t}{t+1}$ with monotonicity $\frac{t}{t+1} \le \frac{x}{x+1}$ ($t \le x$) against $\frac{S \cdot \sigma(m^2)/m^2}{2D^2} = \frac{x}{x+1}$ to eliminate entire infinite $(m, x)$ regimes in $\mathbb{Q}$.

3. **Unbounded Rank-$k$ Analytical Size Bound & Finiteness** ([`OddPerfect/DeficientFiniteness.lean`](OddPerfect/DeficientFiniteness.lean), [`OddPerfect/SpoofFiniteness.lean`](OddPerfect/SpoofFiniteness.lean), [`OddPerfect/ParityDichotomy.lean`](OddPerfect/ParityDichotomy.lean)):
   - `TothBreakout.Analytic.unbounded_toth_radical_size_upper` (`TothPair.radical_size_upper`): Adjoining the formal linear slot $(x, 1)$ to the prime-power components of $n$ and applying the prefix product-gap bound proves, for **all** odd $n$, odd $x > 1$, and $\omega(n) \le k$:
     $$4(k + 1)\, x^3 \left(\prod_{p \mid n} p\right)^2 n \;\le\; \bigl(4(k + 1)\bigr)^{4^{\omega(n) + 1}}.$$
   - `TothBreakout.Analytic.finite_odd_toth_pairs_of_bounded_prime_count`: Explicitly bounds both $n$ and $x$ by $(4(k+1))^{4^{k+1}}$, proving finiteness of nontrivial odd Tóth pairs (and odd deficient-perfect numbers, resolving Dutta–Saikia Conjecture 3.2 / Adajar's theorem) for every $k$.
   - `TothBreakout.Analytic.finite_deficientPerfect_of_bounded_rank_and_two_val`: Extends finiteness to arbitrary parity whenever $\omega(n) \le k$ and $v_2(n) \le A$ (sharp against the infinite even family $n = 2^a$ in `OddPerfect.pow_two_deficientPerfect`).

4. **Coprime Tóth-Split Factor Extraction & Linear-Euler Source Isolation** ([`OddPerfect/TothPrimeObstruction.lean`](OddPerfect/TothPrimeObstruction.lean), [`OddPerfect/TothSplitExistence.lean`](OddPerfect/TothSplitExistence.lean)):
   - `TothBreakout.Analytic.proper_factor_and_unsplit_characterization`: Any coprime factorization $n = ab$ where neither $\sigma(a)$ nor $\sigma(b)$ divides $\sigma(n)/x$ yields a nontrivial proper divisor $1 < \gcd(x, \sigma(a)) < x$ of $x$ (witnessed on Descartes's pair $(9018009, 22021)$ by `49 * 184041`, extracting $\gcd(22021, \sigma(49)) = 19$). Moreover, $(n, x)$ admits no non-absorbing split iff a **unique** prime-power component of $n$ absorbs $x$.
   - `TothBreakout.Analytic.linear_euler_toth_unique_source`: Specializing to an odd perfect candidate $N = q m^2$ ($q$ prime) forces $q \parallel \sigma(m^2)$ from a unique prime $r_0 \mid m$ with $q \parallel \sigma(r_0^{2 v_{r_0}(m)})$, $\sigma(\text{ordCompl}[r_0](m^2)) \mid \sigma(m^2)/q$, and $2q < 3 r_0^{2 v_{r_0}(m)}$.

---

## 2. Tóth's Bounded Uniqueness Theorem (`TothTheorem.lean`)

Combining the analytical engine in `TothAnalytic.lean` with the verified root-tree cover through $m \le 10^6$ (`OddPerfect/TothTrillion.lean` + `OddPerfect/TothTrillion/Part01.lean`–`Part38.lean`, reproducible via [`toth_generator.py`](toth_generator.py)):

- `TothBreakout.Theorem.toth_unique_odd_pair_below_trillion`:
  $$n \le 10^{12},\; \text{Odd } x,\; 1 < x \implies \bigl(\text{TothPair } n\; x \iff n = 9018009 \wedge x = 22021\bigr).$$
- `TothBreakout.Theorem.descartes_non_example_factor_gt_ten_pow_twelve`:
  Stated purely with Mathlib's `Nat.Prime`, `Odd`, `Nat.Coprime`, and `ArithmeticFunction.sigma`, every odd Descartes factorization $m \cdot w \ne 198585576189$ satisfies $10^{12} < m$.
- `TothBreakout.Theorem.deficientPerfect_below_trillion_iff`:
  Among odd $n \le 10^{12}$, $\text{DeficientPerfectWith } n\; d \iff (n, d) = (9018009, 819)$.

---

## 3. Paper-to-Lean Theorem Mapping (`paper/main.tex`)

| Paper Item | Lean Declaration(s) | Location |
| :--- | :--- | :--- |
| Theorem 3 ($m \le 10^{12}$ certified; $10^{18}$ via C) | `descartes_non_example_factor_gt_ten_pow_twelve`, `toth_unique_odd_pair_below_trillion` | [`TothTheorem.lean:48`](TothTheorem.lean#L48), [`TothTheorem.lean:33`](TothTheorem.lean#L33) |
| Corollary 4 (OEIS A271816 $n \le 10^{12}$ certified) | `deficientPerfect_below_trillion_iff` | [`TothTheorem.lean:58`](TothTheorem.lean#L58) |
| Lemma 5 ($\sigma(n)$ odd $\iff n$ square) | `odd_sigma_iff_square_of_odd` | [`OddPerfect/NearPerfect.lean:69`](OddPerfect/NearPerfect.lean#L69) |
| Lemma 6 & Proposition 7 (Parity reduction & bijection) | `odd_toth_square_and_deficient_iff`, `toth_odd_cofactor_square`, `odd_deficientPerfect_iff_toth` | [`TothAnalytic.lean:56`](TothAnalytic.lean#L56), [`OddPerfect/TothCandidates.lean:51`](OddPerfect/TothCandidates.lean#L51), [`OddPerfect/DeficientPerfect.lean:40`](OddPerfect/DeficientPerfect.lean#L40) |
| Section 4(1) (Rational abundancy & interval cut) | `suffix_abundancy_strict_ceiling`, `analytic_interval_cut` | [`TothAnalytic.lean:63`](TothAnalytic.lean#L63), [`TothAnalytic.lean:70`](TothAnalytic.lean#L70) |
| Section 4(2) (Unbounded rank-$r$ bound & finiteness) | `unbounded_toth_radical_size_upper`, `finite_odd_toth_pairs_of_bounded_prime_count`, `proper_factor_and_unsplit_characterization`, `linear_euler_toth_unique_source` | [`TothAnalytic.lean:79`](TothAnalytic.lean#L79), [`TothAnalytic.lean:87`](TothAnalytic.lean#L87), [`TothAnalytic.lean:122`](TothAnalytic.lean#L122), [`TothAnalytic.lean:135`](TothAnalytic.lean#L135) |

Audited totals (`Audit.lean`): **`74` `OddPerfect/*` modules (`36` structural + `38` `TothTrillion` chunks), `940` named theorems, `7,809` declarations** on `[propext, Classical.choice, Quot.sound]`.

---

## Building & Auditing Standalone

From inside `toth-breakout/`:

```sh
# Fetch prebuilt Mathlib cache (if building outside the parent checkout)
lake exe cache get

# 1. Build ONLY the pure general analytical proof (zero certificate parts):
lake build TothAnalytic

# 2. Build the full Tóth 10^12 theorem + run the kernel axiom audit:
lake build
lake lean Audit.lean
```
