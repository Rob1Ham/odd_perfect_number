# Standalone Publication Breakouts & LaTeX Manuscripts — Long-Running Goal Specification

## Objective

Produce **standalone, self-contained Lean `v4.36.0` + Mathlib (`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`) breakout folders**, each paired with a **referee-audited `amsart` LaTeX manuscript (`paper/main.tex`)**, for all five publishable results established in this repository:

| Track | Breakout Directory | Core Mathematical Result | Target Venue Style |
| :--- | :--- | :--- | :--- |
| **0** | `toth-breakout/` *(add `paper/main.tex`)* | Parity reduction & $10^{18}$ extension of Tóth's (2021) Descartes cofactor bound + OEIS A271816 odd deficient-perfect bound + Lean $10^{12}$ & rank-$k$ finiteness proofs | *Integers* / *CMST* / *J. Integer Seq.* |
| **1** | `parity-finiteness-breakout/` | Unrestricted-parity $(k, v_2)$-finiteness dichotomy for deficient-perfect & near-perfect numbers (resolving Dutta–Saikia 2020 Conjecture 3.2 & Yang–Togbé 2023 §6) | *Integers* / *Bull. Aust. Math. Soc.* |
| **2** | `prime-power-index-breakout/` | Unconditional $\mathbb{Z}/p^4\mathbb{Z}$, $\mathbb{Z}_p$ Hensel, & 13-repunit Goormaghtigh obstructions to prime-power component indices $i_r = p^j$ (eliminating pure Nagell–Ljunggren $|S_1|=0$ and $|S_1|\le 12$) | *Colloq. Math.* / *Acta Arith.* |
| **3** | `euler-index-breakout/` | Euler component index $\sigma(m^2)/q^a \ge 2{,}379$ ($7.5\times$ over Broughan–Delbourgo–Zhou's $315$), non-Fermat index support, & Hirakawa $I = \ell t^2$ modular / $\mathbb{Z}[\sqrt{2}]$ Frobenius obstructions | *Integers* / *J. Number Theory* |
| **4** | `restrained-opn-breakout/` | Purely analytical exclusion of three-free restrained odd perfect numbers ($3 \nmid N \implies |\text{largeSources}| \ge 2$), two-large-sources congruence forcing, & $81 \mid N$ for $q \equiv 2 \pmod 3$ | *Integers* / *Math. Comp.* |

---

## Non-Negotiable Quality & Integrity Gates

1. **Untouched Root Pins & Parallel-Worker Safety**:
   - Never modify root `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, or any file inside root `OddPerfect/` that is being edited by another worker. Each breakout lives strictly in its own `<name>-breakout/` folder at the repository root.
2. **De-Bloated Standalone Dependency Closure**:
   - Use `python3 research/tools/export_breakout.py` to inspect and export transitive closures.
   - **No accidental certificate bloat**: Several Wave 6–12 modules in root `OddPerfect/` import umbrella synthesis files (`GlobalWave*Obstruction`, `SizeBound300`, `DeficientFourClassification`) that pull in 400+ unrelated `SizeIndex300` / `DeficientReplay` chunks even when only 1–2 elementary structural lemmas are used. Inside each `<name>-breakout/OddPerfect/` copy, trim umbrella imports to the exact structural leaf modules needed so purely analytical tracks import **zero** unrelated certificate chunks.
3. **Standalone Kernel Build & Axiom Audit**:
   - Every `<name>-breakout/` folder must contain:
     - `.gitignore` (`/.lake/`, `**/__pycache__/`, LaTeX build intermediates `*.aux`, `*.log`, `*.out`, `*.synctex.gz`)
     - `lean-toolchain`, `lake-manifest.json`, `lakefile.toml`
     - Clean top-level public entry module(s) exposing self-contained, Mathlib-readable theorem statements
     - `Audit.lean` verifying via `Lean.Util.CollectAxioms` (`collectAxioms`) that every project constant uses **only** `[propext, Classical.choice, Quot.sound]` (`0` `sorry`, `0` `admit`, `0` custom `axiom`, `0` `native_decide` / `Lean.ofReduceBool` / `Lean.trustCompiler`)
     - `README.md` mapping every theorem in the paper to exact Lean declarations and file/line locations
   - Verify each breakout from a clean `.lake/build` (linking only `.lake/packages -> ../../.lake/packages`, **never** parent `.lake/build`) via:
     ```sh
     lake --dir <name>-breakout build
     lake --dir <name>-breakout lean <name>-breakout/Audit.lean
     ```
4. **Referee-Grade `amsart` LaTeX Manuscripts (`<name>-breakout/paper/main.tex`)**:
   - Every breakout must include a complete, self-contained `\documentclass[11pt]{amsart}` manuscript in `<name>-breakout/paper/main.tex` with:
     - Accurate mathematical proofs matching the Lean formalization step-for-step (every numerical constant, inequality, and edge case checked in Python/Lean — **never** hand-wave bounds like $\sigma(k^2) < 3k^2$ without checking!)
     - Honest, complete scholarly attribution (explicitly distinguishing what was proved previously in the literature/theses/OEIS vs. what is newly proved here, and accurately stating what is kernel-certified in Lean vs. any external C/Python computation)
     - Clean LaTeX hygiene (`\lstset{showstringspaces=false, ...}` if any code listing is included, balanced braces/environments, exact MSC 2020 codes, complete bibliography)
     - Adversarial review pass (`neon-auditor` or independent verification script) checking every numbered Lemma, Theorem, Corollary, Remark, and code listing in `paper/main.tex`.

---

## Detailed Track Specifications

### Track 0 — `toth-breakout/paper/main.tex` (Tóth Bound Reduction & $10^{18}$ Extension)
`toth-breakout/` is already built and axiom-audited (`TothAnalytic.lean`, `TothTheorem.lean`, `Audit.lean`). Add `toth-breakout/paper/main.tex` incorporating all 10 referee fixes:
1. **Remark 8 fix**: Odd $k \le 10^9$ has at most **8** distinct prime factors ($3\cdot 5\cdots 23 = 111{,}546{,}435$, whereas $\times 29 > 3.23 \times 10^9$), giving $\sigma(k^2)/k^2 < 676{,}039/221{,}184 < 3.06$ (noting explicit counterexample $k = 334{,}639{,}305$ to $< 3k^2$), and explain why `(u64)` casts in `printf` are safe because `s < 2n <= 2 * 10^18 < 2^64`.
2. **Corollary 6 & $w > 1$ fixes**: Prove $w = \sigma(k^2)/d_k$ is odd in the converse via Lemma 4 ($\sigma(k^2)$ odd), and prove $w > 1 \iff k > 1$ explicitly ($\sigma(k^2) \ge 1 + k + k^2 > k^2 \implies d_k < \sigma(k^2)$).
3. **Remark 7 & OEIS A271816 corollary**: Prove $d \mid n$ from $2n = d(x+1) = 2dy$ ($x = 2y-1$ odd, $d < n \iff x > 1$), state the explicit corollary that **$9{,}018{,}009$ is the unique odd deficient-perfect number $\le 10^{18}$** (improving Resta's $2 \cdot 10^{12}$ bound on OEIS A271816 by $500{,}000\times$), and cite Tang–Feng (2014), Yang–Togbé (2023), OEIS A222263, and OEIS A271816.
4. **Definition 1 & fair framing of Tóth (2021)**: Note that Banks et al. (2008) and Tóth (2021) omit $\gcd(m, w) = 1$ whereas Formal Conjectures includes it (and Theorem 3 covers both); note right in the Abstract and Section 1 that Tóth's 8-month run tabulated **all** of $\mathcal{S} \cap [1, 10^{12}]$ across both even and odd multipliers $x$.
5. **Section 4 & Appendix A fixes**: State accurately that `toth-breakout` (both `TothTheorem.lean` for $10^{12}$ and `TothAnalytic.lean` for unbounded rank-$k$ finiteness and coprime splits) has been compiled and kernel-audited (`940` theorems, `7,809` declarations); set `showstringspaces=false`, add `argc` / `calloc` / `M <= 3000000000ULL` guards in Appendix A, and verify the C program output on small bounds.

---

### Track 1 — `parity-finiteness-breakout/` (Unrestricted-Parity Finiteness Dichotomy)
- **Root modules**: `OddPerfect.ParityDichotomy`, `OddPerfect.DeficientFiniteness`, `OddPerfect.NearPerfectFinite`, `OddPerfect.Dickson`.
- **Entry module**: `ParityFiniteness.lean` exposing:
  1. Infinite / conditional even families: `pow_two_deficientPerfect` ($2^a$), `thabit_deficientPerfect` ($2^a(3\cdot 2^a - 1)$), `mersenne_nearPerfect_two_pow_mul`, `mersenne_nearPerfect_mul_sq`, `not_deficientPerfectWith_of_perfect_dvd`.
  2. Odd fixed-rank finiteness & explicit $(4(k+1))^{4^{k+1}}$ ceiling (`finite_odd_deficientPerfect_of_prime_count`, `finite_odd_nearPerfect_of_prime_count`).
  3. Weighted prefix product-gap theorem (`labels_bounded_of_weighted_no_balanced_prefix`) and unrestricted-parity $(k, A)$-finiteness (`finite_deficientPerfect_pairs_of_bounded_prime_count_two_val`, `finite_nearPerfect_pairs_of_bounded_prime_count_two_val`).
- **Paper (`paper/main.tex`)**: *"On the Parity Dichotomy and Fixed-Rank Finiteness of Deficient-Perfect and Near-Perfect Numbers"* — resolves Dutta–Saikia (2020) Conjecture 3.2 and answers Yang–Togbé (2023) §6 across all parities, with full historical credit to Adajar (2016 UP Diliman thesis / 2019 ZetaValue abstract), Gumaru–Casuco–Bernal (2018), Dittmer (2014), and BYU (2020).

---

### Track 2 — `prime-power-index-breakout/` (Unconditional $p$-adic & Repunit Obstructions to $i_r = p^j$)
- **Root modules**: `OddPerfect.PrimePowerObstruction`, `OddPerfect.PrimePowerHigherObstruction`, `OddPerfect.EvenIndexSubexponential`, `OddPerfect.ComponentIndexMatrix`, `OddPerfect.TridecupleRepunitObstruction`, `OddPerfect.EvenIndexPrimorialObstruction`, `OddPerfect.PadicEvenIndexObstruction`, `OddPerfect.GaussSumCyclotomicForms` *(decoupled from umbrella `GlobalWave*` / `SizeBound300` imports inside the breakout copy!)*.
- **Entry module**: `PrimePowerIndex.lean` exposing:
  1. Non-Euler exclusion (`v_2(i_r) = 1` for $r \ne q$, confining $i_r = p^j$ to $r = q$) and Fermat-prime exclusion.
  2. Coupled identity $2(s-1)(s+1) = p\,\sigma(p^{2u-1})$, mod-$p^2$ harmonic congruence $\sum_{r \in S_1} \frac{4 e_r (r-1)}{2 e_r + 1} \equiv 1 \pmod p$, universal fourth-order congruence $128(s-1) \equiv 32p + 28p^2 + 25p^3 \pmod{p^4}$, and $\mathbb{Z}_p$ Hensel root distance $\|s - \sigma_p\|_p = p^{-(2u+1)}$.
  3. Unconditional elimination of $|S_1| = 0$ (pure Nagell–Ljunggren branch) and $|S_1| \le 12$ (`HasThirteenOddPrimeRepunits p`, $16 \le \omega(N)$, $\min S_1 \in \{3, 5, 7, 11, 13\}$, Gauss-sum cyclotomic quadratic reciprocity, $p \le 8(u+1)128^{\sqrt{2u}}$, $36{,}207 \le j$, and $13{,}082{,}761{,}331{,}670{,}028 \le j$, $10^{353{,}234{,}555{,}955{,}090{,}756} < N$ for even $j$).
- **Paper (`paper/main.tex`)**: *"Unconditional $p$-adic and Goormaghtigh-Repunit Obstructions to Prime-Power Component Indices of Odd Perfect Numbers"*.

---

### Track 3 — `euler-index-breakout/` (Euler Component Index $\ge 2{,}379$, Non-Fermat Support, & Hirakawa Descent)
- **Root modules**: `OddPerfect.IndexBound2379`, `OddPerfect.FermatIndexObstruction`, `OddPerfect.ExceptionalFermatReduction`, `OddPerfect.HirakawaClosure`, `OddPerfect.ExceptionalFermatCongruences`, `OddPerfect.ExceptionalFermatHigherSieve`, `OddPerfect.ZsqrtTwoFermatDescent` *(decoupled inside the breakout copy from `SizeIndex300` / `DeficientFourClassification` umbrella imports; state any size-dependent corollary cleanly or via self-contained structural bounds)*.
- **Entry module**: `EulerIndexBounds.lean` exposing:
  1. `euler_component_index_ge_2379` ($\sigma(m^2)/q^a \ge 2{,}379$ and $2{,}379 q^a < 2 m^2$).
  2. Non-Fermat prime divisor of every Euler index across all $a \ge 1$, plus odd-valuation prime $p \nmid q - 1$ for $a > 1$.
  3. On $I = \ell t^2$ ($a > 1$): Hirakawa fundamental Pell profile, 148 excluded prime-modulus Fermat residue classes (including $q \not\equiv 2, 4 \pmod 7$ and $q \not\equiv 3 \pmod 5$, forcing $d \ge 241, a \ge 481$ when $3, 5 \nmid N$), `EuclideanDomain (ℤ√2)`, unit classification via $1 + \sqrt{2}$, reduced $d$-th power descent $\langle 1, y \rangle = (1 + \sqrt{2})^k \alpha^d$ with $k \ne 0$, and mod-$d$ Frobenius congruence.
- **Paper (`paper/main.tex`)**: *"Lower Bounds, Non-Fermat Support, and $\mathbb{Z}[\sqrt{2}]$ Descent for the Euler Index of an Odd Perfect Number"*.

---

### Track 4 — `restrained-opn-breakout/` (Analytical Exclusion of Three-Free Restrained Candidates)
- **Root modules**: `OddPerfect.RestrainedExponents`, `OddPerfect.RestrainedThreeFreeObstruction`, `OddPerfect.RestrainedLinearElimination`, `OddPerfect.RestrainedCyclotomicObstruction`, `OddPerfect.RestrainedCommonDivisorObstruction`, `OddPerfect.ThreeFreeRestrainedClosure`, `OddPerfect.ThreeFreeTwoLargeSources`, `OddPerfect.RestrainedThreeSquareObstruction`, `OddPerfect.RestrainedSquareSourcesOneObstruction` *(decoupled inside the breakout copy from umbrella `GlobalWave*` / `SizeBound300` imports so zero certificate chunks are imported!)*.
- **Entry module**: `RestrainedOPN.lean` exposing:
  1. Purely analytical 3-element pigeonhole growth inequality $5 u_0 + 3 \le 2 u_2$ on $\{q, r_0\}$-smooth quadratic sums and unconditional `two_le_largeSources_of_three_free` ($3 \nmid N \implies 2 \le |\text{largeSources } N\; q|$).
  2. Two-large-sources extension (`two_le_oneModThreeLarge_or_three_le_largeSources_of_three_free` and `oneModThreeLarge_nonempty_or_seven_le_largeSources_of_three_free`).
  3. Restrained $3 \mid N$ exponent obstructions: $8 \le v_3(N)$ when `largeSources = ∅`, $81 \mid N$ ($4 \le v_3(N)$) whenever $|\text{largeSources}| \le 1$ and $q \equiv 2 \pmod 3$, and $1 \le |\text{squareSourcesOne } N| \le 2$ at $v_3(N) = 2$.
- **Paper (`paper/main.tex`)**: *"An Elementary Exclusion of Three-Free Restrained Odd Perfect Numbers and Extensions to Two Large Exponents"*.

---

## Master Completion Checklist

The goal is complete **only when all items below are verified**:
- [x] **Track 0**: `toth-breakout/paper/main.tex` written and audited against all 10 referee items; `toth-breakout` `Audit.lean` passes (`940` theorems, `7,809` declarations).
- [x] **Track 1**: `parity-finiteness-breakout/` exported (zero certificate bloat, `28` modules), standalone `lake build` + `lake lean Audit.lean` pass (`158` theorems, `446` declarations on `[propext, Classical.choice, Quot.sound]`), `README.md` + `paper/main.tex` completed and audited.
- [x] **Track 2**: `prime-power-index-breakout/` exported & de-bloated (`172` modules, zero size-tree chunks), standalone `lake build` + `lake lean Audit.lean` pass (`723` theorems, `6,271` declarations), `README.md` + `paper/main.tex` completed and audited.
- [x] **Track 3**: `euler-index-breakout/` exported & de-bloated (`156` modules, zero size-tree chunks), standalone `lake build` + `lake lean Audit.lean` pass (`629` theorems, `4,454` declarations), `README.md` + `paper/main.tex` completed and audited.
- [x] **Track 4**: `restrained-opn-breakout/` exported & de-bloated (`108` modules, zero size-tree chunks), standalone `lake build` + `lake lean Audit.lean` pass (`507` theorems, `4,193` declarations), `README.md` + `paper/main.tex` completed and audited.
- [x] **Summary Index**: `research/PUBLICATION_PORTFOLIO.md` summarizing all 5 breakout folders, exact theorem counts, declaration counts, target journals, and LaTeX manuscript paths.
