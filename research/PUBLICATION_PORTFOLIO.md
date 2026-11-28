# Standalone Publication Breakout Portfolio

This index summarizes the **five self-contained Lean `v4.36.0` + Mathlib (`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`) breakout packages** and companion **`\documentclass[11pt]{amsart}` LaTeX manuscripts** extracted from the `odd_perfect_number` formalization.

Every breakout directory compiles from a clean standalone `.lake/build` (`lake --dir <dir> build`) and passes a kernel axiom audit (`lake --dir <dir> lean <dir>/Audit.lean`) verifying via `Lean.Util.CollectAxioms` that **100% of project declarations depend solely on `[propext, Classical.choice, Quot.sound]`** (`0` `sorry`, `0` `admit`, `0` custom `axiom`, `0` `unsafe`, `0` `@[implemented_by]`, `0` `native_decide`).

---

## Summary Table

| Track | Breakout Package | Entry Module(s) | `OddPerfect/` Modules | Audited Theorems | Audited Declarations | Companion Manuscript | Target Venues |
| :---: | :--- | :--- | :---: | ---: | ---: | :--- | :--- |
| **0** | [`toth-breakout/`](../toth-breakout/README.md) | [`TothAnalytic.lean`](../toth-breakout/TothAnalytic.lean), [`TothTheorem.lean`](../toth-breakout/TothTheorem.lean) | `74` (`36` structural + `38` `TothTrillion`; `0` cert in `TothAnalytic`) | `940` | `7,809` | [`toth-breakout/paper/main.tex`](../toth-breakout/paper/main.tex) | *CMST*, *Integers*, *J. Integer Seq.* |
| **1** | [`parity-finiteness-breakout/`](../parity-finiteness-breakout/README.md) | [`ParityFiniteness.lean`](../parity-finiteness-breakout/ParityFiniteness.lean) | `28` (`0` cert chunks) | `158` | `446` | [`parity-finiteness-breakout/paper/main.tex`](../parity-finiteness-breakout/paper/main.tex) | *Bull. Aust. Math. Soc.*, *Integers* |
| **2** | [`prime-power-index-breakout/`](../prime-power-index-breakout/README.md) | [`PrimePowerIndex.lean`](../prime-power-index-breakout/PrimePowerIndex.lean) | `172` (`0` size-tree chunks) | `723` | `6,271` | [`prime-power-index-breakout/paper/main.tex`](../prime-power-index-breakout/paper/main.tex) | *Colloq. Math.*, *Acta Arith.* |
| **3** | [`euler-index-breakout/`](../euler-index-breakout/README.md) | [`EulerIndexBounds.lean`](../euler-index-breakout/EulerIndexBounds.lean) | `156` (`0` size-tree chunks) | `629` | `4,454` | [`euler-index-breakout/paper/main.tex`](../euler-index-breakout/paper/main.tex) | *J. Number Theory*, *Integers* |
| **4** | [`restrained-opn-breakout/`](../restrained-opn-breakout/README.md) | [`RestrainedOPN.lean`](../restrained-opn-breakout/RestrainedOPN.lean) | `108` (`0` size-tree chunks) | `507` | `4,193` | [`restrained-opn-breakout/paper/main.tex`](../restrained-opn-breakout/paper/main.tex) | *Integers*, *Math. Comp.* |

---

## Detailed Overview by Track

### Track 0 — `toth-breakout/`
- **Manuscript Title**: *"An Elementary Reduction of Tóth's Bound for Descartes Numbers, and an Extension to $10^{18}$"* ([`toth-breakout/paper/main.tex`](../toth-breakout/paper/main.tex))
- **Core Contributions**:
  1. Reduces Tóth's (2021) odd Descartes cofactor bound ($m > 10^{12}$ for $mw \ne 198585576189$) via Euler's square-cofactor parity argument to $5 \times 10^5$ odd square roots $k \le 10^6$ (`0.03s` in C) and extends the search by six orders of magnitude to $m > 10^{18}$ ($k \le 10^9$, ~1 minute in exact 128-bit arithmetic).
  2. Establishes a bijection with odd deficient-perfect numbers (`OEIS A271816`), proving that $9{,}018{,}009$ ($d = 819$) is the unique odd deficient-perfect number $\le 10^{18}$ (a $500{,}000\times$ extension over Resta's $2 \cdot 10^{12}$ bound).
  3. Provides a kernel-verified Lean 4 formalization of the $10^{12}$ classification (`TothTheorem.lean`, resolving `FormalConjectures/Wikipedia/DescartesNumber.lean` `descartes_non_example_factor_gt_ten_pow_twelve`) via rational abundancy pruning (`754` split nodes, `535` final-prime intervals), paired with zero-certificate unbounded rank-$r$ finiteness and coprime-split theorems (`TothAnalytic.lean`).

### Track 1 — `parity-finiteness-breakout/`
- **Manuscript Title**: *"On the Parity Dichotomy and Fixed-Rank Finiteness of Deficient-Perfect and Near-Perfect Numbers"* ([`parity-finiteness-breakout/paper/main.tex`](../parity-finiteness-breakout/paper/main.tex))
- **Core Contributions**:
  1. Resolves **Dutta and Saikia's Conjecture 3.2 (2020)** with the explicit closed-form tower bound $n \le (4(k+1))^{4^{k+1}}$ (`odd_deficientPerfect_explicit_bound_and_finiteness`) and answers **Yang and Togbé's §6 question (2023)** across unrestricted parity (with full historical attribution to Adajar's 2016 UP Diliman M.S. thesis / 2019 abstract).
  2. Proves via a generalized weighted prefix product-gap recurrence (`labels_bounded_of_weighted_no_balanced_prefix`) that for every $(k, A) \in \mathbb{N}^2$, both deficient-perfect pairs and near-perfect pairs with $\omega(n) \le k$ and $v_2(n) \le A$ are finite (`finite_deficient_and_nearPerfect_of_bounded_rank_two_val`), sharp against the infinite $k = 1$ even family $(2^a, 1)$ and conditional $k = 2$ Thabit/Mersenne families.

### Track 2 — `prime-power-index-breakout/`
- **Manuscript Title**: *"Unconditional $p$-adic and Goormaghtigh-Repunit Obstructions to Prime-Power Component Indices of Odd Perfect Numbers"* ([`prime-power-index-breakout/paper/main.tex`](../prime-power-index-breakout/paper/main.tex))
- **Core Contributions**:
  1. Proves the global $2$-adic component-index dichotomy ($v_2(i_q) = 0$ vs. $v_2(i_r) = 1$ for $r \ne q$), eliminating all non-Euler prime-power component indices $i_r = p^j$ ($r \ne q$) and all Fermat-prime bases $p = 2^k + 1$ (`prime_power_index_euler_only_and_nonfermat`).
  2. Introduces the mod-$p$ harmonic congruence $\sum_{r \in S_1} \frac{4 e_r (r - 1)}{2 e_r + 1} \equiv 1 \pmod p$, the universal mod-$p^4$ congruence $128(s - 1) \equiv 32p + 28p^2 + 25p^3 \pmod{p^4}$, and exact $\mathbb{Z}_p$ Hensel distance $\|s - \sigma_p\|_p = p^{-(2u + 1)}$ (`even_prime_power_primorial_padic_and_gauss_reciprocity`).
  3. Unconditionally eliminates the pure Nagell–Ljunggren branch ($S_1 = \emptyset$) and all $|S_1| \le 12$ without assuming Nagell–Ljunggren or Goormaghtigh, forcing $13$ simultaneous prime-length repunit representations of $p$, $\min S_1 \in \{3, 5, 7, 11, 13\}$, $\left(\frac{(-1)^{\lfloor \ell_m / 2 \rfloor}\ell_m}{p}\right) = +1$, $2u \ge 13{,}082{,}761{,}331{,}670{,}028$, and $N > 10^{353{,}234{,}555{,}955{,}090{,}756}$ (`even_prime_power_tridecuple_repunit_and_size_bounds`).

### Track 3 — `euler-index-breakout/`
- **Manuscript Title**: *"Lower Bounds, Non-Fermat Support, and $\mathbb{Z}[\sqrt{2}]$ Descent for the Euler Index of an Odd Perfect Number"* ([`euler-index-breakout/paper/main.tex`](../euler-index-breakout/paper/main.tex))
- **Core Contributions**:
  1. Sharpens Broughan, Delbourgo, and Zhou's (2013) general Euler index lower bound $I = \sigma(m^2)/q^a \ge 315$ by $7.5\times$ to **$I \ge 2{,}379$** (`euler_index_ge_2379`).
  2. Proves every odd component index has at least one non-Fermat prime divisor (`odd_component_index_has_nonfermat_prime`), and for $a > 1$ admits an odd-valuation prime $p \nmid (q - 1)$ (`euler_index_odd_valuation_escape`).
  3. On Hirakawa's (2024) prime-times-square branch $I = \ell t^2$ ($a > 1$), proves $N > 10^{740}$ unconditionally across all $a > 1$, fundamental Pell minimality in $\mathbb{Z}[\sqrt{2q}]$, exclusion of $148$ prime-modulus Fermat residue classes (forcing $d \ge 241, a \ge 481$ when $3, 5 \nmid N$), `EuclideanDomain (ℤ√2)`, unit group $\pm(1 + \sqrt{2})^{\mathbb{Z}}$, and reduced $d$-th power Frobenius descent $1 + y\sqrt{2} = (1 + \sqrt{2})^k \alpha^d$ ($1 \le |k| \le \frac{d-1}{2}$) with $\alpha \equiv (1 + \sqrt{2})^{-k} \pmod{d\mathbb{Z}[\sqrt{2}]}$ (`hirakawa_zsqrtTwo_frobenius_descent`).

### Track 4 — `restrained-opn-breakout/`
- **Manuscript Title**: *"An Elementary Exclusion of Three-Free Restrained Odd Perfect Numbers and Extensions to Two Large Exponents"* ([`restrained-opn-breakout/paper/main.tex`](../restrained-opn-breakout/paper/main.tex))
- **Core Contributions**:
  1. Gives a short, computation-free proof that every odd perfect number with $3 \nmid N$ satisfies $|L(N)| \ge 2$ (`three_free_restrained_excluded`) via the 3-element pigeonhole growth inequality $5 u_0 + 3 \le 2 u_2$ on $\{q, r_0\}$-smooth values of $u^2 + u + 1$ (`smooth_quadratic_three_step_growth`) and the telescoping subsequence bound $\prod (x^2 + x + 1)/x^2 \le (2 y_0 + 5)/(2 y_0)$.
  2. Extends the smooth-quadratic growth engine to $|L(N)| = 2$ ($3 \nmid N$), forcing both primes in $L(N)$ to be $\equiv 1 \pmod 3$, and proving $|L(N)| \ge 7$ whenever $L_1(N) = \emptyset$ (`three_free_two_large_sources_congruence`).
  3. Establishes $v_3(N) \ge 8$ when $L^\circ(N) = \emptyset$, $81 \mid N$ whenever $|L^\circ(N)| \le 1$ and $q \equiv 2 \pmod 3$, and $1 \le |S_1(N)| \le 2$ when $|L^\circ(N)| \le 1$ and $v_3(N) = 2$ (`restrained_three_divisibility_and_exponent_profile`).

---

## Reproducing Standalone Builds & Kernel Axiom Audits

Each directory can be built and audited independently from the repository root (or copied into its own standalone repository and initialized with `lake exe cache get`):

```sh
for pkg in toth-breakout parity-finiteness-breakout prime-power-index-breakout euler-index-breakout restrained-opn-breakout; do
  lake --dir "$pkg" build
  lake --dir "$pkg" lean "$pkg/Audit.lean"
done
```

Breakout dependency closures were extracted with [`research/tools/export_breakout.py`](tools/export_breakout.py) and de-bloated of umbrella synthesis imports inside each breakout copy so that analytical tracks contain zero unrelated size-tree certificate files.
