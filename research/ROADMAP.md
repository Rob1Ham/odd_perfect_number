# Odd Perfect Number — Unconditional Resolution Roadmap

**Target Proposition**: Resolve `OddPerfect.existsOddPerfect` (`∃ n : ℕ, Odd n ∧ Nat.Perfect n`) in `OddPerfect/Question.lean` — constructively equivalent via `OddPerfect.not_existsOddPerfect_iff_forall_perfect_even` to upstream `formal-conjectures` `FormalConjectures/Wikipedia/PerfectNumbers.lean:83` (`PerfectNumbers.odd_perfect_number_conjecture : ∀ n : ℕ, Nat.Perfect n → Even n`) — via a complete, kernel-checked Lean `v4.36.0` proof (`¬ OddPerfect.existsOddPerfect`, or an explicit verified witness) using **only** `propext`, `Classical.choice`, and `Quot.sound`.

**Core Premise**: A complete, unconditional mathematical solution exists and is formalizable on the pinned Lean `v4.36.0` + Mathlib (`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`) checkout with zero custom axioms. Every decision in the Carbon–Neon pipeline is evaluated by whether it builds toward **global candidate-set collapse ($\mathcal{O} = \emptyset$)** rather than open-ended brute-force tree expansion.

---

## Pipeline Principles (Re-Architected)

1. **Structural Collapse Over Brute-Force Bloat**:
   Finite factor-chain trees (`PartNNN.lean`) only eliminate bounded prefixes unless paired with an upper cap on $\omega(N)$ or component index $i_p$. Freeze new large certificate-tree generation unless discharging a finite residual box created by a structural theorem.
2. **Stepping-Stone Progression**:
   Lock in solved unintegrated theorems first (Tier 0), prove tractable open stepping-stone theorems that sharpen our global algebraic/analytic engines next (Tier 1), and converge on the global unconditional obstruction (Tier 2).
3. **Fast-Fail Counterexample Gate**:
   Every proposed global obstruction lemma must be tested immediately against the **Counterexample Filter Bank** in [WHITEBOARD.md](WHITEBOARD.md) (Descartes spoof `198585576189`, Tóth cofactor `9018009`, Johnson near-perfect `173369889`, and local reciprocity cycles) to verify which exact non-spoofable invariant (`I1`–`I4`) it exploits.
4. **Foundational Purity**:
   Zero `sorry`, `admit`, custom `axiom`, `unsafe`, or `@[implemented_by]`. Nothing enters `OddPerfect.lean` without passing `neon-auditor` and `lake build && lake lean research/Audit.lean`.

---

## Tier 0 — Harvest Solved & Nearly-Solved Staged Theorems (Immediate Lock-In)

Before launching open-ended proof searches, harvest high-leverage theorems already sitting in `OddPerfect/` so Carbon and Neon workers can import them directly.

| Priority | Track / Module | Status | Mathematical Payoff | Action |
| :--- | :--- | :--- | :--- | :--- |
| **0.1** | `OddPerfect.NearPerfectFinite` (`NearPerfectFinite`, `NearPerfectPrefix`, `NearAbundant255`) | **`AUDITED`** (`100%`) | **Resolves open-in-journals finiteness**: proves `Set.Finite {n \| Odd n ∧ ω(n) ≤ k ∧ ∃ d, NearPerfectWith n d}` with explicit `productLabelBound`. | Integrated & verified via `Audit.lean`. |
| **0.2** | `OddPerfect.IndexBound2379` (`11` modules) | **`AUDITED`** (`100%`) | Sharpens unconditional Euler component index from $343 \to 2379$ ($2379 q^a < 2m^2$, exceeding published $315$). | Integrated & verified via `Audit.lean`. |
| **0.3** | Analytic & Ranked-Prime Bridge (`PrimeReciprocalLog`, `ZelinskyReciprocal`, `SecondLargestPrime`, `QuasiperfectSupport`) | **`AUDITED`** (`100%`) | Unlocks `Mathlib.Analysis.SpecialFunctions.Log` bounds ($\sum \frac{1}{p-1} > \log 2$, Zelinsky $\sum \frac{1}{r} < \log 2 - \frac{11}{50p^2}$ for $p_{\min} \ge 11$), $b^5 < 2N$, $(abc)^5 < (2N)^3$, and mod-8 quasiperfect fourth powers. | Integrated & verified via `Audit.lean`. |
| **0.4** | `OddPerfect.EvenIndexExponent256` (`12` modules) & `PrimeBoxes` (`9` modules) | **`AUDITED`** (`100%`) | Pushes even prime-power index exponent $j \ge 66 \to 256$, proves subexponential base bound $p \le 8(u+1)128^{\sqrt{2u}}$, $s \equiv 1 \pmod p$, and $p^6 \mid N \vee \omega \ge 443$. | Integrated & verified via `Audit.lean`. |
| **0.5** | `OddPerfect.SizeBound300` (`23` modules, `6,977` prime certs) | **`AUDITED`** (`100%`) | Lifts unconditional size bound $N > 10^{160} \to 10^{300}$ (Brent–Cohen–te Riele 1991), strengthening index/radical corollaries ($i_q > 5 \cdot 10^{99}$ at $a=1$). | Integrated & verified via `Audit.lean`. |
| **0.6** | `OddPerfect.DeficientFourClassification` & `OddPerfect.PrimeFive` (`237` modules) | **`AUDITED`** (`100%`) | Proves Yang–Togbé's unrestricted 4-prime odd deficient-perfect classification (`{(9018009, 819)}`, `toth_odd_pair_four_iff`) and Gradshtein's unconditional **`6 ≤ ω(N)`** (`six_le_distinct_prime_factor_count`). | Integrated & verified via `Audit.lean`. |
| **0.7** | `OddPerfect.HarmonicRange` & `OddPerfect.HarmonicSmooth` | **`AUDITED`** (`100%`) | Integrates Cohen–Sorli odd harmonic interval/residual exclusions and smooth-$\tau(N)$ component bounds. | Integrated & verified via `Audit.lean`. |

---

## Tier 1 — Open Stepping-Stone Theorems (Build Global Obstruction Weapons)

These targets are **open or unproved unconditionally in the published literature** (or unformalized structural pillars) that sit one step above our audited library. Each directly sharpens a mechanism required for Tier 2.

### Stepping Stone S1: Unrestricted-Parity Dichotomy for Yang–Togbé (2023, §6) & Dutta–Saikia Fixed-$k$ Conjectures — **`AUDITED`** (`OddPerfect/ParityDichotomy.lean`)
- **Resolved**:
  1. Proved infinite / conditional even families: `pow_two_deficientPerfect` ($2^a$, $d=1$), `thabit_deficientPerfect` ($2^a(3\cdot 2^a-1)$, $d=2^a$), `mersenne_nearPerfect_two_pow_mul` ($2^{k+1}M_{k+1}$), `mersenne_nearPerfect_mul_sq` ($2^k M_{k+1}^2$), and `not_deficientPerfectWith_of_perfect_dvd`.
  2. **Bounded-$2$-valuation finiteness**: Proved `finite_deficientPerfect_pairs_of_bounded_prime_count_two_val` and `finite_nearPerfect_pairs_of_bounded_prime_count_two_val` via `weightedLabelBound` and complement-parity prefix gaps for all fixed $(k, A)$.

### Stepping Stone S2: Bounded Abundancy Data / Fixed-Support Finiteness & Small-Rank Unconditional Exclusion for `OreHarmonic` — **`AUDITED`** (`OddPerfect/HarmonicFinite.lean`, `OddPerfect/HarmonicSupportFinite.lean`, `OddPerfect/HarmonicCubeFree.lean`)
- **Resolved**:
  1. Proved general rational-abundancy finiteness (`finite_odd_of_bounded_prime_count_abundancy`), bounded-$\tau(N)$ finiteness (`finite_odd_oreHarmonic_of_bounded_divisor_count`), Kanold bounded-mean finiteness (`finite_odd_oreHarmonic_of_bounded_mean`), bounded-$(k, E)$ finiteness (`finite_odd_oreHarmonic_of_bounded_prime_count_and_exponent`), and Kanold fixed-prime-support finiteness (`finite_odd_oreHarmonic_of_primeFactors_subset` via Mathlib Lifting-the-Exponent `Nat.multiplicity_pow_sub_pow`).
  2. Proved exact local 2-adic valuation conservation (`odd_oreHarmonic_component_two_valuation_eq`), odd harmonic mean $M \ge 3$ (`odd_oreHarmonic_odd_harmonic_mean`), Callan–Pomerance's **unconditional two-prime exclusion** (`odd_oreHarmonic_three_le_primeFactors`: $\omega(N) \ge 3$ for all odd harmonic $N$ with zero size cutoff), **unconditional cube-free three-prime exclusion** (`odd_oreHarmonic_four_le_primeFactors_of_cubeFree`: $\omega(N) \ge 4$ for all cube-free odd harmonic $N$), `odd_oreHarmonic_divisor_count_not_pow_two`, and `odd_oreHarmonic_card_three_prime_congruence`.

### Stepping Stone S3: Unconditional Obstructions to Prime-Power Component Indices ($i \ne p^j$) — **`AUDITED`** (`OddPerfect/PrimePowerObstruction.lean`, `OddPerfect/TripleRepunitObstruction.lean`, `OddPerfect/QuadrupleRepunitObstruction.lean`, `OddPerfect/PrimePowerExponent2308.lean`)
- **Resolved**:
  1. Proved `coupled_repunit_diff_eq` ($2(s-1)(s+1) = p\sigma(p^{2u-1})$), `even_index_exact_p_dvd_cofactor_pred` ($p \parallel s-1$, $4((s-1)/p) \equiv 1 \pmod p$), `even_index_exponent_two_adic_of_three_mod_four`, `even_index_jacobi_reciprocity`, `even_index_cofactor_component_order_dvd_pred`, `even_index_repunit_lengths_dvd_pred` ($\prod_{r \in S_1} (2 e_r + 1) \mid (p-1)/2$), and `even_index_S1_exact_mod_sq` ($2(u+1)+r \equiv 0 \pmod{r^2}$, $r \parallel u+1$ for all $r \in S_1$).
  2. **Unconditional Nagell–Ljunggren & Triple-Goormaghtigh Elimination + `j ≥ 2308` Jump**: Established both the mod-$p^2$ harmonic congruence and the second-order `ZMod (p^3)` divisor-power identity (`even_index_mod_p_cube_congruence`), eliminating $|S_1| \in \{0, 1, 2, 3\}$ (`even_prime_power_component_forces_four_repunits_and_seven_primes`) and proving **`component_prime_power_index_exponent_ge_2308` ($2308 \le j \wedge 10^{16156} < i \wedge 10^{16156} < N$, with $12207031 \le p$ for even $j$)** unconditionally across all prime-power component indices!
  3. Proved `odd_index_jacobi_and_cyclotomic_order` on the odd prime-power Euler-index branch.

### Stepping Stone S4: Euler Index Shape Collapse ($I = \ell t^2$ Closure & Dris $q^a < m$ Regimes) — **`AUDITED`** (`OddPerfect/DrisRegimes.lean`, `OddPerfect/EulerExceptionalObstruction.lean`, `OddPerfect/ExceptionalBlockSquare.lean`)
- **Resolved**:
  1. Proved `exceptional_index_cofactor_factorization` ($m = \ell v y t$, $\gcd(\ell v, y) = 1$, $d w \mid y$), `exceptional_euler_second_block_exact_square` ($(q^d+1)/(q+1) = d z^2$, $y = d w z$, $\gcd(w, z) = 1$, $d \nmid z$, $z^2 \equiv 1 \pmod{2 w^2}$), `exceptional_index_parameter_floors` ($d \ge 17, a \ge 33, q \ge 193, \ell \ge 137, t \ge 3$), `exceptional_index_size_gt_ten_pow_740_of_gt_17` ($d > 17 \implies N > 10^{740}$), `exceptional_index_cofactor_odd_targets` ($\text{oddValuationPrimes}(\sigma(m^2)) = \{q, \ell\}$), and `exceptional_euler_reciprocity_and_parity_profile` ($q \equiv 1 \pmod{16}$, $a \equiv 1 \pmod 8$, $J(\ell \mid q) = J(q \mid \ell) = J(\ell \mid d) = 1$, even `threeOddTargets N q` and even `oddSigmaSources N r` for all $r \mid m$).
  2. Proved `euler_exponent_one_index_gt_five_mul_ten_pow_99` ($i_q > 5 \cdot 10^{99}$ at $a = 1$) and unconditional Dris regimes (`dris_of_two_mul_pow_le_index`, `dris_of_two_mul_cofactor_le_index`, `dris_of_small_euler_pow`, `dris_exponent_one_of_not_largest_prime`, `dris_failure_consequences`).

### Stepping Stone S5: Linear Valuation-Slope & Logarithmic Density Tightening — **`AUDITED`** (`OddPerfect/ZelinskySlope.lean`, `OddPerfect/CyclotomicRootSlope.lean`)
- **Resolved**:
  1. **Unconditional Cyclotomic Root-Slot Slope Upgrade**: Proved `card_range_dvd_sq_add_self_add_one_le_two`, `squareSources_root_slot_incidence`, `cyclotomic_slope_with_excess_slack`, **`cyclotomic_slope_three_free` ($8\omega(N) \le 3\Omega(N) + 7$ for $3 \nmid N$, slope $8/3 \approx 2.6667$)**, **`cyclotomic_prime_factor_count` ($21\omega(N) \le 8\Omega(N) + 39$ for all odd perfect $N$, slope $21/8 = 2.625$ vs. Ochem–Rao $18/7 \approx 2.5714$)**, and `cyclotomic_least_prime_pinch`.
  2. Proved `ochem_rao_with_excess_slack`, `quartic_sigma_properties`, `quarticSourcesOne_card_le_five_exponent`, `omega_gt_least_prime_mul_log_two`, `total_prime_factors_and_size_of_slope_and_least_prime`, `zelinsky_reciprocal_omega_lower_bound`, `ochem_rao_least_prime_pinch`, and the Zelinsky-slope envelopes `zelinsky_slope_302_113_envelope` and `zelinsky_slope_66_25_envelope`.

### Stepping Stone S6: Vieta Mod-3 Root-Slot Refinement, Cross-Normalization Identities, & Multi-Block Slope (`554/199`) — **`AUDITED`** (`OddPerfect/ZelinskyFullSlope.lean`)
- **Resolved**:
  1. Proved `card_twoModThree_dvd_sq_add_self_add_one_le_one` (at most one $u \equiv 2 \pmod 3$ root of $\Phi_3(x) \equiv 0 \pmod w$ since $u_1 + u_2 \equiv -1 \pmod w$ and $w \equiv 1 \pmod 3$), strengthening quadratic root-slot incidence to **`sharpened_cyclotomic_slope_three_free` ($8\omega(N) + 4|L_2| \le 3\Omega(N) + 7$ for $3 \nmid N$)** and **`sharpened_cyclotomic_prime_factor_count` ($21\omega(N) + 11|L_2| \le 8\Omega(N) + 39$ unconditionally)**.
  2. Proved cross-normalization identities `four_mul_phi5_eq_sq_sub_five_mul_sq` ($4\Phi_5(x) = (2x^2+x+2)^2 - 5x^2$) and `phi3_comp_phi5_factorization`, sharpened quartic (`quarticSources_sharpened_root_slot_incidence`, slope $5/2$) and sextic (`sexticSources_root_slot_incidence`, $l = 7$) root-slot incidences, and coupled multi-block slope **`multi_block_slope_above_zelinsky` ($554\omega(N) \le 199\Omega(N) + 595$, slope $554/199 \approx 2.7839 > 302/113$)** when $3 \nmid N, 5 \nmid N$ and quadratic sources avoid $1 \pmod 5$.

### Stepping Stone S7: `T`-Independent `ZMod (p^2)` Congruence, `5 ≤ |S₁|`, & `30028 ≤ j` Prime-Power Index Lift — **`AUDITED`** (`OddPerfect/PrimePowerHigherObstruction.lean`)
- **Resolved**:
  1. Extracted the `T`-independent second-order congruence `even_index_mod_p_sq_second_order_congruence` in `ZMod (p^2)` from `even_index_mod_p_cube_congruence` and eliminated $|S_1| = 4$ (`even_prime_power_component_forces_five_repunits_and_eight_primes`: `HasFiveOddPrimeRepunits p ∧ 8 ≤ ω(N)`).
  2. Coupled $\prod_{r \in S_1} r \mid u + 1$ with $|S_1| \ge 5$ to prove **`component_prime_power_index_exponent_ge_30028` ($30028 \le j \wedge 10^{17240} < i \wedge 10^{17240} < N$, and $10^{300280} < i < N$ for even $j$)** unconditionally across all prime-power component indices, alongside `even_index_repunit_product_vs_subexponential`.

### Stepping Stone S8: Unconditional `10^740 < N` Closure at `d = 17` & Closed-Graph Reciprocity on `I = ℓ t^2` — **`AUDITED`** (`OddPerfect/ExceptionalBranchClosure.lean`)
- **Resolved**:
  1. Exploited $(q^{17}+1)/(q+1) = 17 z^2$ and $q + 1 = 34 w^2$ modulo $3$ and $5$ (`exceptional_d17_three_and_five_dvd_w`, $15 \mid w$, $65760 \le w$) to remove the $17 < (a+1)/2$ hypothesis from `exceptional_index_size_gt_ten_pow_740_of_gt_17`, proving **`exceptional_index_size_gt_ten_pow_740` ($10^{740} < N$ unconditionally for ALL $a > 1$ on $I = \ell t^2$)**.
  2. Coupled $\text{oddValuationPrimes}(\sigma(m^2)) = \{q, \ell\}$ with closed-graph Jacobi reciprocity to prove `exceptional_euler_full_reciprocity_and_source_parity` ($J(d \mid \ell) = 1$ and odd `oddSigmaTargets N r` parity across $m$).

### Stepping Stone S9: Ochem–Zelinsky Restrained Exponents & Fifth-Power-Free `OreHarmonic` Exclusion — **`AUDITED`** (`OddPerfect/RestrainedExponents.lean`, `OddPerfect/HarmonicBoundedExp.lean`)
- **Resolved**:
  1. Proved unconditional `six_le_three_exponent_of_largeSources_empty` ($6 \le v_3(N)$) and **`eight_le_three_exponent_of_largeSources_empty` ($8 \le v_3(N)$ when `largeSources N q = ∅`)**, Ochem–Zelinsky restrained bounds `restrained_three_free_bounds` ($14 \le v_q + v_{r_0}$, $14 \le v_{r_0}$ at $v_q = 1$, and $13 \le v_q$ if $r_0 \not\equiv 1 \pmod 3$ whenever $3 \nmid N$ and $|L| \le 1$), and `finite_of_bounded_nonSquare_exponents`.
  2. Extended `odd_oreHarmonic_four_le_primeFactors_of_cubeFree` to **`odd_oreHarmonic_four_le_primeFactors_of_fifthPowerFree`** ($\omega(N) \ge 4$ for all fifth-power-free and fourth-power-free odd `OreHarmonic` numbers).

---

## Tier 2 — Full Unconditional Resolution of `OddPerfect.existsOddPerfect` (`OddPerfect/GlobalObstruction.lean` & `OddPerfect/GlobalWave4Obstruction.lean` Active)

The [resolution handoff](RESOLUTION_HANDOFF.md) tracks the later proof round, with exact statements and one assignment per file. The near-full complement in the Wave 4 account below has since been proved empty.

With Tier 0 (`0.1`–`0.7`) and Tier 1 (`S1`–`S9`) audited in `OddPerfect.lean` (`788` modules, `9,479` named theorems, `55,151` declarations), **Waves 3 & 4** have established and kernel-verified the global conservation laws, non-spoofable `I1` separation, and Four-Bridge reductions across `OddPerfect/GlobalObstruction.lean`, `OddPerfect/GlobalAbundancyObstruction.lean`, and `OddPerfect/GlobalWave4Obstruction.lean`:
- **Non-Spoofable `I1` Separation at $a = 1$ (`euler_exp_one_toth_pair_and_six_primes`) & Unconditional $\omega(N) \ge 6$ (`six_le_distinct_prime_factor_count`)**: Isolates `q.Prime` (`19 ∣ 22021`) against `toth_odd_pair_four_iff` on $N = q m^2$ to separate genuine odd perfect numbers from Descartes's spoof `198585576189` and force $5 \le \omega(m), 6 \le \omega(N)$.
- **Global Component-Index Conservation & Dual Bridge `B3` Reductions (`prod_componentIndex_eq`, `cardFactors_componentIndex_add_eq`, `finite_of_all_componentIndex_near_full`, `near_full_componentIndex_caps_twoModThreeLarge`, `exists_componentIndex_cardFactors_add_five_le_of_two_twoModThreeLarge`, `three_free_sixthPowerFree_forces_147_largeSources`)**: Proves $\prod_{p \in S} i_p = 2^{\omega-1} N^{\omega-2}$, $\Omega(i_p) + e_p + \Omega(\sigma(p^{e_p})) = 1 + \Omega(N)$, unconditional $\exists p \in S,\; \Omega(i_p) + 5 \le \Omega(N)$ whenever $3 \nmid N$, $\Omega(N) \ge 88$, or $|L_2| \ge 2$, Dickson finiteness on the near-full complement ($\Omega \le 87, \omega \le 35$, tightening to $\Omega \le 59, \omega \le 23$ at $|L_2| = 1$), and $147 \le |\text{largeSources}|$ ($1231 \le \Omega(N)$ in the multi-block regime) when $3 \nmid N$ is sixth-power-free.
- **Global Closed-Graph Jacobi Reciprocity (`jacobi_prod_oddSigmaTargets_of_even`, `jacobi_prod_oddSigmaTargets_euler`, `euler_five_mod_eight_forces_nonresidue_odd_target`)**: Proves $\prod_{r \in \text{oddSigmaTargets}(N, p)} J(r \mid p) = 1$ ($p \ne q$) and $= \chi_8(q)$ ($p = q$).
- **Counterexample Filter Bank & Four-Bridge Master Reductions (`counterexample_filter_bank_verified`, `not_existsOddPerfect_of_rank_cap`, `not_existsOddPerfect_of_componentIndex_cap`, `not_existsOddPerfect_of_componentIndex_multiplicity_cap`, `odd_perfect_global_obstruction_profile`)**: Kernel-audited and ready for global candidate-set closure ($\mathcal{O} = \emptyset$):
1. **Front Alpha — Global Functional Collision $\implies \omega(N) \le K_0$ (Bridge `B1`/`B2`/`B3` + `dickson_finite`)**:
   Construct opposing upper and lower bounds on a global additive valuation/order/abundancy functional across $N.primeFactors$ whose slopes cross, capping $\omega(N)$ (or $\Omega(i_p)$) unconditionally and discharging the finite residual set in Lean.
2. **Front Beta — Closed-Support Cyclotomic / Reciprocity Invariant $\implies \mathcal{O} = \emptyset$ Directly (Bridge `B0`)**:
   Isolate a global multiplicative character, 2-adic/p-adic valuation parity, or primitive-divisor ordering invariant on the exact closed equation $\prod_{p \in S} \prod_{d \mid e_p+1, d>1} \Phi_d(p) = 2 \prod_{p \in S} p^{e_p}$ that separates genuine prime-power factorizations from spoofs and yields `False` for every nonempty odd support $S$.
3. **Front Gamma — Verification, Upstream Export, & Final Audit**:
   Derive `theorem not_existsOddPerfect : ¬ OddPerfect.existsOddPerfect` together with the exact upstream `formal-conjectures` signature `theorem odd_perfect_number_conjecture (n : ℕ) (hn : Nat.Perfect n) : Even n` (via `not_existsOddPerfect_iff_forall_perfect_even`, matching `FormalConjectures/Wikipedia/PerfectNumbers.lean:83`) and the unconditional Euclid–Euler characterization (`perfect_iff_mersenne_of_not_existsOddPerfect` in `OddPerfect/Even.lean`) in `OddPerfect/Resolution.lean`, import into `OddPerfect.lean`, and pass `lake build && lake lean research/Audit.lean` with zero non-standard axioms.
