# Current proof ideas

| # | Idea | Branch | Status | Deliverable |
| --- | --- | --- | --- | --- |
| 1 | Locate existing target-reuse work and check its count families | A1_SPF | DONE | Abstract families checked. The [review](STRATEGY_REVIEW.md) records the standalone replay limit. |
| 2 | Iterate suppliers monotonically from the largest prime | A1_SPF | KILLED | A divisor of a quartic block need not be at most the fourth power of its base. Later suppliers need not decrease. |
| 3 | Use a fixed-rank Dickson gap for the even-index system | IQ_PRIME_POWER_EVEN | PAUSED | Requires control of support rank and an incompatible growth rate. |
| 4 | Descend on the coprime quotient equations | A1_G1 | PAUSED | Requires a map preserving the admissible system; a strict inequality between entries of one triple does not furnish it. |
| 5 | Spoof testing | All | DONE | Use branch-matched controls as part of each review. |
| 6 | Count square-source outputs by residue and target valuations | A1_SPF | DONE | Public theorem and high-square-count exclusion. |
| 7 | Charge high-exponent capacity against its outgoing factors | ROOT | KILLED | Vacuous at S = 0, weaker than Vieta mod 3 when 3H + 15U > V - X, and prime Φ_ℓ(t) targets exist for every ℓ ∈ [7, 43] even at H = 0 (NO_GO §8). |
| 8 | Separate incoming partitions by residue (and sharpen 5D ≥ 3k − 2) | A1_SPF | KILLED | Standalone `5 D_all ≥ 4k − 2` proved as `#10`, but coupled 28-row fine/mod-5/mod-4/`Ω ≡ 1 mod 4`/bipartite log-height LP still admits `Ray_18` (`k = 0`, 364-var witness at `ω = 1800`) and `lower-square-count` (`NO_GO §§11, 13`). `A1_SPF` frozen. |
| 9 | Eliminate `r₀ ∤ m_L` (`r₀ ∣ m_R`) unconditionally across all of `A1` | A1 | DONE | Integrated and audited in `OddPerfect/LinearEulerRightSourceForcing.lean` (`linear_euler_unique_source_right_forcing`, `linear_euler_unconditional_right_source_peeling`). |
| 10 | Sharp quartic-chain target bound `5 D_all ≥ 4k − 2` via disjoint mod-5 prime images of `A(w)` and `B(w)` | A1_SPF | DONE | Integrated and audited in `OddPerfect/QuarticChainModFiveTargetReuse.lean` (`quartic_chain_mod_five_target_reuse`, `quarticChainSources_five_mul_allTargets_ge_four_mul_sub_two`); does not close `A1_SPF` or reset its pivot clock. |
| 11 | Branch R1 (`r₀ ∣ g_R`) quadratic reciprocity (`r₀ % 4 = 1`), valuation gap (`k_R ≤ 2b`, `b = 1 → k_R = 1`), sharp bound `A < r₀^(v_{r₀}(I))`, and non-Fermat forcing across all of `A1` | A1 | DONE | Integrated and audited in `OddPerfect/LinearEulerRightBranchStructure.lean` (`linear_euler_right_branch_structure`, `linear_euler_r0_eq_three_mod_twelve`). |
| 12 | Full `A_GT1` Subcase A (`(q^d + 1)/2 = □`) reduction & `PrimePowerFermatObstruction` conditional closure + unconditional Subcase B `I = ℓ₁ ℓ₂ t²` prime-`d` forcing | A_GT1 | DONE | Integrated and audited in `OddPerfect/HighEulerHalfSumReduction.lean` (`half_pow_succ_square_forces_minFac_fermat_witness`, `high_euler_half_sum_not_square_of_prime_power_fermat`, `two_odd_valuations_nonsquare_half_sum_forces_prime_half_length`, `two_odd_valuations_forces_prime_half_length_of_prime_power_fermat`). |

## 6. Modulo-five capacity

**Theorem.** With $S$ square sources, $U$ square sources outside $1\bmod5$, and $Q$ quartic sources congruent to $1\bmod3$, the candidate satisfies $10S\le19Q+5U+10$. The [complete argument](STRATEGY_REVIEW.md#a-direction-that-arithmetic-distinguishes) includes the exceptional Euler target. The [formal proof](../OddPerfect/SquareOutputCapacity.lean) instantiates the inequality using only perfection, sixth-power-freeness and the Euler-prime facts available for every candidate.

**Closure argument.** The modulo-five target budget excludes the square-ramified count family at every positive scale and leaves a smaller named residual.

| Check | Evidence |
| --- | --- |
| Spoofs and local controls | Primality supplies the order-three target restriction, and actual perfection supplies exact incoming valuations. The Descartes composite-base factorization has no such budget. The 4153 and 22639 chains sharing 73 are allowed. |
| Count model | Including the row with the target-reuse inequalities excludes a whole unbounded direction. The lower-square-count family remains. Both substitutions hold algebraically in the parameter. |
| Local solvability | A single congruence cannot force the contradiction. The residue of the entire output controls its multiplicity only when all its targets have the specified residue. Exceptional targets are charged explicitly. |
| Floor and ceiling | The two sides concern the same source counts. On the excluded family the coefficient gap is $2m$. The rank objective remains unbounded. |
| Independent mathematical review | The arithmetic, capacity and elimination steps survived review. Literature priority is unassessed. |

**Branch impact.** When U = 0 and S ≥ 2Q the theorem forces Q ≤ 10. The public bound Q ≥ 80 excludes that entire slice. The lower-square-count family remains a regression case.

## 7. Arbitrary exponents (KILLED)

```
G1 spoof:      N/A (fails G2/G4 first)
G2 count-LP:   FAIL — multi-degree cyclotomic count-LPs on ROOT (e ∈ {2,4,6,10}, mod 3,4,5,7,11) remain UNBOUNDED even at S = 0 (exact bipartite (6k, 4k) ray for e ∈ {4,6} and (5k, 3k) ray for e ∈ {6,10}).
G3 local:      FAIL — concrete primes t ≡ 13 (mod 15) (keeping H = 0!) give prime Φ_ℓ(t) (Ω = 1) for every prime ℓ ∈ {7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43}, e.g. (ℓ=7, t=73), (ℓ=11, t=1213), (ℓ=43, t=163). Also e_t = 24 at t = 22699 gives Ω = 2. No compulsory multiplicity payment proportional to e_t exists.
G4 floor/ceil: FAIL — vacuous at S = 0 (0 ≤ RHS), and strictly weaker than pure Vieta mod 3 (`3S ≤ 2X + V`) whenever 3H + 15U > V - X.
Skeptic:       KILLED at pre-dispatch gates (moved to NO_GO §8).
Closure arg:   None — refuted.
```

## 8. Residues on the surviving family

Start with the coupled 28-constraint fine model (`farkas_int_reductions`), the sharper quartic-reuse bound `5D ≥ 3k − 2`, and residue-labelled partitions (`mod 4`, `mod 5`, `B ≢ 3 mod 5`, `Ω ≡ 1 mod 4` slot compatibility, log-height). Test jointly; if a count family survives, test Ochem–Zelinsky complete-factorization tracking.

## 9. Unconditional `r₀ ∤ m_L` (`r₀ ∣ m_R`) across all of `A1`

**Target node:** `A1` (`N = q m²`, Euler exponent `a = 1`, arbitrary `g = gcd((q+1)/2, i_q) ≥ 1`).

**Informal proof sketch.** Using `linear_euler_gcd_coprime_split_and_quotient_duality`, write `A = (q+1)/2 = g_L g_R h₀²`, `I = g_L g_R u₀²`, `m_L = g_L h₀`, `m_R = g_R u₀`, `m = m_L m_R` with `gcd(m_L, m_R) = 1`. Let `r₀ ∣ m` be the unique prime with `q ∥ σ(r₀^(2 e₀))` (`e₀ = v_{r₀}(m)`), so `σ(r₀^(2 e₀)) = q c₀` (`c₀` odd) and `2 q < 3 r₀^(2 e₀)`. Suppose `r₀ ∣ m_L`. Put `k = v_{r₀}(g_L)`, `a = v_{r₀}(h₀)` (`k + a = e₀ ≥ 1`), and `M = v_{r₀}(A) = k + 2a ≥ 1`. Then `M ≤ 2 e₀ ≤ 2M` and `q = 2 C r₀^M - 1` (`C ≥ 1` odd).
1. If `k = 0`: `M = 2 e₀`, so `2 q ≥ 4 r₀^(2 e₀) - 2 > 3 r₀^(2 e₀)`, contradicting `2 q < 3 r₀^(2 e₀)`.
2. If `k ≥ 1` and `r₀ ≥ 5`: modulo `r₀^M`, `σ(r₀^(2 e₀)) ≡ (r₀^M - 1)/(r₀ - 1)` and `q ≡ -1`, so `(r₀ - 1) c₀ ≡ 1 (mod r₀^M)`, forcing `(r₀ - 1) c₀ ≥ (r₀ - 2) r₀^M + 1`. Then `(r₀ - 1) q c₀ ≥ (2 r₀^M - 1)((r₀ - 2) r₀^M + 1) = (r₀^(2M+1) - 1) + (r₀ - 4) r₀^M (r₀^M - 1) > r₀^(2M+1) - 1 ≥ (r₀ - 1) σ(r₀^(2 e₀))`, contradiction.
3. If `k ≥ 1` and `r₀ = 3`: `2 c₀ ≡ 1 (mod 3^M)` gives `c₀ = (3^M + 1)/2 + t · 3^M` (`t ≥ 0`). If `M` is odd then `(3^M + 1)/2` is even while `c₀` is odd, forcing `t ≥ 1`. Whenever `t ≥ 1` or `C ≥ 3`, `2 q c₀ > 3^(2M+1) - 1 ≥ 2 σ(3^(2 e₀))`. In the sole remaining case `t = 0, C = 1` (`M` even), `2 q c₀ = 2·3^(2M) + 3^M - 1 = 3^M(2·3^M + 1) - 1 ≠ 3^(2 e₀ + 1) - 1` because `2·3^M + 1 > 1` is coprime to `3`.

Hence `¬ r₀ ∣ m_L`, so `r₀ ∣ m_R = g_R u₀` unconditionally, yielding `W_R * σ(m_L²) = g u₀²` and `σ(m_L²) ∣ g u₀²` for EVERY candidate in `A1`. (Corollary: the `r₀ ∣ m_L` branch of `LinearEulerNoncoprimeHalfSuccQuotientDuality.lean` is empty, and for `3 ∤ N`, `g = r` prime with `v_r(m) = 1` is impossible.)

**Closure argument.** Eliminates the entire `r₀ ∣ m_L` half of the `A1` noncoprime quotient dichotomy unconditionally across all `g ≥ 1`, shrinking `A1` to the single `r₀ ∣ m_R` quotient system `W_R * σ(m_L²) = g u₀²`.

```
G1 spoof:      PASS — fails for Descartes (3003, 22021) at `linear_euler_unique_q_source_and_bound` because q = 22021 = 19²·61 is composite and splits across 7², 11², 13² inside m_L = 1001. Uses I1 (primality of q) and I2 (exact q-valuation = 1).
G2 count-LP:   N/A (universal structural reduction on A1, not a count inequality).
G3 local:      PASS — direct size contradiction between (r₀ - 1) q c₀ and r₀^(2 e₀ + 1) - 1 plus 3-adic valuation contradiction at r₀ = 3, C = 1, t = 0; note the complementary r₀ ∣ g_R case DOES admit local prime-q solutions ((r=37, b=3, h₀=1, q=73) and (r=29, b=5, h₀=3, q=521)), confirming sharpness of the boundary r₀ ∤ m_L vs r₀ ∣ m_R.
G4 floor/ceil: PASS — not a floor-raising bound; proves `False` on the entire `r₀ ∣ m_L` branch of A1 (making `61 ≤ g_L` in Wave Q vacuous).
Skeptic:       SURVIVES (separate-session pro review 2026-11-28: all 3 cases verified; Case 3 simplifies via odd s in 2 c₀ = s·3^M + 1; 0 local solutions for r₀ < 200, k,a < 12; Descartes spoof fails at q.Prime; complementary r₀ ∣ g_R locally solvable).
Closure arg:   Eliminates the entire r₀ ∣ m_L half of the A1 noncoprime quotient dichotomy unconditionally across all g ≥ 1, shrinking A1 to the single r₀ ∣ m_R system W_R σ(m_L²) = g u₀².
```

## 10. Sharp quartic-chain target bound `5 D_all ≥ 4k − 2` via disjoint mod-5 prime images

**Target node:** `A1_SPF` (standalone user-requested quartic-reuse goal on `K ⊆ squareSources N` consisting of quartic-to-square chains `s = Φ_5(w)` with `w^4 ∥ N`).

**Informal proof sketch.** Let `N` be a sixth-power-free odd perfect number (`Odd N`, `N.Perfect`, `q ∈ N.primeFactors`, `q % 4 = 1`, `v_q(N) % 4 = 1`, `∀ r ≠ q, Even (v_r(N))`, `∀ p prime, ¬ p^6 ∣ N`), and let `K ⊆ squareSources N` satisfy `∀ s ∈ K, ∃ w ∈ N.primeFactors, v_w(N) = 4 ∧ s = w^4 + w^3 + w^2 + w + 1` (`k := K.card`). Define `allTargets := (N.primeFactors.erase q).filter (fun t => ∃ s ∈ K, t ∣ sigma 1 (s ^ 2))` (`D_all := allTargets.card`) and its mod-5 slices `D_r := (allTargets.filter (· % 5 = r)).card` (`r ∈ {1, 2, 3, 4}`).
1. Since `w ↦ w^4 + w^3 + w^2 + w + 1` is strictly increasing on `ℕ`, each `s ∈ K` determines a unique prime `w(s)` with `w(s)^4 ∥ N` and `s = Φ_5(w(s))`, and `s ↦ w(s)` is injective on `K`. Moreover `5 ∤ N` (`sixth_power_free_five_not_dvd` / `least_prime_ge_53`) and `w ≡ 1 (mod 5) ⇒ 5 ∣ Φ_5(w) = s` (impossible since `s` is prime and `s > 5`), so `w(s) % 5 ∈ {2, 3, 4}` for every `s ∈ K`.
2. By `QuarticChainBaselineAndReuse.lean`, `sigma 1 (s ^ 2) = s ^ 2 + s + 1 = A(w) * B(w)` where `A(w) = w^2 - w + 1 > 1` and `B(w) = w^6 + 3w^5 + 5w^4 + 6w^3 + 7w^2 + 6w + 3 > 1`. Evaluating mod 5 on `w % 5 ∈ {2, 3, 4}`:
   - `w % 5 ∈ {2, 4}` ⇒ `A(w) % 5 = 3` and `B(w) % 5 = 1`;
   - `w % 5 = 3` ⇒ `A(w) % 5 = 2` and `B(w) % 5 = 4`.
   Every prime divisor `t ∣ sigma 1 (s ^ 2)` with `t ≠ q` lies in `allTargets ⊆ oneModThreeLargeSources N q` and has `v_t(N) = 4`; also `v_q(N) = 1`.
3. Let `K_A1 := K.filter (fun s => (A (w s)).Prime)` and `K_B1 := K.filter (fun s => (B (w s)).Prime)` (with mod-5 sub-slices `K_A1_24`, `K_A1_3`, `K_B1_24`, `K_B1_3`). Since `w ↦ A(w)` (for `w ≥ 1`) and `w ↦ B(w)` are strictly increasing and `s ↦ w(s)` is injective, `Img_A := K_A1.image (A ∘ w)` and `Img_B := K_B1.image (B ∘ w)` satisfy `|Img_A| = k_A1`, `|Img_B| = k_B1`, and:
   - `Img_A ⊆ insert q allTargets` with all elements `% 5 ∈ {2, 3}`;
   - `Img_B ⊆ insert q allTargets` with all elements `% 5 ∈ {1, 4}`.
   Because `{2, 3} ∩ {1, 4} = ∅`, **`Img_A` and `Img_B` are disjoint**, yielding per-residue bounds `k_A1_24 ≤ D_3 + q_3`, `k_A1_3 ≤ D_2 + q_2`, `k_B1_24 ≤ D_1 + q_1`, `k_B1_3 ≤ D_4 + q_4` (where `q_r := if (∃ s ∈ K, q ∣ sigma 1 (s ^ 2)) ∧ q % 5 = r then 1 else 0`, so `q_1 + q_2 + q_3 + q_4 = q_tot` by `5 ∤ N`), and summed:
   `k_A1 + k_B1 ≤ D_all + q_tot`, where `q_tot := if ∃ s ∈ K, q ∣ sigma 1 (s ^ 2) then 1 else 0` (`q_tot ≤ 1`).
   (Check: if `q ∈ Img_A ∪ Img_B`, then `∃ s ∈ K, q ∣ A(w(s)) * B(w(s)) = sigma 1 (s ^ 2)`, so `q_tot = 1`; if `q ∉ Img_A ∪ Img_B`, then `Img_A ∪ Img_B ⊆ allTargets` so `k_A1 + k_B1 ≤ D_all ≤ D_all + q_tot`.)
4. By additivity of `cardFactors` (`Ω(A * B) = Ω(A) + Ω(B)` for `A, B > 0`):
   - `s ∈ K_A1` has `Ω(A(w)) = 1`, while `s ∈ K \ K_A1` has `A(w) > 1` composite so `Ω(A(w)) ≥ 2`; thus `∑_{s ∈ K} Ω(A(w(s))) ≥ 2 * k - k_A1`.
   - `s ∈ K_B1` has `Ω(B(w)) = 1`, while `s ∈ K \ K_B1` has `B(w) > 1` composite so `Ω(B(w)) ≥ 2`; thus `∑_{s ∈ K} Ω(B(w(s))) ≥ 2 * k - k_B1`.
   - Summing: `4 * k - (k_A1 + k_B1) ≤ ∑_{s ∈ K} Ω(sigma 1 (s ^ 2))`.
5. On the target side, `∑_{s ∈ K} Ω(sigma 1 (s ^ 2)) = ∑_{p ∈ insert q allTargets} ∑_{s ∈ K} v_p(sigma 1 (s ^ 2)) ≤ (∑_{t ∈ allTargets} v_t(N)) + q_tot = 4 * D_all + q_tot` (since `K ⊆ N.primeFactors` has distinct primes with `v_s(N) = 2`, so `∑_{s ∈ K} v_p(sigma 1 (s ^ 2)) ≤ v_p(sigma 1 N) = v_p(N)` for every prime `p`, and `∑_{s ∈ K} v_q(sigma 1 (s ^ 2)) ≤ q_tot` because `v_q(N) = 1` and `q_tot = 0 ⇒ ∀ s ∈ K, ¬ q ∣ sigma 1 (s ^ 2)`).
6. Combining (3), (4), (5): `4 * k - (D_all + q_tot) ≤ 4 * D_all + q_tot`, hence **`4 * k ≤ 5 * D_all + 2 * q_tot ≤ 5 * D_all + 2`**, i.e., **`5 * D_all ≥ 4 * k - 2`** (strictly implying `4 * D_all ≥ 2 * k - 1` for `k ≥ 2` and `5 * D_all ≥ 3 * k - 2` for `k ≥ 1`, ruling out `(k=4, D_all=2)`, `(k=6, D_all=3)`, and `(k=6, D_all=4)`).

**Closure argument.** Excludes every quartic-reuse count family with `4 * k > 5 * D_all + 2` (sharp in both slope `4/5` and constant `+2` over `(ℤ/20ℤ)^*` and `(ℤ/40ℤ)^*`, sharpening `4 D_all ≥ 2k - 1` and `5 D_all ≥ 3k - 2`); explicitly distinguishes `D_all` from `D_odd` and does NOT close `A1_SPF` or reset `A1_SPF`'s pivot clock (both `lower-square-count` and the `27/10` `k=0` family survive `D_all ≤ Q13`).

```
G1 spoof:      PASS — uses prime `w`, prime `s = Φ_5(w)`, `5 ∤ N`, `v_t(N) = 4`, `v_q(N) = 1`, and perfection `∑ v_p(σ(s²)) ≤ v_p(N)`. Fails on composite/repeated-base spoofs; permits local regression `w ∈ {4153, 22639}` sharing `t = 73`. Explicitly requires `D_all` (all non-Euler prime targets), NOT `D_odd` alone (fails for `D_odd` via `A = p r^2, B = t u^2`).
G2 count-LP:   PASS (on standalone quartic-reuse LP) / HONEST LIMIT (on full A1_SPF): cuts all quartic-reuse families with `4k > 5 D_all + 2` (sharp over `(ℤ/20ℤ)^*` and `(ℤ/40ℤ)^*`: max `k/D_all = 5/4` witnessed at `(k=20, D_all=16, D_1=11, D_3=5)` with `q_tot=0`; max `4k - 5 D_all = 2` witnessed in integers mod 40 at `(k=8+20m, D_all=6+16m, D_1=4+11m, D_3=2+5m, q_1=1)`). Does NOT cut `lower-square-count` or the `27/10` (`k=0`) family on `A1_SPF`.
G3 local:      PASS — direct injectivity + mod-5 disjointness + `Ω` capacity proof; sharp integer witnesses mod 40 above (`(k=3, D_all=2)` obstructed mod 4).
G4 floor/ceil: PASS (for standalone quartic-reuse family exclusion; explicitly not a ceiling on `A1_SPF`).
Skeptic:       SURVIVES (separate-session pro review 2026-11-28: all 7 edge cases verified; LP-sharp in both slope and +2 constant via mod-40 integer family `(8+20m, 6+16m)`; explicit `D_all` vs `D_odd` distinction and `q_r` guard noted).
Closure arg:   Excludes every quartic-reuse count family with 4k > 5 D_all + 2 (sharp over (ℤ/20ℤ)* and (ℤ/40ℤ)*, sharpening 4 D_all ≥ 2k − 1 and 5 D_all ≥ 3k − 2); does not close A1_SPF or reset its pivot clock.
```

## 11. Unconditional `A1` Branch R1 (`r₀ ∣ g_R`) quadratic reciprocity, `k_R ≤ 2b`, `b = 1 → k_R = 1`, sharp `A < r₀^(v_{r₀}(I))`, & non-Fermat forcing

**Target node:** `A1` (`N = q m²`, arbitrary `g = gcd((q+1)/2, i_q) ≥ 1`, Branch R1 `r₀ ∣ g_R`, equivalently `r₀ ∣ (q+1)/2` by `IDEAS #9`).

**Informal proof sketch.** From `linear_euler_unique_source_right_forcing` (`OddPerfect/LinearEulerRightSourceForcing.lean`), `A = (q+1)/2 = g_L g_R h₀²`, `I = g_L g_R u₀²`, `m = m_L m_R`, `r₀ ∤ m_L`, `r₀ ∣ m_R`, `r₀ ∣ u₀`, `σ(r₀^(2 e₀)) = q c₀` (`c₀` odd). Suppose `r₀ ∣ g_R` (equivalently `r₀ ∣ A`). Let `k_R := A.factorization r₀ = g_R.factorization r₀ ≥ 1`, `b := u₀.factorization r₀ ≥ 1`, so `e₀ := m.factorization r₀ = k_R + b ≥ 2`, `I.factorization r₀ = k_R + 2b ≥ 3`. Write `A = C r₀^(k_R)` (`C` odd, `r₀ ∤ C`), so `q = 2 C r₀^(k_R) - 1`.
1. **Quadratic reciprocity (`r₀ % 4 = 1`, eliminating `r₀ = 3` and all `r₀ ≡ 3 mod 4` from Branch R1):**
   Since `q ∣ σ(r₀^(2 e₀)) ∣ r₀^(2 e₀ + 1) - 1`, in `ZMod q` we have `(r₀^(e₀ + 1))^2 = r₀ * r₀^(2 e₀ + 1) = r₀`, so `legendreSym q r₀ = 1` (note `r₀ ≠ q` since `¬ q ∣ m`). Since `q ≡ 1 (mod 4)`, quadratic reciprocity gives `legendreSym r₀ q = legendreSym q r₀ = 1`. Since `r₀ ∣ A`, `q ≡ -1 (mod r₀)`, so `legendreSym r₀ (-1) = 1`, forcing **`r₀ % 4 = 1`** (hence `5 ≤ r₀`, `r₀ ≠ 3`; in particular `r₀ = 3 ⇒ ¬ 3 ∣ A ⇒ q ≡ 1 (mod 12)` unconditionally across all of `A1`).
2. **Non-Fermat order forcing:** Since `2 r₀ ∣ q + 1`, `r₀ < q`, so `q ∤ r₀ - 1`. Hence `r₀ % q ≠ 1`, forcing `orderOf (r₀ : ZMod q) > 1`, dividing both `2 e₀ + 1` (odd) and `q - 1`. Choosing an odd prime `l ∣ orderOf (r₀ : ZMod q)` gives `l ∣ 2 e₀ + 1`, `4 l ∣ q - 1` (as `4 ∣ q - 1` and `l` odd), `13 ≤ q`, and `l ≠ r₀` (since `l ∣ q - 1` while `r₀ ∣ q + 1` and both are odd).
3. **Exact R1 Diophantine equations, sharp upper bounds, `k_R ≤ 2b`, and `b = 1 → k_R = 1`:**
   From `(r₀ - 1) q c₀ + 1 = r₀^(2 e₀ + 1)` and `q + 1 = 2 C r₀^(k_R)`, as in `IDEAS #9`, `(r₀ - 1) c₀ ≡ 1 (mod r₀^(k_R))`, and since `r₀^(k_R) ≡ 1 (mod r₀ - 1)`, writing `(r₀ - 1) c₀ = 1 + t r₀^(k_R)` forces `(r₀ - 1) ∣ 1 + t`, i.e., `1 + t = u (r₀ - 1)` (`u ≥ 1`), giving **`(r₀ - 1) c₀ = u (r₀ - 1) r₀^(k_R) - (r₀^(k_R) - 1)`**, i.e., `c₀ = u r₀^(k_R) - σ(r₀^(k_R - 1))` with `u ≡ k_R + 1 (mod 2)` (since `c₀` is odd and `σ(r₀^(k_R - 1)) ≡ k_R (mod 2)`).
   Substituting `q = 2 C X - 1` and `(r₀ - 1) c₀ = ((r₀ - 1) u - 1) X + 1` (where `X := r₀^(k_R) ≥ 5`) into `(r₀ - 1) q c₀ + 1 = r₀^(2 b + 1) X^2`:
   - `2 C ((r₀ - 1) u - 1) X^2 + (2 C - (r₀ - 1) u + 1) X = r₀^(2 b + 1) X^2`, so `X ∣ 2 C - (r₀ - 1) u + 1`. Write **`2 C - (r₀ - 1) u + 1 = z X`** (`z ∈ ℤ`, `z ≠ 0` since `r₀ ∤ 2 C` while `r₀ ∣ (r₀ - 1) u - 1`? Wait: check `z = 0` directly: `2 C = (r₀ - 1) u - 1 ⇒ 2 C ((r₀ - 1) u - 1) = r₀^(2 b + 1)` is EVEN = ODD, impossible!).
   - Dividing by `X^2`: **`2 C ((r₀ - 1) u - 1) + z = r₀^(2 b + 1)`**, and multiplying `(E1)` by `2 C` gives **`4 C^2 - r₀^(2 b + 1) = z q`**.
   - **Sharp upper bounds:** Since `(r₀ - 1) c₀ ≥ (r₀ - 2) X + 1` (`r₀ ≥ 5`), `(2 C X - 1)((r₀ - 2) X + 1) + 1 ≤ r₀^(2 b + 1) X^2`, which directly yields **`C < r₀^(2 b)`**, **`A = C X < r₀^(k_R + 2 b) = r₀^(I.factorization r₀)`**, and **`q < 2 r₀^(I.factorization r₀)`** (factor `r₀^(k_R)` sharper than `2 q < 3 r₀^(2 e₀)`). When `u ≥ 2` (including all odd `k_R`), `(r₀ - 1) c₀ ≥ (2 r₀ - 3) X + 1`, giving `2 C < r₀^(2 b)` and `2 A < r₀^(I.factorization r₀)`.
   - **Valuation gap (`k_R ≤ 2 b`):**
     - If `z < 0`: `(r₀ - 1) u - 1 = 2 C + |z| X ≥ X + 2`, so `r₀^(2 b + 1) = 2 C ((r₀ - 1) u - 1) - |z| ≥ 2 (X + 2) - |z|`? Careful: write `|z| ≥ 1`, since `2 C ≥ 2`, `2 C ((r₀ - 1) u - 1) - |z| = 4 C^2 + |z| (2 C X - 1) ≥ 4 + (2 X - 1) = 2 X + 3 > X = r₀^(k_R)`. Since `r₀^(2 b + 1) > r₀^(k_R)` and `r₀ ≥ 5`, wait: `r₀^(2 b + 1) ≥ 2 r₀^(k_R) + 3` forces `2 b + 1 ≥ k_R + 1`, hence **`k_R ≤ 2 b`**!!
     - If `z > 0` and `u ≥ 2`: `2 C = z X + (r₀ - 1) u - 1 ≥ X + 2 r₀ - 3 > X`, while `2 C < r₀^(2 b)` forces `r₀^(k_R) < r₀^(2 b)`, hence `k_R < 2 b` (`k_R + 1 ≤ 2 b`)!
     - If `z > 0` and `u = 1` (forces `k_R` even, `k_R ≥ 2`): suppose `2 b < k_R`, so `2 b + 1 ≤ k_R - 1`, hence `r₀^(2 b + 1) < X`. Since `z ≥ 1`, `2 C = z X + r₀ - 2 ≥ X + r₀ - 2`, so `r₀^(2 b + 1) = 2 C (r₀ - 2) + z ≥ (X + r₀ - 2)(r₀ - 2) + 1 > X > r₀^(2 b + 1)`, contradiction! (Even simpler: we don't even need `2b = k_R` excluded for `k_R ≤ 2b`! `k_R ≤ 2b` already allows `k_R = 2b`, and if `k_R > 2b`, i.e., `2 b + 1 ≤ k_R`, then `r₀^(2 b + 1) ≤ X < (X + r₀ - 2)(r₀ - 2) + 1 ≤ 2 C (r₀ - 2) + z = r₀^(2 b + 1)` — instant 1-line contradiction!!)
     - Therefore **`k_R ≤ 2 b`** holds unconditionally across ALL of Branch R1 (`3 * A.factorization r₀ ≤ 2 * m.factorization r₀` and `2 * A.factorization r₀ ≤ I.factorization r₀`)!
   - **`b = 1 → k_R = 1`:** By `k_R ≤ 2 b = 2`, only `k_R = 2` needs exclusion. At `k_R = 2, b = 1`:
     - If `z > 0`: since `2 C ≥ X + r₀ - 2 = r₀^2 + r₀ - 2`, `(r₀ - 2) * (r₀^2 + r₀ - 2) + 1 ≤ r₀^3`, which reduces to `r₀^2 + 3 r₀ - 5 ≤ 2 r₀^2`? Check: `(r₀ - 2)(r₀^2 + r₀ - 2) + 1 = r₀^3 - r₀^2 - 4 r₀ + 5`, wait: for `z = 1, u = 1`, `r₀^3 - r₀^2 - 4 r₀ + 5 < r₀^3`! Aha: equality `z = 1, u = 1` requires `2 C (r₀ - 2) + 1 = r₀^3` with `2 C = r₀^2 + r₀ - 2`, giving `r₀^3 - r₀^2 - 4 r₀ + 5 = r₀^3`, i.e., `r₀^2 + 4 r₀ = 5` ⇒ `r₀ = 1`, impossible! And for `z ≥ 2` or `u ≥ 2`: `u ≥ 3` (`u` odd since `k_R = 2` even!) gives `2 C (3 r₀ - 4) ≥ (r₀^2 + 3 r₀ - 4)(3 r₀ - 4) > r₀^3`, and `z ≥ 2, u = 1` gives `(2 r₀^2 + r₀ - 2)(r₀ - 2) + 2 = 2 r₀^3 - 3 r₀^2 - 4 r₀ + 6 > r₀^3` (`r₀ ≥ 5`)!
     - If `z < 0`: put `t = -z ≥ 1`, so `r₀^3 = 4 C^2 + t q`. Since `q = 2 C r₀^2 - 1 > 2 r₀^2`, we have `t < r₀ / 2` and `2 C < r₀` (actually `4 C^2 < r₀^3` and `2 C t r₀^2 < r₀^3 + t ⇒ 2 C t ≤ r₀`, so `2 C ≤ r₀` and `t ≤ r₀ / 2`). Reducing `r₀^3 = 4 C^2 + t (2 C r₀^2 - 1)` mod `r₀^2` gives `t ≡ 4 C^2 (mod r₀^2)`. Since `0 < t < r₀ < r₀^2` and `0 < 4 C^2 < r₀^2` (as `2 C < r₀` because `2 C t ≤ r₀` and `r₀` odd ⇒ `2 C < r₀`!), we get **`t = 4 C^2`**! Substituting back: `r₀^3 = 4 C^2 + 4 C^2 (2 C r₀^2 - 1) = 8 C^3 r₀^2`, so `r₀ = 8 C^3`, contradicting `Odd r₀`!

**Closure argument.** Eliminates all `r₀ ≡ 3 (mod 4)` (including `r₀ = 3`), all `k_R > 2b`, and all `(b = 1, k_R ≥ 2)` from Branch R1 (`r₀ ∣ (q+1)/2`) across all of `A1`, sharpens `A < r₀^(2 e₀)` to `A < r₀^(v_{r₀}(I))`, and excludes Fermat `q` on Branch R1; leaves `r₀ ≡ 1 (mod 4)` with `k_R ≤ 2b` (and `b ≥ 2` or `(b=1, k_R=1)`) plus Branch R2 open.

```
G1 spoof:      PASS — requires `q.Prime`, `q ≡ 1 (mod 4)`, `r₀.Prime`, `q ∥ σ(r₀^(2 e₀))`, and `IDEAS #9` (`r₀ ∤ m_L`). Fails on Descartes (`q = 22021` composite), Voight (negative base), and BYU composite-base spoofs.
G2 count-LP:   N/A (universal structural reduction across all of `A1`, not a count inequality).
G3 local:      PASS — verified on all 6 local R1 prime-`q` pairs (`r₀ < 200, e₀ ≤ 6`, e.g. `(5, 1, 3, 829)`, `(37, 1, 3, 73)`, `(13, 2, 8, 337)`): every pair satisfies `r₀ % 4 = 1`, `k_R ≤ 2b`, `A < r₀^(k_R+2b)`, and `4l ∣ q - 1`; `0` violations for `r₀ = 3` (`e₀ ≤ 25`) or `(b = 1, k_R ≥ 2)` (`r₀ < 150, k_R ≤ 5`).
G4 floor/ceil: PASS — direct structural exclusions (`False` on `r₀ % 4 = 3`, `k_R > 2b`, `(b = 1, k_R ≥ 2)` inside R1) plus sharper upper bound `A < r₀^(v_{r₀}(I))`.
Skeptic:       SURVIVES (separate-session pro review 2026-11-28: all 6 claims, parities, sign boundaries, and edge cases verified; `Odd z` and `Odd t` vs `Even (4 C²)` simplify `b=1→k_R=1`; verified on all 6 local R1 prime-q pairs for r₀ < 200, e₀ ≤ 6 plus `(13, 2, 8, 337)` at e₀ = 10).
Closure arg:   Eliminates all r₀ ≡ 3 (mod 4) (including r₀ = 3), all k_R > 2b, and all (b = 1, k_R ≥ 2) from Branch R1 (r₀ ∣ (q+1)/2) across all of A1, sharpens A < r₀^(v_{r₀}(I)), and excludes Fermat q on R1.
```

## 12. Full `A_GT1` Subcase A (`(q^d + 1)/2 = □`) reduction & `PrimePowerFermatObstruction` conditional closure + Subcase B `I = ℓ₁ ℓ₂ t²` prime-`d` forcing

**Target node:** `A_GT1` (`N = q^a m²`, `a > 1`, `d = (a+1)/2 ≥ 3` odd, covering `IQ_SQUARE`, `IQ_PRIME_SQUARE`, and `IQ_MULTI`).

**Informal proof sketch.** Let `N = q^a m²` be an odd perfect number with `a > 1`, `q % 4 = 1`, `a % 4 = 1`, `¬ q ∣ m`, `d := (a + 1) / 2 ≥ 3` odd, and `I := sigma 1 (m ^ 2) / q ^ a`.
1. **Unconditional Subcase A (`IsSquare ((q^d + 1) / 2)`) across ALL of `A_GT1` (prime or composite `d`):**
   Write `(q^d + 1) / 2 = y^2` (`0 < y`, `q.Coprime y` since `q^d + 1 = 2 y^2`).
   - By `Hirakawa.lean` (`half_pow_succ_not_square_of_mod_sixteen`, `half_cube_succ_not_square`, `half_fifth_succ_not_square`, `half_pow_succ_not_square_of_factor`), `q % 16 = 1`, `¬ 3 ∣ d`, `¬ 5 ∣ d`.
   - By `ExceptionalFermatReduction.lean` (`pow_add_one_ne_twice_sq_of_mod_seven`), `q % 7 ≠ 2` and `q % 7 ≠ 4`.
   - For EVERY prime `p ∈ d.primeFactors`: write `d = k * p` (`k` odd, `¬ 3 ∣ k`) and `x := q ^ k`. Then `IsPrimePow x` (`1 < x`), `x % 16 = 1` (since `q % 16 = 1`), `x % 7 ≠ 2 ∧ x % 7 ≠ 4` (since `q % 7 ∈ {1, 3, 5, 6}` and `k` odd, `¬ 3 ∣ k` implies `q^k % 7 ∈ {1, 3, 5, 6}`), and `x^p + 1 = 2 y^2` (`IsSquare ((x^p + 1)/2)`). By `AlternatingPell.lean` (`alternatingBlock_not_square`) + `AlternatingBlock.lean` (`half_sum_not_square_of_alternatingBlock`), `p % 8 = 1` (hence `17 ≤ p`, since `p ≠ 2, 3, 5, 7, 11, 13`!) and `p ∣ x + 1`.
   - Consequently: `17 ≤ d`, `33 ≤ a`, `d % 8 = 1`, `a % 8 = 1` (product of primes `≡ 1 mod 8`), and if `¬ d.Prime` then `289 ≤ d ∧ 577 ≤ a`. Taking `p := d.minFac` (`k = d / p`), every prime factor of `k` is `≥ p`, so `Nat.Coprime k (p - 1)`, which upgrades `p ∣ q^k + 1` to `p ∣ q + 1`, and exhibits the exact generalized-Fermat witness `(x, p, y)` with `IsPrimePow x`, `x % 16 = 1`, `x % 7 ≠ 2`, `x % 7 ≠ 4`, `p.Prime`, `17 ≤ p`, `p % 8 = 1`, `0 < y`, `x.Coprime y`, `x ^ p + 1 = 2 * y ^ 2`.
2. **Conditional closure of ALL of Subcase A (`(q^d + 1)/2 = □`) across ALL of `A_GT1`:**
   Define `PrimePowerFermatObstruction : Prop := ∀ x p y : ℕ, IsPrimePow x → x % 16 = 1 → x % 7 ≠ 2 → x % 7 ≠ 4 → p.Prime → 17 ≤ p → p % 8 = 1 → 0 < y → x.Coprime y → x ^ p + 1 ≠ 2 * y ^ 2` (externally proved by Ivorra 2003, Thm. 2(b) and Bennett–Skinner 2004, Prop. 8.1; modular methods absent from pinned Mathlib).
   - `PrimePowerFermatObstruction → ExceptionalFermatObstruction` (immediate from `hq.isPrimePow`).
   - Under `PrimePowerFermatObstruction`, for EVERY odd perfect number in `A_GT1`: **`¬ IsSquare ((q^d + 1) / 2)`**, hence **`2 ≤ (oddValuationPrimes I).card`** (unifying `IQ_SQUARE`, `IQ_PRIME_SQUARE`, and the entire Subcase A half of `IQ_MULTI` under one premise!).
3. **Unconditional Subcase B (`(oddValuationPrimes I).card = 2`, `¬ IsSquare ((q^d + 1) / 2)`) composite-`d` reduction:**
   Since `(oddValuationPrimes I).card = (oddValuationPrimes (geometricBlock q d)).card + (oddValuationPrimes ((q^d + 1)/2)).card` (`HalfLengthSupport.lean`) and both summands are `≥ 1` (`geometricBlock` is non-square by `Hirakawa.lean`, and `(q^d + 1)/2` is non-square by hypothesis), both summands equal `1`.
   - From `(oddValuationPrimes (geometricBlock q d)).card = 1`, `HalfLengthSupport.lean` (`distinct_primes_length_le_odd_valuations`, `length_factor_count_le_twice_odd_valuations`, `prime_pow_length_le_odd_valuations`) gives `d.primeFactors.card = 1` and `cardFactors d ≤ 2`, so either `d.Prime` OR `d = s ^ 2` with `s.Prime`, `Odd s`, and `s ∣ q - 1`.
   - In the `d = s ^ 2` case with `s ∣ q - 1`: `q^s ≡ 1 (mod s)` and `Odd s`, so `s ∤ q^s + 1`. Write `(q^(s^2) + 1) / 2 = ((q^s + 1) / 2) * alternatingBlock (q^s) s`. By `common_prime_alternatingBlock`, any common prime divisor divides `s`, which is impossible since `s ∤ q^s + 1`; hence the two factors are **coprime**!
   - Since `alternatingBlock (q^s) s` is NOT a square (`AlternatingPell.lean`, as `q^s % 4 = 1` and `s` is odd prime), `(oddValuationPrimes (alternatingBlock (q^s) s)).card ≥ 1`. Since the sum equals `1`, **`(oddValuationPrimes ((q^s + 1) / 2)).card = 0`**, forcing **`IsSquare ((q^s + 1) / 2)`**!
   - By Part 1 applied to `(q, s)`, `IsSquare ((q^s + 1)/2)` ALREADY forces **`s ∣ q + 1`** (via `half_pow_succ_not_square_of_mod_sixteen` + `alternatingBlock_not_square` + `half_sum_not_square_of_alternatingBlock`), which directly contradicts **`s ∣ q - 1`** (`s ∣ (q + 1) - (q - 1) = 2`, impossible for odd prime `s`)!
   - Thus on Subcase B (`(oddValuationPrimes I).card = 2 ∧ ¬ IsSquare ((q^d + 1)/2)`), **`d.Prime` holds COMPLETELY UNCONDITIONALLY** (zero Fermat premise needed)!
   - Combining Part 2 + Part 3: under `PrimePowerFermatObstruction` (which eliminates Subcase A for both prime and composite `d`; `ExceptionalFermatObstruction` alone does not suffice when `IsSquare ((q^d + 1)/2)` with composite `d`), **`d.Prime`** holds for unrestricted `I = ℓ₁ ℓ₂ t²` (`(oddValuationPrimes I).card = 2`)!

**Closure argument.** Conditionally closes the entire `(q^d + 1)/2 = □` half of `A_GT1` (prime and composite `d`, unifying `IQ_SQUARE`, `IQ_PRIME_SQUARE`, and Subcase A of `IQ_MULTI`) on `PrimePowerFermatObstruction` (Ivorra 2003 / Bennett–Skinner 2004, absent from pinned Mathlib), unconditionally forces `d` prime on Subcase B of `I = ℓ₁ ℓ₂ t²`, and forces `d` prime on unrestricted `I = ℓ₁ ℓ₂ t²` under `PrimePowerFermatObstruction`.

```
G1 spoof:      PASS — uses `q.Prime`, `q % 4 = 1`, `N.Perfect`, `Hirakawa` (`geometricBlock_not_square`), and `AlternatingPell` (`alternatingBlock_not_square`). Fails on negative-base (Voight) and composite-base spoofs.
G2 count-LP:   N/A (Diophantine/structural reduction on `A_GT1`, not a count inequality).
G3 local:      PASS — `0` solutions to `(x^d + 1)/2 = y^2` for `x % 4 = 1`, `3 ≤ d ≤ 39` odd (`x ≤ 50000` at `d=3`, `x ≤ 10000` for `d ≥ 5`), and `0` counterexamples to `d = s^2` in `I = ℓ₁ ℓ₂ t²` for `s ∈ {3, 5, 7}, q < 3000` (`exp_iq_multi.py`, `exp_round2_root_s0.py`); complementary Subcase B (`d` prime) has concrete prime witnesses `(17, 13, 7)` and `(293, 5, 3)`.
G4 floor/ceil: PASS — conditional `False` on all of Subcase A across `A_GT1` + unconditional `d.Prime` on Subcase B of `I = ℓ₁ ℓ₂ t²`, isolating the exact external modular/generalized-Fermat premise.
Skeptic:       SURVIVES (separate-session pro review 2026-11-28: all Subcase A steps verified; strengthened Subcase B `d.Prime` to UNCONDITIONAL via `s ∣ q - 1` vs `s ∣ q + 1`; clarified unrestricted `I = ℓ₁ ℓ₂ t²` requires `PrimePowerFermatObstruction`, not `ExceptionalFermatObstruction`).
Closure arg:   Conditionally closes the entire (q^d + 1)/2 = □ half of A_GT1 (prime and composite d) on PrimePowerFermatObstruction (Ivorra 2003 / Bennett–Skinner 2004), unconditionally forces d prime on Subcase B of I = ℓ₁ ℓ₂ t², and forces d prime on unrestricted I = ℓ₁ ℓ₂ t² under PrimePowerFermatObstruction.
```
