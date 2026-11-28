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
| 8 | Separate incoming partitions by residue (and sharpen 5D ≥ 3k − 2) | A1_SPF | PROPOSED | Test coupled fine model + residue-specific quartic reuse + Ochem–Zelinsky full-factorization tracking. |
| 9 | Eliminate `r₀ ∤ m_L` (`r₀ ∣ m_R`) unconditionally across all of `A1` | A1 | DONE | Integrated and audited in `OddPerfect/LinearEulerRightSourceForcing.lean` (`linear_euler_unique_source_right_forcing`, `linear_euler_unconditional_right_source_peeling`). |
| 10 | Sharp quartic-chain target bound `5 D_all ≥ 4k − 2` via disjoint mod-5 prime images of `A(w)` and `B(w)` | A1_SPF | DONE | Integrated and audited in `OddPerfect/QuarticChainModFiveTargetReuse.lean` (`quartic_chain_mod_five_target_reuse`, `quarticChainSources_five_mul_allTargets_ge_four_mul_sub_two`); does not close `A1_SPF` or reset its pivot clock. |

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
