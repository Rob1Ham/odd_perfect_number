module

public import OddPerfect.OchemRao
public import OddPerfect.PrimeReciprocalLog
public import OddPerfect.ZelinskyReciprocal
public import OddPerfect.SizeChain
public import OddPerfect.Primitive
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Zelinsky Slope, Quartic Component Incidence, and Logarithmic Pinch Bounds

Stepping Stone S5:
1. Sharpened Ochem–Rao linear incidence inequality retaining Euler exponent slack
   `N.factorization q - 1` and large-exponent slack `∑ r ∈ largeSources N q, (N.factorization r - 4)`.
2. Quartic component (`v_r(N) = 4`) normalized divisor sum `normalizedQuarticSum` and
   5-adic valuation incidence `quarticSourcesOne_card_le_five_exponent`.
3. Logarithmic prime-reciprocal and slope pinch bounds linking least prime factor `p`,
   `ω(N)`, `Ω(N)`, and `p ^ Ω(N) ≤ N`, including instantiations for Ochem–Rao and
   Zelinsky (2021) linear slope regimes.
-/

public section

namespace OddPerfect

open ArithmeticFunction

/-! ## 1. Sharpened Ochem–Rao Incidence Inequality with Excess Slack -/

/-- Sharpened Ochem–Rao linear incidence inequality retaining both Euler exponent slack
`(N.factorization q - 1)` and higher-exponent slack `∑ r ∈ largeSources N q, (N.factorization r - 4)`. -/
theorem ochem_rao_with_excess_slack {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    ∃ q ∈ N.primeFactors, q % 4 = 1 ∧ N.factorization q % 4 = 1 ∧
      (∀ r, r ≠ q → Even (N.factorization r)) ∧
      (3 ∣ N → 18 * N.primeFactors.card + N.factorization 3 + 5 * (N.factorization q - 1) +
        5 * (∑ r ∈ largeSources N q, (N.factorization r - 4)) ≤ 7 * N.primeFactorsList.length + 33) ∧
      (¬ 3 ∣ N → 18 * N.primeFactors.card + 5 * (N.factorization q - 1) +
        5 * (∑ r ∈ largeSources N q, (N.factorization r - 4)) ≤ 7 * N.primeFactorsList.length + 15) := by
  obtain ⟨q, hq, hq4, he, hev⟩ := euler_exponents ho hN
  refine ⟨q, hq, hq4, he, hev, ?_⟩
  have hinc := ochem_rao_incidence ho hN hq hq4 he hev
  let S := (N.primeFactors.erase q).erase 3
  have hpos {r : ℕ} (hr : r ∈ N.primeFactors) : 0 < N.factorization r :=
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr)
  have hparts : S = squareSources N ∪ largeSources N q := by
    ext r
    simp only [S, Finset.mem_erase, squareSources, largeSources, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hr3, hrq, hr⟩
      obtain ⟨k, hk⟩ := hev r hrq
      have := hpos hr
      by_cases htwo : N.factorization r = 2
      · exact Or.inl ⟨hr, hr3, htwo⟩
      · exact Or.inr ⟨hr, hr3, hrq, by omega⟩
    · rintro (⟨hr, hr3, htwo⟩ | ⟨hr, hr3, hrq, _⟩)
      · exact ⟨hr3, fun h => by subst r; omega, hr⟩
      · exact ⟨hr3, hrq, hr⟩
  have hdis : Disjoint (squareSources N) (largeSources N q) := by
    apply Finset.disjoint_left.mpr
    intro r hs hl
    have htwo := (Finset.mem_filter.mp hs).2.2
    have hlarge := (Finset.mem_filter.mp hl).2.2.2
    omega
  have hcard : S.card = (squareSources N).card + (largeSources N q).card := by
    rw [hparts, Finset.card_union_of_disjoint hdis]
  have hsum : (∑ r ∈ S, N.factorization r) =
      2 * (squareSources N).card + ∑ r ∈ largeSources N q, N.factorization r := by
    rw [hparts, Finset.sum_union hdis]
    congr 1
    calc
      _ = ∑ _r ∈ squareSources N, (2 : ℕ) :=
        Finset.sum_congr rfl fun _ hr => (Finset.mem_filter.mp hr).2.2
      _ = _ := by simp [Nat.mul_comm]
  have hlarge_eq : (∑ r ∈ largeSources N q, N.factorization r) =
      4 * (largeSources N q).card + ∑ r ∈ largeSources N q, (N.factorization r - 4) := by
    have hadd : (∑ r ∈ largeSources N q, N.factorization r) =
        ∑ r ∈ largeSources N q, (4 + (N.factorization r - 4)) := by
      refine Finset.sum_congr rfl fun r hr => ?_
      have hge4 : 4 ≤ N.factorization r := (Finset.mem_filter.mp hr).2.2.2
      omega
    rw [hadd, Finset.sum_add_distrib]
    simp [Nat.mul_comm]
  have htot : N.primeFactorsList.length =
      N.factorization q + ∑ r ∈ N.primeFactors.erase q, N.factorization r := by
    rw [← cardFactors_apply, cardFactors_eq_sum_factorization]
    exact (Finset.add_sum_erase N.primeFactors _ hq).symm
  have hqcount := Finset.card_erase_add_one hq
  have hbound := squareSourcesOne_card_le_three_exponent hN
  by_cases h3 : 3 ∈ N.primeFactors
  · have h3q : 3 ≠ q := by omega
    have h3mem := Finset.mem_erase.mpr ⟨h3q, h3⟩
    have h3card : S.card + 1 = (N.primeFactors.erase q).card := Finset.card_erase_add_one h3mem
    have h3sum : N.factorization 3 + (∑ r ∈ S, N.factorization r) =
        ∑ r ∈ N.primeFactors.erase q, N.factorization r :=
      Finset.add_sum_erase _ _ h3mem
    have := hpos h3
    obtain ⟨k, hk⟩ := hev 3 h3q
    exact ⟨fun _ => by omega, fun hd => (hd (Nat.dvd_of_mem_primeFactors h3)).elim⟩
  · have h3zero : N.factorization 3 = 0 := Finsupp.notMem_support_iff.mp h3
    have h3erase : S = N.primeFactors.erase q :=
      Finset.erase_eq_of_notMem fun h => h3 (Finset.mem_of_mem_erase h)
    rw [← h3erase] at htot hqcount
    exact ⟨fun hd => (h3 (Nat.mem_primeFactors.mpr ⟨by decide, hd, hN.2.ne'⟩)).elim,
      fun _ => by omega⟩

/-! ## 2. Quartic Component Normalized Sum & 5-Adic Incidence -/

/-- The quartic divisor sum `u^4 + u^3 + u^2 + u + 1` with its factor of 5 removed
when `u ≡ 1 [MOD 5]`. -/
@[expose] def normalizedQuarticSum (u : ℕ) : ℕ :=
  if u % 5 = 1 then (u ^ 4 + u ^ 3 + u ^ 2 + u + 1) / 5 else u ^ 4 + u ^ 3 + u ^ 2 + u + 1

/-- Non-Euler primes with exact exponent 4 that are congruent to 1 modulo 5. -/
@[expose] def quarticSourcesOne (N q : ℕ) : Finset ℕ :=
  (N.primeFactors.erase q).filter (fun r => N.factorization r = 4 ∧ r % 5 = 1)

private theorem quartic_at_one (k : ℕ) :
    normalizedQuarticSum (5 * k + 1) =
      125 * k ^ 4 + 125 * k ^ 3 + 50 * k ^ 2 + 10 * k + 1 := by
  rw [normalizedQuarticSum, ite_eq_left (show (5 * k + 1) % 5 = 1 by omega)]
  rw [show (5 * k + 1) ^ 4 + (5 * k + 1) ^ 3 + (5 * k + 1) ^ 2 + (5 * k + 1) + 1 =
      5 * (125 * k ^ 4 + 125 * k ^ 3 + 50 * k ^ 2 + 10 * k + 1) by ring]
  simp

private theorem five_mul_normalizedQuarticSum {u : ℕ} (h : u % 5 = 1) :
    5 * normalizedQuarticSum u = u ^ 4 + u ^ 3 + u ^ 2 + u + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, u = 5 * k + 1 := ⟨u / 5, by omega⟩
  rw [quartic_at_one]
  ring

private lemma geom_sum_five (r : ℕ) :
    (∑ i ∈ Finset.range 5, r ^ i) = r ^ 4 + r ^ 3 + r ^ 2 + r + 1 := by
  simp [Finset.sum_range_succ]
  ring

/-- Core arithmetic properties of `sigma 1 (r ^ 4)` and `normalizedQuarticSum r`:
1. `3 ∤ sigma 1 (r ^ 4)`
2. `normalizedQuarticSum r ∣ sigma 1 (r ^ 4)`
3. `5 ∤ normalizedQuarticSum r`
4. Every prime divisor `w` of `normalizedQuarticSum r` satisfies `w ≡ 1 [MOD 5]`. -/
theorem quartic_sigma_properties {r : ℕ} (hr : r.Prime) (_hr3 : 3 ≤ r) :
    ¬ 3 ∣ sigma 1 (r ^ 4) ∧ normalizedQuarticSum r ∣ sigma 1 (r ^ 4) ∧
      ¬ 5 ∣ normalizedQuarticSum r ∧ (∀ w, w.Prime → w ∣ normalizedQuarticSum r → w % 5 = 1) := by
  have hsig : sigma 1 (r ^ 4) = r ^ 4 + r ^ 3 + r ^ 2 + r + 1 := by
    rw [sigma_one_apply_prime_pow hr, geom_sum_five]
  have hnot3 : ¬ 3 ∣ sigma 1 (r ^ 4) := by
    rw [hsig]
    have hc : r ≡ r % 3 [MOD 3] := (Nat.mod_modEq r 3).symm
    have hpoly : r ^ 4 + r ^ 3 + r ^ 2 + r + 1 ≡
        (r % 3) ^ 4 + (r % 3) ^ 3 + (r % 3) ^ 2 + (r % 3) + 1 [MOD 3] :=
      ((((hc.pow 4).add (hc.pow 3)).add (hc.pow 2)).add hc).add (Nat.ModEq.refl 1)
    have hrem : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 := by omega
    rcases hrem with h | h | h <;> rw [h] at hpoly <;>
      change (r ^ 4 + r ^ 3 + r ^ 2 + r + 1) % 3 = _ at hpoly <;> omega
  have hdvd : normalizedQuarticSum r ∣ sigma 1 (r ^ 4) := by
    rw [hsig]
    by_cases h5 : r % 5 = 1
    · rw [← five_mul_normalizedQuarticSum h5]
      exact dvd_mul_left _ _
    · simp [normalizedQuarticSum, h5]
  have hnot5 : ¬ 5 ∣ normalizedQuarticSum r := by
    by_cases h5 : r % 5 = 1
    · have hmul : 5 * normalizedQuarticSum r = ∑ i ∈ Finset.range 5, r ^ i := by
        rw [geom_sum_five, five_mul_normalizedQuarticSum h5]
      have h5dvd : 5 ∣ ∑ i ∈ Finset.range 5, r ^ i := by
        rw [← hmul]
        exact dvd_mul_right _ _
      have h52 := not_sq_dvd_geom_sum (b := r) (l := 5) (by decide) (by decide) h5dvd
      intro hdiv
      apply h52
      rw [← hmul, pow_two]
      exact Nat.mul_dvd_mul_left 5 hdiv
    · simp only [normalizedQuarticSum, ite_eq_right h5]
      have hc : r ≡ r % 5 [MOD 5] := (Nat.mod_modEq r 5).symm
      have hpoly : r ^ 4 + r ^ 3 + r ^ 2 + r + 1 ≡
          (r % 5) ^ 4 + (r % 5) ^ 3 + (r % 5) ^ 2 + (r % 5) + 1 [MOD 5] :=
        ((((hc.pow 4).add (hc.pow 3)).add (hc.pow 2)).add hc).add (Nat.ModEq.refl 1)
      have hrem : r % 5 = 0 ∨ r % 5 = 2 ∨ r % 5 = 3 ∨ r % 5 = 4 := by omega
      rcases hrem with h | h | h | h <;> rw [h] at hpoly <;>
        change (r ^ 4 + r ^ 3 + r ^ 2 + r + 1) % 5 = _ at hpoly <;> omega
  have hw_mod : ∀ w, w.Prime → w ∣ normalizedQuarticSum r → w % 5 = 1 := by
    intro w hw hwn
    let : Fact w.Prime := ⟨hw⟩
    have hw_sig : w ∣ ∑ d ∈ (r ^ 4).divisors, d := by
      rw [← sigma_one_apply]
      exact hwn.trans hdvd
    have hiff := (dvd_sum_divisors_prime_pow_iff hr hw 4).mp hw_sig
    split_ifs at hiff with hrz
    · have hw5 : w ∣ 5 := by simpa using hiff
      have heq : w = 5 := ((Nat.dvd_prime (by decide : Nat.Prime 5)).mp hw5).resolve_left hw.ne_one
      subst heq
      exact (hnot5 hwn).elim
    · have hord_dvd : orderOf (r : ZMod w) ∣ 5 := by simpa using hiff
      rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hord_dvd with h1 | h5
      · exact (hrz (orderOf_eq_one_iff.mp h1)).elim
      · have hr_ne0 : (r : ZMod w) ≠ 0 := by
          intro hz
          rw [hz, orderOf_zero] at h5
          omega
        have hsub : orderOf (r : ZMod w) ∣ w - 1 := ZMod.orderOf_dvd_card_sub_one hr_ne0
        rw [h5] at hsub
        have hw_gt1 := hw.one_lt
        omega
  exact ⟨hnot3, hdvd, hnot5, hw_mod⟩

/-- The cardinality of quartic components `r ≠ q` with `v_r(N) = 4` and `r ≡ 1 [MOD 5]`
is bounded above by `N.factorization 5`. -/
theorem quarticSourcesOne_card_le_five_exponent {N q : ℕ} (hN : N.Perfect) :
    (quarticSourcesOne N q).card ≤ N.factorization 5 := by
  apply card_le_factorization_of_sigma_sources hN (by decide) (by decide)
  · exact (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
  · intro r hr
    obtain ⟨hmem, hfour, hmod⟩ := Finset.mem_filter.mp hr
    have hrp := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hmem)
    rw [hfour, sigma_one_apply_prime_pow hrp, geom_sum_five, ← five_mul_normalizedQuarticSum hmod]
    exact dvd_mul_right _ _

/-! ## 3. Logarithmic Prime-Reciprocal & Slope Pinch Bounds -/

/-- Unconditional logarithmic lower bound on `ω(N)` in terms of the least prime factor `p`:
`((p : ℝ) - 1) * Real.log 2 < ω(N)`. -/
theorem omega_gt_least_prime_mul_log_two {N p : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hp : p ∈ N.primeFactors) (hmin : ∀ s ∈ N.primeFactors, p ≤ s) :
    ((p : ℝ) - 1) * Real.log 2 < (N.primeFactors.card : ℝ) := by
  have hp_prime := Nat.prime_of_mem_primeFactors hp
  have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp_prime.one_lt
  have hp_sub_pos : (0 : ℝ) < (p : ℝ) - 1 := sub_pos.mpr hp_gt1
  have hlog := log_two_lt_sum_inv_primeFactors_sub_one ho hN
  have hsum_le : (∑ r ∈ N.primeFactors, (1 : ℝ) / ((r : ℝ) - 1)) ≤
      (N.primeFactors.card : ℝ) / ((p : ℝ) - 1) := by
    calc
      (∑ r ∈ N.primeFactors, (1 : ℝ) / ((r : ℝ) - 1))
          ≤ ∑ _r ∈ N.primeFactors, (1 : ℝ) / ((p : ℝ) - 1) := by
            apply Finset.sum_le_sum
            intro r hr
            have hpr : (p : ℝ) ≤ (r : ℝ) := by exact_mod_cast hmin r hr
            exact div_le_div_of_nonneg_left zero_le_one hp_sub_pos (by linarith)
      _ = (N.primeFactors.card : ℝ) / ((p : ℝ) - 1) := by
            simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  have hlt : Real.log 2 < (N.primeFactors.card : ℝ) / ((p : ℝ) - 1) := lt_of_lt_of_le hlog hsum_le
  exact (lt_div_iff₀ hp_sub_pos).mp hlt |>.trans_eq' (mul_comm _ _)

/-- Any linear slope inequality `c_ω * ω(N) ≤ c_Ω * Ω(N) + c_0` together with least prime factor
`p` yields a logarithmic lower bound on `Ω(N)` and the exponential size bound `p ^ Ω(N) ≤ N`. -/
theorem total_prime_factors_and_size_of_slope_and_least_prime {N p c_ω c_Ω c_0 : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hp : p ∈ N.primeFactors)
    (hmin : ∀ s ∈ N.primeFactors, p ≤ s) (hcΩ : 0 < c_Ω)
    (hslope : c_ω * N.primeFactors.card ≤ c_Ω * N.primeFactorsList.length + c_0) :
    ((c_ω : ℝ) * ((p : ℝ) - 1) * Real.log 2 - (c_0 : ℝ)) / (c_Ω : ℝ) <
        (N.primeFactorsList.length : ℝ) ∧
      p ^ N.primeFactorsList.length ≤ N := by
  have hpow : p ^ N.primeFactorsList.length ≤ N := by
    simpa [cardFactors_apply] using FactorBudget.pow_cardFactors_le hN.2.ne' hmin
  refine ⟨?_, hpow⟩
  have hcΩ_pos : (0 : ℝ) < (c_Ω : ℝ) := by exact_mod_cast hcΩ
  have hslope_real : (c_ω : ℝ) * (N.primeFactors.card : ℝ) ≤
      (c_Ω : ℝ) * (N.primeFactorsList.length : ℝ) + (c_0 : ℝ) := by
    exact_mod_cast hslope
  rw [div_lt_iff₀ hcΩ_pos]
  rcases Nat.eq_zero_or_pos c_ω with rfl | hcω_pos
  · have hlen_pos : 0 < N.primeFactorsList.length :=
      List.length_pos_of_mem (Nat.mem_primeFactors_iff_mem_primeFactorsList.mp hp)
    have hlen_real : (0 : ℝ) < (N.primeFactorsList.length : ℝ) := by exact_mod_cast hlen_pos
    have hc0_nonneg : (0 : ℝ) ≤ (c_0 : ℝ) := Nat.cast_nonneg _
    simp only [Nat.cast_zero, zero_mul, zero_sub]
    nlinarith
  · have hcω_real : (0 : ℝ) < (c_ω : ℝ) := by exact_mod_cast hcω_pos
    have homega := omega_gt_least_prime_mul_log_two ho hN hp hmin
    have hmul : (c_ω : ℝ) * (((p : ℝ) - 1) * Real.log 2) <
        (c_ω : ℝ) * (N.primeFactors.card : ℝ) :=
      mul_lt_mul_of_pos_left homega hcω_real
    linarith

/-- Zelinsky's quadratic prime-reciprocal gap combined with the abundancy lower bound
yields the exact reciprocal-difference pinch and reciprocal-sum decomposition. -/
theorem zelinsky_reciprocal_omega_lower_bound {N p : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hp : p ∈ N.primeFactors) (hmin : ∀ s ∈ N.primeFactors, p ≤ s) (hp11 : 11 ≤ p) :
    11 / (50 * (p : ℝ) ^ 2) < (N.primeFactors.card : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ∧
      11 * ((p : ℝ) - 1) / (50 * (p : ℝ)) < (N.primeFactors.card : ℝ) ∧
      ∑ r ∈ N.primeFactors, (1 : ℝ) / ((r : ℝ) - 1) =
        (∑ r ∈ N.primeFactors, (1 : ℝ) / (r : ℝ)) +
          ∑ r ∈ N.primeFactors, (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) := by
  have hp_real : (11 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp11
  have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
  have hp_sub_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hsum_id :
      ∑ r ∈ N.primeFactors, (1 : ℝ) / ((r : ℝ) - 1) =
        (∑ r ∈ N.primeFactors, (1 : ℝ) / (r : ℝ)) +
          ∑ r ∈ N.primeFactors, (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr_ge_p : (p : ℝ) ≤ (r : ℝ) := by exact_mod_cast hmin r hr
    have hr_ne0 : (r : ℝ) ≠ 0 := by linarith
    have hr_sub_ne0 : (r : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  have hupp := zelinsky_prime_reciprocal_bound ho hN hp hmin hp11
  have hlow := log_two_lt_sum_inv_primeFactors_sub_one ho hN
  have hdiff_lt :
      11 / (50 * (p : ℝ) ^ 2) <
        ∑ r ∈ N.primeFactors, (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) := by
    linarith [hsum_id, hupp, hlow]
  have hdiff_le :
      ∑ r ∈ N.primeFactors, (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) ≤
        (N.primeFactors.card : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
    calc
      ∑ r ∈ N.primeFactors, (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1))
          ≤ ∑ _r ∈ N.primeFactors, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
            apply Finset.sum_le_sum
            intro r hr
            have hr_ge_p : (p : ℝ) ≤ (r : ℝ) := by exact_mod_cast hmin r hr
            have hprod_le : (p : ℝ) * ((p : ℝ) - 1) ≤ (r : ℝ) * ((r : ℝ) - 1) :=
              mul_le_mul hr_ge_p (by linarith) hp_sub_pos.le (by linarith)
            exact div_le_div_of_nonneg_left zero_le_one (mul_pos hp_pos hp_sub_pos) hprod_le
      _ = (N.primeFactors.card : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
            simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  have hpinch : 11 / (50 * (p : ℝ) ^ 2) < (N.primeFactors.card : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) :=
    lt_of_lt_of_le hdiff_lt hdiff_le
  have homega : 11 * ((p : ℝ) - 1) / (50 * (p : ℝ)) < (N.primeFactors.card : ℝ) := by
    have hmul := (lt_div_iff₀ (mul_pos hp_pos hp_sub_pos)).mp hpinch
    have hcalc : (11 / (50 * (p : ℝ) ^ 2)) * ((p : ℝ) * ((p : ℝ) - 1)) =
        11 * ((p : ℝ) - 1) / (50 * (p : ℝ)) := by
      field_simp
    linarith
  exact ⟨hpinch, homega, hsum_id⟩

/-- Unconditional Ochem–Rao least-prime pinch combining `ochem_rao_prime_factor_count`,
the `¬ 3 ∣ N` refinement from `ochem_rao_count_cases`, and Zelinsky's `11 ≤ p` reciprocal pinch. -/
theorem ochem_rao_least_prime_pinch {N p : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hp : p ∈ N.primeFactors) (hmin : ∀ s ∈ N.primeFactors, p ≤ s) :
    (18 * ((p : ℝ) - 1) * Real.log 2 - 31) / 7 < (N.primeFactorsList.length : ℝ) ∧
      (¬ 3 ∣ N → (18 * ((p : ℝ) - 1) * Real.log 2 - 15) / 7 < (N.primeFactorsList.length : ℝ)) ∧
      (11 ≤ p → 11 / (50 * (p : ℝ) ^ 2) < (N.primeFactors.card : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) := by
  have hmain := (total_prime_factors_and_size_of_slope_and_least_prime ho hN hp hmin
    (by decide : 0 < 7) (ochem_rao_prime_factor_count ho hN)).1
  have hno3 : ¬ 3 ∣ N →
      (18 * ((p : ℝ) - 1) * Real.log 2 - 15) / 7 < (N.primeFactorsList.length : ℝ) := by
    intro hnd
    have hslope := (ochem_rao_count_cases ho hN).2 hnd
    exact (total_prime_factors_and_size_of_slope_and_least_prime ho hN hp hmin
      (by decide : 0 < 7) hslope).1
  have hp11_bound : 11 ≤ p →
      11 / (50 * (p : ℝ) ^ 2) < (N.primeFactors.card : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
    intro hp11
    exact (zelinsky_reciprocal_omega_lower_bound ho hN hp hmin hp11).1
  refine ⟨?_, ?_, hp11_bound⟩
  · simpa using hmain
  · intro hnd
    simpa using hno3 hnd

/-- Instantiation of `total_prime_factors_and_size_of_slope_and_least_prime` for Zelinsky's
(2021) linear slope `302 * ω(N) ≤ 113 * Ω(N) + 286`. -/
theorem zelinsky_slope_302_113_envelope {N p : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hp : p ∈ N.primeFactors) (hmin : ∀ s ∈ N.primeFactors, p ≤ s)
    (hslope : 302 * N.primeFactors.card ≤ 113 * N.primeFactorsList.length + 286) :
    (302 * ((p : ℝ) - 1) * Real.log 2 - 286) / 113 < (N.primeFactorsList.length : ℝ) ∧
      p ^ N.primeFactorsList.length ≤ N := by
  simpa using total_prime_factors_and_size_of_slope_and_least_prime ho hN hp hmin (by decide) hslope

/-- Instantiation of `total_prime_factors_and_size_of_slope_and_least_prime` for Zelinsky's
(2021) linear slope `66 * ω(N) ≤ 25 * Ω(N) + 125`. -/
theorem zelinsky_slope_66_25_envelope {N p : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hp : p ∈ N.primeFactors) (hmin : ∀ s ∈ N.primeFactors, p ≤ s)
    (hslope : 66 * N.primeFactors.card ≤ 25 * N.primeFactorsList.length + 125) :
    (66 * ((p : ℝ) - 1) * Real.log 2 - 125) / 25 < (N.primeFactorsList.length : ℝ) ∧
      p ^ N.primeFactorsList.length ≤ N := by
  simpa using total_prime_factors_and_size_of_slope_and_least_prime ho hN hp hmin (by decide) hslope

end OddPerfect
