module

public import OddPerfect.GlobalWave5Obstruction
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Global Slope–Logarithmic Abundancy & Component-Index Multiplicity Pinch
(`OddPerfect.GlobalLogSlopePinch`)

Tier 2 synthesis bridging Front Alpha / Bridges `B1` & `B3`:
1. `sharpened_cyclotomic_least_prime_and_L2_pinch`: couples
   `sharpened_cyclotomic_prime_factor_count` (`21ω + 11|L₂| ≤ 8Ω + 39`) and
   `sharpened_cyclotomic_slope_three_free` (`8ω + 4|L₂| ≤ 3Ω + 7`) with
   `omega_gt_least_prime_mul_log_two` and `p ^ Ω(N) ≤ N` to obtain explicit
   least-prime and `L₂` lower bounds on `Ω(N)` and `Real.log N`.
2. `three_free_uncond_five_log_slope_pinch`: couples
   `zelinsky_and_clayton_hansen_three_free_uncond_five` (no `¬ 5 ∣ N` hypothesis)
   with `omega_gt_least_prime_mul_log_two`, `zelinsky_reciprocal_omega_lower_bound`,
   and `Real.log_two_gt_d9` to derive `1199/447`, `401/149`, `302/113`, and `51/19`
   logarithmic least-prime bounds on `Ω(N)` and `Real.log N`.
3. `componentIndex_min_multiplicity_bounds_rank_and_least_prime`: bridges `B3 → B1`
   via `prime_count_le_of_component_index_factors` and `sum_cardFactors_componentIndex`,
   proving `ω(N) ≤ 4 * K + 4` and `((N.minFac : ℝ) - 1) * Real.log 2 < 4 * K + 4`
   for any `p ∈ N.primeFactors` with `Ω(i_p) ≤ K`, the existence of a component with
   `ω(N) * Ω(i_p) ≤ (ω(N) - 1) + (ω(N) - 2) * Ω(N)`, and the `B3`-coupled
   `sharpened_cyclotomic_prime_factor_count` inequality.
4. `global_avg_component_capture_lower_bound`: derives the exact global component
   capture sum `∑ p ∈ N.primeFactors, (v_p(N) + Ω(σ(p^{v_p(N)}))) = 2 * Ω(N) + 1`
   and couples it with `sharpened_cyclotomic_prime_factor_count` (and
   `sharpened_cyclotomic_slope_three_free`) for explicit average-capture bounds
   exceeding `21/4` asymptotically (`16/3` when `¬ 3 ∣ N`).
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private theorem minFac_mem_primeFactors_and_le {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    N.minFac ∈ N.primeFactors ∧ (∀ s ∈ N.primeFactors, N.minFac ≤ s) ∧ 3 ≤ N.minFac := by
  have h5 := five_le_distinct_prime_factor_count ho hN
  have hN1 : N ≠ 1 := by
    rintro rfl
    simp at h5
  have hp_prime : N.minFac.Prime := Nat.minFac_prime hN1
  have hp_mem : N.minFac ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp_prime, Nat.minFac_dvd N, hN.2.ne'⟩
  have hmin : ∀ s ∈ N.primeFactors, N.minFac ≤ s := fun s hs =>
    Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hs).two_le
      (Nat.dvd_of_mem_primeFactors hs)
  have hodd_p : Odd N.minFac := ho.of_dvd_nat (Nat.minFac_dvd N)
  have h2 := hp_prime.two_le
  have hne2 : N.minFac ≠ 2 := fun h => hodd_p.not_two_dvd_nat (h ▸ dvd_rfl)
  exact ⟨hp_mem, hmin, by omega⟩

private theorem real_log_bound_of_cardFactors_gt {N p : ℕ} {L : ℝ}
    (hp1 : 1 < p) (hpow : p ^ cardFactors N ≤ N) (hL : L < (cardFactors N : ℝ)) :
    L * Real.log (p : ℝ) < Real.log (N : ℝ) := by
  have hp_real : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp1
  have hlog_pos : 0 < Real.log (p : ℝ) := Real.log_pos hp_real
  have hpow_pos : (0 : ℝ) < ((p : ℝ) ^ cardFactors N) := by positivity
  have hpow_real : ((p : ℝ) ^ cardFactors N) ≤ (N : ℝ) := by exact_mod_cast hpow
  have hlog_le : (cardFactors N : ℝ) * Real.log (p : ℝ) ≤ Real.log (N : ℝ) := by
    rw [← Real.log_pow (p : ℝ) (cardFactors N)]
    exact Real.log_le_log hpow_pos hpow_real
  have hmul : L * Real.log (p : ℝ) < (cardFactors N : ℝ) * Real.log (p : ℝ) :=
    mul_lt_mul_of_pos_right hL hlog_pos
  linarith

private theorem cardFactors_gt_of_weighted_slope_and_least_prime
    {N p c_ω c_L M c_Ω c_0 : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hp : p ∈ N.primeFactors) (hmin : ∀ s ∈ N.primeFactors, p ≤ s)
    (hcω : 0 < c_ω) (hcΩ : 0 < c_Ω)
    (hslope : c_ω * N.primeFactors.card + c_L * M ≤ c_Ω * cardFactors N + c_0) :
    ((c_ω : ℝ) * ((p : ℝ) - 1) * Real.log 2 + (c_L : ℝ) * (M : ℝ) - (c_0 : ℝ)) / (c_Ω : ℝ) <
        (cardFactors N : ℝ) ∧
      p ^ cardFactors N ≤ N := by
  have hpow : p ^ cardFactors N ≤ N := FactorBudget.pow_cardFactors_le hN.2.ne' hmin
  refine ⟨?_, hpow⟩
  have hcΩ_pos : (0 : ℝ) < (c_Ω : ℝ) := by exact_mod_cast hcΩ
  have hcω_pos : (0 : ℝ) < (c_ω : ℝ) := by exact_mod_cast hcω
  have hslope_real :
      (c_ω : ℝ) * (N.primeFactors.card : ℝ) + (c_L : ℝ) * (M : ℝ) ≤
        (c_Ω : ℝ) * (cardFactors N : ℝ) + (c_0 : ℝ) := by
    exact_mod_cast hslope
  have homega := omega_gt_least_prime_mul_log_two ho hN hp hmin
  have hmul : (c_ω : ℝ) * (((p : ℝ) - 1) * Real.log 2) <
      (c_ω : ℝ) * (N.primeFactors.card : ℝ) :=
    mul_lt_mul_of_pos_left homega hcω_pos
  rw [div_lt_iff₀ hcΩ_pos]
  linarith

/-- Coupled `21/8` (unconditional) and `8/3` (`¬ 3 ∣ N`) cyclotomic least-prime and
`twoModThreeLargeSources` lower bounds on `Ω(N)` and `Real.log N`. -/
theorem sharpened_cyclotomic_least_prime_and_L2_pinch {N q : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) :
    (21 * ((N.minFac : ℝ) - 1) * Real.log 2 +
        11 * ((twoModThreeLargeSources N q).card : ℝ) - 39) / 8 < (cardFactors N : ℝ) ∧
      ((21 * ((N.minFac : ℝ) - 1) * Real.log 2 +
          11 * ((twoModThreeLargeSources N q).card : ℝ) - 39) / 8) *
          Real.log (N.minFac : ℝ) < Real.log (N : ℝ) ∧
      (¬ 3 ∣ N →
        (8 * ((N.minFac : ℝ) - 1) * Real.log 2 +
            4 * ((twoModThreeLargeSources N q).card : ℝ) - 7) / 3 < (cardFactors N : ℝ) ∧
          ((8 * ((N.minFac : ℝ) - 1) * Real.log 2 +
              4 * ((twoModThreeLargeSources N q).card : ℝ) - 7) / 3) *
              Real.log (N.minFac : ℝ) < Real.log (N : ℝ)) ∧
      N.minFac ^ cardFactors N ≤ N := by
  obtain ⟨hp_mem, hmin, hp3⟩ := minFac_mem_primeFactors_and_le ho hN
  have hp1 : 1 < N.minFac := by omega
  have h21 : 21 * N.primeFactors.card + 11 * (twoModThreeLargeSources N q).card ≤
      8 * cardFactors N + 39 := by
    simpa [cardFactors_apply] using sharpened_cyclotomic_prime_factor_count ho hN hq hq4 he hev
  obtain ⟨hΩ_uncond, hpow⟩ := cardFactors_gt_of_weighted_slope_and_least_prime ho hN hp_mem hmin
    (by decide : 0 < 21) (by decide : 0 < 8) h21
  have hlog_uncond := real_log_bound_of_cardFactors_gt hp1 hpow hΩ_uncond
  refine ⟨by simpa using hΩ_uncond, by simpa using hlog_uncond, ?_, hpow⟩
  intro h3
  have h8 : 8 * N.primeFactors.card + 4 * (twoModThreeLargeSources N q).card ≤
      3 * cardFactors N + 7 := by
    simpa [cardFactors_apply] using (sharpened_cyclotomic_slope_three_free ho hN hq hq4 he hev h3).2
  obtain ⟨hΩ_3, _⟩ := cardFactors_gt_of_weighted_slope_and_least_prime ho hN hp_mem hmin
    (by decide : 0 < 8) (by decide : 0 < 3) h8
  have hlog_3 := real_log_bound_of_cardFactors_gt hp1 hpow hΩ_3
  exact ⟨by simpa using hΩ_3, by simpa using hlog_3⟩

private theorem log_two_gt_0693 : (0.693 : ℝ) < Real.log 2 := by
  have hy0 : (0 : ℝ) ≤ 0.693 := by norm_num
  have hy1 : (0.693 : ℝ) ≤ 1 := by norm_num
  have h := Real.exp_bound' hy0 hy1 (n := 5) (by decide)
  have hsum : (∑ m ∈ Finset.range 5, (0.693 : ℝ) ^ m / m.factorial) =
      1 + 0.693 + 0.693 ^ 2 / 2 + 0.693 ^ 3 / 6 + 0.693 ^ 4 / 24 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at h
  have hexp : Real.exp (0.693 : ℝ) < 2 := by
    have htail : (0.693 : ℝ) ^ 5 * ((5 : ℕ) + 1) / ((5 : ℕ).factorial * (5 : ℕ)) <
        2 - (1 + 0.693 + 0.693 ^ 2 / 2 + 0.693 ^ 3 / 6 + 0.693 ^ 4 / 24) := by
      norm_num [Nat.factorial]
    linarith
  have hlog : Real.log (Real.exp (0.693 : ℝ)) < Real.log 2 :=
    Real.log_lt_log (Real.exp_pos _) hexp
  rwa [Real.log_exp] at hlog

/-- `5`-unconditional `3`-free logarithmic least-prime slope pinches coupling
`zelinsky_and_clayton_hansen_three_free_uncond_five`, `omega_gt_least_prime_mul_log_two`,
and `zelinsky_reciprocal_omega_lower_bound` without assuming `¬ 5 ∣ N`. -/
theorem three_free_uncond_five_log_slope_pinch {N : ℕ} (ho : Odd N) (hN : N.Perfect)
    (h3 : ¬ 3 ∣ N) :
    (6 * ((squareSources N).filter (· % 5 = 1)).card ≤ N.primeFactors.card →
      (1199 * ((N.minFac : ℝ) - 1) * Real.log 2 - 3297) / 447 < (cardFactors N : ℝ) ∧
      ((1199 * ((N.minFac : ℝ) - 1) * Real.log 2 - 3297) / 447) *
          Real.log (N.minFac : ℝ) < Real.log (N : ℝ) ∧
      (497 ≤ N.primeFactors.card ∨ 718 ≤ N.minFac →
        (302 * ((N.minFac : ℝ) - 1) * Real.log 2 - 286) / 113 < (cardFactors N : ℝ) ∧
        ((302 * ((N.minFac : ℝ) - 1) * Real.log 2 - 286) / 113) *
            Real.log (N.minFac : ℝ) < Real.log (N : ℝ))) ∧
    (7 * ((squareSources N).filter (· % 5 = 1)).card ≤ N.primeFactors.card →
      (401 * ((N.minFac : ℝ) - 1) * Real.log 2 - 1099) / 149 < (cardFactors N : ℝ) ∧
      ((401 * ((N.minFac : ℝ) - 1) * Real.log 2 - 1099) / 149) *
          Real.log (N.minFac : ℝ) < Real.log (N : ℝ) ∧
      (259 ≤ N.primeFactors.card ∨ 374 ≤ N.minFac →
        (302 * ((N.minFac : ℝ) - 1) * Real.log 2 - 286) / 113 < (cardFactors N : ℝ) ∧
        ((302 * ((N.minFac : ℝ) - 1) * Real.log 2 - 286) / 113) *
            Real.log (N.minFac : ℝ) < Real.log (N : ℝ)) ∧
      (702 ≤ N.primeFactors.card ∨ 1013 ≤ N.minFac →
        (51 * ((N.minFac : ℝ) - 1) * Real.log 2 - 46) / 19 < (cardFactors N : ℝ) ∧
        ((51 * ((N.minFac : ℝ) - 1) * Real.log 2 - 46) / 19) *
            Real.log (N.minFac : ℝ) < Real.log (N : ℝ))) ∧
    (11 ≤ N.minFac →
      11 / (50 * (N.minFac : ℝ) ^ 2) <
        (N.primeFactors.card : ℝ) / ((N.minFac : ℝ) * ((N.minFac : ℝ) - 1)) ∧
      11 * ((N.minFac : ℝ) - 1) / (50 * (N.minFac : ℝ)) < (N.primeFactors.card : ℝ)) ∧
    N.minFac ^ cardFactors N ≤ N := by
  obtain ⟨hp_mem, hmin, hp3⟩ := minFac_mem_primeFactors_and_le ho hN
  have hp1 : 1 < N.minFac := by omega
  have hpow : N.minFac ^ cardFactors N ≤ N := FactorBudget.pow_cardFactors_le hN.2.ne' hmin
  have homega := omega_gt_least_prime_mul_log_two ho hN hp_mem hmin
  have hlog2 : (0.693 : ℝ) < Real.log 2 := log_two_gt_0693
  obtain ⟨h6_slope, h7_slope⟩ := zelinsky_and_clayton_hansen_three_free_uncond_five ho hN h3
  have omega_ge_of_minFac : ∀ (k m : ℕ),
      (k : ℝ) < ((m : ℝ) - 1) * (0.693 : ℝ) → m ≤ N.minFac →
      k + 1 ≤ N.primeFactors.card := by
    intro k m hk hm
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hm_real : (m : ℝ) ≤ (N.minFac : ℝ) := by exact_mod_cast hm
    have hm_sub_pos : (0 : ℝ) ≤ (m : ℝ) - 1 := by nlinarith
    have h1 : ((m : ℝ) - 1) * (0.693 : ℝ) ≤ ((N.minFac : ℝ) - 1) * Real.log 2 :=
      mul_le_mul (by linarith) hlog2.le (by norm_num) (by linarith)
    have hlt_real : (k : ℝ) < (N.primeFactors.card : ℝ) := by linarith
    have hlt_nat : k < N.primeFactors.card := by exact_mod_cast hlt_real
    omega
  refine ⟨?_, ?_, ?_, hpow⟩
  · intro h6
    obtain ⟨h1199, h302_497⟩ := h6_slope h6
    have h1199' : 1199 * N.primeFactors.card + 0 * 0 ≤ 447 * cardFactors N + 3297 := by
      simpa [cardFactors_apply] using h1199
    obtain ⟨hΩ_1199, _⟩ := cardFactors_gt_of_weighted_slope_and_least_prime ho hN hp_mem hmin
      (by decide : 0 < 1199) (by decide : 0 < 447) h1199'
    have hlog_1199 := real_log_bound_of_cardFactors_gt hp1 hpow hΩ_1199
    refine ⟨by simpa using hΩ_1199, by simpa using hlog_1199, ?_⟩
    intro hcond
    have h497 : 497 ≤ N.primeFactors.card := by
      rcases hcond with hω | hm
      · exact hω
      · exact omega_ge_of_minFac 496 718 (by norm_num) hm
    have h302' : 302 * N.primeFactors.card + 0 * 0 ≤ 113 * cardFactors N + 286 := by
      simpa [cardFactors_apply] using h302_497 h497
    obtain ⟨hΩ_302, _⟩ := cardFactors_gt_of_weighted_slope_and_least_prime ho hN hp_mem hmin
      (by decide : 0 < 302) (by decide : 0 < 113) h302'
    have hlog_302 := real_log_bound_of_cardFactors_gt hp1 hpow hΩ_302
    exact ⟨by simpa using hΩ_302, by simpa using hlog_302⟩
  · intro h7
    obtain ⟨h401, h302_259, h51_702⟩ := h7_slope h7
    have h401' : 401 * N.primeFactors.card + 0 * 0 ≤ 149 * cardFactors N + 1099 := by
      simpa [cardFactors_apply] using h401
    obtain ⟨hΩ_401, _⟩ := cardFactors_gt_of_weighted_slope_and_least_prime ho hN hp_mem hmin
      (by decide : 0 < 401) (by decide : 0 < 149) h401'
    have hlog_401 := real_log_bound_of_cardFactors_gt hp1 hpow hΩ_401
    refine ⟨by simpa using hΩ_401, by simpa using hlog_401, ?_, ?_⟩
    · intro hcond
      have h259 : 259 ≤ N.primeFactors.card := by
        rcases hcond with hω | hm
        · exact hω
        · exact omega_ge_of_minFac 258 374 (by norm_num) hm
      have h302' : 302 * N.primeFactors.card + 0 * 0 ≤ 113 * cardFactors N + 286 := by
        simpa [cardFactors_apply] using h302_259 h259
      obtain ⟨hΩ_302, _⟩ := cardFactors_gt_of_weighted_slope_and_least_prime ho hN hp_mem hmin
        (by decide : 0 < 302) (by decide : 0 < 113) h302'
      have hlog_302 := real_log_bound_of_cardFactors_gt hp1 hpow hΩ_302
      exact ⟨by simpa using hΩ_302, by simpa using hlog_302⟩
    · intro hcond
      have h702 : 702 ≤ N.primeFactors.card := by
        rcases hcond with hω | hm
        · exact hω
        · exact omega_ge_of_minFac 701 1013 (by norm_num) hm
      have h51' : 51 * N.primeFactors.card + 0 * 0 ≤ 19 * cardFactors N + 46 := by
        simpa [cardFactors_apply] using h51_702 h702
      obtain ⟨hΩ_51, _⟩ := cardFactors_gt_of_weighted_slope_and_least_prime ho hN hp_mem hmin
        (by decide : 0 < 51) (by decide : 0 < 19) h51'
      have hlog_51 := real_log_bound_of_cardFactors_gt hp1 hpow hΩ_51
      exact ⟨by simpa using hΩ_51, by simpa using hlog_51⟩
  · intro hp11
    have hz := zelinsky_reciprocal_omega_lower_bound ho hN hp_mem hmin hp11
    exact ⟨hz.1, hz.2.1⟩

/-- Bridge `B3 → B1 → least-prime pinch`:
1. Any component `p ∈ N.primeFactors` with `Ω(i_p) ≤ K` bounds `ω(N) ≤ 4 * K + 4`
   and `((N.minFac : ℝ) - 1) * Real.log 2 < (4 * K + 4 : ℝ)`.
2. At least one prime factor `p ∈ N.primeFactors` satisfies
   `ω(N) * Ω(i_p) ≤ (ω(N) - 1) + (ω(N) - 2) * Ω(N)`.
3. For every `p ∈ N.primeFactors`, `sharpened_cyclotomic_prime_factor_count` (and its
   `3`-free refinement) transfers directly to `Ω(i_p) + v_p(N) + Ω(σ(p^{v_p(N)}))`. -/
theorem componentIndex_min_multiplicity_bounds_rank_and_least_prime {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) :
    (∀ p ∈ N.primeFactors, ∀ K : ℕ, cardFactors (componentIndex N p) ≤ K →
      N.primeFactors.card ≤
          2 * ((componentIndex N p).primeFactors.card + cardFactors (componentIndex N p)) + 4 ∧
        N.primeFactors.card ≤ 4 * K + 4 ∧
        ((N.minFac : ℝ) - 1) * Real.log 2 < (4 * K + 4 : ℝ) ∧
        (N.minFac : ℝ) * Real.log 2 < (4 * K + 4 : ℝ) + Real.log 2) ∧
    (∃ p ∈ N.primeFactors,
      N.primeFactors.card * cardFactors (componentIndex N p) ≤
        (N.primeFactors.card - 1) + (N.primeFactors.card - 2) * cardFactors N) ∧
    (∀ q ∈ N.primeFactors, q % 4 = 1 → N.factorization q % 4 = 1 →
      (∀ r : ℕ, r ≠ q → Even (N.factorization r)) →
      ∀ p ∈ N.primeFactors,
        21 * N.primeFactors.card + 11 * (twoModThreeLargeSources N q).card ≤
          8 * (cardFactors (componentIndex N p) + N.factorization p +
            cardFactors (sigma 1 (ordProj[p] N))) + 31 ∧
        (¬ 3 ∣ N →
          8 * N.primeFactors.card + 4 * (twoModThreeLargeSources N q).card ≤
            3 * (cardFactors (componentIndex N p) + N.factorization p +
              cardFactors (sigma 1 (ordProj[p] N))) + 4)) := by
  obtain ⟨hp_mem, hmin, _⟩ := minFac_mem_primeFactors_and_le ho hN
  have homega := omega_gt_least_prime_mul_log_two ho hN hp_mem hmin
  refine ⟨?_, ?_, ?_⟩
  · intro p hp K hK
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have ha_pos : 0 < N.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
    have hNb : N = p ^ N.factorization p * ordCompl[p] N :=
      (Nat.ordProj_mul_ordCompl_eq_self N p).symm
    have hpb : ¬ p ∣ ordCompl[p] N := Nat.not_dvd_ordCompl hp_prime hN.2.ne'
    obtain ⟨i, _, hleft, hright, _⟩ := exists_component_index hN hp_prime hNb hpb
    have hci : componentIndex N p = i := by
      rw [componentIndex, hleft]
      exact Nat.mul_div_cancel_left i (pow_pos hp_prime.pos _)
    have hrank := prime_count_le_of_component_index_factors hN ho hp_prime ha_pos hNb hpb hleft hright
    rw [← hci] at hrank
    have hdist : (componentIndex N p).primeFactors.card ≤ cardFactors (componentIndex N p) := by
      rw [← cardDistinctFactors_eq_card_primeFactors,
        cardDistinctFactors_eq_length_dedup_primeFactorsList, cardFactors_apply]
      exact (componentIndex N p).primeFactorsList.dedup_sublist.length_le
    have h4K : N.primeFactors.card ≤ 4 * K + 4 := by omega
    have h4K_real : (N.primeFactors.card : ℝ) ≤ (4 * K + 4 : ℝ) := by exact_mod_cast h4K
    have hlt_min : ((N.minFac : ℝ) - 1) * Real.log 2 < (4 * K + 4 : ℝ) := by linarith
    have hlt_min' : (N.minFac : ℝ) * Real.log 2 < (4 * K + 4 : ℝ) + Real.log 2 := by linarith
    exact ⟨hrank, h4K, hlt_min, hlt_min'⟩
  · have hne : N.primeFactors.Nonempty := by
      have h5 := five_le_distinct_prime_factor_count ho hN
      exact Finset.card_pos.mp (by omega)
    obtain ⟨p, hp_mem', hp_min⟩ :=
      Finset.exists_min_image N.primeFactors (fun r => cardFactors (componentIndex N r)) hne
    refine ⟨p, hp_mem', ?_⟩
    calc
      N.primeFactors.card * cardFactors (componentIndex N p)
          = ∑ _r ∈ N.primeFactors, cardFactors (componentIndex N p) := by
            simp [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ r ∈ N.primeFactors, cardFactors (componentIndex N r) :=
            Finset.sum_le_sum fun r hr => hp_min r hr
      _ = (N.primeFactors.card - 1) + (N.primeFactors.card - 2) * cardFactors N :=
            sum_cardFactors_componentIndex ho hN
  · intro q hq hq4 he hev p hp
    have hcons := cardFactors_componentIndex_add_eq hN hp
    have h21 : 21 * N.primeFactors.card + 11 * (twoModThreeLargeSources N q).card ≤
        8 * cardFactors N + 39 := by
      simpa [cardFactors_apply] using sharpened_cyclotomic_prime_factor_count ho hN hq hq4 he hev
    refine ⟨by omega, ?_⟩
    intro h3
    have h8 : 8 * N.primeFactors.card + 4 * (twoModThreeLargeSources N q).card ≤
        3 * cardFactors N + 7 := by
      simpa [cardFactors_apply] using
        (sharpened_cyclotomic_slope_three_free ho hN hq hq4 he hev h3).2
    omega

/-- Exact global component-capture sum derived from `cardFactors_componentIndex_add_eq`
and `sum_cardFactors_componentIndex`:
`∑ p ∈ N.primeFactors, (v_p(N) + Ω(σ(p^{v_p(N)}))) = 2 * Ω(N) + 1`. -/
theorem sum_component_capture_eq_two_mul_cardFactors_add_one {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) :
    (∑ p ∈ N.primeFactors, (N.factorization p + cardFactors (sigma 1 (ordProj[p] N)))) =
      2 * cardFactors N + 1 := by
  have hω : 5 ≤ N.primeFactors.card := five_le_distinct_prime_factor_count ho hN
  have hsum_add :
      (∑ p ∈ N.primeFactors, cardFactors (componentIndex N p)) +
        (∑ p ∈ N.primeFactors, (N.factorization p + cardFactors (sigma 1 (ordProj[p] N)))) =
      N.primeFactors.card * (1 + cardFactors N) := by
    rw [← Finset.sum_add_distrib]
    calc
      ∑ p ∈ N.primeFactors,
          (cardFactors (componentIndex N p) +
            (N.factorization p + cardFactors (sigma 1 (ordProj[p] N))))
          = ∑ _p ∈ N.primeFactors, (1 + cardFactors N) := by
            refine Finset.sum_congr rfl fun p hp => ?_
            have hcons := cardFactors_componentIndex_add_eq hN hp
            omega
      _ = N.primeFactors.card * (1 + cardFactors N) := by
            simp [Finset.sum_const, smul_eq_mul]
  rw [sum_cardFactors_componentIndex ho hN] at hsum_add
  zify [show 1 ≤ N.primeFactors.card by omega, show 2 ≤ N.primeFactors.card by omega] at hsum_add ⊢
  nlinarith

/-- Global average component-capture lower bound coupling
`sum_component_capture_eq_two_mul_cardFactors_add_one` with `sharpened_cyclotomic_prime_factor_count`
and `sharpened_cyclotomic_slope_three_free`: the average capture per prime component
`(2 * Ω(N) + 1) / ω(N)` exceeds `21/4` asymptotically (and `16/3` when `¬ 3 ∣ N`). -/
theorem global_avg_component_capture_lower_bound {N q : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) :
    (∑ p ∈ N.primeFactors, (N.factorization p + cardFactors (sigma 1 (ordProj[p] N)))) =
        2 * cardFactors N + 1 ∧
      21 * N.primeFactors.card + 11 * (twoModThreeLargeSources N q).card ≤
        4 * (∑ p ∈ N.primeFactors, (N.factorization p + cardFactors (sigma 1 (ordProj[p] N)))) +
          35 ∧
      (21 : ℝ) / 4 + 11 * ((twoModThreeLargeSources N q).card : ℝ) /
          (4 * (N.primeFactors.card : ℝ)) - 35 / (4 * (N.primeFactors.card : ℝ)) ≤
        ((∑ p ∈ N.primeFactors,
          (N.factorization p + cardFactors (sigma 1 (ordProj[p] N))) : ℕ) : ℝ) /
          (N.primeFactors.card : ℝ) ∧
      (¬ 3 ∣ N →
        16 * N.primeFactors.card + 8 * (twoModThreeLargeSources N q).card ≤
          3 * (∑ p ∈ N.primeFactors, (N.factorization p + cardFactors (sigma 1 (ordProj[p] N)))) +
            11 ∧
        (16 : ℝ) / 3 + 8 * ((twoModThreeLargeSources N q).card : ℝ) /
            (3 * (N.primeFactors.card : ℝ)) - 11 / (3 * (N.primeFactors.card : ℝ)) ≤
          ((∑ p ∈ N.primeFactors,
            (N.factorization p + cardFactors (sigma 1 (ordProj[p] N))) : ℕ) : ℝ) /
            (N.primeFactors.card : ℝ)) := by
  have hcap := sum_component_capture_eq_two_mul_cardFactors_add_one ho hN
  have h21 : 21 * N.primeFactors.card + 11 * (twoModThreeLargeSources N q).card ≤
      8 * cardFactors N + 39 := by
    simpa [cardFactors_apply] using sharpened_cyclotomic_prime_factor_count ho hN hq hq4 he hev
  have hω_pos : (0 : ℝ) < (N.primeFactors.card : ℝ) := by
    have h5 := five_le_distinct_prime_factor_count ho hN
    exact_mod_cast (by omega : 0 < N.primeFactors.card)
  have h21_cap : 21 * N.primeFactors.card + 11 * (twoModThreeLargeSources N q).card ≤
      4 * (∑ p ∈ N.primeFactors, (N.factorization p + cardFactors (sigma 1 (ordProj[p] N)))) + 35 := by
    omega
  have h21_real :
      (21 : ℝ) * (N.primeFactors.card : ℝ) + 11 * ((twoModThreeLargeSources N q).card : ℝ) ≤
        4 * ((∑ p ∈ N.primeFactors,
          (N.factorization p + cardFactors (sigma 1 (ordProj[p] N))) : ℕ) : ℝ) + 35 := by
    exact_mod_cast h21_cap
  have havg_uncond :
      (21 : ℝ) / 4 + 11 * ((twoModThreeLargeSources N q).card : ℝ) /
          (4 * (N.primeFactors.card : ℝ)) - 35 / (4 * (N.primeFactors.card : ℝ)) ≤
        ((∑ p ∈ N.primeFactors,
          (N.factorization p + cardFactors (sigma 1 (ordProj[p] N))) : ℕ) : ℝ) /
          (N.primeFactors.card : ℝ) := by
    have h4ω : 0 < 4 * (N.primeFactors.card : ℝ) := by linarith
    rw [le_div_iff₀ hω_pos]
    have hmul := (div_le_div_iff_of_pos_right h4ω).mp
      (show (21 * (N.primeFactors.card : ℝ) + 11 * ((twoModThreeLargeSources N q).card : ℝ) - 35) /
          (4 * (N.primeFactors.card : ℝ)) ≤
        (4 * ((∑ p ∈ N.primeFactors,
          (N.factorization p + cardFactors (sigma 1 (ordProj[p] N))) : ℕ) : ℝ)) /
          (4 * (N.primeFactors.card : ℝ)) by
        exact div_le_div_of_nonneg_right (by linarith) h4ω.le)
    have hdiv :
        (21 * (N.primeFactors.card : ℝ) + 11 * ((twoModThreeLargeSources N q).card : ℝ) - 35) /
            (4 * (N.primeFactors.card : ℝ)) =
          21 / 4 + 11 * ((twoModThreeLargeSources N q).card : ℝ) /
            (4 * (N.primeFactors.card : ℝ)) - 35 / (4 * (N.primeFactors.card : ℝ)) := by
      field_simp
    have hrhs :
        4 * ((∑ p ∈ N.primeFactors,
          (N.factorization p + cardFactors (sigma 1 (ordProj[p] N))) : ℕ) : ℝ) /
            (4 * (N.primeFactors.card : ℝ)) =
          ((∑ p ∈ N.primeFactors,
            (N.factorization p + cardFactors (sigma 1 (ordProj[p] N))) : ℕ) : ℝ) /
            (N.primeFactors.card : ℝ) := by
      field_simp
    have hle' :
        21 / 4 + 11 * ((twoModThreeLargeSources N q).card : ℝ) /
            (4 * (N.primeFactors.card : ℝ)) - 35 / (4 * (N.primeFactors.card : ℝ)) ≤
          ((∑ p ∈ N.primeFactors,
            (N.factorization p + cardFactors (sigma 1 (ordProj[p] N))) : ℕ) : ℝ) /
            (N.primeFactors.card : ℝ) := by
      calc
        _ = (21 * (N.primeFactors.card : ℝ) +
              11 * ((twoModThreeLargeSources N q).card : ℝ) - 35) /
              (4 * (N.primeFactors.card : ℝ)) := hdiv.symm
        _ ≤ 4 * ((∑ p ∈ N.primeFactors,
              (N.factorization p + cardFactors (sigma 1 (ordProj[p] N))) : ℕ) : ℝ) /
              (4 * (N.primeFactors.card : ℝ)) := by
            exact div_le_div_of_nonneg_right (by linarith) h4ω.le
        _ = _ := hrhs
    exact (le_div_iff₀ hω_pos).mp hle'
  refine ⟨hcap, h21_cap, havg_uncond, ?_⟩
  intro h3
  have h8 : 8 * N.primeFactors.card + 4 * (twoModThreeLargeSources N q).card ≤
      3 * cardFactors N + 7 := by
    simpa [cardFactors_apply] using
      (sharpened_cyclotomic_slope_three_free ho hN hq hq4 he hev h3).2
  have h16_cap : 16 * N.primeFactors.card + 8 * (twoModThreeLargeSources N q).card ≤
      3 * (∑ p ∈ N.primeFactors, (N.factorization p + cardFactors (sigma 1 (ordProj[p] N)))) + 11 := by
    omega
  have h16_real :
      (16 : ℝ) * (N.primeFactors.card : ℝ) + 8 * ((twoModThreeLargeSources N q).card : ℝ) ≤
        3 * ((∑ p ∈ N.primeFactors,
          (N.factorization p + cardFactors (sigma 1 (ordProj[p] N))) : ℕ) : ℝ) + 11 := by
    exact_mod_cast h16_cap
  refine ⟨h16_cap, ?_⟩
  have h3ω : 0 < 3 * (N.primeFactors.card : ℝ) := by linarith
  have hdiv3 :
      (16 * (N.primeFactors.card : ℝ) + 8 * ((twoModThreeLargeSources N q).card : ℝ) - 11) /
          (3 * (N.primeFactors.card : ℝ)) =
        16 / 3 + 8 * ((twoModThreeLargeSources N q).card : ℝ) /
          (3 * (N.primeFactors.card : ℝ)) - 11 / (3 * (N.primeFactors.card : ℝ)) := by
    field_simp
  have hrhs3 :
      3 * ((∑ p ∈ N.primeFactors,
        (N.factorization p + cardFactors (sigma 1 (ordProj[p] N))) : ℕ) : ℝ) /
          (3 * (N.primeFactors.card : ℝ)) =
        ((∑ p ∈ N.primeFactors,
          (N.factorization p + cardFactors (sigma 1 (ordProj[p] N))) : ℕ) : ℝ) /
          (N.primeFactors.card : ℝ) := by
    field_simp
  calc
    (16 : ℝ) / 3 + 8 * ((twoModThreeLargeSources N q).card : ℝ) /
        (3 * (N.primeFactors.card : ℝ)) - 11 / (3 * (N.primeFactors.card : ℝ))
        = (16 * (N.primeFactors.card : ℝ) + 8 * ((twoModThreeLargeSources N q).card : ℝ) - 11) /
            (3 * (N.primeFactors.card : ℝ)) := hdiv3.symm
    _ ≤ 3 * ((∑ p ∈ N.primeFactors,
          (N.factorization p + cardFactors (sigma 1 (ordProj[p] N))) : ℕ) : ℝ) /
          (3 * (N.primeFactors.card : ℝ)) :=
        div_le_div_of_nonneg_right (by linarith) h3ω.le
    _ = ((∑ p ∈ N.primeFactors,
          (N.factorization p + cardFactors (sigma 1 (ordProj[p] N))) : ℕ) : ℝ) /
          (N.primeFactors.card : ℝ) := hrhs3

end OddPerfect
