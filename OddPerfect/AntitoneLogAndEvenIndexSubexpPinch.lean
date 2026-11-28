module

public import OddPerfect.PrimeReciprocalLog
public import OddPerfect.FactorialStirlingSupportObstruction
public import OddPerfect.PrimeFive
public import OddPerfect.SixthPowerFreeQuarticCollisionPinch
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Antitone Log-Over-Self Prime-Reciprocal Bounds and Monotone Stirling Rank Pinches

Formalizes:
1. `odd_perfect_antitone_log_div_self_prime_reciprocal_bounds`:
   Applies `Real.log_div_self_antitoneOn` on `Set.Ici (Real.exp 1)` using `Real.exp_one_lt_three < 3`
   to bound `log p / p ≤ log (N.minFac) / N.minFac ≤ log 3 / 3` for all `p ∈ N.primeFactors`,
   and combines with `sum_inv_primeFactors_lt_log_two` to yield
   `∑ p ∈ N.primeFactors, log p / p ^ 2 < (log (N.minFac) / N.minFac) * log 2 ≤ (log 3 / 3) * log 2`.
2. `odd_perfect_stirling_monotone_rank_and_sixth_power_free_bounds`:
   Deduces monotone-rank bounds `6 * K * (log (2 * K) - 1) < log 3 + 4 * log N` for all
   `1 ≤ K ≤ ω(N)`, the linear bound `6 * ω(N) < log 3 + 4 * log N`, and the sixth-power-free
   strengthening `30 * ω(N) < log 3 + 4 * log N`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- Antitone `log x / x` bounds on prime factors of an odd perfect number `N`, coupled with
`sum_inv_primeFactors_lt_log_two` to bound `∑ p ∈ N.primeFactors, log p / p ^ 2`. -/
theorem odd_perfect_antitone_log_div_self_prime_reciprocal_bounds {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) :
    (∀ p ∈ N.primeFactors,
      Real.log (p : ℝ) / (p : ℝ) ≤ Real.log (N.minFac : ℝ) / (N.minFac : ℝ) ∧
      Real.log (p : ℝ) / (p : ℝ) ≤ Real.log 3 / 3) ∧
    (∑ p ∈ N.primeFactors, Real.log (p : ℝ) / (p : ℝ) ^ 2) <
      (Real.log (N.minFac : ℝ) / (N.minFac : ℝ)) * Real.log 2 ∧
    (∑ p ∈ N.primeFactors, Real.log (p : ℝ) / (p : ℝ) ^ 2) <
      (Real.log 3 / 3) * Real.log 2 := by
  have h6 : 6 ≤ N.primeFactors.card := six_le_distinct_prime_factor_count ho hN
  have hne1 : N ≠ 1 := by
    intro h1
    subst h1
    simp at h6
  have hmin_prime : N.minFac.Prime := Nat.minFac_prime hne1
  have hmin_dvd : N.minFac ∣ N := Nat.minFac_dvd N
  have hmin_odd : Odd N.minFac := ho.of_dvd_nat hmin_dvd
  have hmin_ge3 : 3 ≤ N.minFac := by
    have h2 : 2 ≤ N.minFac := hmin_prime.two_le
    obtain ⟨k, hk⟩ := hmin_odd
    omega
  have hexp1 : Real.exp 1 < 3 := Real.exp_one_lt_three
  have h3_mem : (3 : ℝ) ∈ Set.Ici (Real.exp 1) := hexp1.le
  have hmin_real_ge3 : (3 : ℝ) ≤ (N.minFac : ℝ) := by exact_mod_cast hmin_ge3
  have hmin_mem : (N.minFac : ℝ) ∈ Set.Ici (Real.exp 1) := le_trans hexp1.le hmin_real_ge3
  have hmin_le_3 :
      Real.log (N.minFac : ℝ) / (N.minFac : ℝ) ≤ Real.log 3 / 3 :=
    Real.log_div_self_antitoneOn h3_mem hmin_mem hmin_real_ge3
  have hpt : ∀ p ∈ N.primeFactors,
      Real.log (p : ℝ) / (p : ℝ) ≤ Real.log (N.minFac : ℝ) / (N.minFac : ℝ) ∧
      Real.log (p : ℝ) / (p : ℝ) ≤ Real.log 3 / 3 := by
    intro p hp
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp_dvd : p ∣ N := Nat.dvd_of_mem_primeFactors hp
    have hmin_le_p : N.minFac ≤ p := Nat.minFac_le_of_dvd hp_prime.two_le hp_dvd
    have hp_real_ge : (N.minFac : ℝ) ≤ (p : ℝ) := by exact_mod_cast hmin_le_p
    have hp_mem : (p : ℝ) ∈ Set.Ici (Real.exp 1) := le_trans hmin_mem hp_real_ge
    have hp_le_min :
        Real.log (p : ℝ) / (p : ℝ) ≤ Real.log (N.minFac : ℝ) / (N.minFac : ℝ) :=
      Real.log_div_self_antitoneOn hmin_mem hp_mem hp_real_ge
    exact ⟨hp_le_min, hp_le_min.trans hmin_le_3⟩
  have hsum_le :
      (∑ p ∈ N.primeFactors, Real.log (p : ℝ) / (p : ℝ) ^ 2) ≤
        (Real.log (N.minFac : ℝ) / (N.minFac : ℝ)) * ∑ p ∈ N.primeFactors, (1 : ℝ) / (p : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have hp_pos : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    have hinv_nonneg : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    have hle := (hpt p hp).1
    calc
      Real.log (p : ℝ) / (p : ℝ) ^ 2
          = (Real.log (p : ℝ) / (p : ℝ)) * (1 / (p : ℝ)) := by ring
      _ ≤ (Real.log (N.minFac : ℝ) / (N.minFac : ℝ)) * (1 / (p : ℝ)) :=
          mul_le_mul_of_nonneg_right hle hinv_nonneg
  have hC_pos : 0 < Real.log (N.minFac : ℝ) / (N.minFac : ℝ) := by
    have hlog_pos : 0 < Real.log (N.minFac : ℝ) := Real.log_pos (by linarith)
    have hmin_pos : (0 : ℝ) < (N.minFac : ℝ) := by linarith
    positivity
  have hrec := sum_inv_primeFactors_lt_log_two ho hN
  have hlt_min :
      (∑ p ∈ N.primeFactors, Real.log (p : ℝ) / (p : ℝ) ^ 2) <
        (Real.log (N.minFac : ℝ) / (N.minFac : ℝ)) * Real.log 2 :=
    lt_of_le_of_lt hsum_le (mul_lt_mul_of_pos_left hrec hC_pos)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hle_three :
      (Real.log (N.minFac : ℝ) / (N.minFac : ℝ)) * Real.log 2 ≤
        (Real.log 3 / 3) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hmin_le_3 hlog2_pos.le
  exact ⟨hpt, hlt_min, lt_of_lt_of_le hlt_min hle_three⟩

/-- Monotone-rank Stirling bounds `6 * K * (log (2 * K) - 1) < log 3 + 4 * log N` for
`1 ≤ K ≤ ω(N)`, together with `6 * ω(N) < log 3 + 4 * log N` unconditionally and
`30 * ω(N) < log 3 + 4 * log N` when `N` is sixth-power-free. -/
theorem odd_perfect_stirling_monotone_rank_and_sixth_power_free_bounds {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) :
    (∀ K : ℕ, 1 ≤ K → K ≤ N.primeFactors.card →
      6 * (K : ℝ) * (Real.log (2 * (K : ℝ)) - 1) < Real.log 3 + 4 * Real.log (N : ℝ)) ∧
    6 * (N.primeFactors.card : ℝ) < Real.log 3 + 4 * Real.log (N : ℝ) ∧
    ((∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) →
      30 * (N.primeFactors.card : ℝ) < Real.log 3 + 4 * Real.log (N : ℝ)) := by
  let ω : ℝ := (N.primeFactors.card : ℝ)
  have hstirl : 6 * ω * (Real.log (2 * ω) - 1) < Real.log 3 + 4 * Real.log (N : ℝ) :=
    (odd_perfect_stirling_superlinear_log_bound ho hN).2
  have h6 : 6 ≤ N.primeFactors.card := six_le_distinct_prime_factor_count ho hN
  have hω6 : (6 : ℝ) ≤ ω := Nat.cast_le.mpr h6
  have hNpos : 0 < N := hN.2
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNpos
  have hlogN_nonneg : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hrhs_pos : 0 < Real.log 3 + 4 * Real.log (N : ℝ) := by linarith
  have hmono_rank :
      ∀ K : ℕ, 1 ≤ K → K ≤ N.primeFactors.card →
        6 * (K : ℝ) * (Real.log (2 * (K : ℝ)) - 1) < Real.log 3 + 4 * Real.log (N : ℝ) := by
    intro K hK1 hKω
    by_cases hK_one : K = 1
    · subst hK_one
      have hlog2_lt : Real.log 2 < 1 :=
        (Real.log_lt_iff_lt_exp (by norm_num)).mpr Real.exp_one_gt_two
      have hlhs_neg : 6 * ((1 : ℕ) : ℝ) * (Real.log (2 * ((1 : ℕ) : ℝ)) - 1) < 0 := by
        simp only [Nat.cast_one, mul_one]
        linarith
      exact lt_trans hlhs_neg hrhs_pos
    · have hK2 : 2 ≤ K := by omega
      have hK_real2 : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK2
      have hK_le_ω : (K : ℝ) ≤ ω := Nat.cast_le.mpr hKω
      have hexp_lt_2K : Real.exp 1 < 2 * (K : ℝ) := by
        linarith [Real.exp_one_lt_three]
      have h1_lt_log2K : 1 < Real.log (2 * (K : ℝ)) :=
        (Real.lt_log_iff_exp_lt (by linarith)).mpr hexp_lt_2K
      have hlog_le : Real.log (2 * (K : ℝ)) ≤ Real.log (2 * ω) :=
        Real.log_le_log (by linarith) (by linarith)
      have hsub_nonneg : 0 ≤ Real.log (2 * (K : ℝ)) - 1 := by linarith
      have h6K_le : 6 * (K : ℝ) ≤ 6 * ω := by linarith
      have hmul_le :
          6 * (K : ℝ) * (Real.log (2 * (K : ℝ)) - 1) ≤ 6 * ω * (Real.log (2 * ω) - 1) :=
        mul_le_mul h6K_le (by linarith) hsub_nonneg (by linarith)
      exact lt_of_le_of_lt hmul_le hstirl
  have hexp2 : Real.exp 2 < 2 * ω := by
    have h2eq : (2 : ℝ) = ((2 : ℕ) : ℝ) * 1 := by norm_num
    conv_lhs => rw [h2eq, Real.exp_nat_mul]
    have hexp1_pos : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
    have hpow : (Real.exp 1) ^ 2 < 3 ^ 2 := by
      gcongr
      exact Real.exp_one_lt_three
    linarith
  have hlog2ω_gt2 : 2 < Real.log (2 * ω) :=
    (Real.lt_log_iff_exp_lt (by linarith)).mpr hexp2
  have h6ω_lt : 6 * ω < Real.log 3 + 4 * Real.log (N : ℝ) := by
    have hmul : 6 * ω < 6 * ω * (Real.log (2 * ω) - 1) := by
      nlinarith
    exact lt_trans hmul hstirl
  have hfree_bound :
      (∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) →
        30 * ω < Real.log 3 + 4 * Real.log (N : ℝ) := by
    intro hfree
    have h443 : 443 ≤ N.primeFactors.card := by
      rcases sixth_power_or_large_support ho hN with ⟨p, hp, hpow⟩ | ⟨hcard, _, _⟩
      · exact (hfree p hp hpow).elim
      · exact hcard
    have hω443 : (443 : ℝ) ≤ ω := Nat.cast_le.mpr h443
    have hexp6 : Real.exp 6 < 2 * ω := by
      have h6eq : (6 : ℝ) = ((6 : ℕ) : ℝ) * 1 := by norm_num
      conv_lhs => rw [h6eq, Real.exp_nat_mul]
      have hexp1_pos : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
      have hpow : (Real.exp 1) ^ 6 < 3 ^ 6 := by
        gcongr
        exact Real.exp_one_lt_three
      linarith
    have hlog2ω_gt6 : 6 < Real.log (2 * ω) :=
      (Real.lt_log_iff_exp_lt (by linarith)).mpr hexp6
    have hmul : 30 * ω < 6 * ω * (Real.log (2 * ω) - 1) := by
      nlinarith
    exact lt_trans hmul hstirl
  exact ⟨hmono_rank, h6ω_lt, hfree_bound⟩

end OddPerfect
