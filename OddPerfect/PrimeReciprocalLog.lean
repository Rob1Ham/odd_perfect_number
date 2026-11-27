module

public import OddPerfect.AbundancyLimit
public import OddPerfect.Euler
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Real-logarithmic prime-reciprocal bounds for odd perfect numbers

Unconditional bounds on `∑ p ∈ N.primeFactors, (1 : ℝ) / p` and
`∑ p ∈ N.primeFactors, (1 : ℝ) / (p - 1)` relative to `Real.log 2` for any
odd perfect number `N`.
-/

public section

namespace OddPerfect

open ArithmeticFunction

/-- Lower bound on the sum of `1 / (p - 1)` over the prime factors of an odd perfect number
via limiting abundancies and `Real.log x ≤ x - 1`. -/
theorem log_two_lt_sum_inv_primeFactors_sub_one {N : ℕ} (_ho : Odd N) (hN : N.Perfect) :
    Real.log 2 < ∑ p ∈ N.primeFactors, (1 : ℝ) / ((p : ℝ) - 1) := by
  have hq : (2 : ℚ) < ∏ p ∈ N.primeFactors, primeAbundancyLimit p :=
    two_lt_prod_primeAbundancyLimit hN
  have hr : (2 : ℝ) < ∏ p ∈ N.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
    have hcast : (2 : ℝ) < ((∏ p ∈ N.primeFactors, primeAbundancyLimit p : ℚ) : ℝ) := by
      exact_mod_cast hq
    rw [Rat.cast_prod] at hcast
    refine lt_of_lt_of_eq hcast (Finset.prod_congr rfl fun p hp => ?_)
    have hp1 : 1 < p := (Nat.prime_of_mem_primeFactors hp).one_lt
    simp only [primeAbundancyLimit, Rat.cast_div, Rat.cast_natCast]
    rw [Nat.cast_sub hp1.le, Nat.cast_one]
  have hpos : ∀ p ∈ N.primeFactors, (0 : ℝ) < (p : ℝ) / ((p : ℝ) - 1) := by
    intro p hp
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    positivity
  have hlog : Real.log 2 < Real.log (∏ p ∈ N.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) :=
    Real.log_lt_log (by norm_num) hr
  rw [Real.log_prod (fun p hp => (hpos p hp).ne')] at hlog
  refine lt_of_lt_of_le hlog (Finset.sum_le_sum fun p hp => ?_)
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have hsub : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hp1.ne'
  calc Real.log ((p : ℝ) / ((p : ℝ) - 1))
      ≤ (p : ℝ) / ((p : ℝ) - 1) - 1 := Real.log_le_sub_one_of_pos (hpos p hp)
    _ = 1 / ((p : ℝ) - 1) := by field_simp; ring

private lemma exp_le_cubic_bound {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Real.exp y ≤ 1 + y + y ^ 2 / 2 + 2 * y ^ 3 / 9 := by
  have h := Real.exp_bound' hy0 hy1 (n := 3) (by decide)
  have hsum : (∑ m ∈ Finset.range 3, y ^ m / m.factorial) = 1 + y + y ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at h
  have htail : y ^ 3 * ((3 : ℕ) + 1) / ((3 : ℕ).factorial * (3 : ℕ)) = 2 * y ^ 3 / 9 := by
    norm_num [Nat.factorial]
    ring
  linarith [h, htail]

private lemma abundancy_ge_quadratic {p e : ℕ} (hp : p.Prime) (he : 2 ≤ e) :
    1 + 1 / (p : ℝ) + 1 / (p : ℝ) ^ 2 ≤ (sigma 1 (p ^ e) : ℝ) / (p ^ e : ℝ) := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hsub : p ^ (e - 2) + p ^ (e - 1) + p ^ e ≤ sigma 1 (p ^ e) := by
    rw [sigma_one_apply_prime_pow hp]
    have hsub_mem : ({e - 2, e - 1, e} : Finset ℕ) ⊆ Finset.range (e + 1) := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
    have h12 : e - 2 ∉ ({e - 1, e} : Finset ℕ) := by simp; omega
    have h23 : e - 1 ∉ ({e} : Finset ℕ) := by simp; omega
    have hsum_sub : (∑ i ∈ ({e - 2, e - 1, e} : Finset ℕ), p ^ i) ≤
        ∑ i ∈ Finset.range (e + 1), p ^ i :=
      Finset.sum_le_sum_of_subset hsub_mem
    rw [Finset.sum_insert h12, Finset.sum_insert h23, Finset.sum_singleton] at hsum_sub
    linarith
  have hcast : (p ^ (e - 2) : ℝ) + (p ^ (e - 1) : ℝ) + (p ^ e : ℝ) ≤ (sigma 1 (p ^ e) : ℝ) := by
    exact_mod_cast hsub
  have hpe_pos : (0 : ℝ) < (p ^ e : ℝ) := by positivity
  have hdiv : ((p ^ (e - 2) : ℝ) + (p ^ (e - 1) : ℝ) + (p ^ e : ℝ)) / (p ^ e : ℝ) ≤
      (sigma 1 (p ^ e) : ℝ) / (p ^ e : ℝ) :=
    div_le_div_of_nonneg_right hcast hpe_pos.le
  have he2 : e = (e - 2) + 2 := by omega
  have he1 : e = (e - 1) + 1 := by omega
  have hpow2 : (p ^ e : ℝ) = (p ^ (e - 2) : ℝ) * (p : ℝ) ^ 2 := by
    exact_mod_cast (show p ^ e = p ^ (e - 2) * p ^ 2 by rw [← pow_add, ← he2])
  have hpow1 : (p ^ e : ℝ) = (p ^ (e - 1) : ℝ) * (p : ℝ) := by
    exact_mod_cast (show p ^ e = p ^ (e - 1) * p by
      calc p ^ e = p ^ ((e - 1) + 1) := by rw [← he1]
        _ = p ^ (e - 1) * p := pow_succ p (e - 1))
  have hpe2_ne : (p ^ (e - 2) : ℝ) ≠ 0 := by positivity
  have hpe1_ne : (p ^ (e - 1) : ℝ) ≠ 0 := by positivity
  have hpe_ne : (p ^ e : ℝ) ≠ 0 := hpe_pos.ne'
  have hid : ((p ^ (e - 2) : ℝ) + (p ^ (e - 1) : ℝ) + (p ^ e : ℝ)) / (p ^ e : ℝ) =
      1 + 1 / (p : ℝ) + 1 / (p : ℝ) ^ 2 := by
    rw [add_div, add_div, div_self hpe_ne]
    nth_rw 1 [hpow2]
    nth_rw 1 [hpow1]
    field_simp
    ring
  linarith

private lemma log_abundancy_nonspecial_bound {p e : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (he : 2 ≤ e) :
    1 / (p : ℝ) + 1 / (4 * (p : ℝ) ^ 2) <
      Real.log ((sigma 1 (p ^ e) : ℝ) / (p ^ e : ℝ)) := by
  let x : ℝ := 1 / (p : ℝ)
  have hp_real : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hx3 : x ≤ 1 / 3 := by
    dsimp [x]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  let y : ℝ := x + x ^ 2 / 4
  have hy_def : y = x + x ^ 2 / 4 := rfl
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hy1 : y ≤ 1 := by dsimp [y]; nlinarith
  have hexp : Real.exp y ≤ 1 + y + y ^ 2 / 2 + 2 * y ^ 3 / 9 := exp_le_cubic_bound hy0 hy1
  have hpoly : 1 + y + y ^ 2 / 2 + 2 * y ^ 3 / 9 < 1 + x + x ^ 2 := by
    have hy_le : y ≤ 13 / 12 * x := by rw [hy_def]; nlinarith
    have hy2 : y ^ 2 ≤ (169 / 144) * x ^ 2 := by nlinarith
    have hy3 : y ^ 3 ≤ (2197 / 5184) * x ^ 2 := by
      have h1 : y ^ 3 ≤ (13 / 12 * x) ^ 3 := pow_le_pow_left₀ hy0 hy_le 3
      have h2 : x ^ 3 ≤ (1 / 3) * x ^ 2 := by nlinarith
      nlinarith
    have hx2_pos : 0 < x ^ 2 := sq_pos_of_pos hx0
    linarith [hy_def, hy2, hy3, hx2_pos]
  have hab : 1 + x + x ^ 2 ≤ (sigma 1 (p ^ e) : ℝ) / (p ^ e : ℝ) := by
    dsimp [x]
    rw [one_div_pow]
    exact abundancy_ge_quadratic hp he
  have hsig_pos : 0 < (sigma 1 (p ^ e) : ℝ) / (p ^ e : ℝ) := by
    have h1 : (0 : ℝ) < 1 + x + x ^ 2 := by positivity
    linarith
  rw [Real.lt_log_iff_exp_lt hsig_pos]
  have hy_eq : y = 1 / (p : ℝ) + 1 / (4 * (p : ℝ) ^ 2) := by
    dsimp [y, x]
    field_simp
  rw [← hy_eq]
  linarith

private lemma log_abundancy_euler_one_bound {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) :
    1 / (q : ℝ) - 1 / (2 * (q : ℝ) ^ 2) <
      Real.log ((sigma 1 (q ^ 1) : ℝ) / (q ^ 1 : ℝ)) := by
  let x : ℝ := 1 / (q : ℝ)
  have hq_real : (5 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq5
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hx5 : x ≤ 1 / 5 := by
    dsimp [x]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  let y : ℝ := x - x ^ 2 / 2
  have hy_def : y = x - x ^ 2 / 2 := rfl
  have hy0 : 0 ≤ y := by dsimp [y]; nlinarith
  have hy1 : y ≤ 1 := by dsimp [y]; nlinarith
  have hexp : Real.exp y ≤ 1 + y + y ^ 2 / 2 + 2 * y ^ 3 / 9 := exp_le_cubic_bound hy0 hy1
  have hpoly : 1 + y + y ^ 2 / 2 + 2 * y ^ 3 / 9 < 1 + x := by
    have hdiff : (1 + x) - (1 + y + y ^ 2 / 2 + 2 * y ^ 3 / 9) =
        x ^ 3 * (5 / 18 + (5 / 24 - x / 6) * x + x ^ 3 / 36) := by
      dsimp [y]
      ring
    have hpos : 0 < x ^ 3 * (5 / 18 + (5 / 24 - x / 6) * x + x ^ 3 / 36) := by
      have hx3 : 0 < x ^ 3 := pow_pos hx0 3
      have hterm : 0 < 5 / 18 + (5 / 24 - x / 6) * x + x ^ 3 / 36 := by
        have h1 : 0 ≤ (5 / 24 - x / 6) * x := mul_nonneg (by linarith) hx0.le
        have h2 : 0 ≤ x ^ 3 / 36 := by positivity
        linarith
      exact mul_pos hx3 hterm
    linarith
  have hsig_eq : (sigma 1 (q ^ 1) : ℝ) / (q ^ 1 : ℝ) = 1 + x := by
    rw [sigma_one_apply_prime_pow hq]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one]
    push_cast
    dsimp [x]
    have hq_ne : (q : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [hsig_eq, Real.lt_log_iff_exp_lt (by positivity)]
  have hy_eq : y = 1 / (q : ℝ) - 1 / (2 * (q : ℝ) ^ 2) := by
    dsimp [y, x]
    field_simp
  rw [← hy_eq]
  linarith

/-- Unconditional strict upper bound on the sum of prime reciprocals of any odd perfect number. -/
theorem sum_inv_primeFactors_lt_log_two {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    (∑ p ∈ N.primeFactors, (1 : ℝ) / (p : ℝ)) < Real.log 2 := by
  have hn : N ≠ 0 := hN.2.ne'
  have hsig : sigma 1 N = 2 * N :=
    (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN)
  have hprod_sig : (∏ p ∈ N.primeFactors, sigma 1 (p ^ N.factorization p)) = 2 * N := by
    trans sigma 1 N
    · exact (isMultiplicative_sigma.multiplicative_factorization _ hn).symm
    · exact hsig
  have hprod_pow : (∏ p ∈ N.primeFactors, p ^ N.factorization p) = N :=
    (Nat.prod_primeFactors_pow_factorization hn).symm
  have hpos_term : ∀ p ∈ N.primeFactors,
      0 < (sigma 1 (p ^ N.factorization p) : ℝ) / (p ^ N.factorization p : ℝ) := by
    intro p hp
    have hp0 : p ≠ 0 := (Nat.prime_of_mem_primeFactors hp).ne_zero
    have hs : 0 < sigma 1 (p ^ N.factorization p) := sigma_pos 1 _ (pow_ne_zero _ hp0)
    positivity
  have hprod_real :
      (∏ p ∈ N.primeFactors, (sigma 1 (p ^ N.factorization p) : ℝ) / (p ^ N.factorization p : ℝ)) = 2 := by
    rw [Finset.prod_div_distrib]
    have hnum : (∏ p ∈ N.primeFactors, (sigma 1 (p ^ N.factorization p) : ℝ)) = ((2 * N : ℕ) : ℝ) := by
      rw [← hprod_sig, Nat.cast_prod]
    have hden : (∏ p ∈ N.primeFactors, ((p ^ N.factorization p : ℕ) : ℝ)) = (N : ℝ) := by
      rw [← Nat.cast_prod, hprod_pow]
    have hden' : (∏ p ∈ N.primeFactors, (p : ℝ) ^ N.factorization p) = (N : ℝ) := by
      simpa only [Nat.cast_pow] using hden
    rw [hnum, hden']
    push_cast
    have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    field_simp
  have hlog2 :
      Real.log 2 = ∑ p ∈ N.primeFactors,
        Real.log ((sigma 1 (p ^ N.factorization p) : ℝ) / (p ^ N.factorization p : ℝ)) := by
    rw [← hprod_real, Real.log_prod (fun p hp => (hpos_term p hp).ne')]
  rw [hlog2]
  have hprime3 : ∀ p ∈ N.primeFactors, 3 ≤ p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hodd : Odd p := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
    have hp2 : p ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hodd
    have := hpp.two_le
    omega
  obtain ⟨q, hq_mem, hq_mod, hq_exp_mod, h_even⟩ := euler_exponents ho hN
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
  have hq5 : 5 ≤ q := by
    have := hq_prime.two_le
    omega
  have h_nonspec : ∀ p ∈ N.primeFactors.erase q,
      1 / (p : ℝ) + 1 / (4 * (p : ℝ) ^ 2) <
        Real.log ((sigma 1 (p ^ N.factorization p) : ℝ) / (p ^ N.factorization p : ℝ)) := by
    intro p hp
    have hp_mem : p ∈ N.primeFactors := Finset.mem_of_mem_erase hp
    have hp_ne : p ≠ q := (Finset.mem_erase.mp hp).1
    have hp_prime := Nat.prime_of_mem_primeFactors hp_mem
    have hpe_ne : N.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp_mem
    have heven := h_even p hp_ne
    have hge2 : 2 ≤ N.factorization p := by
      rcases heven with ⟨k, hk⟩
      omega
    exact log_abundancy_nonspecial_bound hp_prime (hprime3 p hp_mem) hge2
  by_cases hqe : 2 ≤ N.factorization q
  · apply Finset.sum_lt_sum_of_nonempty ⟨q, hq_mem⟩
    intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp_prime.pos
    by_cases hpq : p = q
    · subst hpq
      have hlt := log_abundancy_nonspecial_bound hp_prime (hprime3 p hp) hqe
      have hpos : (0 : ℝ) < 1 / (4 * (p : ℝ) ^ 2) := by positivity
      linarith
    · have hp_er : p ∈ N.primeFactors.erase q := Finset.mem_erase.mpr ⟨hpq, hp⟩
      have hlt := h_nonspec p hp_er
      have hpos : (0 : ℝ) < 1 / (4 * (p : ℝ) ^ 2) := by positivity
      linarith
  · have hq_eq1 : N.factorization q = 1 := by omega
    have hhalf_gt1 : 1 < (q + 1) / 2 := by omega
    obtain ⟨r, hr_prime, hr_dvd⟩ := Nat.exists_prime_and_dvd hhalf_gt1.ne'
    have hhalf_odd : Odd ((q + 1) / 2) := by
      obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero (show (q - 1) % 4 = 0 by omega)
      have : (q + 1) / 2 = 2 * k + 1 := by omega
      rw [this]
      exact ⟨k, rfl⟩
    have hr_odd : Odd r := hhalf_odd.of_dvd_nat hr_dvd
    have hr_dvd_qp1 : r ∣ q + 1 := by
      have h2 : (q + 1) / 2 ∣ q + 1 := by
        refine ⟨2, ?_⟩
        omega
      exact hr_dvd.trans h2
    have hsig_q : sigma 1 (q ^ N.factorization q) = q + 1 := by
      rw [hq_eq1, sigma_one_apply_prime_pow hq_prime]
      simp [Finset.sum_range_succ, add_comm]
    have hr_dvd_2N : r ∣ 2 * N := by
      rw [← hprod_sig]
      exact hr_dvd_qp1.trans (hsig_q ▸ Finset.dvd_prod_of_mem _ hq_mem)
    have hr_dvd_N : r ∣ N := hr_odd.coprime_two_right.dvd_of_dvd_mul_left hr_dvd_2N
    have hr_mem : r ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hr_prime, hr_dvd_N, hn⟩
    have hr_ne_q : r ≠ q := by
      intro h
      subst h
      have h1 : r ∣ 1 := (Nat.dvd_add_right (dvd_refl r)).mp hr_dvd_qp1
      exact hr_prime.not_dvd_one h1
    have hr_er : r ∈ N.primeFactors.erase q := Finset.mem_erase.mpr ⟨hr_ne_q, hr_mem⟩
    have hr_le : 2 * r ≤ q + 1 := by
      have hpos : 0 < (q + 1) / 2 := by omega
      have hle := Nat.le_of_dvd hpos hr_dvd
      omega
    have hq_r_ineq : 1 / (2 * (q : ℝ) ^ 2) < 1 / (4 * (r : ℝ) ^ 2) := by
      have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq_prime.pos
      have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr_prime.pos
      have hq5_real : (5 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq5
      have hr_le_real : 2 * (r : ℝ) ≤ (q : ℝ) + 1 := by exact_mod_cast hr_le
      have hr_bound : (r : ℝ) ≤ 3 * (q : ℝ) / 5 := by linarith
      have hsq : 4 * (r : ℝ) ^ 2 < 2 * (q : ℝ) ^ 2 := by nlinarith
      exact div_lt_div_of_pos_left (by norm_num) (by positivity) hsq
    have hlog_q : 1 / (q : ℝ) - 1 / (2 * (q : ℝ) ^ 2) <
        Real.log ((sigma 1 (q ^ N.factorization q) : ℝ) / (q ^ N.factorization q : ℝ)) := by
      rw [hq_eq1]
      exact log_abundancy_euler_one_bound hq_prime hq5
    have hlog_r := h_nonspec r hr_er
    have hrest_le :
        (∑ p ∈ (N.primeFactors.erase q).erase r, (1 : ℝ) / (p : ℝ)) ≤
          ∑ p ∈ (N.primeFactors.erase q).erase r,
            Real.log ((sigma 1 (p ^ N.factorization p) : ℝ) / (p ^ N.factorization p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp_er : p ∈ N.primeFactors.erase q := Finset.mem_of_mem_erase hp
      have hp_mem : p ∈ N.primeFactors := Finset.mem_of_mem_erase hp_er
      have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp_mem).pos
      have hlt := h_nonspec p hp_er
      have hpos : (0 : ℝ) < 1 / (4 * (p : ℝ) ^ 2) := by positivity
      linarith
    have hsplit_lhs (f : ℕ → ℝ) :
        (∑ p ∈ N.primeFactors, f p) =
          f q + f r + ∑ p ∈ (N.primeFactors.erase q).erase r, f p := by
      rw [← Finset.add_sum_erase N.primeFactors f hq_mem,
        ← Finset.add_sum_erase (N.primeFactors.erase q) f hr_er]
      ring
    rw [hsplit_lhs (fun p => 1 / (p : ℝ)),
      hsplit_lhs (fun p => Real.log ((sigma 1 (p ^ N.factorization p) : ℝ) / (p ^ N.factorization p : ℝ)))]
    linarith

end OddPerfect
