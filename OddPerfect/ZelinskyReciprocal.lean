module

public import OddPerfect.Euler
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Zelinsky (2025), Corollary 1: Quadratic prime-reciprocal gap for least prime ≥ 11

Formalization of Zelinsky's theorem that the least prime factor `p` of an odd
perfect number `N` satisfies `2 ≤ N.factorization p`, and when `11 ≤ p`,
`∑ r ∈ N.primeFactors, (1 : ℝ) / r < Real.log 2 - 11 / (50 * p ^ 2)`.
-/

public section

namespace OddPerfect

open ArithmeticFunction

private lemma exists_odd_prime_factor_of_euler_one {N q : ℕ} (hN : N.Perfect)
    (hq_mem : q ∈ N.primeFactors) (hq_mod : q % 4 = 1) (hq_eq1 : N.factorization q = 1) :
    ∃ r ∈ N.primeFactors.erase q, 2 * r ≤ q + 1 := by
  have hn : N ≠ 0 := hN.2.ne'
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
  have hq5 : 5 ≤ q := by
    have := hq_prime.two_le
    omega
  have hsig : sigma 1 N = 2 * N :=
    (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN)
  have hprod_sig : (∏ p ∈ N.primeFactors, sigma 1 (p ^ N.factorization p)) = 2 * N := by
    trans sigma 1 N
    · exact (isMultiplicative_sigma.multiplicative_factorization _ hn).symm
    · exact hsig
  have hhalf_gt1 : 1 < (q + 1) / 2 := by omega
  obtain ⟨r, hr_prime, hr_dvd⟩ := Nat.exists_prime_and_dvd hhalf_gt1.ne'
  have hhalf_odd : Odd ((q + 1) / 2) := by
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero (show (q - 1) % 4 = 0 by omega)
    have : (q + 1) / 2 = 2 * k + 1 := by omega
    rw [this]
    exact ⟨k, rfl⟩
  have hr_odd : Odd r := hhalf_odd.of_dvd_nat hr_dvd
  have hr_dvd_qp1 : r ∣ q + 1 := by
    have h2 : (q + 1) / 2 ∣ q + 1 := ⟨2, by omega⟩
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
  exact ⟨r, hr_er, hr_le⟩

/-- The least prime factor of an odd perfect number always appears with exponent at least 2. -/
theorem two_le_factorization_of_least_primeFactor {N p : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hp : p ∈ N.primeFactors) (hmin : ∀ s ∈ N.primeFactors, p ≤ s) :
    2 ≤ N.factorization p := by
  by_contra hlt
  have hpe_ne : N.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
  have hpe_eq1 : N.factorization p = 1 := by omega
  obtain ⟨q, hq_mem, hq_mod, _hq_exp_mod, h_even⟩ := euler_exponents ho hN
  have hpq : p = q := by
    by_contra hne
    rcases h_even p hne with ⟨k, hk⟩
    omega
  subst hpq
  obtain ⟨r, hr_er, hr_le⟩ := exists_odd_prime_factor_of_euler_one hN hq_mem hq_mod hpe_eq1
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp5 : 5 ≤ p := by
    have := hp_prime.two_le
    omega
  have hr_lt : r < p := by omega
  have hr_mem : r ∈ N.primeFactors := Finset.mem_of_mem_erase hr_er
  have := hmin r hr_mem
  omega

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

private lemma log_abundancy_ge11_bound {p e : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) (he : 2 ≤ e) :
    1 / (p : ℝ) + 2 / (5 * (p : ℝ) ^ 2) <
      Real.log ((sigma 1 (p ^ e) : ℝ) / (p ^ e : ℝ)) := by
  let x : ℝ := 1 / (p : ℝ)
  have hp_real : (11 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp11
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hx11 : x ≤ 1 / 11 := by
    dsimp [x]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  let y : ℝ := x + (2 / 5) * x ^ 2
  have hy_def : y = x + (2 / 5) * x ^ 2 := rfl
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hy1 : y ≤ 1 := by dsimp [y]; nlinarith
  have hexp : Real.exp y ≤ 1 + y + y ^ 2 / 2 + 2 * y ^ 3 / 9 := exp_le_cubic_bound hy0 hy1
  have hpoly : 1 + y + y ^ 2 / 2 + 2 * y ^ 3 / 9 < 1 + x + x ^ 2 := by
    have hy_le : y ≤ (57 / 55) * x := by rw [hy_def]; nlinarith
    have hy2 : y ^ 2 ≤ (3249 / 3025) * x ^ 2 := by nlinarith
    have hy3 : y ^ 3 ≤ (185193 / 1830125) * x ^ 2 := by
      have h1 : y ^ 3 ≤ ((57 / 55) * x) ^ 3 := pow_le_pow_left₀ hy0 hy_le 3
      have h2 : x ^ 3 ≤ (1 / 11) * x ^ 2 := by nlinarith
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
  have hy_eq : y = 1 / (p : ℝ) + 2 / (5 * (p : ℝ) ^ 2) := by
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

/-- Zelinsky (2025), Corollary 1: For an odd perfect number `N` whose least prime factor
`p` satisfies `11 ≤ p`, `∑ r ∈ N.primeFactors, (1 : ℝ) / r < Real.log 2 - 11 / (50 * p ^ 2)`. -/
theorem zelinsky_prime_reciprocal_bound {N p : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hp : p ∈ N.primeFactors) (hmin : ∀ s ∈ N.primeFactors, p ≤ s) (hp11 : 11 ≤ p) :
    (∑ r ∈ N.primeFactors, (1 : ℝ) / (r : ℝ)) < Real.log 2 - 11 / (50 * (p : ℝ) ^ 2) := by
  have hn : N ≠ 0 := hN.2.ne'
  have hsig : sigma 1 N = 2 * N :=
    (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN)
  have hprod_sig : (∏ s ∈ N.primeFactors, sigma 1 (s ^ N.factorization s)) = 2 * N := by
    trans sigma 1 N
    · exact (isMultiplicative_sigma.multiplicative_factorization _ hn).symm
    · exact hsig
  have hprod_pow : (∏ s ∈ N.primeFactors, s ^ N.factorization s) = N :=
    (Nat.prod_primeFactors_pow_factorization hn).symm
  have hpos_term : ∀ s ∈ N.primeFactors,
      0 < (sigma 1 (s ^ N.factorization s) : ℝ) / (s ^ N.factorization s : ℝ) := by
    intro s hs
    have hs0 : s ≠ 0 := (Nat.prime_of_mem_primeFactors hs).ne_zero
    have hss : 0 < sigma 1 (s ^ N.factorization s) := sigma_pos 1 _ (pow_ne_zero _ hs0)
    positivity
  have hprod_real :
      (∏ s ∈ N.primeFactors, (sigma 1 (s ^ N.factorization s) : ℝ) / (s ^ N.factorization s : ℝ)) = 2 := by
    rw [Finset.prod_div_distrib]
    have hnum : (∏ s ∈ N.primeFactors, (sigma 1 (s ^ N.factorization s) : ℝ)) = ((2 * N : ℕ) : ℝ) := by
      rw [← hprod_sig, Nat.cast_prod]
    have hden : (∏ s ∈ N.primeFactors, ((s ^ N.factorization s : ℕ) : ℝ)) = (N : ℝ) := by
      rw [← Nat.cast_prod, hprod_pow]
    have hden' : (∏ s ∈ N.primeFactors, (s : ℝ) ^ N.factorization s) = (N : ℝ) := by
      simpa only [Nat.cast_pow] using hden
    rw [hnum, hden']
    push_cast
    have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    field_simp
  have hlog2 :
      Real.log 2 = ∑ s ∈ N.primeFactors,
        Real.log ((sigma 1 (s ^ N.factorization s) : ℝ) / (s ^ N.factorization s : ℝ)) := by
    rw [← hprod_real, Real.log_prod (fun s hs => (hpos_term s hs).ne')]
  suffices hgoal :
      (∑ s ∈ N.primeFactors, (1 : ℝ) / (s : ℝ)) + 11 / (50 * (p : ℝ) ^ 2) <
        ∑ s ∈ N.primeFactors,
          Real.log ((sigma 1 (s ^ N.factorization s) : ℝ) / (s ^ N.factorization s : ℝ)) by
    linarith [hlog2, hgoal]
  have hprime3 : ∀ s ∈ N.primeFactors, 3 ≤ s := by
    intro s hs
    have hss := Nat.prime_of_mem_primeFactors hs
    have hodd : Odd s := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hs)
    have hs2 : s ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hodd
    have := hss.two_le
    omega
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp_prime.pos
  have hp_exp : 2 ≤ N.factorization p :=
    two_le_factorization_of_least_primeFactor ho hN hp hmin
  have hlog_p :
      1 / (p : ℝ) + 2 / (5 * (p : ℝ) ^ 2) <
        Real.log ((sigma 1 (p ^ N.factorization p) : ℝ) / (p ^ N.factorization p : ℝ)) :=
    log_abundancy_ge11_bound hp_prime hp11 hp_exp
  have hgap_p : 11 / (50 * (p : ℝ) ^ 2) < 2 / (5 * (p : ℝ) ^ 2) := by
    have hp2_pos : (0 : ℝ) < (p : ℝ) ^ 2 := sq_pos_of_pos hp_pos
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  obtain ⟨q, hq_mem, hq_mod, _hq_exp_mod, h_even⟩ := euler_exponents ho hN
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
  have hq5 : 5 ≤ q := by
    have := hq_prime.two_le
    omega
  have h_nonspec : ∀ s ∈ N.primeFactors.erase q,
      1 / (s : ℝ) + 1 / (4 * (s : ℝ) ^ 2) <
        Real.log ((sigma 1 (s ^ N.factorization s) : ℝ) / (s ^ N.factorization s : ℝ)) := by
    intro s hs
    have hs_mem : s ∈ N.primeFactors := Finset.mem_of_mem_erase hs
    have hs_ne : s ≠ q := (Finset.mem_erase.mp hs).1
    have hs_prime := Nat.prime_of_mem_primeFactors hs_mem
    have hse_ne : N.factorization s ≠ 0 := Finsupp.mem_support_iff.mp hs_mem
    have heven := h_even s hs_ne
    have hge2 : 2 ≤ N.factorization s := by
      rcases heven with ⟨k, hk⟩
      omega
    exact log_abundancy_nonspecial_bound hs_prime (hprime3 s hs_mem) hge2
  by_cases hqe : 2 ≤ N.factorization q
  · have hrest_le :
        (∑ s ∈ N.primeFactors.erase p, (1 : ℝ) / (s : ℝ)) ≤
          ∑ s ∈ N.primeFactors.erase p,
            Real.log ((sigma 1 (s ^ N.factorization s) : ℝ) / (s ^ N.factorization s : ℝ)) := by
      apply Finset.sum_le_sum
      intro s hs
      have hs_mem : s ∈ N.primeFactors := Finset.mem_of_mem_erase hs
      have hs_prime := Nat.prime_of_mem_primeFactors hs_mem
      have hs_pos : (0 : ℝ) < (s : ℝ) := Nat.cast_pos.mpr hs_prime.pos
      have hs_ge2 : 2 ≤ N.factorization s := by
        by_cases hsq : s = q
        · subst hsq; exact hqe
        · have hse_ne : N.factorization s ≠ 0 := Finsupp.mem_support_iff.mp hs_mem
          rcases h_even s hsq with ⟨k, hk⟩
          omega
      have hlt := log_abundancy_nonspecial_bound hs_prime (hprime3 s hs_mem) hs_ge2
      have hpos : (0 : ℝ) < 1 / (4 * (s : ℝ) ^ 2) := by positivity
      linarith
    have hsplit (f : ℕ → ℝ) :
        (∑ s ∈ N.primeFactors, f s) = f p + ∑ s ∈ N.primeFactors.erase p, f s :=
      (Finset.add_sum_erase N.primeFactors f hp).symm
    rw [hsplit (fun s => 1 / (s : ℝ)),
      hsplit (fun s => Real.log ((sigma 1 (s ^ N.factorization s) : ℝ) / (s ^ N.factorization s : ℝ)))]
    linarith
  · have hq_eq1 : N.factorization q = 1 := by omega
    have hqp : q ≠ p := by
      intro h
      subst h
      omega
    obtain ⟨r, hr_er, hr_le⟩ := exists_odd_prime_factor_of_euler_one hN hq_mem hq_mod hq_eq1
    have hr_mem : r ∈ N.primeFactors := Finset.mem_of_mem_erase hr_er
    have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr_mem
    have hlog_q : 1 / (q : ℝ) - 1 / (2 * (q : ℝ) ^ 2) <
        Real.log ((sigma 1 (q ^ N.factorization q) : ℝ) / (q ^ N.factorization q : ℝ)) := by
      rw [hq_eq1]
      exact log_abundancy_euler_one_bound hq_prime hq5
    by_cases hrp : r = p
    · subst hrp
      have hp_er : r ∈ N.primeFactors.erase q := hr_er
      have hrest_le :
          (∑ s ∈ (N.primeFactors.erase q).erase r, (1 : ℝ) / (s : ℝ)) ≤
            ∑ s ∈ (N.primeFactors.erase q).erase r,
              Real.log ((sigma 1 (s ^ N.factorization s) : ℝ) / (s ^ N.factorization s : ℝ)) := by
        apply Finset.sum_le_sum
        intro s hs
        have hs_er : s ∈ N.primeFactors.erase q := Finset.mem_of_mem_erase hs
        have hs_mem : s ∈ N.primeFactors := Finset.mem_of_mem_erase hs_er
        have hs_pos : (0 : ℝ) < (s : ℝ) :=
          Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hs_mem).pos
        have hlt := h_nonspec s hs_er
        have hpos : (0 : ℝ) < 1 / (4 * (s : ℝ) ^ 2) := by positivity
        linarith
      have hq_r_bound : 1 / (2 * (q : ℝ) ^ 2) ≤ 121 / (882 * (r : ℝ) ^ 2) := by
        have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq_prime.pos
        have hr11_real : (11 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hp11
        have hr_le_real : 2 * (r : ℝ) ≤ (q : ℝ) + 1 := by exact_mod_cast hr_le
        have hq_ge : (21 / 11) * (r : ℝ) ≤ (q : ℝ) := by linarith
        have hq2_ge : (441 / 121) * (r : ℝ) ^ 2 ≤ (q : ℝ) ^ 2 := by nlinarith
        have hden : (882 * (r : ℝ) ^ 2) / 121 ≤ 2 * (q : ℝ) ^ 2 := by linarith
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have hgap_pair : 11 / (50 * (r : ℝ) ^ 2) < 2 / (5 * (r : ℝ) ^ 2) - 1 / (2 * (q : ℝ) ^ 2) := by
        have hr2_pos : (0 : ℝ) < (r : ℝ) ^ 2 := sq_pos_of_pos hp_pos
        have h1 : 11 / (50 * (r : ℝ) ^ 2) < (2 / 5 - 121 / 882) / (r : ℝ) ^ 2 := by
          rw [div_lt_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        have h2 : (2 / 5 - 121 / 882) / (r : ℝ) ^ 2 =
            2 / (5 * (r : ℝ) ^ 2) - 121 / (882 * (r : ℝ) ^ 2) := by
          field_simp
        linarith
      have hsplit (f : ℕ → ℝ) :
          (∑ s ∈ N.primeFactors, f s) =
            f q + f r + ∑ s ∈ (N.primeFactors.erase q).erase r, f s := by
        rw [← Finset.add_sum_erase N.primeFactors f hq_mem,
          ← Finset.add_sum_erase (N.primeFactors.erase q) f hp_er]
        ring
      rw [hsplit (fun s => 1 / (s : ℝ)),
        hsplit (fun s => Real.log ((sigma 1 (s ^ N.factorization s) : ℝ) / (s ^ N.factorization s : ℝ)))]
      linarith
    · have hp_er2 : p ∈ (N.primeFactors.erase q).erase r :=
        Finset.mem_erase.mpr ⟨Ne.symm hrp, Finset.mem_erase.mpr ⟨hqp.symm, hp⟩⟩
      have hq_r_ineq : 1 / (2 * (q : ℝ) ^ 2) < 1 / (4 * (r : ℝ) ^ 2) := by
        have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq_prime.pos
        have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr_prime.pos
        have hq5_real : (5 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq5
        have hr_le_real : 2 * (r : ℝ) ≤ (q : ℝ) + 1 := by exact_mod_cast hr_le
        have hr_bound : (r : ℝ) ≤ 3 * (q : ℝ) / 5 := by linarith
        have hsq : 4 * (r : ℝ) ^ 2 < 2 * (q : ℝ) ^ 2 := by nlinarith
        exact div_lt_div_of_pos_left (by norm_num) (by positivity) hsq
      have hlog_r := h_nonspec r hr_er
      have hrest_le :
          (∑ s ∈ ((N.primeFactors.erase q).erase r).erase p, (1 : ℝ) / (s : ℝ)) ≤
            ∑ s ∈ ((N.primeFactors.erase q).erase r).erase p,
              Real.log ((sigma 1 (s ^ N.factorization s) : ℝ) / (s ^ N.factorization s : ℝ)) := by
        apply Finset.sum_le_sum
        intro s hs
        have hs_er2 : s ∈ (N.primeFactors.erase q).erase r := Finset.mem_of_mem_erase hs
        have hs_er : s ∈ N.primeFactors.erase q := Finset.mem_of_mem_erase hs_er2
        have hs_mem : s ∈ N.primeFactors := Finset.mem_of_mem_erase hs_er
        have hs_pos : (0 : ℝ) < (s : ℝ) :=
          Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hs_mem).pos
        have hlt := h_nonspec s hs_er
        have hpos : (0 : ℝ) < 1 / (4 * (s : ℝ) ^ 2) := by positivity
        linarith
      have hsplit (f : ℕ → ℝ) :
          (∑ s ∈ N.primeFactors, f s) =
            f q + f r + f p + ∑ s ∈ ((N.primeFactors.erase q).erase r).erase p, f s := by
        rw [← Finset.add_sum_erase N.primeFactors f hq_mem,
          ← Finset.add_sum_erase (N.primeFactors.erase q) f hr_er,
          ← Finset.add_sum_erase ((N.primeFactors.erase q).erase r) f hp_er2]
        ring
      rw [hsplit (fun s => 1 / (s : ℝ)),
        hsplit (fun s => Real.log ((sigma 1 (s ^ N.factorization s) : ℝ) / (s ^ N.factorization s : ℝ)))]
      linarith

end OddPerfect
