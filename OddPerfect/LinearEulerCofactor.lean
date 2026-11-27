module

public import OddPerfect.TothSplitExistence
public import OddPerfect.QuarticTargetCapacity
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Linear Euler Cofactor Quotient Structure and Pure Prime-Source Split

Formalizes structural divisibility identities for the unique Euler-prime source `r₀` in the
linear Euler branch `N = q * m ^ 2`, its specialization when `σ(r₀ ^ (2 * v_{r₀}(m))) = q`,
and the congruence `q ≡ 1 [MOD 12] ∨ q ≡ 1 [MOD 20]` for sixth-power-free odd perfect
candidates.
-/

public section

namespace OddPerfect

open ArithmeticFunction

/-- Structural quotient and coprimality identities for the unique `q`-source prime `r₀`
in the linear Euler branch `N = q * m ^ 2`. -/
theorem linear_euler_cofactor_quotient_structure {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2) :
    ∃ r₀ ∈ m.primeFactors,
      let e₀ := m.factorization r₀
      let B := ordCompl[r₀] (m ^ 2)
      let c₀ := sigma 1 (r₀ ^ (2 * e₀)) / q
      let i_q := sigma 1 (m ^ 2) / q
      sigma 1 (r₀ ^ (2 * e₀)) = q * c₀ ∧
      ¬ q ∣ c₀ ∧
      Odd c₀ ∧
      Nat.Coprime c₀ (r₀ ^ (2 * e₀)) ∧
      i_q = c₀ * sigma 1 B ∧
      (q + 1) * c₀ * sigma 1 B = 2 * r₀ ^ (2 * e₀) * B ∧
      c₀ ∣ B ∧
      r₀ ^ (2 * e₀) ∣ ((q + 1) / 2) * sigma 1 B := by
  obtain ⟨_, r₀, hr₀_m, hq_dvd_r0, hfact_r0, _, _, _⟩ :=
    linear_euler_unique_q_source_and_bound ho hN hq hqm hform
  refine ⟨r₀, hr₀_m, ?_⟩
  let e₀ := m.factorization r₀
  let B := ordCompl[r₀] (m ^ 2)
  let c₀ := sigma 1 (r₀ ^ (2 * e₀)) / q
  let i_q := sigma 1 (m ^ 2) / q
  have hqodd : Odd q := ho.of_dvd_nat (hform ▸ dvd_mul_right q (m ^ 2))
  have hmodd : Odd m :=
    ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
  have hm0 : m ≠ 0 := hmodd.pos.ne'
  have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀_m
  have hr₀_odd : Odd r₀ := hmodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr₀_m)
  have h_mul_c0 : sigma 1 (r₀ ^ (2 * e₀)) = q * c₀ :=
    (Nat.mul_div_cancel' hq_dvd_r0).symm
  have hsig_r0_ne0 : sigma 1 (r₀ ^ (2 * e₀)) ≠ 0 :=
    (sigma_pos 1 _ (pow_ne_zero _ hr₀_prime.ne_zero)).ne'
  have h_nq_c0 : ¬ q ∣ c₀ := by
    intro hqc
    have hq2 : q ^ 2 ∣ sigma 1 (r₀ ^ (2 * e₀)) := by
      rw [h_mul_c0, pow_two]
      exact Nat.mul_dvd_mul_left q hqc
    have hle : 2 ≤ (sigma 1 (r₀ ^ (2 * e₀))).factorization q :=
      (hq.pow_dvd_iff_le_factorization hsig_r0_ne0).mp hq2
    have h1 : (sigma 1 (r₀ ^ (2 * e₀))).factorization q = 1 := hfact_r0
    omega
  have h_odd_sig_r0 : Odd (sigma 1 (r₀ ^ (2 * e₀))) := by
    have hmod : sigma 1 (r₀ ^ (2 * e₀)) ≡ 2 * e₀ + 1 [MOD 2] :=
      sigma_modEq_of_one hr₀_prime (Nat.odd_iff.mp hr₀_odd) (2 * e₀)
    change sigma 1 (r₀ ^ (2 * e₀)) % 2 = (2 * e₀ + 1) % 2 at hmod
    exact Nat.odd_iff.mpr (by omega)
  have h_odd_c0 : Odd c₀ :=
    h_odd_sig_r0.of_dvd_nat (h_mul_c0 ▸ dvd_mul_left c₀ q)
  have h_nr0_sig : ¬ r₀ ∣ sigma 1 (r₀ ^ (2 * e₀)) := by
    rw [Nat.dvd_iff_mod_eq_zero, sigma_prime_pow_mod_self hr₀_prime]
    decide
  have h_cop_sig_r0 : (r₀ ^ (2 * e₀)).Coprime (sigma 1 (r₀ ^ (2 * e₀))) :=
    (hr₀_prime.coprime_iff_not_dvd.mpr h_nr0_sig).pow_left (2 * e₀)
  have h_cop_c0 : Nat.Coprime c₀ (r₀ ^ (2 * e₀)) :=
    h_cop_sig_r0.symm.coprime_dvd_left (h_mul_c0 ▸ dvd_mul_left c₀ q)
  have hproj_eq : ordProj[r₀] (m ^ 2) = r₀ ^ (2 * e₀) := by
    dsimp [e₀]
    rw [pow_two, Nat.factorization_mul hm0 hm0, Finsupp.add_apply, ← two_mul]
  have h_r0_cop_B : (r₀ ^ (2 * e₀)).Coprime B := by
    rw [← hproj_eq]
    exact (Nat.coprime_ordCompl hr₀_prime hm20).pow_left _
  have hm2_split : m ^ 2 = r₀ ^ (2 * e₀) * B := by
    rw [← hproj_eq]
    exact (Nat.ordProj_mul_ordCompl_eq_self (m ^ 2) r₀).symm
  have hsig_m2 : sigma 1 (m ^ 2) = q * (c₀ * sigma 1 B) := by
    calc
      sigma 1 (m ^ 2) = sigma 1 (r₀ ^ (2 * e₀) * B) := congrArg (sigma 1) hm2_split
      _ = sigma 1 (r₀ ^ (2 * e₀)) * sigma 1 B :=
          isMultiplicative_sigma.map_mul_of_coprime h_r0_cop_B
      _ = (q * c₀) * sigma 1 B := by rw [h_mul_c0]
      _ = q * (c₀ * sigma 1 B) := by ring
  have h_iq_eq : i_q = c₀ * sigma 1 B := by
    dsimp [i_q]
    rw [hsig_m2, Nat.mul_div_cancel_left _ hq.pos]
  have hsig_N : sigma 1 N = 2 * N :=
    (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul ho.pos).mp hN)
  have hq_cop_m2 : q.Coprime (m ^ 2) :=
    hq.coprime_iff_not_dvd.mpr (fun h => hqm (hq.dvd_of_dvd_pow h))
  have hsig_q : sigma 1 q = q + 1 := by
    rw [← pow_one q, sigma_one_apply_prime_pow hq]
    simp [Finset.sum_range_succ]
    ring
  have h_bal_q : q * ((q + 1) * c₀ * sigma 1 B) = q * (2 * r₀ ^ (2 * e₀) * B) := by
    calc
      q * ((q + 1) * c₀ * sigma 1 B)
          = (q + 1) * (q * (c₀ * sigma 1 B)) := by ring
      _ = sigma 1 q * sigma 1 (m ^ 2) := by rw [hsig_q, hsig_m2]
      _ = sigma 1 (q * m ^ 2) := (isMultiplicative_sigma.map_mul_of_coprime hq_cop_m2).symm
      _ = sigma 1 N := by rw [← hform]
      _ = 2 * N := hsig_N
      _ = 2 * (q * (r₀ ^ (2 * e₀) * B)) := by rw [hform, hm2_split]
      _ = q * (2 * r₀ ^ (2 * e₀) * B) := by ring
  have h_balance : (q + 1) * c₀ * sigma 1 B = 2 * r₀ ^ (2 * e₀) * B :=
    Nat.mul_left_cancel hq.pos h_bal_q
  have hq1_even : q + 1 = 2 * ((q + 1) / 2) := by
    have := Nat.odd_iff.mp hqodd
    omega
  have h_half_bal : ((q + 1) / 2) * c₀ * sigma 1 B = r₀ ^ (2 * e₀) * B := by
    apply Nat.mul_left_cancel (by decide : 0 < 2)
    calc
      2 * (((q + 1) / 2) * c₀ * sigma 1 B)
          = (2 * ((q + 1) / 2)) * c₀ * sigma 1 B := by ring
      _ = (q + 1) * c₀ * sigma 1 B := by rw [← hq1_even]
      _ = 2 * r₀ ^ (2 * e₀) * B := h_balance
      _ = 2 * (r₀ ^ (2 * e₀) * B) := by ring
  have h_c0_dvd_B : c₀ ∣ B :=
    h_cop_c0.dvd_of_dvd_mul_left ⟨((q + 1) / 2) * sigma 1 B, by rw [← h_half_bal]; ring⟩
  have h_r0_dvd : r₀ ^ (2 * e₀) ∣ ((q + 1) / 2) * sigma 1 B :=
    h_cop_c0.symm.dvd_of_dvd_mul_right ⟨B, by rw [← h_half_bal]; ring⟩
  exact ⟨h_mul_c0, h_nq_c0, h_odd_c0, h_cop_c0, h_iq_eq, h_balance, h_c0_dvd_B, h_r0_dvd⟩

/-- When the unique `q`-source satisfies `σ(r₀ ^ (2 * v_{r₀}(m))) = q`, `(q + 1) / 2` is
coprime to `r₀ ^ (2 * v_{r₀}(m))` and splits both the complementary square `B` and `σ(B)` via
a common positive cofactor `t`. -/
theorem linear_euler_pure_prime_source_split {N q m r₀ : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hr₀ : r₀ ∈ m.primeFactors) (hpure : sigma 1 (r₀ ^ (2 * m.factorization r₀)) = q) :
    let e₀ := m.factorization r₀
    let B := ordCompl[r₀] (m ^ 2)
    Nat.Coprime ((q + 1) / 2) (r₀ ^ (2 * e₀)) ∧
    ∃ t : ℕ, 0 < t ∧ B = ((q + 1) / 2) * t ∧ sigma 1 B = r₀ ^ (2 * e₀) * t ∧
      sigma 1 (m ^ 2) / q = r₀ ^ (2 * e₀) * t := by
  let e₀ := m.factorization r₀
  let B := ordCompl[r₀] (m ^ 2)
  have hqodd : Odd q := ho.of_dvd_nat (hform ▸ dvd_mul_right q (m ^ 2))
  have hmodd : Odd m :=
    ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
  have hm0 : m ≠ 0 := hmodd.pos.ne'
  have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀
  have hr₀_odd : Odd r₀ := hmodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr₀)
  have hr₀_ge3 : 3 ≤ r₀ := by
    obtain ⟨k, hk⟩ := hr₀_odd
    have := hr₀_prime.two_le
    omega
  have hq_mod : q % r₀ = 1 := by
    rw [← hpure]
    exact sigma_prime_pow_mod_self hr₀_prime (2 * e₀)
  have h_nr0_q1 : ¬ r₀ ∣ q + 1 := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hq_mod]
    have hlt1 : 1 < r₀ := hr₀_prime.one_lt
    have hlt2 : 2 < r₀ := by omega
    rw [Nat.mod_eq_of_lt hlt1, show (1 : ℕ) + 1 = 2 by rfl, Nat.mod_eq_of_lt hlt2]
    decide
  have hq1_even : q + 1 = 2 * ((q + 1) / 2) := by
    have := Nat.odd_iff.mp hqodd
    omega
  have h_nr0_half : ¬ r₀ ∣ (q + 1) / 2 := fun hd =>
    h_nr0_q1 (hq1_even ▸ dvd_mul_of_dvd_right hd 2)
  have h_cop_half : Nat.Coprime ((q + 1) / 2) (r₀ ^ (2 * e₀)) :=
    (hr₀_prime.coprime_iff_not_dvd.mpr h_nr0_half).symm.pow_right (2 * e₀)
  have hproj_eq : ordProj[r₀] (m ^ 2) = r₀ ^ (2 * e₀) := by
    dsimp [e₀]
    rw [pow_two, Nat.factorization_mul hm0 hm0, Finsupp.add_apply, ← two_mul]
  have h_r0_cop_B : (r₀ ^ (2 * e₀)).Coprime B := by
    rw [← hproj_eq]
    exact (Nat.coprime_ordCompl hr₀_prime hm20).pow_left _
  have hm2_split : m ^ 2 = r₀ ^ (2 * e₀) * B := by
    rw [← hproj_eq]
    exact (Nat.ordProj_mul_ordCompl_eq_self (m ^ 2) r₀).symm
  have hsig_m2 : sigma 1 (m ^ 2) = q * sigma 1 B := by
    calc
      sigma 1 (m ^ 2) = sigma 1 (r₀ ^ (2 * e₀) * B) := congrArg (sigma 1) hm2_split
      _ = sigma 1 (r₀ ^ (2 * e₀)) * sigma 1 B :=
          isMultiplicative_sigma.map_mul_of_coprime h_r0_cop_B
      _ = q * sigma 1 B := by rw [hpure]
  have hiq_eq : sigma 1 (m ^ 2) / q = sigma 1 B := by
    rw [hsig_m2, Nat.mul_div_cancel_left _ hq.pos]
  have hsig_N : sigma 1 N = 2 * N :=
    (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul ho.pos).mp hN)
  have hq_cop_m2 : q.Coprime (m ^ 2) :=
    hq.coprime_iff_not_dvd.mpr (fun h => hqm (hq.dvd_of_dvd_pow h))
  have hsig_q : sigma 1 q = q + 1 := by
    rw [← pow_one q, sigma_one_apply_prime_pow hq]
    simp [Finset.sum_range_succ]
    ring
  have h_bal_q : q * ((q + 1) * sigma 1 B) = q * (2 * (r₀ ^ (2 * e₀) * B)) := by
    calc
      q * ((q + 1) * sigma 1 B)
          = (q + 1) * (q * sigma 1 B) := by ring
      _ = sigma 1 q * sigma 1 (m ^ 2) := by rw [hsig_q, hsig_m2]
      _ = sigma 1 (q * m ^ 2) := (isMultiplicative_sigma.map_mul_of_coprime hq_cop_m2).symm
      _ = sigma 1 N := by rw [← hform]
      _ = 2 * N := hsig_N
      _ = 2 * (q * (r₀ ^ (2 * e₀) * B)) := by rw [hform, hm2_split]
      _ = q * (2 * (r₀ ^ (2 * e₀) * B)) := by ring
  have h_bal : (q + 1) * sigma 1 B = 2 * (r₀ ^ (2 * e₀) * B) :=
    Nat.mul_left_cancel hq.pos h_bal_q
  have h_half_bal : ((q + 1) / 2) * sigma 1 B = r₀ ^ (2 * e₀) * B := by
    apply Nat.mul_left_cancel (by decide : 0 < 2)
    calc
      2 * (((q + 1) / 2) * sigma 1 B)
          = (2 * ((q + 1) / 2)) * sigma 1 B := by ring
      _ = (q + 1) * sigma 1 B := by rw [← hq1_even]
      _ = 2 * (r₀ ^ (2 * e₀) * B) := h_bal
  have h_half_dvd_B : (q + 1) / 2 ∣ B :=
    h_cop_half.dvd_of_dvd_mul_left ⟨sigma 1 B, h_half_bal.symm⟩
  let t := B / ((q + 1) / 2)
  have hB_eq : B = ((q + 1) / 2) * t := (Nat.mul_div_cancel' h_half_dvd_B).symm
  have hB_pos : 0 < B := Nat.ordCompl_pos r₀ hm20
  have h_half_pos : 0 < (q + 1) / 2 := by
    have := hq.two_le
    omega
  have ht_pos : 0 < t := Nat.div_pos (Nat.le_of_dvd hB_pos h_half_dvd_B) h_half_pos
  have hsigB_eq : sigma 1 B = r₀ ^ (2 * e₀) * t := by
    apply Nat.mul_left_cancel h_half_pos
    calc
      ((q + 1) / 2) * sigma 1 B = r₀ ^ (2 * e₀) * B := h_half_bal
      _ = r₀ ^ (2 * e₀) * (((q + 1) / 2) * t) := by rw [hB_eq]
      _ = ((q + 1) / 2) * (r₀ ^ (2 * e₀) * t) := by ring
  exact ⟨h_cop_half, t, ht_pos, hB_eq, hsigB_eq, hiq_eq.trans hsigB_eq⟩

/-- For every `3`-free odd perfect number `N`, the Euler prime `q` satisfies
`q % 12 = 1` and `13 ≤ q`. -/
theorem three_free_euler_prime_mod_twelve {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (h3 : ¬ 3 ∣ N) :
    q % 12 = 1 ∧ 13 ≤ q := by
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hq_dvd_N : q ∣ N := Nat.dvd_of_mem_primeFactors hq
  have hsplit : N = q ^ N.factorization q * ordCompl[q] N :=
    (Nat.ordProj_mul_ordCompl_eq_self N q).symm
  have hq_ndvd : ¬ q ∣ ordCompl[q] N := Nat.not_dvd_ordCompl hq_prime ho.pos.ne'
  have hsig_dvd : sigma 1 (q ^ N.factorization q) ∣ 2 * ordCompl[q] N :=
    sigma_exact_pow_dvd_twice_cofactor hN hq_prime hsplit hq_ndvd
  have he_odd : Odd (N.factorization q) := Nat.odd_iff.mpr (by omega)
  have hq1_dvd : q + 1 ∣ 2 * N :=
    (succ_dvd_sigma_prime_pow hq_prime he_odd).trans
      (hsig_dvd.trans (Nat.mul_dvd_mul_left 2 (Nat.ordCompl_dvd N q)))
  have hq3_ne0 : q % 3 ≠ 0 := fun h0 =>
    h3 ((Nat.dvd_of_mod_eq_zero h0).trans hq_dvd_N)
  have hq3_ne2 : q % 3 ≠ 2 := by
    intro h2
    have h3_dvd_q1 : 3 ∣ q + 1 := Nat.dvd_of_mod_eq_zero (by omega)
    have h3_dvd_2N : 3 ∣ 2 * N := h3_dvd_q1.trans hq1_dvd
    rcases (by decide : Nat.Prime 3).dvd_mul.mp h3_dvd_2N with h32 | h3N
    · exact (by decide : ¬ 3 ∣ 2) h32
    · exact h3 h3N
  have := hq_prime.two_le
  exact ⟨by omega, by omega⟩

/-- For any sixth-power-free odd perfect number `N` with Euler prime `q`, `q` satisfies
`q % 12 = 1` and `13 ≤ q` (and in particular `q % 12 = 1 ∨ q % 20 = 1`). -/
theorem sixth_power_free_euler_prime_mod_twelve_or_twenty {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (_hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    q % 12 = 1 ∧ 13 ≤ q :=
  three_free_euler_prime_mod_twelve ho hN hq hq4 he (sixth_power_free_three_not_dvd ho hN hfree)

end OddPerfect
