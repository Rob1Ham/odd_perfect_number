module

public import OddPerfect.LinearEulerSquareDescent
public import OddPerfect.SixthPowerFreeCofactorObstruction
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Linear Euler Iterated Peeling and Square-Source Descent

Formalizes unconditional elimination of the `r₀ ∣ (q + 1) / 2` branch for square sources
(`m.factorization r₀ = 1`), unconditional split-vs.-absorber descent, sixth-power-free
specialization on `(squareSources N).filter (· % 5 = 1)`, and finite-support iterated
cofactor-peeling dichotomy (collision, half-successor hit, or directed `σ`-cycle):

1. `linear_euler_square_source_coprime_half_succ`:
   Unconditional proof of `Nat.Coprime r₀ ((q + 1) / 2)` and `r₀ ^ 2 ∣ sigma 1 B` whenever
   `m.factorization r₀ = 1`.
2. `linear_euler_square_source_unconditional_split_or_absorber`:
   Unconditional three-divisor descent and split-vs.-single-absorber dichotomy when
   `m.factorization r₀ = 1`.
3. `sixth_power_free_unique_q_source_S51_forces_descent`:
   Specialization to sixth-power-free odd perfect numbers when the unique `q`-source `r₀`
   lies in `(squareSources N).filter (· % 5 = 1)`.
4. `peeling_chain_dichotomy_on_finite_square`:
   General finite-support iterated cofactor-peeling theorem on odd squares `B'`.
5. `linear_euler_peeling_collision_or_cycle`:
   Every linear Euler odd perfect number `N = q * m ^ 2` admits either a prime collision
   between two distinct components of `m`, a prime `p ∈ m.primeFactors` dividing `(q + 1) / 2`,
   or a directed `σ`-cycle of length `≥ 2` inside `m.primeFactors`.
-/

public section

namespace OddPerfect

open ArithmeticFunction Finset

private lemma sigma_one_sq_prime {p : ℕ} (hp : p.Prime) :
    sigma 1 (p ^ 2) = p ^ 2 + p + 1 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

private lemma ordProj_eq_of_dvd_coprime_left {A B C p : ℕ}
    (hp : p.Prime) (hAB : A = B * C) (hcop : B.Coprime C) (hpB : p ∈ B.primeFactors) :
    ordProj[p] A = ordProj[p] B := by
  have hB0 : B ≠ 0 := by
    intro h0
    subst h0
    simp at hpB
  have hp_dvd_B : p ∣ B := Nat.dvd_of_mem_primeFactors hpB
  have hC0 : C ≠ 0 := by
    intro h0
    rw [h0] at hcop
    rw [Nat.coprime_zero_right] at hcop
    rw [hcop] at hp_dvd_B
    exact hp.not_dvd_one hp_dvd_B
  have hp_ndvd_C : ¬ p ∣ C := fun hpC =>
    hp.not_dvd_one (hcop ▸ Nat.dvd_gcd hp_dvd_B hpC)
  have hA_fact : A.factorization p = B.factorization p := by
    rw [hAB, Nat.factorization_mul hB0 hC0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hp_ndvd_C, add_zero]
  rw [hA_fact]

private lemma sigma_ordProj_dvd_sigma_of_coprime_left {A B C p : ℕ}
    (hp : p.Prime) (hAB : A = B * C) (hcop : B.Coprime C) (hpB : p ∈ B.primeFactors) :
    sigma 1 (ordProj[p] A) ∣ sigma 1 B := by
  have hB0 : B ≠ 0 := by
    intro h0
    subst h0
    simp at hpB
  have hB_split : B = ordProj[p] B * ordCompl[p] B :=
    (Nat.ordProj_mul_ordCompl_eq_self B p).symm
  have hB_cop : (ordProj[p] B).Coprime (ordCompl[p] B) :=
    (Nat.coprime_ordCompl hp hB0).pow_left _
  rw [ordProj_eq_of_dvd_coprime_left hp hAB hcop hpB]
  conv_rhs => rw [hB_split, isMultiplicative_sigma.map_mul_of_coprime hB_cop]
  exact dvd_mul_right _ _

/-- **1. Unconditional Half-Successor Coprimality for Square Sources**:
Whenever the unique `q`-source `r₀` has exponent `m.factorization r₀ = 1`, the branch
`r₀ ∣ (q + 1) / 2` is impossible (`(2 * r₀ - 1)^2 ≤ q * c₀ = r₀^2 + r₀ + 1`), forcing
`Nat.Coprime r₀ ((q + 1) / 2)`, `¬ r₀ ∣ (q + 1) / 2`, `r₀ ^ 2 ∣ sigma 1 (ordCompl[r₀] (m ^ 2))`,
and `(sigma 1 (ordCompl[r₀] (m ^ 2))).factorization r₀ = 2`. -/
theorem linear_euler_square_source_coprime_half_succ {N q m r₀ : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hr₀ : r₀ ∈ m.primeFactors) (hq_dvd : q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀)))
    (he₀ : m.factorization r₀ = 1) :
    Nat.Coprime r₀ ((q + 1) / 2) ∧
    ¬ r₀ ∣ (q + 1) / 2 ∧
    r₀ ^ 2 ∣ sigma 1 (ordCompl[r₀] (m ^ 2)) ∧
    (sigma 1 (ordCompl[r₀] (m ^ 2))).factorization r₀ = 2 := by
  have hqodd : Odd q := ho.of_dvd_nat (hform ▸ dvd_mul_right q (m ^ 2))
  have hmodd : Odd m :=
    ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀
  have hr₀_odd : Odd r₀ := hmodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr₀)
  have hr₀_ge3 : 3 ≤ r₀ := by
    obtain ⟨k, hk⟩ := hr₀_odd
    have := hr₀_prime.two_le
    omega
  obtain h_full | h_cong :=
    linear_euler_r0_full_pow_or_c0_congruence_of_source ho hN hq hqm hform hr₀ hq_dvd
  · have hcop : Nat.Coprime r₀ ((q + 1) / 2) := h_full.1
    have hndvd : ¬ r₀ ∣ (q + 1) / 2 := hr₀_prime.coprime_iff_not_dvd.mp hcop
    have hdvd : r₀ ^ 2 ∣ sigma 1 (ordCompl[r₀] (m ^ 2)) := by
      have h1 := h_full.2.1
      rwa [he₀, mul_one] at h1
    have hfact :=
      (linear_euler_coprime_three_divisor_square_descent ho hN hq hqm hform hr₀ hq_dvd hcop).1
    rw [he₀, mul_one] at hfact
    exact ⟨hcop, hndvd, hdvd, hfact⟩
  · exfalso
    obtain ⟨hmul_c0, _, _, _, _, _, _, _, _⟩ :=
      linear_euler_cofactor_quotient_structure_of_source ho hN hq hqm hform hr₀ hq_dvd
    let c₀ := sigma 1 (r₀ ^ (2 * m.factorization r₀)) / q
    have hqc0 : q * c₀ = r₀ ^ 2 + r₀ + 1 := by
      have h1 : sigma 1 (r₀ ^ (2 * m.factorization r₀)) = q * c₀ := hmul_c0
      rw [he₀, mul_one, sigma_one_sq_prime hr₀_prime] at h1
      exact h1.symm
    obtain ⟨hr₀_half, _, hle_c0, _, _⟩ := h_cong
    change 2 * r₀ - 1 ≤ c₀ at hle_c0
    have hhalf_pos : 0 < (q + 1) / 2 := by
      have := hq.two_le
      omega
    have hr₀_le_half : r₀ ≤ (q + 1) / 2 := Nat.le_of_dvd hhalf_pos hr₀_half
    have hq1_even : q + 1 = 2 * ((q + 1) / 2) := by
      have := Nat.odd_iff.mp hqodd
      omega
    have hle_q : 2 * r₀ - 1 ≤ q := by omega
    have hmul_le : (2 * r₀ - 1) * (2 * r₀ - 1) ≤ q * c₀ :=
      Nat.mul_le_mul hle_q hle_c0
    rw [hqc0] at hmul_le
    zify [show 1 ≤ 2 * r₀ by omega] at hmul_le hr₀_ge3
    nlinarith

/-- **2. Unconditional Split-vs.-Single-Absorber Descent for Square Sources**:
When `m.factorization r₀ = 1`, `B := ordCompl[r₀] (m ^ 2)`, `c₀ := sigma 1 (r₀ ^ 2) / q`,
and `D₀ := sigma 1 B / r₀ ^ 2`, we have `B = ((q + 1) / 2) * c₀ * D₀` unconditionally, and
either two distinct prime components of `B` split `r₀ ^ 2` with valuation `1` each (giving
`B = B₁ * B₂` with `gcd(r₀ ^ 2, sigma 1 B₁) = r₀`), or a unique prime `r₁ ∈ B.primeFactors`
absorbs `r₀ ^ 2` and drives the coprime peeling step on `B₁ := ordCompl[r₁] B`. -/
theorem linear_euler_square_source_unconditional_split_or_absorber {N q m r₀ : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hr₀ : r₀ ∈ m.primeFactors) (hq_dvd : q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀)))
    (he₀ : m.factorization r₀ = 1) :
    let B := ordCompl[r₀] (m ^ 2)
    let c₀ := sigma 1 (r₀ ^ 2) / q
    let D₀ := sigma 1 B / r₀ ^ 2
    Nat.Coprime r₀ ((q + 1) / 2) ∧
    sigma 1 B = r₀ ^ 2 * D₀ ∧
    B = ((q + 1) / 2) * c₀ * D₀ ∧
    (Nat.Coprime r₀ D₀ ∧ Odd D₀ ∧ 0 < D₀) ∧
    (((∃ p₁ ∈ B.primeFactors, ∃ p₂ ∈ B.primeFactors,
        p₁ ≠ p₂ ∧
        r₀ ∣ sigma 1 (ordProj[p₁] B) ∧
        r₀ ∣ sigma 1 (ordProj[p₂] B) ∧
        (sigma 1 (ordProj[p₁] B)).factorization r₀ = 1 ∧
        (sigma 1 (ordProj[p₂] B)).factorization r₀ = 1) ∧
      (∃ B₁ B₂ : ℕ,
        B = B₁ * B₂ ∧
        B₁.Coprime B₂ ∧
        r₀ ∣ Nat.gcd (sigma 1 B₁) (sigma 1 B₂) ∧
        Nat.gcd (r₀ ^ 2) (sigma 1 B₁) = r₀)) ∨
     (∃ r₁ ∈ B.primeFactors,
        r₀ ^ 2 ∣ sigma 1 (ordProj[r₁] B) ∧
        (sigma 1 (ordProj[r₁] B)).factorization r₀ = 2 ∧
        Nat.Coprime r₀ (sigma 1 (ordCompl[r₁] B)) ∧
        (∀ p ∈ B.primeFactors, r₀ ∣ sigma 1 (ordProj[p] B) → p = r₁) ∧
        let e₁ := m.factorization r₁
        let c₁ := sigma 1 (r₁ ^ (2 * e₁)) / r₀ ^ 2
        let B₁ := ordCompl[r₁] B
        ordProj[r₁] B = r₁ ^ (2 * e₁) ∧
        sigma 1 (r₁ ^ (2 * e₁)) = r₀ ^ 2 * c₁ ∧
        Nat.Coprime c₁ r₁ ∧
        (((q + 1) / 2) * c₀ * c₁) * sigma 1 B₁ = r₁ ^ (2 * e₁) * B₁ ∧
        (1 < B₁ → ((q + 1) / 2) * c₀ * c₁ < r₁ ^ (2 * e₁)))) := by
  let B := ordCompl[r₀] (m ^ 2)
  let c₀ := sigma 1 (r₀ ^ 2) / q
  let D₀ := sigma 1 B / r₀ ^ 2
  have hmodd : Odd m :=
    ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
  have hm0 : m ≠ 0 := hmodd.pos.ne'
  have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀
  have hB0 : B ≠ 0 := (Nat.ordCompl_pos r₀ hm20).ne'
  obtain ⟨hcop, _, _, h_sigB_fact⟩ :=
    linear_euler_square_source_coprime_half_succ ho hN hq hqm hform hr₀ hq_dvd he₀
  obtain ⟨_, h_sigB_eq, h_B_eq, _, h_D0, _⟩ :=
    linear_euler_coprime_three_divisor_square_descent ho hN hq hqm hform hr₀ hq_dvd hcop
  have h_sigB_eq' : sigma 1 B = r₀ ^ 2 * D₀ := by
    simpa [B, D₀, he₀] using h_sigB_eq
  have h_B_eq' : B = ((q + 1) / 2) * c₀ * D₀ := by
    simpa [B, c₀, D₀, he₀] using h_B_eq
  have h_D0' : Nat.Coprime r₀ D₀ ∧ Odd D₀ ∧ 0 < D₀ := by
    simpa [B, D₀, he₀] using h_D0
  refine ⟨hcop, h_sigB_eq', h_B_eq', h_D0', ?_⟩
  obtain hsplit | habs :=
    linear_euler_composite_square_split_or_single_absorber ho hN hq hqm hform hr₀ hq_dvd hcop
  · left
    obtain ⟨B₁, B₂, hB_split, hB_cop, hr0_gcd12, hgcd_gt1, hgcd_lt⟩ := hsplit
    change B = B₁ * B₂ at hB_split
    have hgcd_lt' : Nat.gcd (r₀ ^ 2) (sigma 1 B₁) < r₀ ^ 2 := by
      simpa [he₀] using hgcd_lt
    have hgcd_gt1' : 1 < Nat.gcd (r₀ ^ 2) (sigma 1 B₁) := by
      simpa [he₀] using hgcd_gt1
    have hgcd_eq_r0 : Nat.gcd (r₀ ^ 2) (sigma 1 B₁) = r₀ := by
      obtain ⟨k, hk_le, hk_eq⟩ :=
        (Nat.dvd_prime_pow hr₀_prime).mp (Nat.gcd_dvd_left (r₀ ^ 2) (sigma 1 B₁))
      have hk_ne0 : k ≠ 0 := by
        intro hk0
        rw [hk0, pow_zero] at hk_eq
        omega
      have hk_ne2 : k ≠ 2 := by
        intro hk2
        rw [hk2] at hk_eq
        omega
      have hk1 : k = 1 := by omega
      simpa [hk1] using hk_eq
    have hr0_dvd_B₁ : r₀ ∣ sigma 1 B₁ := hr0_gcd12.trans (Nat.gcd_dvd_left _ _)
    have hr0_dvd_B₂ : r₀ ∣ sigma 1 B₂ := hr0_gcd12.trans (Nat.gcd_dvd_right _ _)
    have hB₁0 : B₁ ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hB_split
      exact hB0 hB_split
    have hB₂0 : B₂ ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hB_split
      exact hB0 hB_split
    have hsigB₁_prod : sigma 1 B₁ = ∏ p ∈ B₁.primeFactors, sigma 1 (ordProj[p] B₁) := by
      rw [isMultiplicative_sigma.multiplicative_factorization (sigma 1) hB₁0]
      exact Finset.prod_congr B₁.support_factorization fun _ _ => rfl
    have hsigB₂_prod : sigma 1 B₂ = ∏ p ∈ B₂.primeFactors, sigma 1 (ordProj[p] B₂) := by
      rw [isMultiplicative_sigma.multiplicative_factorization (sigma 1) hB₂0]
      exact Finset.prod_congr B₂.support_factorization fun _ _ => rfl
    obtain ⟨p₁, hp₁B₁, hr0_dvd_p₁⟩ := by
      rw [hsigB₁_prod] at hr0_dvd_B₁
      exact (hr₀_prime.prime.dvd_finsetProd_iff _).mp hr0_dvd_B₁
    obtain ⟨p₂, hp₂B₂, hr0_dvd_p₂⟩ := by
      rw [hsigB₂_prod] at hr0_dvd_B₂
      exact (hr₀_prime.prime.dvd_finsetProd_iff _).mp hr0_dvd_B₂
    have hp₁_prime : p₁.Prime := Nat.prime_of_mem_primeFactors hp₁B₁
    have hp₂_prime : p₂.Prime := Nat.prime_of_mem_primeFactors hp₂B₂
    have hp₁_B : p₁ ∈ B.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp₁_prime, (Nat.dvd_of_mem_primeFactors hp₁B₁).trans ⟨B₂, hB_split⟩, hB0⟩
    have hp₂_B : p₂ ∈ B.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp₂_prime, (Nat.dvd_of_mem_primeFactors hp₂B₂).trans ⟨B₁, by rw [hB_split, mul_comm]⟩, hB0⟩
    have hp_ne : p₁ ≠ p₂ := by
      intro heq
      subst heq
      exact hp₁_prime.not_dvd_one
        (hB_cop ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp₁B₁) (Nat.dvd_of_mem_primeFactors hp₂B₂))
    have h_ordProj_p₁ : ordProj[p₁] B = ordProj[p₁] B₁ :=
      ordProj_eq_of_dvd_coprime_left hp₁_prime hB_split hB_cop hp₁B₁
    have h_ordProj_p₂ : ordProj[p₂] B = ordProj[p₂] B₂ :=
      ordProj_eq_of_dvd_coprime_left hp₂_prime (hB_split.trans (mul_comm _ _)) hB_cop.symm hp₂B₂
    have hr0_dvd_proj1 : r₀ ∣ sigma 1 (ordProj[p₁] B) := by
      rw [h_ordProj_p₁]
      exact hr0_dvd_p₁
    have hr0_dvd_proj2 : r₀ ∣ sigma 1 (ordProj[p₂] B) := by
      rw [h_ordProj_p₂]
      exact hr0_dvd_p₂
    have h_sig_proj1_dvd_B₁ : sigma 1 (ordProj[p₁] B) ∣ sigma 1 B₁ :=
      sigma_ordProj_dvd_sigma_of_coprime_left hp₁_prime hB_split hB_cop hp₁B₁
    have h_sig_proj2_dvd_B₂ : sigma 1 (ordProj[p₂] B) ∣ sigma 1 B₂ :=
      sigma_ordProj_dvd_sigma_of_coprime_left hp₂_prime (hB_split.trans (mul_comm _ _)) hB_cop.symm hp₂B₂
    have hsigB_mul : sigma 1 B = sigma 1 B₁ * sigma 1 B₂ := by
      rw [hB_split, isMultiplicative_sigma.map_mul_of_coprime hB_cop]
    have hsigB₁_ne0 : sigma 1 B₁ ≠ 0 := (sigma_pos 1 B₁ hB₁0).ne'
    have hsigB₂_ne0 : sigma 1 B₂ ≠ 0 := (sigma_pos 1 B₂ hB₂0).ne'
    have hsig_p₁_ne0 : sigma 1 (ordProj[p₁] B) ≠ 0 :=
      (sigma_pos 1 _ (pow_ne_zero _ hp₁_prime.ne_zero)).ne'
    have hsig_p₂_ne0 : sigma 1 (ordProj[p₂] B) ≠ 0 :=
      (sigma_pos 1 _ (pow_ne_zero _ hp₂_prime.ne_zero)).ne'
    have h1_le_B₁ : 1 ≤ (sigma 1 B₁).factorization r₀ :=
      (hr₀_prime.pow_dvd_iff_le_factorization hsigB₁_ne0).mp (by simpa using hr0_dvd_B₁)
    have h1_le_B₂ : 1 ≤ (sigma 1 B₂).factorization r₀ :=
      (hr₀_prime.pow_dvd_iff_le_factorization hsigB₂_ne0).mp (by simpa using hr0_dvd_B₂)
    have hadd_fact :
        (sigma 1 B).factorization r₀ =
          (sigma 1 B₁).factorization r₀ + (sigma 1 B₂).factorization r₀ := by
      rw [hsigB_mul, Nat.factorization_mul hsigB₁_ne0 hsigB₂_ne0, Finsupp.add_apply]
    change (sigma 1 B).factorization r₀ = 2 at h_sigB_fact
    have hB₁_fact_eq1 : (sigma 1 B₁).factorization r₀ = 1 := by omega
    have hB₂_fact_eq1 : (sigma 1 B₂).factorization r₀ = 1 := by omega
    have h1_le_p₁ : 1 ≤ (sigma 1 (ordProj[p₁] B)).factorization r₀ :=
      (hr₀_prime.pow_dvd_iff_le_factorization hsig_p₁_ne0).mp (by simpa using hr0_dvd_proj1)
    have hp₁_le_B₁ : (sigma 1 (ordProj[p₁] B)).factorization r₀ ≤ (sigma 1 B₁).factorization r₀ :=
      Nat.factorization_le_iff_dvd hsig_p₁_ne0 hsigB₁_ne0 |>.mpr h_sig_proj1_dvd_B₁ r₀
    have hp₁_fact_eq1 : (sigma 1 (ordProj[p₁] B)).factorization r₀ = 1 := by omega
    have h1_le_p₂ : 1 ≤ (sigma 1 (ordProj[p₂] B)).factorization r₀ :=
      (hr₀_prime.pow_dvd_iff_le_factorization hsig_p₂_ne0).mp (by simpa using hr0_dvd_proj2)
    have hp₂_le_B₂ : (sigma 1 (ordProj[p₂] B)).factorization r₀ ≤ (sigma 1 B₂).factorization r₀ :=
      Nat.factorization_le_iff_dvd hsig_p₂_ne0 hsigB₂_ne0 |>.mpr h_sig_proj2_dvd_B₂ r₀
    have hp₂_fact_eq1 : (sigma 1 (ordProj[p₂] B)).factorization r₀ = 1 := by omega
    exact ⟨⟨p₁, hp₁_B, p₂, hp₂_B, hp_ne, hr0_dvd_proj1, hr0_dvd_proj2, hp₁_fact_eq1, hp₂_fact_eq1⟩,
      ⟨B₁, B₂, hB_split, hB_cop, hr0_gcd12, hgcd_eq_r0⟩⟩
  · right
    obtain ⟨r₁, hr₁_B, hr0_dvd_r₁, hfact_r₁, hcop_r0_B₁, h_proj, h_sig_eq, hcop_c₁, h_bal, h_lt⟩ := habs
    have hr₁_prime : r₁.Prime := Nat.prime_of_mem_primeFactors hr₁_B
    have huniq_r₁ : ∀ p ∈ B.primeFactors, r₀ ∣ sigma 1 (ordProj[p] B) → p = r₁ := by
      intro p hpB hr0_dvd_p
      by_contra hp_ne
      let B₁ := ordCompl[r₁] B
      have hB_split : B = ordProj[r₁] B * B₁ := (Nat.ordProj_mul_ordCompl_eq_self B r₁).symm
      have hB_cop : (ordProj[r₁] B).Coprime B₁ := (Nat.coprime_ordCompl hr₁_prime hB0).pow_left _
      have hp_B₁ : p ∈ B₁.primeFactors := by
        have hp_prime := Nat.prime_of_mem_primeFactors hpB
        have hB₁0 : B₁ ≠ 0 := (Nat.ordCompl_pos r₁ hB0).ne'
        have hp_dvd_B : p ∣ B := Nat.dvd_of_mem_primeFactors hpB
        have hp_dvd_B₁ : p ∣ B₁ := by
          rw [hB_split] at hp_dvd_B
          rcases hp_prime.dvd_mul.mp hp_dvd_B with hp_pow | hp_B₁
          · exact (hp_ne (hp_prime.dvd_of_dvd_pow hp_pow |> fun h =>
              (Nat.dvd_prime hr₁_prime).mp h |>.resolve_left hp_prime.ne_one)).elim
          · exact hp_B₁
        exact Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd_B₁, hB₁0⟩
      have hdvd_sigB₁ : sigma 1 (ordProj[p] B) ∣ sigma 1 B₁ :=
        sigma_ordProj_dvd_sigma_of_coprime_left (Nat.prime_of_mem_primeFactors hpB)
          (hB_split.trans (mul_comm _ _)) hB_cop.symm hp_B₁
      exact hr₀_prime.not_dvd_one
        (hcop_r0_B₁ ▸ Nat.dvd_gcd (dvd_refl r₀) (hr0_dvd_p.trans hdvd_sigB₁))
    refine ⟨r₁, hr₁_B, ?_, ?_, hcop_r0_B₁, huniq_r₁, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [he₀] using hr0_dvd_r₁
    · simpa [he₀] using hfact_r₁
    · exact h_proj
    · simpa [he₀] using h_sig_eq
    · simpa [he₀] using hcop_c₁
    · simpa [c₀, he₀] using h_bal
    · simpa [c₀, he₀] using h_lt

/-- **3. Sixth-Power-Free `S₅₁` Unique `q`-Source Descent**:
On any sixth-power-free odd perfect number `N`, combining
`sixth_power_free_unique_q_source_mirror_dichotomy` with
`linear_euler_square_source_coprime_half_succ` and
`linear_euler_square_source_unconditional_split_or_absorber`: whenever the unique `q`-source
`r₀` lies in `squareSources N`, we have `r₀ ∈ (squareSources N).filter (· % 5 = 1)`,
`m.factorization r₀ = 1`, `Nat.Coprime r₀ ((q + 1) / 2)` unconditionally,
`r₀ ^ 2 ∣ sigma 1 (ordCompl[r₀] (m ^ 2))`, and either `r₀` splits across two distinct prime
components of `m` with valuation `1` each or a unique prime `r₁ ∈ (ordCompl[r₀] (m ^ 2)).primeFactors`
absorbs `r₀ ^ 2` (`r₀ ^ 2 ∣ sigma 1 (ordProj[r₁] (m ^ 2))`). -/
theorem sixth_power_free_unique_q_source_S51_forces_descent {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    ∃ m r₀ : ℕ,
      Odd m ∧ ¬ q ∣ m ∧ N = q * m ^ 2 ∧
      r₀ ∈ m.primeFactors ∧
      q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀)) ∧
      (r₀ ∈ squareSources N →
        r₀ ∈ (squareSources N).filter (· % 5 = 1) ∧
        m.factorization r₀ = 1 ∧
        Nat.Coprime r₀ ((q + 1) / 2) ∧
        r₀ ^ 2 ∣ sigma 1 (ordCompl[r₀] (m ^ 2)) ∧
        (sigma 1 (ordCompl[r₀] (m ^ 2))).factorization r₀ = 2 ∧
        let B := ordCompl[r₀] (m ^ 2)
        ((∃ p₁ ∈ B.primeFactors, ∃ p₂ ∈ B.primeFactors,
            p₁ ≠ p₂ ∧
            (sigma 1 (ordProj[p₁] (m ^ 2))).factorization r₀ = 1 ∧
            (sigma 1 (ordProj[p₂] (m ^ 2))).factorization r₀ = 1) ∨
         (∃ r₁ ∈ B.primeFactors,
            r₀ ^ 2 ∣ sigma 1 (ordProj[r₁] (m ^ 2)) ∧
            (sigma 1 (ordProj[r₁] (m ^ 2))).factorization r₀ = 2 ∧
            Nat.Coprime r₀ (sigma 1 (ordCompl[r₁] B)) ∧
            ∀ p ∈ B.primeFactors, r₀ ∣ sigma 1 (ordProj[p] B) → p = r₁))) := by
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  obtain ⟨m, r₀, hm_odd, hqm, hform, hr₀_m, hmul_c0, _, _, _, _, _, _, h_dich⟩ :=
    sixth_power_free_unique_q_source_mirror_dichotomy ho hN hq hq4 he hev hfree
  have hq_dvd : q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀)) := by
    change sigma 1 (r₀ ^ (2 * m.factorization r₀)) = q * (sigma 1 (r₀ ^ (2 * m.factorization r₀)) / q)
      at hmul_c0
    rw [hmul_c0]
    exact dvd_mul_right q _
  refine ⟨m, r₀, hm_odd, hqm, hform, hr₀_m, hq_dvd, fun hr₀_sq => ?_⟩
  have hS51 : r₀ ∈ (squareSources N).filter (· % 5 = 1) ∧ m.factorization r₀ = 1 := by
    rcases h_dich with hsq_branch | hlg_branch
    · exact ⟨Finset.mem_filter.mpr ⟨hr₀_sq, hsq_branch.2.1⟩, hsq_branch.2.2.2.1⟩
    · have h2 : N.factorization r₀ = 2 := (Finset.mem_filter.mp hr₀_sq).2.2
      have h4 : N.factorization r₀ = 4 := hlg_branch.2.2.1
      omega
  obtain ⟨hr₀_S51, he₀⟩ := hS51
  obtain ⟨hcop, _, hr₀_sq_dvd, hsigB_fact⟩ :=
    linear_euler_square_source_coprime_half_succ ho hN hq_prime hqm hform hr₀_m hq_dvd he₀
  obtain ⟨_, _, _, _, hsplit_or_abs⟩ :=
    linear_euler_square_source_unconditional_split_or_absorber
      ho hN hq_prime hqm hform hr₀_m hq_dvd he₀
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀_m
  have hproj_r₀ : ordProj[r₀] (m ^ 2) = r₀ ^ 2 := by
    rw [pow_two, Nat.factorization_mul hm0 hm0, Finsupp.add_apply, ← two_mul, he₀, mul_one]
  have hm2_split : m ^ 2 = ordCompl[r₀] (m ^ 2) * r₀ ^ 2 := by
    rw [mul_comm, ← hproj_r₀]
    exact (Nat.ordProj_mul_ordCompl_eq_self (m ^ 2) r₀).symm
  have hm2_cop : (ordCompl[r₀] (m ^ 2)).Coprime (r₀ ^ 2) := by
    rw [← hproj_r₀]
    exact ((Nat.coprime_ordCompl hr₀_prime hm20).pow_left _).symm
  refine ⟨hr₀_S51, he₀, hcop, hr₀_sq_dvd, hsigB_fact, ?_⟩
  rcases hsplit_or_abs with ⟨⟨p₁, hp₁B, p₂, hp₂B, hp_ne, _, _, hp₁_f, hp₂_f⟩, _⟩ |
      ⟨r₁, hr₁B, hr0_dvd_r₁, hfact_r₁, hcop_r0_B₁, huniq_r₁, _⟩
  · left
    have hp₁_ord : ordProj[p₁] (m ^ 2) = ordProj[p₁] (ordCompl[r₀] (m ^ 2)) :=
      ordProj_eq_of_dvd_coprime_left (Nat.prime_of_mem_primeFactors hp₁B) hm2_split hm2_cop hp₁B
    have hp₂_ord : ordProj[p₂] (m ^ 2) = ordProj[p₂] (ordCompl[r₀] (m ^ 2)) :=
      ordProj_eq_of_dvd_coprime_left (Nat.prime_of_mem_primeFactors hp₂B) hm2_split hm2_cop hp₂B
    exact ⟨p₁, hp₁B, p₂, hp₂B, hp_ne, by rwa [hp₁_ord], by rwa [hp₂_ord]⟩
  · right
    have hr₁_ord : ordProj[r₁] (m ^ 2) = ordProj[r₁] (ordCompl[r₀] (m ^ 2)) :=
      ordProj_eq_of_dvd_coprime_left (Nat.prime_of_mem_primeFactors hr₁B) hm2_split hm2_cop hr₁B
    exact ⟨r₁, hr₁B, by rwa [hr₁_ord], by rwa [hr₁_ord], hcop_r0_B₁, huniq_r₁⟩

private lemma square_peel_step_invariant {B' r e Y : ℕ}
    (hB'_odd : Odd B') (hr : r.Prime) (he : 0 < e) (hY : 1 < Y)
    (heven : ∀ p ∈ B'.primeFactors, Even (B'.factorization p))
    (hnotdvd : ¬ r ∣ B') (hbal : Y * sigma 1 B' = r ^ (2 * e) * B')
    (hr_ndvd_Y : ¬ r ∣ Y)
    (hnocoll : ¬ ∃ r' : ℕ, r'.Prime ∧ ∃ p₁ ∈ B'.primeFactors, ∃ p₂ ∈ B'.primeFactors,
      p₁ ≠ p₂ ∧ r' ∣ sigma 1 (ordProj[p₁] B') ∧ r' ∣ sigma 1 (ordProj[p₂] B')) :
    ∃ r₁ ∈ B'.primeFactors,
      ∃ e₁ : ℕ,
        0 < e₁ ∧
        B'.factorization r₁ = 2 * e₁ ∧
        r ^ (2 * e) ∣ sigma 1 (ordProj[r₁] B') ∧
        let c₁ := sigma 1 (ordProj[r₁] B') / r ^ (2 * e)
        let B₁ := ordCompl[r₁] B'
        1 < Y * c₁ ∧
        Odd B₁ ∧
        ¬ r₁ ∣ B₁ ∧
        (∀ p ∈ B₁.primeFactors, Even (B₁.factorization p)) ∧
        (Y * c₁) * sigma 1 B₁ = r₁ ^ (2 * e₁) * B₁ ∧
        Nat.Coprime c₁ r₁ ∧
        B₁.primeFactors ⊆ B'.primeFactors ∧
        B₁.primeFactors.card < B'.primeFactors.card ∧
        (∀ p ∈ B₁.primeFactors, ordProj[p] B₁ = ordProj[p] B') := by
  have hcop_r_Y : Nat.Coprime r Y := hr.coprime_iff_not_dvd.mpr hr_ndvd_Y
  have hB'_pos : 0 < B' := hB'_odd.pos
  have hB'0 : B' ≠ 0 := hB'_pos.ne'
  obtain ⟨_, _, hpow_dvd_sigB', _, _⟩ :=
    peeling_step_no_terminal_unit_of_coprime hr he hY hB'_pos hnotdvd hcop_r_Y hbal
  have hr_dvd_sigB' : r ∣ sigma 1 B' :=
    (dvd_pow_self r (by omega : 2 * e ≠ 0)).trans hpow_dvd_sigB'
  have hsigB'_prod : sigma 1 B' = ∏ p ∈ B'.primeFactors, sigma 1 (ordProj[p] B') := by
    rw [isMultiplicative_sigma.multiplicative_factorization (sigma 1) hB'0]
    exact Finset.prod_congr B'.support_factorization fun _ _ => rfl
  obtain ⟨r₁, hr₁_B', hr_dvd_r₁⟩ := by
    rw [hsigB'_prod] at hr_dvd_sigB'
    exact (hr.prime.dvd_finsetProd_iff _).mp hr_dvd_sigB'
  have hr₁_prime : r₁.Prime := Nat.prime_of_mem_primeFactors hr₁_B'
  have hr₁_pos_fact : 0 < B'.factorization r₁ :=
    (hr₁_prime.dvd_iff_one_le_factorization hB'0).mp (Nat.dvd_of_mem_primeFactors hr₁_B')
  obtain ⟨e₁, he₁_add⟩ := heven r₁ hr₁_B'
  have hB'_fact_r₁ : B'.factorization r₁ = 2 * e₁ := by omega
  have he₁_pos : 0 < e₁ := by omega
  let B₁ := ordCompl[r₁] B'
  have hB'_split : B' = ordProj[r₁] B' * B₁ := (Nat.ordProj_mul_ordCompl_eq_self B' r₁).symm
  have hB'_cop : (ordProj[r₁] B').Coprime B₁ := (Nat.coprime_ordCompl hr₁_prime hB'0).pow_left _
  have hB₁_odd : Odd B₁ := hB'_odd.of_dvd_nat (Nat.ordCompl_dvd B' r₁)
  have hB₁0 : B₁ ≠ 0 := hB₁_odd.pos.ne'
  have hr₁_ndvd_B₁ : ¬ r₁ ∣ B₁ := Nat.not_dvd_ordCompl hr₁_prime hB'0
  have hB₁_sub : B₁.primeFactors ⊆ B'.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primeFactors hp, (Nat.dvd_of_mem_primeFactors hp).trans (Nat.ordCompl_dvd B' r₁), hB'0⟩
  have h_ordProj_B₁ : ∀ p ∈ B₁.primeFactors, ordProj[p] B₁ = ordProj[p] B' := by
    intro p hp
    exact (ordProj_eq_of_dvd_coprime_left (Nat.prime_of_mem_primeFactors hp)
      (hB'_split.trans (mul_comm _ _)) hB'_cop.symm hp).symm
  have hB₁_even : ∀ p ∈ B₁.primeFactors, Even (B₁.factorization p) := by
    intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have hp_B' := hB₁_sub hp
    have hp_ne : p ≠ r₁ := fun h => hr₁_ndvd_B₁ (h ▸ Nat.dvd_of_mem_primeFactors hp)
    have h1 : B'.factorization p = (ordProj[r₁] B').factorization p + B₁.factorization p := by
      conv_lhs => rw [hB'_split]
      rw [Nat.factorization_mul (pow_ne_zero _ hr₁_prime.ne_zero) hB₁0, Finsupp.add_apply]
    have h2 : (ordProj[r₁] B').factorization p = 0 := by
      rw [hr₁_prime.factorization_pow, Finsupp.single_eq_of_ne hp_ne]
    have h3 : B₁.factorization p = B'.factorization p := by omega
    rw [h3]
    exact heven p hp_B'
  have hr_ndvd_sigB₁ : ¬ r ∣ sigma 1 B₁ := by
    have hsigB₁_prod : sigma 1 B₁ = ∏ p ∈ B₁.primeFactors, sigma 1 (ordProj[p] B₁) := by
      rw [isMultiplicative_sigma.multiplicative_factorization (sigma 1) hB₁0]
      exact Finset.prod_congr B₁.support_factorization fun _ _ => rfl
    rw [hsigB₁_prod, hr.prime.dvd_finsetProd_iff]
    rintro ⟨p, hpB₁, hr_dvd_p⟩
    have hp_B' := hB₁_sub hpB₁
    have hp_ne : p ≠ r₁ := fun h => hr₁_ndvd_B₁ (h ▸ Nat.dvd_of_mem_primeFactors hpB₁)
    rw [h_ordProj_B₁ p hpB₁] at hr_dvd_p
    exact hnocoll ⟨r, hr, r₁, hr₁_B', p, hp_B', hp_ne.symm, hr_dvd_r₁, hr_dvd_p⟩
  have hcop_r_sigB₁ : Nat.Coprime r (sigma 1 B₁) := hr.coprime_iff_not_dvd.mpr hr_ndvd_sigB₁
  have hsigB'_mul : sigma 1 B' = sigma 1 (ordProj[r₁] B') * sigma 1 B₁ := by
    conv_lhs => rw [hB'_split, isMultiplicative_sigma.map_mul_of_coprime hB'_cop]
  have hr_pow_dvd_r₁ : r ^ (2 * e) ∣ sigma 1 (ordProj[r₁] B') := by
    rw [hsigB'_mul] at hpow_dvd_sigB'
    exact (hcop_r_sigB₁.pow_left (2 * e)).dvd_of_dvd_mul_right hpow_dvd_sigB'
  let c₁ := sigma 1 (ordProj[r₁] B') / r ^ (2 * e)
  have hsig_r₁_eq : sigma 1 (ordProj[r₁] B') = r ^ (2 * e) * c₁ :=
    (Nat.mul_div_cancel' hr_pow_dvd_r₁).symm
  have hsig_r₁_ne0 : sigma 1 (ordProj[r₁] B') ≠ 0 :=
    (sigma_pos 1 _ (pow_ne_zero _ hr₁_prime.ne_zero)).ne'
  have hc₁_pos : 0 < c₁ := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, mul_zero] at hsig_r₁_eq
    exact hsig_r₁_ne0 hsig_r₁_eq
  have hYc₁_gt1 : 1 < Y * c₁ := by nlinarith
  have hr₁_ndvd_sig_r₁ : ¬ r₁ ∣ sigma 1 (ordProj[r₁] B') := by
    rw [hB'_fact_r₁, Nat.dvd_iff_mod_eq_zero, sigma_prime_pow_mod_self hr₁_prime]
    decide
  have hr₁_ndvd_c₁ : ¬ r₁ ∣ c₁ := fun h =>
    hr₁_ndvd_sig_r₁ (h.trans ⟨r ^ (2 * e), by rw [hsig_r₁_eq, mul_comm]⟩)
  have hcop_c₁_r₁ : Nat.Coprime c₁ r₁ := (hr₁_prime.coprime_iff_not_dvd.mpr hr₁_ndvd_c₁).symm
  have hr_pow_pos : 0 < r ^ (2 * e) := pow_pos hr.pos _
  have hpeel_bal : (Y * c₁) * sigma 1 B₁ = r₁ ^ (2 * e₁) * B₁ := by
    apply Nat.mul_left_cancel hr_pow_pos
    calc
      r ^ (2 * e) * ((Y * c₁) * sigma 1 B₁)
          = Y * ((r ^ (2 * e) * c₁) * sigma 1 B₁) := by ring
      _ = Y * (sigma 1 (ordProj[r₁] B') * sigma 1 B₁) := by rw [← hsig_r₁_eq]
      _ = Y * sigma 1 B' := by rw [← hsigB'_mul]
      _ = r ^ (2 * e) * B' := hbal
      _ = r ^ (2 * e) * (ordProj[r₁] B' * B₁) := by rw [← hB'_split]
      _ = r ^ (2 * e) * (r₁ ^ (2 * e₁) * B₁) := by
          rw [hB'_fact_r₁]
  have hr₁_notin_B₁ : r₁ ∉ B₁.primeFactors := fun h =>
    hr₁_ndvd_B₁ (Nat.dvd_of_mem_primeFactors h)
  have hcard_lt : B₁.primeFactors.card < B'.primeFactors.card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hB₁_sub, fun heq =>
      hr₁_notin_B₁ (heq ▸ hr₁_B')⟩)
  exact ⟨r₁, hr₁_B', e₁, he₁_pos, hB'_fact_r₁, hr_pow_dvd_r₁, hYc₁_gt1, hB₁_odd,
    hr₁_ndvd_B₁, hB₁_even, hpeel_bal, hcop_c₁_r₁, hB₁_sub, hcard_lt, h_ordProj_B₁⟩

private lemma peeling_chain_dichotomy_aux :
    ∀ k B' r e Y : ℕ,
      B'.primeFactors.card ≤ k →
      Odd B' → r.Prime → 0 < e → 1 < Y →
      (∀ p ∈ B'.primeFactors, Even (B'.factorization p)) →
      ¬ r ∣ B' →
      Y * sigma 1 B' = r ^ (2 * e) * B' →
      (∃ r' : ℕ, r'.Prime ∧
        ∃ p₁ ∈ B'.primeFactors, ∃ p₂ ∈ B'.primeFactors,
          p₁ ≠ p₂ ∧ r' ∣ sigma 1 (ordProj[p₁] B') ∧ r' ∣ sigma 1 (ordProj[p₂] B')) ∨
      r ∣ Y ∨
      (∃ p ∈ B'.primeFactors,
        p ∣ Y ∨ ∃ q' ∈ B'.primeFactors, p ≠ q' ∧ p ∣ sigma 1 (ordProj[q'] B')) := by
  intro k
  induction k with
  | zero =>
    intro B' r e Y hcard hB'_odd hr he hY heven hnotdvd hbal
    by_cases hrY : r ∣ Y
    · exact Or.inr (Or.inl hrY)
    · exfalso
      have hcop : Nat.Coprime r Y := hr.coprime_iff_not_dvd.mpr hrY
      obtain ⟨hB'_gt1, _, _, _, _⟩ :=
        peeling_step_no_terminal_unit_of_coprime hr he hY hB'_odd.pos hnotdvd hcop hbal
      have hcard0 : B'.primeFactors.card = 0 := Nat.le_zero.mp hcard
      have hB'1 : B' = 1 := by
        by_contra hne1
        obtain ⟨p, hp⟩ := Nat.exists_prime_and_dvd hne1
        have hp_mem : p ∈ B'.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hp.1, hp.2, hB'_odd.pos.ne'⟩
        have hpos := Finset.card_pos.mpr ⟨p, hp_mem⟩
        omega
      omega
  | succ k ih =>
    intro B' r e Y hcard hB'_odd hr he hY heven hnotdvd hbal
    by_cases hrY : r ∣ Y
    · exact Or.inr (Or.inl hrY)
    · by_cases hcoll : ∃ r' : ℕ, r'.Prime ∧
        ∃ p₁ ∈ B'.primeFactors, ∃ p₂ ∈ B'.primeFactors,
          p₁ ≠ p₂ ∧ r' ∣ sigma 1 (ordProj[p₁] B') ∧ r' ∣ sigma 1 (ordProj[p₂] B')
      · exact Or.inl hcoll
      · obtain ⟨r₁, hr₁_B', e₁, he₁_pos, hB'_fact_r₁, hr_pow_dvd_r₁, hYc₁_gt1, hB₁_odd,
          hr₁_ndvd_B₁, hB₁_even, hpeel_bal, hcop_c₁_r₁, hB₁_sub, hcard_lt, h_ordProj_B₁⟩ :=
          square_peel_step_invariant hB'_odd hr he hY heven hnotdvd hbal hrY hcoll
        let c₁ := sigma 1 (ordProj[r₁] B') / r ^ (2 * e)
        let B₁ := ordCompl[r₁] B'
        have hr₁_prime : r₁.Prime := Nat.prime_of_mem_primeFactors hr₁_B'
        have hcard_B₁ : B₁.primeFactors.card ≤ k := Nat.le_of_lt_succ (lt_of_lt_of_le hcard_lt hcard)
        obtain h1 | h2 | h3 :=
          ih B₁ r₁ e₁ (Y * c₁) hcard_B₁ hB₁_odd hr₁_prime he₁_pos hYc₁_gt1
            hB₁_even hr₁_ndvd_B₁ hpeel_bal
        · left
          obtain ⟨r', hr', p₁, hp₁, p₂, hp₂, hp_ne, hd₁, hd₂⟩ := h1
          refine ⟨r', hr', p₁, hB₁_sub hp₁, p₂, hB₁_sub hp₂, hp_ne, ?_, ?_⟩
          · rwa [← h_ordProj_B₁ p₁ hp₁]
          · rwa [← h_ordProj_B₁ p₂ hp₂]
        · right; right
          have hr₁_dvd_Y : r₁ ∣ Y := hcop_c₁_r₁.symm.dvd_of_dvd_mul_right h2
          exact ⟨r₁, hr₁_B', Or.inl hr₁_dvd_Y⟩
        · right; right
          obtain ⟨p, hpB₁, hp_or⟩ := h3
          have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hpB₁
          have hp_B' : p ∈ B'.primeFactors := hB₁_sub hpB₁
          have hp_ne_r₁ : p ≠ r₁ := by
            intro h
            have hd : p ∣ B₁ := Nat.dvd_of_mem_primeFactors hpB₁
            rw [h] at hd
            exact hr₁_ndvd_B₁ hd
          refine ⟨p, hp_B', ?_⟩
          rcases hp_or with hp_Yc₁ | ⟨q', hq'B₁, hp_ne_q', hp_dvd_q'⟩
          · rcases hp_prime.dvd_mul.mp hp_Yc₁ with hp_Y | hp_c₁
            · exact Or.inl hp_Y
            · have hp_dvd_sig_r₁ : p ∣ sigma 1 (ordProj[r₁] B') := by
                have h_eq : sigma 1 (ordProj[r₁] B') = r ^ (2 * e) * c₁ :=
                  (Nat.mul_div_cancel' hr_pow_dvd_r₁).symm
                rw [h_eq]
                exact hp_c₁.trans (dvd_mul_left c₁ _)
              exact Or.inr ⟨r₁, hr₁_B', hp_ne_r₁, hp_dvd_sig_r₁⟩
          · rw [h_ordProj_B₁ q' hq'B₁] at hp_dvd_q'
            exact Or.inr ⟨q', hB₁_sub hq'B₁, hp_ne_q', hp_dvd_q'⟩

/-- **4. Finite-Support Iterated Cofactor-Peeling Dichotomy**:
On any odd square `B'` with `¬ r ∣ B'`, `r.Prime`, `0 < e`, `1 < Y`, and balance
`Y * sigma 1 B' = r ^ (2 * e) * B'`, either two distinct prime components of `B'` share a prime
divisor `r*`, or `r ∣ Y`, or some `p ∈ B'.primeFactors` divides `Y` or another prime component
of `B'`. -/
theorem peeling_chain_dichotomy_on_finite_square {B' r e Y : ℕ}
    (hB'_odd : Odd B') (hr : r.Prime) (he : 0 < e) (hY : 1 < Y)
    (heven : ∀ p ∈ B'.primeFactors, Even (B'.factorization p))
    (hnotdvd : ¬ r ∣ B') (hbal : Y * sigma 1 B' = r ^ (2 * e) * B') :
    (∃ r' : ℕ, r'.Prime ∧
      ∃ p₁ ∈ B'.primeFactors, ∃ p₂ ∈ B'.primeFactors,
        p₁ ≠ p₂ ∧
        r' ∣ sigma 1 (ordProj[p₁] B') ∧
        r' ∣ sigma 1 (ordProj[p₂] B')) ∨
    r ∣ Y ∨
    (∃ p ∈ B'.primeFactors,
      p ∣ Y ∨ ∃ q' ∈ B'.primeFactors, p ≠ q' ∧ p ∣ sigma 1 (ordProj[q'] B')) :=
  peeling_chain_dichotomy_aux B'.primeFactors.card B' r e Y le_rfl
    hB'_odd hr he hY heven hnotdvd hbal

private def PeelingChain (m : ℕ) : List ℕ → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest =>
      b ^ (2 * m.factorization b) ∣ sigma 1 (ordProj[a] (m ^ 2)) ∧
      PeelingChain m (b :: rest)

private lemma peelingChain_to_getElem {m : ℕ} :
    ∀ L : List ℕ, PeelingChain m L →
      ∀ i : ℕ, ∀ (hi : i + 1 < L.length),
        L[i + 1] ^ (2 * m.factorization L[i + 1]) ∣ sigma 1 (ordProj[L[i]] (m ^ 2))
  | [], _, _, hi => by simp at hi
  | [_], _, _, hi => by simp at hi
  | _ :: b :: rest, hchain, 0, _ => hchain.1
  | _ :: b :: rest, hchain, i + 1, hi =>
    peelingChain_to_getElem (b :: rest) hchain.2 i (by simpa using hi)

private lemma extract_peeling_prefix {m a c : ℕ} :
    ∀ {rest : List ℕ},
      c ∈ rest →
      (a :: rest).Nodup →
      (∀ x ∈ a :: rest, x ∈ m.primeFactors) →
      PeelingChain m (a :: rest) →
      ∃ L : List ℕ,
        2 ≤ L.length ∧
        L.Nodup ∧
        (∀ x ∈ L, x ∈ m.primeFactors) ∧
        PeelingChain m L ∧
        (∀ h : L ≠ [], L.head h = a ∧ L.getLast h = c) ∧
        (∀ x ∈ L, x ∈ a :: rest)
  | [], hc, _, _, _ => by simp at hc
  | b :: rest', hc, hnodup, hm, hchain => by
    rcases List.mem_cons.mp hc with rfl | hc_rest
    · refine ⟨[a, c], by simp, ?_, ?_, ⟨hchain.1, trivial⟩, fun _ => ⟨rfl, rfl⟩, ?_⟩
      · rw [List.nodup_cons]
        refine ⟨fun h => ?_, List.nodup_singleton c⟩
        have ha_notin : a ∉ c :: rest' := (List.nodup_cons.mp hnodup).1
        rw [List.mem_singleton.mp h] at ha_notin
        exact ha_notin List.mem_cons_self
      · intro x hx
        rcases List.mem_cons.mp hx with hx_eq | hx'
        · rw [hx_eq]
          exact hm _ List.mem_cons_self
        · rw [List.mem_singleton.mp hx']
          exact hm _ (List.mem_cons_of_mem _ List.mem_cons_self)
      · intro x hx
        rcases List.mem_cons.mp hx with hx_eq | hx'
        · rw [hx_eq]
          exact List.mem_cons_self
        · rw [List.mem_singleton.mp hx']
          exact List.mem_cons_of_mem _ List.mem_cons_self
    · have hnodup' : (b :: rest').Nodup := (List.nodup_cons.mp hnodup).2
      have hm' : ∀ x ∈ b :: rest', x ∈ m.primeFactors := fun x hx => hm x (by simp [hx])
      obtain ⟨L, hlen, hL_nodup, hL_m, hL_chain, hL_ends, hL_sub⟩ :=
        extract_peeling_prefix (a := b) hc_rest hnodup' hm' hchain.2
      have ha_notin_rest : a ∉ b :: rest' := (List.nodup_cons.mp hnodup).1
      have ha_notin_L : a ∉ L := fun ha => ha_notin_rest (hL_sub a ha)
      have hL_ne : L ≠ [] := by
        intro h0
        rw [h0] at hlen
        simp at hlen
      have h_ends := hL_ends hL_ne
      have h_chain_aL : PeelingChain m (a :: L) := by
        cases L with
        | nil => exact (hL_ne rfl).elim
        | cons b' L' =>
          have hb'_eq : b' = b := h_ends.1
          subst hb'_eq
          exact ⟨hchain.1, hL_chain⟩
      refine ⟨a :: L, by simp; omega, List.nodup_cons.mpr ⟨ha_notin_L, hL_nodup⟩, ?_,
        h_chain_aL, fun _ => ⟨rfl, ?_⟩, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with hx_eq | hxL
        · rw [hx_eq]
          exact hm _ List.mem_cons_self
        · exact hL_m x hxL
      · rw [List.getLast_cons hL_ne]
        exact h_ends.2
      · intro x hx
        rcases List.mem_cons.mp hx with hx_eq | hxL
        · rw [hx_eq]
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hL_sub x hxL)

private lemma peeling_chain_history_aux {m Y₀ : ℕ} (hm_odd : Odd m) :
    ∀ k B' r e Y : ℕ, ∀ prev : List ℕ,
      B'.primeFactors.card ≤ k →
      Odd B' →
      r.Prime →
      0 < e →
      1 < Y →
      (∀ p ∈ B'.primeFactors, Even (B'.factorization p)) →
      ¬ r ∣ B' →
      Y * sigma 1 B' = r ^ (2 * e) * B' →
      e = m.factorization r →
      (∀ p ∈ B'.primeFactors, p ∈ m.primeFactors ∧ ordProj[p] B' = ordProj[p] (m ^ 2)) →
      (r :: prev).Nodup →
      (∀ x ∈ r :: prev, x ∈ m.primeFactors) →
      (∀ x ∈ prev, ¬ x ∣ B') →
      PeelingChain m (r :: prev) →
      (∀ p : ℕ, p.Prime → p ∣ Y →
        p ∣ Y₀ ∨ ∃ c ∈ r :: prev, p ∣ sigma 1 (ordProj[c] (m ^ 2))) →
      (∃ r' : ℕ, r'.Prime ∧
        ∃ p₁ ∈ m.primeFactors, ∃ p₂ ∈ m.primeFactors,
          p₁ ≠ p₂ ∧
          r' ∣ sigma 1 (ordProj[p₁] (m ^ 2)) ∧
          r' ∣ sigma 1 (ordProj[p₂] (m ^ 2))) ∨
      (∃ p ∈ m.primeFactors, p ∣ Y₀) ∨
      (∃ L : List ℕ,
        2 ≤ L.length ∧
        L.Nodup ∧
        (∀ p ∈ L, p ∈ m.primeFactors) ∧
        (∀ i : ℕ, ∀ (hi : i + 1 < L.length),
          L[i + 1] ^ (2 * m.factorization L[i + 1]) ∣ sigma 1 (ordProj[L[i]] (m ^ 2))) ∧
        (∀ hL : L ≠ [], L.head hL ∣ sigma 1 (ordProj[L.getLast hL] (m ^ 2)))) := by
  intro k
  induction k with
  | zero =>
    intro B' r e Y prev hcard hB'_odd hr he hY heven hnotdvd hbal _ _ hnodup hm_list _ hchain hY_src
    by_cases hrY : r ∣ Y
    · rcases hY_src r hr hrY with hr_Y0 | ⟨c, hc_mem, hr_dvd_c⟩
      · exact Or.inr (Or.inl ⟨r, hm_list r (by simp), hr_Y0⟩)
      · rcases List.mem_cons.mp hc_mem with hc_eq | hc_prev
        · exfalso
          rw [hc_eq] at hr_dvd_c
          have hm0 : m ≠ 0 := hm_odd.pos.ne'
          have hr_pow_eq : ordProj[r] (m ^ 2) = r ^ (2 * m.factorization r) := by
            rw [pow_two, Nat.factorization_mul hm0 hm0, Finsupp.add_apply, ← two_mul]
          rw [hr_pow_eq, Nat.dvd_iff_mod_eq_zero, sigma_prime_pow_mod_self hr] at hr_dvd_c
          omega
        · obtain ⟨L, hlen, hL_nodup, hL_m, hL_chain, hL_ends, _⟩ :=
            extract_peeling_prefix hc_prev hnodup hm_list hchain
          right; right
          refine ⟨L, hlen, hL_nodup, hL_m, peelingChain_to_getElem L hL_chain, fun hL => ?_⟩
          rw [(hL_ends hL).1, (hL_ends hL).2]
          exact hr_dvd_c
    · exfalso
      have hcop : Nat.Coprime r Y := hr.coprime_iff_not_dvd.mpr hrY
      obtain ⟨hB'_gt1, _, _, _, _⟩ :=
        peeling_step_no_terminal_unit_of_coprime hr he hY hB'_odd.pos hnotdvd hcop hbal
      have hcard0 : B'.primeFactors.card = 0 := Nat.le_zero.mp hcard
      have hB'1 : B' = 1 := by
        by_contra hne1
        obtain ⟨p, hp⟩ := Nat.exists_prime_and_dvd hne1
        have hp_mem : p ∈ B'.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hp.1, hp.2, hB'_odd.pos.ne'⟩
        have hpos := Finset.card_pos.mpr ⟨p, hp_mem⟩
        omega
      omega
  | succ k ih =>
    intro B' r e Y prev hcard hB'_odd hr he hY heven hnotdvd hbal he_eq hB'_info
      hnodup hm_list hprev_ndvd hchain hY_src
    by_cases hrY : r ∣ Y
    · rcases hY_src r hr hrY with hr_Y0 | ⟨c, hc_mem, hr_dvd_c⟩
      · exact Or.inr (Or.inl ⟨r, hm_list r (by simp), hr_Y0⟩)
      · rcases List.mem_cons.mp hc_mem with hc_eq | hc_prev
        · exfalso
          rw [hc_eq] at hr_dvd_c
          have hm0 : m ≠ 0 := hm_odd.pos.ne'
          have hr_pow_eq : ordProj[r] (m ^ 2) = r ^ (2 * m.factorization r) := by
            rw [pow_two, Nat.factorization_mul hm0 hm0, Finsupp.add_apply, ← two_mul]
          rw [hr_pow_eq, Nat.dvd_iff_mod_eq_zero, sigma_prime_pow_mod_self hr] at hr_dvd_c
          omega
        · obtain ⟨L, hlen, hL_nodup, hL_m, hL_chain, hL_ends, _⟩ :=
            extract_peeling_prefix hc_prev hnodup hm_list hchain
          right; right
          refine ⟨L, hlen, hL_nodup, hL_m, peelingChain_to_getElem L hL_chain, fun hL => ?_⟩
          rw [(hL_ends hL).1, (hL_ends hL).2]
          exact hr_dvd_c
    · by_cases hcoll : ∃ r' : ℕ, r'.Prime ∧
        ∃ p₁ ∈ B'.primeFactors, ∃ p₂ ∈ B'.primeFactors,
          p₁ ≠ p₂ ∧ r' ∣ sigma 1 (ordProj[p₁] B') ∧ r' ∣ sigma 1 (ordProj[p₂] B')
      · left
        obtain ⟨r', hr', p₁, hp₁, p₂, hp₂, hp_ne, hd₁, hd₂⟩ := hcoll
        refine ⟨r', hr', p₁, (hB'_info p₁ hp₁).1, p₂, (hB'_info p₂ hp₂).1, hp_ne, ?_, ?_⟩
        · rwa [← (hB'_info p₁ hp₁).2]
        · rwa [← (hB'_info p₂ hp₂).2]
      · obtain ⟨r₁, hr₁_B', e₁, he₁_pos, hB'_fact_r₁, hr_pow_dvd_r₁, hYc₁_gt1, hB₁_odd,
          hr₁_ndvd_B₁, hB₁_even, hpeel_bal, _, hB₁_sub, hcard_lt, h_ordProj_B₁⟩ :=
          square_peel_step_invariant hB'_odd hr he hY heven hnotdvd hbal hrY hcoll
        let c₁ := sigma 1 (ordProj[r₁] B') / r ^ (2 * e)
        let B₁ := ordCompl[r₁] B'
        have hr₁_prime : r₁.Prime := Nat.prime_of_mem_primeFactors hr₁_B'
        have hm0 : m ≠ 0 := hm_odd.pos.ne'
        have he₁_eq : e₁ = m.factorization r₁ := by
          have hr₁_m2_ord : ordProj[r₁] (m ^ 2) = ordProj[r₁] B' := (hB'_info r₁ hr₁_B').2.symm
          have h1 : ordProj[r₁] (m ^ 2) = r₁ ^ (2 * m.factorization r₁) := by
            rw [pow_two, Nat.factorization_mul hm0 hm0, Finsupp.add_apply, ← two_mul]
          have h2 : ordProj[r₁] B' = r₁ ^ (2 * e₁) := by
            rw [hB'_fact_r₁]
          have hpow_eq : r₁ ^ (2 * m.factorization r₁) = r₁ ^ (2 * e₁) := by
            rw [← h1, hr₁_m2_ord, h2]
          have hinj := Nat.pow_right_injective hr₁_prime.two_le hpow_eq
          omega
        have hB₁_info : ∀ p ∈ B₁.primeFactors,
            p ∈ m.primeFactors ∧ ordProj[p] B₁ = ordProj[p] (m ^ 2) := by
          intro p hp
          exact ⟨(hB'_info p (hB₁_sub hp)).1, (h_ordProj_B₁ p hp).trans (hB'_info p (hB₁_sub hp)).2⟩
        have hr₁_notin_r_prev : r₁ ∉ r :: prev := by
          intro hmem
          rcases List.mem_cons.mp hmem with rfl | hr₁_prev
          · exact hnotdvd (Nat.dvd_of_mem_primeFactors hr₁_B')
          · exact hprev_ndvd r₁ hr₁_prev (Nat.dvd_of_mem_primeFactors hr₁_B')
        have hnodup' : (r₁ :: r :: prev).Nodup := List.nodup_cons.mpr ⟨hr₁_notin_r_prev, hnodup⟩
        have hm_list' : ∀ x ∈ r₁ :: r :: prev, x ∈ m.primeFactors := by
          intro x hx
          rcases List.mem_cons.mp hx with hx_eq | hx'
          · rw [hx_eq]
            exact (hB'_info r₁ hr₁_B').1
          · exact hm_list x hx'
        have hprev_ndvd' : ∀ x ∈ r :: prev, ¬ x ∣ B₁ := by
          intro x hx hdvd
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hnotdvd (hdvd.trans (Nat.ordCompl_dvd B' r₁))
          · exact hprev_ndvd x hx' (hdvd.trans (Nat.ordCompl_dvd B' r₁))
        have hchain' : PeelingChain m (r₁ :: r :: prev) := by
          have hr_edge : r ^ (2 * m.factorization r) ∣ sigma 1 (ordProj[r₁] (m ^ 2)) := by
            rw [← he_eq, ← (hB'_info r₁ hr₁_B').2]
            exact hr_pow_dvd_r₁
          exact ⟨hr_edge, hchain⟩
        have hY_src' : ∀ p : ℕ, p.Prime → p ∣ Y * c₁ →
            p ∣ Y₀ ∨ ∃ c ∈ r₁ :: r :: prev, p ∣ sigma 1 (ordProj[c] (m ^ 2)) := by
          intro p hp hp_Yc₁
          rcases hp.dvd_mul.mp hp_Yc₁ with hp_Y | hp_c₁
          · rcases hY_src p hp hp_Y with hp_Y0 | ⟨c, hc_mem, hp_c⟩
            · exact Or.inl hp_Y0
            · exact Or.inr ⟨c, List.mem_cons_of_mem r₁ hc_mem, hp_c⟩
          · refine Or.inr ⟨r₁, by simp, ?_⟩
            have h_eq : sigma 1 (ordProj[r₁] B') = r ^ (2 * e) * c₁ :=
              (Nat.mul_div_cancel' hr_pow_dvd_r₁).symm
            rw [← (hB'_info r₁ hr₁_B').2, h_eq]
            exact hp_c₁.trans (dvd_mul_left c₁ _)
        have hcard_B₁ : B₁.primeFactors.card ≤ k := Nat.le_of_lt_succ (lt_of_lt_of_le hcard_lt hcard)
        exact ih B₁ r₁ e₁ (Y * c₁) (r :: prev) hcard_B₁ hB₁_odd hr₁_prime he₁_pos hYc₁_gt1
          hB₁_even hr₁_ndvd_B₁ hpeel_bal he₁_eq hB₁_info hnodup' hm_list' hprev_ndvd' hchain' hY_src'

/-- **5. Linear Euler Iterated Peeling Collision, Half-Successor Hit, or Directed Cycle**:
On every linear Euler odd perfect number `N = q * m ^ 2`, iterated cofactor peeling from
the unique `q`-source `r₀` terminates in one of three global structural configurations:
1. **(Collision)**: Two distinct primes `p₁ ≠ p₂` in `m.primeFactors` share a prime divisor
   `r*` dividing both `sigma 1 (ordProj[p₁] (m ^ 2))` and `sigma 1 (ordProj[p₂] (m ^ 2))`.
2. **(Half-successor hit)**: Some prime `p ∈ m.primeFactors` divides `(q + 1) / 2`.
3. **(Directed `σ`-cycle)**: There exists a `Nodup` cycle `L` of length `≥ 2` in
   `m.primeFactors` where `L[i + 1] ^ (2 * m.factorization L[i + 1]) ∣ sigma 1 (ordProj[L[i]] (m ^ 2))`
   along every edge and `L.head ∣ sigma 1 (ordProj[L.getLast] (m ^ 2))` closes the cycle. -/
theorem linear_euler_peeling_collision_or_cycle {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2) :
    (∃ r' : ℕ, r'.Prime ∧
      ∃ p₁ ∈ m.primeFactors, ∃ p₂ ∈ m.primeFactors,
        p₁ ≠ p₂ ∧
        r' ∣ sigma 1 (ordProj[p₁] (m ^ 2)) ∧
        r' ∣ sigma 1 (ordProj[p₂] (m ^ 2))) ∨
    (∃ p ∈ m.primeFactors, p ∣ (q + 1) / 2) ∨
    (∃ L : List ℕ,
      2 ≤ L.length ∧
      L.Nodup ∧
      (∀ p ∈ L, p ∈ m.primeFactors) ∧
      (∀ i : ℕ, ∀ (hi : i + 1 < L.length),
        L[i + 1] ^ (2 * m.factorization L[i + 1]) ∣ sigma 1 (ordProj[L[i]] (m ^ 2))) ∧
      (∀ hL : L ≠ [], L.head hL ∣ sigma 1 (ordProj[L.getLast hL] (m ^ 2)))) := by
  obtain ⟨r₀, hr₀_m, hmul_c0, _, hc0_odd, _, _, h_bal, _, _, _⟩ :=
    linear_euler_cofactor_quotient_structure ho hN hq hqm hform
  let e₀ := m.factorization r₀
  let B := ordCompl[r₀] (m ^ 2)
  let c₀ := sigma 1 (r₀ ^ (2 * e₀)) / q
  have hqodd : Odd q := ho.of_dvd_nat (hform ▸ dvd_mul_right q (m ^ 2))
  have hmodd : Odd m :=
    ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
  have hm0 : m ≠ 0 := hmodd.pos.ne'
  have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀_m
  have he₀_pos : 0 < e₀ :=
    (hr₀_prime.dvd_iff_one_le_factorization hm0).mp (Nat.dvd_of_mem_primeFactors hr₀_m)
  have hB_odd : Odd B := hmodd.pow.of_dvd_nat (Nat.ordCompl_dvd (m ^ 2) r₀)
  have hB0 : B ≠ 0 := hB_odd.pos.ne'
  have hr₀_ndvd_B : ¬ r₀ ∣ B := Nat.not_dvd_ordCompl hr₀_prime hm20
  have hq_ge3 : 3 ≤ q := by
    have := hq.two_le
    have := Nat.odd_iff.mp hqodd
    omega
  have hhalf_ge2 : 2 ≤ (q + 1) / 2 := by omega
  have hc0_pos : 1 ≤ c₀ := hc0_odd.pos
  have hY_gt1 : 1 < ((q + 1) / 2) * c₀ := by nlinarith
  have hq1_even : q + 1 = 2 * ((q + 1) / 2) := by
    have := Nat.odd_iff.mp hqodd
    omega
  have h_half_bal : (((q + 1) / 2) * c₀) * sigma 1 B = r₀ ^ (2 * e₀) * B := by
    apply Nat.mul_left_cancel (by decide : 0 < 2)
    calc
      2 * ((((q + 1) / 2) * c₀) * sigma 1 B)
          = (2 * ((q + 1) / 2)) * c₀ * sigma 1 B := by ring
      _ = (q + 1) * c₀ * sigma 1 B := by rw [← hq1_even]
      _ = 2 * r₀ ^ (2 * e₀) * B := h_bal
      _ = 2 * (r₀ ^ (2 * e₀) * B) := by ring
  have hproj_r₀ : ordProj[r₀] (m ^ 2) = r₀ ^ (2 * e₀) := by
    dsimp [e₀]
    rw [pow_two, Nat.factorization_mul hm0 hm0, Finsupp.add_apply, ← two_mul]
  have hm2_split : m ^ 2 = B * r₀ ^ (2 * e₀) := by
    rw [mul_comm, ← hproj_r₀]
    exact (Nat.ordProj_mul_ordCompl_eq_self (m ^ 2) r₀).symm
  have hm2_cop : B.Coprime (r₀ ^ (2 * e₀)) := by
    rw [← hproj_r₀]
    exact ((Nat.coprime_ordCompl hr₀_prime hm20).pow_left _).symm
  have hB_info : ∀ p ∈ B.primeFactors,
      p ∈ m.primeFactors ∧ ordProj[p] B = ordProj[p] (m ^ 2) := by
    intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have hp_dvd_m2 : p ∣ m ^ 2 := (Nat.dvd_of_mem_primeFactors hp).trans (Nat.ordCompl_dvd (m ^ 2) r₀)
    have hp_m : p ∈ m.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp_prime, hp_prime.dvd_of_dvd_pow hp_dvd_m2, hm0⟩
    have hord : ordProj[p] B = ordProj[p] (m ^ 2) :=
      (ordProj_eq_of_dvd_coprime_left hp_prime hm2_split hm2_cop hp).symm
    exact ⟨hp_m, hord⟩
  have hB_even : ∀ p ∈ B.primeFactors, Even (B.factorization p) := by
    intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have h1 : B.factorization p = (m ^ 2).factorization p := by
      have hne : p ≠ r₀ := fun h => hr₀_ndvd_B (h ▸ Nat.dvd_of_mem_primeFactors hp)
      have h_mul : (m ^ 2).factorization p = B.factorization p + (r₀ ^ (2 * e₀)).factorization p := by
        conv_lhs => rw [hm2_split]
        rw [Nat.factorization_mul hB0 (pow_ne_zero _ hr₀_prime.ne_zero), Finsupp.add_apply]
      have h_pow : (r₀ ^ (2 * e₀)).factorization p = 0 := by
        rw [hr₀_prime.factorization_pow, Finsupp.single_eq_of_ne hne]
      omega
    rw [h1, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    exact ⟨m.factorization p, by ring⟩
  have hY_src : ∀ p : ℕ, p.Prime → p ∣ ((q + 1) / 2) * c₀ →
      p ∣ (q + 1) / 2 ∨ ∃ c ∈ [r₀], p ∣ sigma 1 (ordProj[c] (m ^ 2)) := by
    intro p hp hp_mul
    rcases hp.dvd_mul.mp hp_mul with hp_half | hp_c0
    · exact Or.inl hp_half
    · refine Or.inr ⟨r₀, by simp, ?_⟩
      rw [hproj_r₀]
      have hc0_eq : sigma 1 (r₀ ^ (2 * e₀)) = q * c₀ := hmul_c0
      rw [hc0_eq]
      exact hp_c0.trans (dvd_mul_left c₀ q)
  exact peeling_chain_history_aux (Y₀ := (q + 1) / 2) hmodd B.primeFactors.card
    B r₀ e₀ (((q + 1) / 2) * c₀) [] le_rfl hB_odd hr₀_prime he₀_pos hY_gt1
    hB_even hr₀_ndvd_B h_half_bal rfl hB_info (List.nodup_singleton r₀)
    (fun x hx => by rw [List.mem_singleton.mp hx]; exact hr₀_m)
    (fun x hx => by simp at hx) trivial hY_src

end OddPerfect