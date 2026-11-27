module

public import OddPerfect.LinearEulerCofactor
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Linear Euler Tóth-Split Cofactor Obstruction

Develops unconditional structural obstructions on the unique `q`-source `r₀ ∈ m.primeFactors`
and complementary square `B := ordCompl[r₀] (m ^ 2)` on the linear Euler branch `N = q * m ^ 2`:

1. `linear_euler_cofactor_strict_bound`:
   Proves `1 < B`, `B < sigma 1 B`, and the strict inequalities
   `(q + 1) * c₀ < 2 * r₀ ^ (2 * e₀)`, `((q + 1) / 2) * c₀ < r₀ ^ (2 * e₀)`, and
   `(q + 1) / 2 < r₀ ^ (2 * e₀)`.
2. `linear_euler_unique_source_dvd_sigma_B_and_index`:
   Proves `¬ r₀ ^ (2 * e₀) ∣ (q + 1) / 2`, `r₀ ∣ sigma 1 B`, `r₀ ∣ i_q`,
   `r₀ ∈ (sigma 1 B).primeFactors`, `r₀ ∈ i_q.primeFactors`, and
   `∃ p ∈ B.primeFactors, r₀ ∣ sigma 1 (ordProj[p] B)`.
3. `linear_euler_r0_full_pow_or_c0_congruence`:
   Establishes the exact dichotomy between full-power absorption
   (`Nat.Coprime r₀ ((q + 1) / 2) ∧ r₀ ^ (2 * e₀) ∣ sigma 1 B ∧ r₀ ^ (2 * e₀) ∣ i_q`)
   and the congruence-bound branch
   (`r₀ ∣ (q + 1) / 2 ∧ 2 * r₀ ∣ c₀ + 1 ∧ 2 * r₀ - 1 ≤ c₀ ∧ (q + 1) * (2 * r₀ - 1) < 2 * r₀ ^ (2 * e₀) ∧ r₀ ∣ sigma 1 B`).
4. `linear_euler_pure_prime_source_full_pow_and_gap`:
   Specializes to `sigma 1 (r₀ ^ (2 * e₀)) = q` (`c₀ = 1`), proving full-power absorption,
   `r₀ ^ (2 * e₀) < q + 1 < 2 * r₀ ^ (2 * e₀)`, `sigma 1 B < 2 * B`, and the exact deficiency identity
   `(q + 1) * (2 * B - sigma 1 B) = 2 * (q + 1 - r₀ ^ (2 * e₀)) * B`.
5. `linear_euler_toth_split_absorption_profile`:
   Combines with `tothPair_of_linear_euler` and `tothPair_sigma_dvd_index_iff_coprime` to show
   that on any coprime split `B = B₁ * B₂`, both `sigma 1 B₁` and `sigma 1 B₂` divide `i_q` and
   are coprime to `q`, and at least one is divisible by `r₀`.
-/

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- Helper packaging `linear_euler_cofactor_quotient_structure` together with `2 * q < 3 * r₀ ^ (2 * e₀)`
for an explicit `q`-source `r₀ ∈ m.primeFactors`. -/
theorem linear_euler_cofactor_quotient_structure_of_source {N q m r₀ : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hr₀ : r₀ ∈ m.primeFactors) (hq_dvd : q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀))) :
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
    r₀ ^ (2 * e₀) ∣ ((q + 1) / 2) * sigma 1 B ∧
    2 * q < 3 * r₀ ^ (2 * e₀) := by
  obtain ⟨_, r₁, hr₁_m, _, _, _, hbound₁, huniq⟩ :=
    linear_euler_unique_q_source_and_bound ho hN hq hqm hform
  have hr_eq1 : r₀ = r₁ := huniq r₀ hr₀ hq_dvd
  obtain ⟨r₂, hr₂_m, h2⟩ := linear_euler_cofactor_quotient_structure ho hN hq hqm hform
  have hq_dvd2 : q ∣ sigma 1 (r₂ ^ (2 * m.factorization r₂)) := by
    have := h2.1
    rw [this]
    exact dvd_mul_right q _
  have hr_eq2 : r₂ = r₁ := huniq r₂ hr₂_m hq_dvd2
  have hr₀_eq : r₀ = r₂ := hr_eq1.trans hr_eq2.symm
  subst hr₀_eq
  refine ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2.1, h2.2.2.2.2.2.1,
    h2.2.2.2.2.2.2.1, h2.2.2.2.2.2.2.2, ?_⟩
  simpa [hr_eq2] using hbound₁

/-- Explicit-source version of `linear_euler_cofactor_strict_bound`. -/
theorem linear_euler_cofactor_strict_bound_of_source {N q m r₀ : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hr₀ : r₀ ∈ m.primeFactors) (hq_dvd : q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀))) :
    let e₀ := m.factorization r₀
    let B := ordCompl[r₀] (m ^ 2)
    let c₀ := sigma 1 (r₀ ^ (2 * e₀)) / q
    1 < B ∧
    B < sigma 1 B ∧
    (q + 1) * c₀ < 2 * r₀ ^ (2 * e₀) ∧
    ((q + 1) / 2) * c₀ < r₀ ^ (2 * e₀) ∧
    (q + 1) / 2 < r₀ ^ (2 * e₀) := by
  let e₀ := m.factorization r₀
  let B := ordCompl[r₀] (m ^ 2)
  let c₀ := sigma 1 (r₀ ^ (2 * e₀)) / q
  obtain ⟨_, _, hc0_odd, _, _, h_bal, hc0_dvd_B, _, hbound⟩ :=
    linear_euler_cofactor_quotient_structure_of_source ho hN hq hqm hform hr₀ hq_dvd
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
  have he₀_pos : 0 < e₀ := by
    dsimp [e₀]
    exact (hr₀_prime.dvd_iff_one_le_factorization hm0).mp (Nat.dvd_of_mem_primeFactors hr₀)
  have hpow_ge9 : 9 ≤ r₀ ^ (2 * e₀) := by
    have h1 : 3 ^ 2 ≤ r₀ ^ 2 := Nat.pow_le_pow_left hr₀_ge3 2
    have h2 : r₀ ^ 2 ≤ r₀ ^ (2 * e₀) := Nat.pow_le_pow_right hr₀_prime.pos (by omega)
    omega
  have hB_pos : 0 < B := Nat.ordCompl_pos r₀ hm20
  dsimp only [e₀, B, c₀] at h_bal hc0_dvd_B hbound ⊢
  have hB_gt1 : 1 < B := by
    by_contra hle
    have hB1 : B = 1 := by omega
    have hc0_1 : c₀ = 1 := Nat.dvd_one.mp (by change c₀ ∣ B at hc0_dvd_B; rwa [hB1] at hc0_dvd_B)
    have hsig1 : sigma 1 B = 1 := by rw [hB1, sigma_one 1]
    have hq_eq : q + 1 = 2 * r₀ ^ (2 * e₀) := by
      have hb := h_bal
      change (q + 1) * c₀ * sigma 1 B = 2 * r₀ ^ (2 * e₀) * B at hb
      rw [hc0_1, hsig1, hB1] at hb
      simpa using hb
    have hbound' : 2 * q < 3 * r₀ ^ (2 * e₀) := hbound
    omega
  have hB_lt_sig : B < sigma 1 B := self_lt_sigma_of_one_lt hB_gt1
  have h_strict1 : (q + 1) * c₀ < 2 * r₀ ^ (2 * e₀) := by
    by_contra! hle
    have h_pos_lhs : 0 < (q + 1) * c₀ := Nat.mul_pos (Nat.succ_pos q) hc0_odd.pos
    have h1 : 2 * r₀ ^ (2 * e₀) * B ≤ (q + 1) * c₀ * B :=
      Nat.mul_le_mul_right B hle
    have h2 : (q + 1) * c₀ * B < (q + 1) * c₀ * sigma 1 B :=
      Nat.mul_lt_mul_of_pos_left hB_lt_sig h_pos_lhs
    have hb : (q + 1) * c₀ * sigma 1 B = 2 * r₀ ^ (2 * e₀) * B := h_bal
    linarith
  have hq1_even : q + 1 = 2 * ((q + 1) / 2) := by
    have := Nat.odd_iff.mp hqodd
    omega
  have h_strict2 : ((q + 1) / 2) * c₀ < r₀ ^ (2 * e₀) := by
    have : 2 * (((q + 1) / 2) * c₀) < 2 * r₀ ^ (2 * e₀) := by
      calc
        2 * (((q + 1) / 2) * c₀) = (2 * ((q + 1) / 2)) * c₀ := by ring
        _ = (q + 1) * c₀ := by rw [← hq1_even]
        _ < 2 * r₀ ^ (2 * e₀) := h_strict1
    omega
  have h_strict3 : (q + 1) / 2 < r₀ ^ (2 * e₀) := by
    have hc0_pos : 1 ≤ c₀ := hc0_odd.pos
    have hle : (q + 1) / 2 ≤ ((q + 1) / 2) * c₀ := Nat.le_mul_of_pos_right _ hc0_pos
    exact lt_of_le_of_lt hle h_strict2
  exact ⟨hB_gt1, hB_lt_sig, h_strict1, h_strict2, h_strict3⟩

/-- **1. Strict Cofactor Bound on `N = q * m ^ 2`**:
On the linear Euler branch `N = q * m ^ 2`, the complementary square `B := ordCompl[r₀] (m ^ 2)`
satisfies `1 < B < σ(B)`, forcing `(q + 1) * c₀ < 2 * r₀ ^ (2 * e₀)`,
`((q + 1) / 2) * c₀ < r₀ ^ (2 * e₀)`, and `(q + 1) / 2 < r₀ ^ (2 * e₀)`. -/
theorem linear_euler_cofactor_strict_bound {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2) :
    ∃ r₀ ∈ m.primeFactors,
      q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀)) ∧
      let e₀ := m.factorization r₀
      let B := ordCompl[r₀] (m ^ 2)
      let c₀ := sigma 1 (r₀ ^ (2 * e₀)) / q
      1 < B ∧
      B < sigma 1 B ∧
      (q + 1) * c₀ < 2 * r₀ ^ (2 * e₀) ∧
      ((q + 1) / 2) * c₀ < r₀ ^ (2 * e₀) ∧
      (q + 1) / 2 < r₀ ^ (2 * e₀) := by
  obtain ⟨_, r₀, hr₀_m, hq_dvd, _, _, _, _⟩ :=
    linear_euler_unique_q_source_and_bound ho hN hq hqm hform
  exact ⟨r₀, hr₀_m, hq_dvd,
    linear_euler_cofactor_strict_bound_of_source ho hN hq hqm hform hr₀_m hq_dvd⟩

/-- Explicit-source version of `linear_euler_unique_source_dvd_sigma_B_and_index`. -/
theorem linear_euler_unique_source_dvd_sigma_B_and_index_of_source {N q m r₀ : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hr₀ : r₀ ∈ m.primeFactors) (hq_dvd : q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀))) :
    let e₀ := m.factorization r₀
    let B := ordCompl[r₀] (m ^ 2)
    let i_q := sigma 1 (m ^ 2) / q
    ¬ r₀ ^ (2 * e₀) ∣ (q + 1) / 2 ∧
    r₀ ∣ sigma 1 B ∧
    r₀ ∣ i_q ∧
    r₀ ∈ (sigma 1 B).primeFactors ∧
    r₀ ∈ i_q.primeFactors ∧
    ∃ p ∈ B.primeFactors, r₀ ∣ sigma 1 (ordProj[p] B) := by
  let e₀ := m.factorization r₀
  let B := ordCompl[r₀] (m ^ 2)
  let c₀ := sigma 1 (r₀ ^ (2 * e₀)) / q
  let i_q := sigma 1 (m ^ 2) / q
  obtain ⟨_, _, hc0_odd, _, hiq_eq, _, _, hr0_dvd, _⟩ :=
    linear_euler_cofactor_quotient_structure_of_source ho hN hq hqm hform hr₀ hq_dvd
  obtain ⟨hB_gt1, _, _, _, h_half_lt⟩ :=
    linear_euler_cofactor_strict_bound_of_source ho hN hq hqm hform hr₀ hq_dvd
  change i_q = c₀ * sigma 1 B at hiq_eq
  change r₀ ^ (2 * e₀) ∣ ((q + 1) / 2) * sigma 1 B at hr0_dvd
  change 1 < B at hB_gt1
  change (q + 1) / 2 < r₀ ^ (2 * e₀) at h_half_lt
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀
  have h_half_pos : 0 < (q + 1) / 2 := by
    have := hq.two_le
    omega
  have h_ndvd_half : ¬ r₀ ^ (2 * e₀) ∣ (q + 1) / 2 := by
    intro hd
    have hle := Nat.le_of_dvd h_half_pos hd
    omega
  have hr₀_dvd_sigB : r₀ ∣ sigma 1 B := by
    by_contra hnsig
    have hcop : Nat.Coprime (r₀ ^ (2 * e₀)) (sigma 1 B) :=
      (hr₀_prime.coprime_iff_not_dvd.mpr hnsig).pow_left (2 * e₀)
    exact h_ndvd_half (hcop.dvd_of_dvd_mul_right hr0_dvd)
  have hr₀_dvd_iq : r₀ ∣ i_q := by
    rw [hiq_eq]
    exact dvd_mul_of_dvd_right hr₀_dvd_sigB c₀
  have hB0 : B ≠ 0 := (by omega : 0 < B).ne'
  have hsigB_ne0 : sigma 1 B ≠ 0 := (sigma_pos 1 B hB0).ne'
  have hiq_ne0 : i_q ≠ 0 := by
    rw [hiq_eq]
    exact mul_ne_zero hc0_odd.pos.ne' hsigB_ne0
  have hr₀_mem_sigB : r₀ ∈ (sigma 1 B).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hr₀_prime, hr₀_dvd_sigB, hsigB_ne0⟩
  have hr₀_mem_iq : r₀ ∈ i_q.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hr₀_prime, hr₀_dvd_iq, hiq_ne0⟩
  have hsigB_prod : sigma 1 B = ∏ p ∈ B.primeFactors, sigma 1 (ordProj[p] B) := by
    rw [isMultiplicative_sigma.multiplicative_factorization (sigma 1) hB0]
    exact Finset.prod_congr B.support_factorization fun _ _ => rfl
  have hex_edge : ∃ p ∈ B.primeFactors, r₀ ∣ sigma 1 (ordProj[p] B) := by
    rw [hsigB_prod] at hr₀_dvd_sigB
    exact (hr₀_prime.prime.dvd_finsetProd_iff _).mp hr₀_dvd_sigB
  exact ⟨h_ndvd_half, hr₀_dvd_sigB, hr₀_dvd_iq, hr₀_mem_sigB, hr₀_mem_iq, hex_edge⟩

/-- **2. Forced Incoming Edge to the Unique `q`-Source `r₀`**:
On `N = q * m ^ 2`, `r₀ ^ (2 * e₀)` cannot divide `(q + 1) / 2`, so `r₀` always divides
`σ(B)` and `i_q = σ(m ^ 2) / q`, and some prime component `p ∈ B.primeFactors` satisfies
`r₀ ∣ σ(ordProj[p] B)`. -/
theorem linear_euler_unique_source_dvd_sigma_B_and_index {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2) :
    ∃ r₀ ∈ m.primeFactors,
      q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀)) ∧
      let e₀ := m.factorization r₀
      let B := ordCompl[r₀] (m ^ 2)
      let i_q := sigma 1 (m ^ 2) / q
      ¬ r₀ ^ (2 * e₀) ∣ (q + 1) / 2 ∧
      r₀ ∣ sigma 1 B ∧
      r₀ ∣ i_q ∧
      r₀ ∈ (sigma 1 B).primeFactors ∧
      r₀ ∈ i_q.primeFactors ∧
      ∃ p ∈ B.primeFactors, r₀ ∣ sigma 1 (ordProj[p] B) := by
  obtain ⟨_, r₀, hr₀_m, hq_dvd, _, _, _, _⟩ :=
    linear_euler_unique_q_source_and_bound ho hN hq hqm hform
  exact ⟨r₀, hr₀_m, hq_dvd,
    linear_euler_unique_source_dvd_sigma_B_and_index_of_source ho hN hq hqm hform hr₀_m hq_dvd⟩

/-- Explicit-source version of `linear_euler_r0_full_pow_or_c0_congruence`. -/
theorem linear_euler_r0_full_pow_or_c0_congruence_of_source {N q m r₀ : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hr₀ : r₀ ∈ m.primeFactors) (hq_dvd : q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀))) :
    let e₀ := m.factorization r₀
    let B := ordCompl[r₀] (m ^ 2)
    let c₀ := sigma 1 (r₀ ^ (2 * e₀)) / q
    let i_q := sigma 1 (m ^ 2) / q
    (Nat.Coprime r₀ ((q + 1) / 2) ∧ r₀ ^ (2 * e₀) ∣ sigma 1 B ∧ r₀ ^ (2 * e₀) ∣ i_q) ∨
    (r₀ ∣ (q + 1) / 2 ∧ 2 * r₀ ∣ c₀ + 1 ∧ 2 * r₀ - 1 ≤ c₀ ∧
      (q + 1) * (2 * r₀ - 1) < 2 * r₀ ^ (2 * e₀) ∧ r₀ ∣ sigma 1 B) := by
  let e₀ := m.factorization r₀
  let B := ordCompl[r₀] (m ^ 2)
  let c₀ := sigma 1 (r₀ ^ (2 * e₀)) / q
  let i_q := sigma 1 (m ^ 2) / q
  obtain ⟨h_mul_c0, _, hc0_odd, _, hiq_eq, _, _, hr0_dvd, _⟩ :=
    linear_euler_cofactor_quotient_structure_of_source ho hN hq hqm hform hr₀ hq_dvd
  obtain ⟨_, _, h_strict1, _, _⟩ :=
    linear_euler_cofactor_strict_bound_of_source ho hN hq hqm hform hr₀ hq_dvd
  obtain ⟨_, hr₀_dvd_sigB, _, _, _, _⟩ :=
    linear_euler_unique_source_dvd_sigma_B_and_index_of_source ho hN hq hqm hform hr₀ hq_dvd
  change sigma 1 (r₀ ^ (2 * e₀)) = q * c₀ at h_mul_c0
  change Odd c₀ at hc0_odd
  change i_q = c₀ * sigma 1 B at hiq_eq
  change r₀ ^ (2 * e₀) ∣ ((q + 1) / 2) * sigma 1 B at hr0_dvd
  change (q + 1) * c₀ < 2 * r₀ ^ (2 * e₀) at h_strict1
  change r₀ ∣ sigma 1 B at hr₀_dvd_sigB
  have hqodd : Odd q := ho.of_dvd_nat (hform ▸ dvd_mul_right q (m ^ 2))
  have hmodd : Odd m :=
    ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀
  have hr₀_odd : Odd r₀ := hmodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr₀)
  by_cases hr₀_half : r₀ ∣ (q + 1) / 2
  · right
    have hq1_even : q + 1 = 2 * ((q + 1) / 2) := by
      have := Nat.odd_iff.mp hqodd
      omega
    have hr₀_dvd_q1 : r₀ ∣ q + 1 := hq1_even ▸ dvd_mul_of_dvd_right hr₀_half 2
    have hqc0_mod : (q * c₀) % r₀ = 1 := by
      rw [← h_mul_c0]
      exact sigma_prime_pow_mod_self hr₀_prime (2 * e₀)
    have hq1c0_mod : ((q + 1) * c₀) % r₀ = 0 :=
      Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hr₀_dvd_q1 c₀)
    have hr₀_dvd_c01 : r₀ ∣ c₀ + 1 := by
      have h_eq : (q + 1) * c₀ = q * c₀ + c₀ := by ring
      rw [h_eq, Nat.add_mod, hqc0_mod] at hq1c0_mod
      have hlt : c₀ % r₀ < r₀ := Nat.mod_lt c₀ hr₀_prime.pos
      have hdvd_sum : r₀ ∣ 1 + c₀ % r₀ := Nat.dvd_of_mod_eq_zero hq1c0_mod
      obtain ⟨k, hk⟩ := hdvd_sum
      have hk_eq : k = 1 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hk0 | hk2
        · have : k = 0 := by omega
          rw [this, mul_zero] at hk
          omega
        · have : 2 * r₀ ≤ r₀ * k := by nlinarith
          omega
      have hc0_mod_eq : c₀ % r₀ = r₀ - 1 := by
        rw [hk_eq, mul_one] at hk
        omega
      rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hc0_mod_eq,
        Nat.mod_eq_of_lt hr₀_prime.one_lt, Nat.sub_add_cancel hr₀_prime.pos, Nat.mod_self]
    have h2_dvd_c01 : 2 ∣ c₀ + 1 := by
      obtain ⟨k, hk⟩ := hc0_odd
      exact ⟨k + 1, by omega⟩
    have hcop_2_r0 : Nat.Coprime 2 r₀ :=
      Nat.prime_two.coprime_iff_not_dvd.mpr hr₀_odd.not_two_dvd_nat
    have h2r0_dvd : 2 * r₀ ∣ c₀ + 1 :=
      hcop_2_r0.mul_dvd_of_dvd_of_dvd h2_dvd_c01 hr₀_dvd_c01
    have hc01_pos : 0 < c₀ + 1 := Nat.succ_pos c₀
    have hle_c0 : 2 * r₀ - 1 ≤ c₀ := by
      have hle := Nat.le_of_dvd hc01_pos h2r0_dvd
      omega
    have h_mul_lt : (q + 1) * (2 * r₀ - 1) < 2 * r₀ ^ (2 * e₀) :=
      lt_of_le_of_lt (Nat.mul_le_mul_left (q + 1) hle_c0) h_strict1
    exact ⟨hr₀_half, h2r0_dvd, hle_c0, h_mul_lt, hr₀_dvd_sigB⟩
  · left
    have hcop_r0 : Nat.Coprime r₀ ((q + 1) / 2) :=
      hr₀_prime.coprime_iff_not_dvd.mpr hr₀_half
    have hcop_pow : Nat.Coprime (r₀ ^ (2 * e₀)) ((q + 1) / 2) :=
      hcop_r0.pow_left (2 * e₀)
    have hr0_pow_dvd_sigB : r₀ ^ (2 * e₀) ∣ sigma 1 B :=
      hcop_pow.dvd_of_dvd_mul_left hr0_dvd
    have hr0_pow_dvd_iq : r₀ ^ (2 * e₀) ∣ i_q := by
      rw [hiq_eq]
      exact dvd_mul_of_dvd_right hr0_pow_dvd_sigB c₀
    exact ⟨hcop_r0, hr0_pow_dvd_sigB, hr0_pow_dvd_iq⟩

/-- **3. Full-Power Absorption vs. `2r₀ ∣ c₀ + 1` Dichotomy**:
For the unique `q`-source `r₀` on `N = q * m ^ 2`, either `r₀` is coprime to `(q + 1) / 2` and
the full prime power `r₀ ^ (2 * e₀)` divides both `σ(B)` and `i_q`, or `r₀ ∣ (q + 1) / 2`,
forcing `2 * r₀ ∣ c₀ + 1`, `2 * r₀ - 1 ≤ c₀`, `(q + 1) * (2 * r₀ - 1) < 2 * r₀ ^ (2 * e₀)`, and
`r₀ ∣ σ(B)`. -/
theorem linear_euler_r0_full_pow_or_c0_congruence {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2) :
    ∃ r₀ ∈ m.primeFactors,
      q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀)) ∧
      let e₀ := m.factorization r₀
      let B := ordCompl[r₀] (m ^ 2)
      let c₀ := sigma 1 (r₀ ^ (2 * e₀)) / q
      let i_q := sigma 1 (m ^ 2) / q
      (Nat.Coprime r₀ ((q + 1) / 2) ∧ r₀ ^ (2 * e₀) ∣ sigma 1 B ∧ r₀ ^ (2 * e₀) ∣ i_q) ∨
      (r₀ ∣ (q + 1) / 2 ∧ 2 * r₀ ∣ c₀ + 1 ∧ 2 * r₀ - 1 ≤ c₀ ∧
        (q + 1) * (2 * r₀ - 1) < 2 * r₀ ^ (2 * e₀) ∧ r₀ ∣ sigma 1 B) := by
  obtain ⟨_, r₀, hr₀_m, hq_dvd, _, _, _, _⟩ :=
    linear_euler_unique_q_source_and_bound ho hN hq hqm hform
  exact ⟨r₀, hr₀_m, hq_dvd,
    linear_euler_r0_full_pow_or_c0_congruence_of_source ho hN hq hqm hform hr₀_m hq_dvd⟩

/-- **4. Pure Prime-Source (`c₀ = 1`) Full-Power Absorption and Deficiency Gap Identity**:
When `σ(r₀ ^ (2 * e₀)) = q`, `r₀` is coprime to `(q + 1) / 2`, `r₀ ^ (2 * e₀)` divides both
`σ(B)` and `i_q`, `r₀ ^ (2 * e₀) < q + 1 < 2 * r₀ ^ (2 * e₀)`, `σ(B) < 2 * B`, and
`(q + 1) * (2 * B - σ(B)) = 2 * (q + 1 - r₀ ^ (2 * e₀)) * B`. -/
theorem linear_euler_pure_prime_source_full_pow_and_gap {N q m r₀ : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hr₀ : r₀ ∈ m.primeFactors) (hpure : sigma 1 (r₀ ^ (2 * m.factorization r₀)) = q) :
    let e₀ := m.factorization r₀
    let B := ordCompl[r₀] (m ^ 2)
    let i_q := sigma 1 (m ^ 2) / q
    Nat.Coprime r₀ ((q + 1) / 2) ∧
    r₀ ^ (2 * e₀) ∣ sigma 1 B ∧
    r₀ ^ (2 * e₀) ∣ i_q ∧
    q + 1 < 2 * r₀ ^ (2 * e₀) ∧
    r₀ ^ (2 * e₀) < q + 1 ∧
    sigma 1 B < 2 * B ∧
    (q + 1) * (2 * B - sigma 1 B) = 2 * (q + 1 - r₀ ^ (2 * e₀)) * B := by
  let e₀ := m.factorization r₀
  let B := ordCompl[r₀] (m ^ 2)
  let c₀ := sigma 1 (r₀ ^ (2 * e₀)) / q
  let i_q := sigma 1 (m ^ 2) / q
  have hq_dvd : q ∣ sigma 1 (r₀ ^ (2 * e₀)) := by
    rw [hpure]
  have hc0_eq1 : c₀ = 1 := by
    dsimp [c₀, e₀]
    rw [hpure, Nat.div_self hq.pos]
  obtain ⟨_, _, _, _, _, h_bal, _, _, _⟩ :=
    linear_euler_cofactor_quotient_structure_of_source ho hN hq hqm hform hr₀ hq_dvd
  obtain ⟨_, _, h_strict1, _, _⟩ :=
    linear_euler_cofactor_strict_bound_of_source ho hN hq hqm hform hr₀ hq_dvd
  obtain h_full | h_cong :=
    linear_euler_r0_full_pow_or_c0_congruence_of_source ho hN hq hqm hform hr₀ hq_dvd
  · have hq1_lt : q + 1 < 2 * r₀ ^ (2 * e₀) := by
      have := h_strict1
      change (q + 1) * c₀ < 2 * r₀ ^ (2 * e₀) at this
      rw [hc0_eq1, mul_one] at this
      exact this
    have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀
    have hmodd : Odd m :=
      ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
    have hm0 : m ≠ 0 := hmodd.pos.ne'
    have he₀_pos : 0 < e₀ :=
      (hr₀_prime.dvd_iff_one_le_factorization hm0).mp (Nat.dvd_of_mem_primeFactors hr₀)
    have hpow_gt1 : 1 < r₀ ^ (2 * e₀) :=
      one_lt_pow₀ hr₀_prime.one_lt (by omega)
    have hr0_lt_q1 : r₀ ^ (2 * e₀) < q + 1 := by
      have h1 : r₀ ^ (2 * e₀) < sigma 1 (r₀ ^ (2 * e₀)) := self_lt_sigma_of_one_lt hpow_gt1
      rw [hpure] at h1
      omega
    have hB_pos : 0 < B := Nat.ordCompl_pos r₀ (pow_ne_zero 2 hm0)
    have h_bal1 : (q + 1) * sigma 1 B = 2 * r₀ ^ (2 * e₀) * B := by
      have := h_bal
      change (q + 1) * c₀ * sigma 1 B = 2 * r₀ ^ (2 * e₀) * B at this
      rw [hc0_eq1, mul_one] at this
      exact this
    have hsigB_lt : sigma 1 B < 2 * B := by
      have h_mul : (q + 1) * sigma 1 B < (q + 1) * (2 * B) := by
        calc
          (q + 1) * sigma 1 B = 2 * r₀ ^ (2 * e₀) * B := h_bal1
          _ < 2 * (q + 1) * B := by
              apply Nat.mul_lt_mul_of_pos_right _ hB_pos
              exact Nat.mul_lt_mul_of_pos_left hr0_lt_q1 (by decide : 0 < 2)
          _ = (q + 1) * (2 * B) := by ring
      exact Nat.lt_of_mul_lt_mul_left h_mul
    have h_gap : (q + 1) * (2 * B - sigma 1 B) = 2 * (q + 1 - r₀ ^ (2 * e₀)) * B := by
      have hle1 : sigma 1 B ≤ 2 * B := hsigB_lt.le
      have hle2 : r₀ ^ (2 * e₀) ≤ q + 1 := hr0_lt_q1.le
      zify [hle1, hle2]
      have h_bal1Z : ((q : ℤ) + 1) * (sigma 1 B : ℤ) = 2 * (r₀ ^ (2 * e₀) : ℤ) * (B : ℤ) := by
        exact_mod_cast h_bal1
      linarith
    exact ⟨h_full.1, h_full.2.1, h_full.2.2, hq1_lt, hr0_lt_q1, hsigB_lt, h_gap⟩
  · exfalso
    have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀
    have h2r0_dvd : 2 * r₀ ∣ 2 := by
      have := h_cong.2.1
      change 2 * r₀ ∣ c₀ + 1 at this
      rwa [hc0_eq1] at this
    have hle : 2 * r₀ ≤ 2 := Nat.le_of_dvd (by decide) h2r0_dvd
    have := hr₀_prime.two_le
    omega

/-- Explicit-source version of `linear_euler_toth_split_absorption_profile`. -/
theorem linear_euler_toth_split_absorption_profile_of_source {N q m r₀ : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hr₀ : r₀ ∈ m.primeFactors) (hq_dvd : q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀))) :
    let B := ordCompl[r₀] (m ^ 2)
    let i_q := sigma 1 (m ^ 2) / q
    TothPair (m ^ 2) q ∧
    ∀ B₁ B₂ : ℕ, B = B₁ * B₂ → B₁.Coprime B₂ →
      sigma 1 B₁ ∣ i_q ∧
      sigma 1 B₂ ∣ i_q ∧
      Nat.Coprime (sigma 1 B₁) q ∧
      Nat.Coprime (sigma 1 B₂) q ∧
      (r₀ ∣ sigma 1 B₁ ∨ r₀ ∣ sigma 1 B₂) := by
  let e₀ := m.factorization r₀
  let B := ordCompl[r₀] (m ^ 2)
  let i_q := sigma 1 (m ^ 2) / q
  have hqodd : Odd q := ho.of_dvd_nat (hform ▸ dvd_mul_right q (m ^ 2))
  have hm2odd : Odd (m ^ 2) := ho.of_dvd_nat (hform ▸ dvd_mul_left (m ^ 2) q)
  have hmodd : Odd m :=
    ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
  have hm0 : m ≠ 0 := hmodd.pos.ne'
  have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hqm2 : ¬ q ∣ m ^ 2 := fun h => hqm (hq.dvd_of_dvd_pow h)
  have hcop_m2q : (m ^ 2).Coprime q := (hq.coprime_iff_not_dvd.mpr hqm2).symm
  have hperf : (m ^ 2 * q).Perfect := by rwa [mul_comm, ← hform]
  have hpair : TothPair (m ^ 2) q := tothPair_of_linear_euler hm2odd hq hcop_m2q hperf
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀
  have hproj_eq : ordProj[r₀] (m ^ 2) = r₀ ^ (2 * e₀) := by
    dsimp [e₀]
    rw [pow_two, Nat.factorization_mul hm0 hm0, Finsupp.add_apply, ← two_mul]
  have hm2_split : m ^ 2 = r₀ ^ (2 * e₀) * B := by
    rw [← hproj_eq]
    exact (Nat.ordProj_mul_ordCompl_eq_self (m ^ 2) r₀).symm
  have h_r0_cop_B : (r₀ ^ (2 * e₀)).Coprime B := by
    rw [← hproj_eq]
    exact (Nat.coprime_ordCompl hr₀_prime hm20).pow_left _
  obtain ⟨_, _, _, _, hiq_eq, _, _, _, _⟩ :=
    linear_euler_cofactor_quotient_structure_of_source ho hN hq hqm hform hr₀ hq_dvd
  obtain ⟨_, hr₀_dvd_sigB, _, _, _, _⟩ :=
    linear_euler_unique_source_dvd_sigma_B_and_index_of_source ho hN hq hqm hform hr₀ hq_dvd
  change i_q = (sigma 1 (r₀ ^ (2 * e₀)) / q) * sigma 1 B at hiq_eq
  change r₀ ∣ sigma 1 B at hr₀_dvd_sigB
  have hsigB_dvd_iq : sigma 1 B ∣ i_q := by
    rw [hiq_eq]
    exact dvd_mul_left _ _
  refine ⟨hpair, fun B₁ B₂ hB hcop12 => ?_⟩
  change B = B₁ * B₂ at hB
  have hsigB_mul : sigma 1 B = sigma 1 B₁ * sigma 1 B₂ := by
    rw [hB, isMultiplicative_sigma.map_mul_of_coprime hcop12]
  have hsig1_dvd : sigma 1 B₁ ∣ i_q :=
    (hsigB_mul ▸ dvd_mul_right (sigma 1 B₁) (sigma 1 B₂)).trans hsigB_dvd_iq
  have hsig2_dvd : sigma 1 B₂ ∣ i_q :=
    (hsigB_mul ▸ dvd_mul_left (sigma 1 B₂) (sigma 1 B₁)).trans hsigB_dvd_iq
  have hm2_1 : m ^ 2 = B₁ * (r₀ ^ (2 * e₀) * B₂) := by
    rw [hm2_split, hB]
    ring
  have hcop1 : B₁.Coprime (r₀ ^ (2 * e₀) * B₂) :=
    Nat.Coprime.mul_right (h_r0_cop_B.symm.coprime_dvd_left ⟨B₂, hB⟩) hcop12
  have hcop_sig1 : (sigma 1 B₁).Coprime q :=
    (tothPair_sigma_dvd_index_iff_coprime hpair hqodd hq.one_lt hcop_m2q hm2_1 hcop1).mp
      hsig1_dvd
  have hm2_2 : m ^ 2 = B₂ * (r₀ ^ (2 * e₀) * B₁) := by
    rw [hm2_split, hB]
    ring
  have hcop2 : B₂.Coprime (r₀ ^ (2 * e₀) * B₁) :=
    Nat.Coprime.mul_right (h_r0_cop_B.symm.coprime_dvd_left ⟨B₁, hB.trans (mul_comm _ _)⟩) hcop12.symm
  have hcop_sig2 : (sigma 1 B₂).Coprime q :=
    (tothPair_sigma_dvd_index_iff_coprime hpair hqodd hq.one_lt hcop_m2q hm2_2 hcop2).mp
      hsig2_dvd
  have hr₀_or : r₀ ∣ sigma 1 B₁ ∨ r₀ ∣ sigma 1 B₂ := by
    rw [hsigB_mul] at hr₀_dvd_sigB
    exact hr₀_prime.dvd_mul.mp hr₀_dvd_sigB
  exact ⟨hsig1_dvd, hsig2_dvd, hcop_sig1, hcop_sig2, hr₀_or⟩

/-- **5. Tóth-Split Absorption Profile of the Complementary Square `B`**:
Combining with `tothPair_of_linear_euler` and `tothPair_sigma_dvd_index_iff_coprime`, on any
coprime split `B = B₁ * B₂` of `B := ordCompl[r₀] (m ^ 2)`, both `σ(B₁)` and `σ(B₂)` divide
`i_q = σ(m ^ 2) / q` and are coprime to `q`, and `r₀ ∣ σ(B₁) ∨ r₀ ∣ σ(B₂)`. -/
theorem linear_euler_toth_split_absorption_profile {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2) :
    ∃ r₀ ∈ m.primeFactors,
      q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀)) ∧
      let B := ordCompl[r₀] (m ^ 2)
      let i_q := sigma 1 (m ^ 2) / q
      TothPair (m ^ 2) q ∧
      ∀ B₁ B₂ : ℕ, B = B₁ * B₂ → B₁.Coprime B₂ →
        sigma 1 B₁ ∣ i_q ∧
        sigma 1 B₂ ∣ i_q ∧
        Nat.Coprime (sigma 1 B₁) q ∧
        Nat.Coprime (sigma 1 B₂) q ∧
        (r₀ ∣ sigma 1 B₁ ∨ r₀ ∣ sigma 1 B₂) := by
  obtain ⟨_, r₀, hr₀_m, hq_dvd, _, _, _, _⟩ :=
    linear_euler_unique_q_source_and_bound ho hN hq hqm hform
  exact ⟨r₀, hr₀_m, hq_dvd,
    linear_euler_toth_split_absorption_profile_of_source ho hN hq hqm hform hr₀_m hq_dvd⟩

end OddPerfect
