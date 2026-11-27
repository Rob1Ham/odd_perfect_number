module

public import OddPerfect.LinearEulerTothObstruction
public import OddPerfect.HalfLengthSupport
public import OddPerfect.NearPerfect
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Linear Euler Square Descent and Peeling Obstruction

Develops square-descent and cofactor-peeling theorems on the linear Euler branch `N = q * m ^ 2`:

1. `linear_euler_half_succ_mul_index_and_deficient_square`:
   Proves `((q + 1) / 2) * i_q = m ^ 2`, `oddValuationPrimes ((q + 1) / 2) = oddValuationPrimes i_q`,
   and `DeficientPerfectWith (m ^ 2) i_q`.
2. `linear_euler_r0_valuation_conservation`:
   Proves `((q + 1) / 2).factorization r₀ + (sigma 1 B).factorization r₀ = 2 * e₀`.
3. `linear_euler_coprime_three_divisor_square_descent`:
   Under `Nat.Coprime r₀ ((q + 1) / 2)`, proves exact factorization and three-divisor descent
   identities for `B`, `sigma 1 B`, `D₀ = sigma 1 B / r₀ ^ (2 * e₀)`, and `i_q`.
4. `linear_euler_composite_square_split_or_single_absorber`:
   Establishes the split-vs.-single-absorber dichotomy across prime-power components of `B`.
5. `peeling_step_no_terminal_unit_of_coprime`:
   General iterated cofactor-peeling termination obstruction on finite support.
-/

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- **1. Half-Successor Index Identity and Deficient-Perfect Square**:
On `N = q * m ^ 2` with `i_q := sigma 1 (m ^ 2) / q`, proves `((q + 1) / 2) * i_q = m ^ 2`,
equality of odd-valuation prime supports `oddValuationPrimes ((q + 1) / 2) = oddValuationPrimes i_q`,
and `DeficientPerfectWith (m ^ 2) i_q`. -/
theorem linear_euler_half_succ_mul_index_and_deficient_square {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2) :
    let i_q := sigma 1 (m ^ 2) / q
    ((q + 1) / 2) * i_q = m ^ 2 ∧
    oddValuationPrimes ((q + 1) / 2) = oddValuationPrimes i_q ∧
    DeficientPerfectWith (m ^ 2) i_q := by
  let i_q := sigma 1 (m ^ 2) / q
  have hqodd : Odd q := ho.of_dvd_nat (hform ▸ dvd_mul_right q (m ^ 2))
  have hmodd : Odd m :=
    ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
  have hm0 : m ≠ 0 := hmodd.pos.ne'
  have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hq_cop_m2 : q.Coprime (m ^ 2) :=
    hq.coprime_iff_not_dvd.mpr (fun h => hqm (hq.dvd_of_dvd_pow h))
  have hsig_N : sigma 1 N = 2 * N :=
    (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul ho.pos).mp hN)
  have hsig_q : sigma 1 q = q + 1 := by
    rw [← pow_one q, sigma_one_apply_prime_pow hq]
    simp [Finset.sum_range_succ]
    ring
  have h_sig_bal : (q + 1) * sigma 1 (m ^ 2) = 2 * (q * m ^ 2) := by
    calc
      (q + 1) * sigma 1 (m ^ 2)
          = sigma 1 q * sigma 1 (m ^ 2) := by rw [hsig_q]
      _ = sigma 1 (q * m ^ 2) := (isMultiplicative_sigma.map_mul_of_coprime hq_cop_m2).symm
      _ = sigma 1 N := by rw [← hform]
      _ = 2 * N := hsig_N
      _ = 2 * (q * m ^ 2) := by rw [hform]
  have hq_cop_q1 : q.Coprime (q + 1) :=
    hq.coprime_iff_not_dvd.mpr (fun hd => hq.not_dvd_one ((Nat.dvd_add_right (dvd_refl q)).mp hd))
  have hq_dvd_sig_m2 : q ∣ sigma 1 (m ^ 2) :=
    hq_cop_q1.dvd_of_dvd_mul_left ⟨2 * m ^ 2, by rw [h_sig_bal]; ring⟩
  have h_sig_m2 : sigma 1 (m ^ 2) = q * i_q := (Nat.mul_div_cancel' hq_dvd_sig_m2).symm
  have h_q_mul : q * ((q + 1) * i_q) = q * (2 * m ^ 2) := by
    calc
      q * ((q + 1) * i_q) = (q + 1) * (q * i_q) := by ring
      _ = (q + 1) * sigma 1 (m ^ 2) := by rw [h_sig_m2]
      _ = 2 * (q * m ^ 2) := h_sig_bal
      _ = q * (2 * m ^ 2) := by ring
  have h_q1_iq : (q + 1) * i_q = 2 * m ^ 2 := Nat.mul_left_cancel hq.pos h_q_mul
  have hq1_even : q + 1 = 2 * ((q + 1) / 2) := by
    have := Nat.odd_iff.mp hqodd
    omega
  have h_half_mul : ((q + 1) / 2) * i_q = m ^ 2 := by
    apply Nat.mul_left_cancel (by decide : 0 < 2)
    calc
      2 * (((q + 1) / 2) * i_q) = (2 * ((q + 1) / 2)) * i_q := by ring
      _ = (q + 1) * i_q := by rw [← hq1_even]
      _ = 2 * m ^ 2 := h_q1_iq
  have h_half_ne0 : (q + 1) / 2 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h_half_mul
    exact hm20 h_half_mul.symm
  have hiq_ne0 : i_q ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h_half_mul
    exact hm20 h_half_mul.symm
  have h_odd_supp : oddValuationPrimes ((q + 1) / 2) = oddValuationPrimes i_q := by
    ext p
    simp only [mem_oddValuationPrimes]
    have hfact : ((q + 1) / 2).factorization p + i_q.factorization p = 2 * m.factorization p := by
      calc
        ((q + 1) / 2).factorization p + i_q.factorization p
            = (((q + 1) / 2) * i_q).factorization p := by
                rw [Nat.factorization_mul h_half_ne0 hiq_ne0, Finsupp.add_apply]
        _ = (m ^ 2).factorization p := by rw [h_half_mul]
        _ = 2 * m.factorization p := by
            rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    rw [Nat.odd_iff, Nat.odd_iff]
    omega
  have hq_ge3 : 3 ≤ q := by
    have := hq.two_le
    have := Nat.odd_iff.mp hqodd
    omega
  have h_half_ge2 : 2 ≤ (q + 1) / 2 := by omega
  have hiq_pos : 0 < i_q := Nat.pos_of_ne_zero hiq_ne0
  have hiq_lt_m2 : i_q < m ^ 2 := by
    calc
      i_q = 1 * i_q := (one_mul i_q).symm
      _ < ((q + 1) / 2) * i_q := Nat.mul_lt_mul_of_pos_right (by omega) hiq_pos
      _ = m ^ 2 := h_half_mul
  have hiq_dvd_m2 : i_q ∣ m ^ 2 := ⟨(q + 1) / 2, by rw [← h_half_mul, mul_comm]⟩
  have hdef : DeficientPerfectWith (m ^ 2) i_q := by
    refine ⟨Nat.mem_properDivisors.mpr ⟨hiq_dvd_m2, hiq_lt_m2⟩, ?_⟩
    calc
      sigma 1 (m ^ 2) + i_q = q * i_q + i_q := by rw [h_sig_m2]
      _ = (q + 1) * i_q := by ring
      _ = 2 * m ^ 2 := h_q1_iq
  exact ⟨h_half_mul, h_odd_supp, hdef⟩

/-- **2. Valuation Conservation at the Unique `q`-Source `r₀`**:
Proves `((q + 1) / 2).factorization r₀ + (sigma 1 B).factorization r₀ = 2 * e₀`. -/
theorem linear_euler_r0_valuation_conservation {N q m r₀ : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hr₀ : r₀ ∈ m.primeFactors) (hq_dvd : q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀))) :
    let e₀ := m.factorization r₀
    let B := ordCompl[r₀] (m ^ 2)
    ((q + 1) / 2).factorization r₀ + (sigma 1 B).factorization r₀ = 2 * e₀ := by
  let e₀ := m.factorization r₀
  let B := ordCompl[r₀] (m ^ 2)
  let c₀ := sigma 1 (r₀ ^ (2 * e₀)) / q
  obtain ⟨_, _, hc0_odd, hc0_cop, _, h_bal, _, _, _⟩ :=
    linear_euler_cofactor_quotient_structure_of_source ho hN hq hqm hform hr₀ hq_dvd
  change Odd c₀ at hc0_odd
  change Nat.Coprime c₀ (r₀ ^ (2 * e₀)) at hc0_cop
  change (q + 1) * c₀ * sigma 1 B = 2 * r₀ ^ (2 * e₀) * B at h_bal
  have hqodd : Odd q := ho.of_dvd_nat (hform ▸ dvd_mul_right q (m ^ 2))
  have hmodd : Odd m :=
    ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
  have hm0 : m ≠ 0 := hmodd.pos.ne'
  have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀
  have he₀_pos : 0 < e₀ :=
    (hr₀_prime.dvd_iff_one_le_factorization hm0).mp (Nat.dvd_of_mem_primeFactors hr₀)
  have hq1_even : q + 1 = 2 * ((q + 1) / 2) := by
    have := Nat.odd_iff.mp hqodd
    omega
  have h_half_bal : ((q + 1) / 2) * c₀ * sigma 1 B = r₀ ^ (2 * e₀) * B := by
    apply Nat.mul_left_cancel (by decide : 0 < 2)
    calc
      2 * (((q + 1) / 2) * c₀ * sigma 1 B)
          = (2 * ((q + 1) / 2)) * c₀ * sigma 1 B := by ring
      _ = (q + 1) * c₀ * sigma 1 B := by rw [← hq1_even]
      _ = 2 * r₀ ^ (2 * e₀) * B := h_bal
      _ = 2 * (r₀ ^ (2 * e₀) * B) := by ring
  have h_half_ne0 : (q + 1) / 2 ≠ 0 := by
    have := hq.two_le
    omega
  have hc0_ne0 : c₀ ≠ 0 := hc0_odd.pos.ne'
  have hB_pos : 0 < B := Nat.ordCompl_pos r₀ hm20
  have hB_ne0 : B ≠ 0 := hB_pos.ne'
  have hsigB_ne0 : sigma 1 B ≠ 0 := (sigma_pos 1 B hB_ne0).ne'
  have hr0_pow_ne0 : r₀ ^ (2 * e₀) ≠ 0 := pow_ne_zero _ hr₀_prime.ne_zero
  have hr0_dvd_pow : r₀ ∣ r₀ ^ (2 * e₀) := dvd_pow_self r₀ (by omega)
  have hr0_ndvd_c0 : ¬ r₀ ∣ c₀ := fun h =>
    hr₀_prime.not_dvd_one (hc0_cop ▸ Nat.dvd_gcd h hr0_dvd_pow)
  have hc0_fact : c₀.factorization r₀ = 0 := Nat.factorization_eq_zero_of_not_dvd hr0_ndvd_c0
  have hr0_ndvd_B : ¬ r₀ ∣ B := Nat.not_dvd_ordCompl hr₀_prime hm20
  have hB_fact : B.factorization r₀ = 0 := Nat.factorization_eq_zero_of_not_dvd hr0_ndvd_B
  have h_pow_fact : (r₀ ^ (2 * e₀)).factorization r₀ = 2 * e₀ := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hr₀_prime.factorization_self, mul_one]
  have h_mul_fact :
      (((q + 1) / 2) * c₀ * sigma 1 B).factorization r₀ = (r₀ ^ (2 * e₀) * B).factorization r₀ :=
    congrArg (fun x => x.factorization r₀) h_half_bal
  rw [Nat.factorization_mul (mul_ne_zero h_half_ne0 hc0_ne0) hsigB_ne0,
    Nat.factorization_mul h_half_ne0 hc0_ne0,
    Nat.factorization_mul hr0_pow_ne0 hB_ne0,
    Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply,
    hc0_fact, hB_fact, h_pow_fact, add_zero, add_zero] at h_mul_fact
  exact h_mul_fact

/-- **3. Coprime Three-Divisor Square Descent**:
When `Nat.Coprime r₀ ((q + 1) / 2)`, `r₀ ^ (2 * e₀)` is absorbed completely by `sigma 1 B`,
yielding the three-divisor factorization `B = ((q + 1) / 2) * c₀ * D₀` and coprime descent
identities for `D₀ := sigma 1 B / r₀ ^ (2 * e₀)` and `i_q`. -/
theorem linear_euler_coprime_three_divisor_square_descent {N q m r₀ : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hr₀ : r₀ ∈ m.primeFactors) (hq_dvd : q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀)))
    (hcop : Nat.Coprime r₀ ((q + 1) / 2)) :
    let e₀ := m.factorization r₀
    let B := ordCompl[r₀] (m ^ 2)
    let c₀ := sigma 1 (r₀ ^ (2 * e₀)) / q
    let D₀ := sigma 1 B / r₀ ^ (2 * e₀)
    let i_q := sigma 1 (m ^ 2) / q
    (sigma 1 B).factorization r₀ = 2 * e₀ ∧
    sigma 1 B = r₀ ^ (2 * e₀) * D₀ ∧
    B = ((q + 1) / 2) * c₀ * D₀ ∧
    (((q + 1) / 2) * c₀) * sigma 1 B = r₀ ^ (2 * e₀) * B ∧
    (Nat.Coprime r₀ D₀ ∧ Odd D₀ ∧ 0 < D₀) ∧
    (Nat.Coprime (r₀ ^ (2 * e₀)) (((q + 1) / 2) * c₀) ∧ i_q = r₀ ^ (2 * e₀) * c₀ * D₀) := by
  let e₀ := m.factorization r₀
  let B := ordCompl[r₀] (m ^ 2)
  let c₀ := sigma 1 (r₀ ^ (2 * e₀)) / q
  let D₀ := sigma 1 B / r₀ ^ (2 * e₀)
  let i_q := sigma 1 (m ^ 2) / q
  obtain ⟨_, _, hc0_odd, hc0_cop, hiq_eq, h_bal, _, hr0_dvd, _⟩ :=
    linear_euler_cofactor_quotient_structure_of_source ho hN hq hqm hform hr₀ hq_dvd
  change Odd c₀ at hc0_odd
  change Nat.Coprime c₀ (r₀ ^ (2 * e₀)) at hc0_cop
  change i_q = c₀ * sigma 1 B at hiq_eq
  change (q + 1) * c₀ * sigma 1 B = 2 * r₀ ^ (2 * e₀) * B at h_bal
  change r₀ ^ (2 * e₀) ∣ ((q + 1) / 2) * sigma 1 B at hr0_dvd
  have hqodd : Odd q := ho.of_dvd_nat (hform ▸ dvd_mul_right q (m ^ 2))
  have hmodd : Odd m :=
    ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
  have hm0 : m ≠ 0 := hmodd.pos.ne'
  have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀
  have hB_pos : 0 < B := Nat.ordCompl_pos r₀ hm20
  have hB_ne0 : B ≠ 0 := hB_pos.ne'
  have hsigB_ne0 : sigma 1 B ≠ 0 := (sigma_pos 1 B hB_ne0).ne'
  have hr0_pow_pos : 0 < r₀ ^ (2 * e₀) := pow_pos hr₀_prime.pos _
  have hr0_ndvd_half : ¬ r₀ ∣ (q + 1) / 2 := hr₀_prime.coprime_iff_not_dvd.mp hcop
  have h_half_fact : ((q + 1) / 2).factorization r₀ = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hr0_ndvd_half
  have h_cons := linear_euler_r0_valuation_conservation ho hN hq hqm hform hr₀ hq_dvd
  dsimp only at h_cons
  have h_sigB_fact : (sigma 1 B).factorization r₀ = 2 * e₀ := by
    rw [h_half_fact, zero_add] at h_cons
    exact h_cons
  have hr0_pow_dvd_sigB : r₀ ^ (2 * e₀) ∣ sigma 1 B :=
    (hcop.pow_left (2 * e₀)).dvd_of_dvd_mul_left hr0_dvd
  have h_sigB_eq : sigma 1 B = r₀ ^ (2 * e₀) * D₀ :=
    (Nat.mul_div_cancel' hr0_pow_dvd_sigB).symm
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
  have h_B_eq : B = ((q + 1) / 2) * c₀ * D₀ := by
    apply Nat.mul_left_cancel hr0_pow_pos
    calc
      r₀ ^ (2 * e₀) * B = (((q + 1) / 2) * c₀) * sigma 1 B := h_half_bal.symm
      _ = (((q + 1) / 2) * c₀) * (r₀ ^ (2 * e₀) * D₀) := by rw [h_sigB_eq]
      _ = r₀ ^ (2 * e₀) * (((q + 1) / 2) * c₀ * D₀) := by ring
  have hr0_ndvd_D0 : ¬ r₀ ∣ D₀ := by
    intro hr0_D0
    have hpow1_dvd : r₀ ^ (2 * e₀ + 1) ∣ sigma 1 B := by
      rw [h_sigB_eq, pow_succ]
      exact Nat.mul_dvd_mul_left _ hr0_D0
    have hle : 2 * e₀ + 1 ≤ (sigma 1 B).factorization r₀ :=
      (hr₀_prime.pow_dvd_iff_le_factorization hsigB_ne0).mp hpow1_dvd
    omega
  have hcop_r0_D0 : Nat.Coprime r₀ D₀ := hr₀_prime.coprime_iff_not_dvd.mpr hr0_ndvd_D0
  have hB_odd : Odd B := (hmodd.pow).of_dvd_nat (Nat.ordCompl_dvd (m ^ 2) r₀)
  have hD0_odd : Odd D₀ := hB_odd.of_dvd_nat ⟨((q + 1) / 2) * c₀, by rw [h_B_eq]; ring⟩
  have hD0_pos : 0 < D₀ := hD0_odd.pos
  have hcop_pow_half_c0 : Nat.Coprime (r₀ ^ (2 * e₀)) (((q + 1) / 2) * c₀) :=
    Nat.Coprime.mul_right (hcop.pow_left (2 * e₀)) hc0_cop.symm
  have hiq_eq' : i_q = r₀ ^ (2 * e₀) * c₀ * D₀ := by
    rw [hiq_eq, h_sigB_eq]
    ring
  exact ⟨h_sigB_fact, h_sigB_eq, h_B_eq, h_half_bal, ⟨hcop_r0_D0, hD0_odd, hD0_pos⟩,
    ⟨hcop_pow_half_c0, hiq_eq'⟩⟩

/-- **4. Composite Square Split vs. Single-Absorber Peeling Dichotomy**:
Under `Nat.Coprime r₀ ((q + 1) / 2)`, either `B` splits into coprime factors `B = B₁ * B₂`
whose divisor sums both share `r₀` (strictly splitting `r₀ ^ (2 * e₀)`), or a single prime power
`ordProj[r₁] B = r₁ ^ (2 * e₁)` absorbs the entire `r₀ ^ (2 * e₀)` and initiates a coprime peeling
step on `B₁ := ordCompl[r₁] B`. -/
theorem linear_euler_composite_square_split_or_single_absorber {N q m r₀ : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hr₀ : r₀ ∈ m.primeFactors) (hq_dvd : q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀)))
    (hcop : Nat.Coprime r₀ ((q + 1) / 2)) :
    let e₀ := m.factorization r₀
    let B := ordCompl[r₀] (m ^ 2)
    let c₀ := sigma 1 (r₀ ^ (2 * e₀)) / q
    (∃ B₁ B₂ : ℕ,
      B = B₁ * B₂ ∧
      B₁.Coprime B₂ ∧
      r₀ ∣ Nat.gcd (sigma 1 B₁) (sigma 1 B₂) ∧
      1 < Nat.gcd (r₀ ^ (2 * e₀)) (sigma 1 B₁) ∧
      Nat.gcd (r₀ ^ (2 * e₀)) (sigma 1 B₁) < r₀ ^ (2 * e₀)) ∨
    (∃ r₁ ∈ B.primeFactors,
      r₀ ^ (2 * e₀) ∣ sigma 1 (ordProj[r₁] B) ∧
      (sigma 1 (ordProj[r₁] B)).factorization r₀ = 2 * e₀ ∧
      Nat.Coprime r₀ (sigma 1 (ordCompl[r₁] B)) ∧
      let e₁ := m.factorization r₁
      let c₁ := sigma 1 (r₁ ^ (2 * e₁)) / r₀ ^ (2 * e₀)
      let B₁ := ordCompl[r₁] B
      ordProj[r₁] B = r₁ ^ (2 * e₁) ∧
      sigma 1 (r₁ ^ (2 * e₁)) = r₀ ^ (2 * e₀) * c₁ ∧
      Nat.Coprime c₁ r₁ ∧
      (((q + 1) / 2) * c₀ * c₁) * sigma 1 B₁ = r₁ ^ (2 * e₁) * B₁ ∧
      (1 < B₁ → ((q + 1) / 2) * c₀ * c₁ < r₁ ^ (2 * e₁))) := by
  let e₀ := m.factorization r₀
  let B := ordCompl[r₀] (m ^ 2)
  let c₀ := sigma 1 (r₀ ^ (2 * e₀)) / q
  obtain ⟨_, _, hc0_odd, _, _, _, _, _, _⟩ :=
    linear_euler_cofactor_quotient_structure_of_source ho hN hq hqm hform hr₀ hq_dvd
  change Odd c₀ at hc0_odd
  obtain ⟨_, _, _, _, _, hex_edge⟩ :=
    linear_euler_unique_source_dvd_sigma_B_and_index_of_source ho hN hq hqm hform hr₀ hq_dvd
  obtain ⟨h_sigB_fact, _, _, h_half_bal, _, _⟩ :=
    linear_euler_coprime_three_divisor_square_descent ho hN hq hqm hform hr₀ hq_dvd hcop
  change ∃ p ∈ B.primeFactors, r₀ ∣ sigma 1 (ordProj[p] B) at hex_edge
  change (sigma 1 B).factorization r₀ = 2 * e₀ at h_sigB_fact
  change (((q + 1) / 2) * c₀) * sigma 1 B = r₀ ^ (2 * e₀) * B at h_half_bal
  have hmodd : Odd m :=
    ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
  have hm0 : m ≠ 0 := hmodd.pos.ne'
  have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀
  have he₀_pos : 0 < e₀ :=
    (hr₀_prime.dvd_iff_one_le_factorization hm0).mp (Nat.dvd_of_mem_primeFactors hr₀)
  have hB_pos : 0 < B := Nat.ordCompl_pos r₀ hm20
  have hB_ne0 : B ≠ 0 := hB_pos.ne'
  have hsigB_ne0 : sigma 1 B ≠ 0 := (sigma_pos 1 B hB_ne0).ne'
  have hr0_pow_pos : 0 < r₀ ^ (2 * e₀) := pow_pos hr₀_prime.pos _
  have hr0_pow_ne0 : r₀ ^ (2 * e₀) ≠ 0 := hr0_pow_pos.ne'
  let S : Finset ℕ := B.primeFactors.filter (fun p => r₀ ∣ sigma 1 (ordProj[p] B))
  have hS_ne : S.Nonempty := by
    obtain ⟨p, hp, hpd⟩ := hex_edge
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, hpd⟩⟩
  by_cases hS_card : 1 < S.card
  · left
    obtain ⟨p₁, hp₁S, p₂, hp₂S, hp_ne⟩ := Finset.one_lt_card.mp hS_card
    have hp₁B : p₁ ∈ B.primeFactors := (Finset.mem_filter.mp hp₁S).1
    have hp₁_dvd : r₀ ∣ sigma 1 (ordProj[p₁] B) := (Finset.mem_filter.mp hp₁S).2
    have hp₂B : p₂ ∈ B.primeFactors := (Finset.mem_filter.mp hp₂S).1
    have hp₂_dvd : r₀ ∣ sigma 1 (ordProj[p₂] B) := (Finset.mem_filter.mp hp₂S).2
    have hp₁_prime : p₁.Prime := Nat.prime_of_mem_primeFactors hp₁B
    have hp₂_prime : p₂.Prime := Nat.prime_of_mem_primeFactors hp₂B
    let B₁ := ordProj[p₁] B
    let B₂ := ordCompl[p₁] B
    have hB_split : B = B₁ * B₂ := (Nat.ordProj_mul_ordCompl_eq_self B p₁).symm
    have hB_cop : B₁.Coprime B₂ := (Nat.coprime_ordCompl hp₁_prime hB_ne0).pow_left _
    have hsigB_mul : sigma 1 B = sigma 1 B₁ * sigma 1 B₂ := by
      rw [hB_split, isMultiplicative_sigma.map_mul_of_coprime hB_cop]
    have hB₂_ne0 : B₂ ≠ 0 := (Nat.ordCompl_pos p₁ hB_ne0).ne'
    have hB₂_fact_p₂ : B₂.factorization p₂ = B.factorization p₂ := by
      have h1 : B.factorization p₂ = B₁.factorization p₂ + B₂.factorization p₂ := by
        conv_lhs => rw [hB_split]
        rw [Nat.factorization_mul (pow_ne_zero _ hp₁_prime.ne_zero) hB₂_ne0, Finsupp.add_apply]
      have h2 : B₁.factorization p₂ = 0 := by
        dsimp [B₁]
        rw [hp₁_prime.factorization_pow, Finsupp.single_eq_of_ne hp_ne.symm]
      omega
    have h_ordProj_p₂ : ordProj[p₂] B = ordProj[p₂] B₂ := by
      rw [hB₂_fact_p₂]
    have hB₂_split : B₂ = ordProj[p₂] B₂ * ordCompl[p₂] B₂ :=
      (Nat.ordProj_mul_ordCompl_eq_self B₂ p₂).symm
    have hB₂_cop : (ordProj[p₂] B₂).Coprime (ordCompl[p₂] B₂) :=
      (Nat.coprime_ordCompl hp₂_prime hB₂_ne0).pow_left _
    have h_sig_p₂_dvd_B₂ : sigma 1 (ordProj[p₂] B) ∣ sigma 1 B₂ := by
      rw [h_ordProj_p₂]
      conv_rhs => rw [hB₂_split, isMultiplicative_sigma.map_mul_of_coprime hB₂_cop]
      exact dvd_mul_right _ _
    have hr₀_dvd_B₂ : r₀ ∣ sigma 1 B₂ := hp₂_dvd.trans h_sig_p₂_dvd_B₂
    have hr₀_dvd_gcd12 : r₀ ∣ Nat.gcd (sigma 1 B₁) (sigma 1 B₂) :=
      Nat.dvd_gcd hp₁_dvd hr₀_dvd_B₂
    have hr₀_dvd_pow : r₀ ∣ r₀ ^ (2 * e₀) := dvd_pow_self r₀ (by omega)
    have hr₀_dvd_gcd : r₀ ∣ Nat.gcd (r₀ ^ (2 * e₀)) (sigma 1 B₁) :=
      Nat.dvd_gcd hr₀_dvd_pow hp₁_dvd
    have hgcd_pos : 0 < Nat.gcd (r₀ ^ (2 * e₀)) (sigma 1 B₁) :=
      Nat.gcd_pos_of_pos_left (sigma 1 B₁) hr0_pow_pos
    have hgcd_gt1 : 1 < Nat.gcd (r₀ ^ (2 * e₀)) (sigma 1 B₁) :=
      lt_of_lt_of_le hr₀_prime.one_lt (Nat.le_of_dvd hgcd_pos hr₀_dvd_gcd)
    have hgcd_le : Nat.gcd (r₀ ^ (2 * e₀)) (sigma 1 B₁) ≤ r₀ ^ (2 * e₀) :=
      Nat.le_of_dvd hr0_pow_pos (Nat.gcd_dvd_left _ _)
    have hgcd_lt : Nat.gcd (r₀ ^ (2 * e₀)) (sigma 1 B₁) < r₀ ^ (2 * e₀) := by
      refine lt_of_le_of_ne hgcd_le ?_
      intro heq
      have hpow_dvd_B₁ : r₀ ^ (2 * e₀) ∣ sigma 1 B₁ := by
        rw [← heq]
        exact Nat.gcd_dvd_right _ _
      have hpow1_dvd_sigB : r₀ ^ (2 * e₀ + 1) ∣ sigma 1 B := by
        rw [hsigB_mul, pow_succ]
        exact Nat.mul_dvd_mul hpow_dvd_B₁ hr₀_dvd_B₂
      have hle : 2 * e₀ + 1 ≤ (sigma 1 B).factorization r₀ :=
        (hr₀_prime.pow_dvd_iff_le_factorization hsigB_ne0).mp hpow1_dvd_sigB
      omega
    exact ⟨B₁, B₂, hB_split, hB_cop, hr₀_dvd_gcd12, hgcd_gt1, hgcd_lt⟩
  · right
    have hS_card1 : S.card = 1 := by
      have := hS_ne.card_pos
      omega
    obtain ⟨r₁, hr₁_S⟩ := Finset.card_eq_one.mp hS_card1
    have hr₁_mem_S : r₁ ∈ S := by rw [hr₁_S]; exact Finset.mem_singleton_self r₁
    have hr₁_B : r₁ ∈ B.primeFactors := (Finset.mem_filter.mp hr₁_mem_S).1
    have hr₁_prime : r₁.Prime := Nat.prime_of_mem_primeFactors hr₁_B
    let B₁ := ordCompl[r₁] B
    have hB_split : B = ordProj[r₁] B * B₁ := (Nat.ordProj_mul_ordCompl_eq_self B r₁).symm
    have hB_cop : (ordProj[r₁] B).Coprime B₁ :=
      (Nat.coprime_ordCompl hr₁_prime hB_ne0).pow_left _
    have hsigB_mul : sigma 1 B = sigma 1 (ordProj[r₁] B) * sigma 1 B₁ := by
      conv_lhs => rw [hB_split, isMultiplicative_sigma.map_mul_of_coprime hB_cop]
    have hB₁_pos : 0 < B₁ := Nat.ordCompl_pos r₁ hB_ne0
    have hB₁_ne0 : B₁ ≠ 0 := hB₁_pos.ne'
    have hsigB₁_pos : 0 < sigma 1 B₁ := sigma_pos 1 B₁ hB₁_ne0
    have hsigB₁_ne0 : sigma 1 B₁ ≠ 0 := hsigB₁_pos.ne'
    have hsigB₁_prod : sigma 1 B₁ = ∏ p ∈ B₁.primeFactors, sigma 1 (ordProj[p] B₁) := by
      rw [isMultiplicative_sigma.multiplicative_factorization (sigma 1) hB₁_ne0]
      exact Finset.prod_congr B₁.support_factorization fun _ _ => rfl
    have hr₀_ndvd_sigB₁ : ¬ r₀ ∣ sigma 1 B₁ := by
      rw [hsigB₁_prod, hr₀_prime.prime.dvd_finsetProd_iff]
      rintro ⟨p, hpB₁, hr₀_dvd_p⟩
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hpB₁
      have hp_dvd_B₁ : p ∣ B₁ := Nat.dvd_of_mem_primeFactors hpB₁
      have hp_dvd_B : p ∣ B := hp_dvd_B₁.trans (Nat.ordCompl_dvd B r₁)
      have hpB : p ∈ B.primeFactors := Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd_B, hB_ne0⟩
      have hp_ne_r₁ : p ≠ r₁ := by
        intro hpeq
        subst hpeq
        exact Nat.not_dvd_ordCompl hr₁_prime hB_ne0 hp_dvd_B₁
      have hB₁_fact_p : B₁.factorization p = B.factorization p := by
        have h1 : B.factorization p = (ordProj[r₁] B).factorization p + B₁.factorization p := by
          conv_lhs => rw [hB_split]
          rw [Nat.factorization_mul (pow_ne_zero _ hr₁_prime.ne_zero) hB₁_ne0, Finsupp.add_apply]
        have h2 : (ordProj[r₁] B).factorization p = 0 := by
          rw [hr₁_prime.factorization_pow, Finsupp.single_eq_of_ne hp_ne_r₁]
        omega
      have h_ordProj_p : ordProj[p] B₁ = ordProj[p] B := by
        rw [hB₁_fact_p]
      rw [h_ordProj_p] at hr₀_dvd_p
      have hp_in_S : p ∈ S := Finset.mem_filter.mpr ⟨hpB, hr₀_dvd_p⟩
      rw [hr₁_S, Finset.mem_singleton] at hp_in_S
      exact hp_ne_r₁ hp_in_S
    have hcop_r0_sigB₁ : Nat.Coprime r₀ (sigma 1 B₁) :=
      hr₀_prime.coprime_iff_not_dvd.mpr hr₀_ndvd_sigB₁
    have hr₀_pow_dvd_sigB : r₀ ^ (2 * e₀) ∣ sigma 1 B := by
      rw [← h_sigB_fact]
      exact Nat.ordProj_dvd (sigma 1 B) r₀
    have hr₀_pow_dvd_r₁ : r₀ ^ (2 * e₀) ∣ sigma 1 (ordProj[r₁] B) := by
      rw [hsigB_mul] at hr₀_pow_dvd_sigB
      exact (hcop_r0_sigB₁.pow_left (2 * e₀)).dvd_of_dvd_mul_right hr₀_pow_dvd_sigB
    have hsig_r₁_ne0 : sigma 1 (ordProj[r₁] B) ≠ 0 :=
      (sigma_pos 1 _ (pow_ne_zero _ hr₁_prime.ne_zero)).ne'
    have hsig_r₁_fact : (sigma 1 (ordProj[r₁] B)).factorization r₀ = 2 * e₀ := by
      have h1 : (sigma 1 B).factorization r₀ =
          (sigma 1 (ordProj[r₁] B)).factorization r₀ + (sigma 1 B₁).factorization r₀ := by
        rw [hsigB_mul, Nat.factorization_mul hsig_r₁_ne0 hsigB₁_ne0, Finsupp.add_apply]
      have h2 : (sigma 1 B₁).factorization r₀ = 0 :=
        Nat.factorization_eq_zero_of_not_dvd hr₀_ndvd_sigB₁
      omega
    have hr₁_ne_r₀ : r₁ ≠ r₀ := by
      intro heq
      subst heq
      exact Nat.not_dvd_ordCompl hr₀_prime hm20 (Nat.dvd_of_mem_primeFactors hr₁_B)
    have hproj_r₀ : ordProj[r₀] (m ^ 2) = r₀ ^ (2 * e₀) := by
      dsimp [e₀]
      rw [pow_two, Nat.factorization_mul hm0 hm0, Finsupp.add_apply, ← two_mul]
    have hm2_split : m ^ 2 = r₀ ^ (2 * e₀) * B := by
      rw [← hproj_r₀]
      exact (Nat.ordProj_mul_ordCompl_eq_self (m ^ 2) r₀).symm
    let e₁ := m.factorization r₁
    have hB_fact_r₁ : B.factorization r₁ = 2 * e₁ := by
      have h1 : (m ^ 2).factorization r₁ = (r₀ ^ (2 * e₀)).factorization r₁ + B.factorization r₁ := by
        conv_lhs => rw [hm2_split]
        rw [Nat.factorization_mul hr0_pow_ne0 hB_ne0, Finsupp.add_apply]
      have h2 : (r₀ ^ (2 * e₀)).factorization r₁ = 0 := by
        rw [hr₀_prime.factorization_pow, Finsupp.single_eq_of_ne hr₁_ne_r₀]
      have h3 : (m ^ 2).factorization r₁ = 2 * e₁ := by
        dsimp [e₁]
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
      omega
    have h_ordProj_r₁ : ordProj[r₁] B = r₁ ^ (2 * e₁) := by
      rw [hB_fact_r₁]
    let c₁ := sigma 1 (r₁ ^ (2 * e₁)) / r₀ ^ (2 * e₀)
    have hr₀_pow_dvd_pow_r₁ : r₀ ^ (2 * e₀) ∣ sigma 1 (r₁ ^ (2 * e₁)) := by
      rw [← h_ordProj_r₁]
      exact hr₀_pow_dvd_r₁
    have h_sig_r₁_eq : sigma 1 (r₁ ^ (2 * e₁)) = r₀ ^ (2 * e₀) * c₁ :=
      (Nat.mul_div_cancel' hr₀_pow_dvd_pow_r₁).symm
    have hr₁_ndvd_sig_r₁ : ¬ r₁ ∣ sigma 1 (r₁ ^ (2 * e₁)) := by
      rw [Nat.dvd_iff_mod_eq_zero, sigma_prime_pow_mod_self hr₁_prime]
      decide
    have hr₁_ndvd_c₁ : ¬ r₁ ∣ c₁ := fun h =>
      hr₁_ndvd_sig_r₁ (h.trans ⟨r₀ ^ (2 * e₀), by rw [h_sig_r₁_eq, mul_comm]⟩)
    have hcop_c₁_r₁ : Nat.Coprime c₁ r₁ := (hr₁_prime.coprime_iff_not_dvd.mpr hr₁_ndvd_c₁).symm
    have h_peel_bal : (((q + 1) / 2) * c₀ * c₁) * sigma 1 B₁ = r₁ ^ (2 * e₁) * B₁ := by
      apply Nat.mul_left_cancel hr0_pow_pos
      calc
        r₀ ^ (2 * e₀) * ((((q + 1) / 2) * c₀ * c₁) * sigma 1 B₁)
            = (((q + 1) / 2) * c₀) * ((r₀ ^ (2 * e₀) * c₁) * sigma 1 B₁) := by ring
        _ = (((q + 1) / 2) * c₀) * (sigma 1 (r₁ ^ (2 * e₁)) * sigma 1 B₁) := by rw [← h_sig_r₁_eq]
        _ = (((q + 1) / 2) * c₀) * (sigma 1 (ordProj[r₁] B) * sigma 1 B₁) := by rw [← h_ordProj_r₁]
        _ = (((q + 1) / 2) * c₀) * sigma 1 B := by rw [← hsigB_mul]
        _ = r₀ ^ (2 * e₀) * B := h_half_bal
        _ = r₀ ^ (2 * e₀) * (ordProj[r₁] B * B₁) := by rw [← hB_split]
        _ = r₀ ^ (2 * e₀) * (r₁ ^ (2 * e₁) * B₁) := by rw [h_ordProj_r₁]
    have h_strict_peel : 1 < B₁ → ((q + 1) / 2) * c₀ * c₁ < r₁ ^ (2 * e₁) := by
      intro hB₁_gt1
      have hB₁_lt_sig : B₁ < sigma 1 B₁ := self_lt_sigma_of_one_lt hB₁_gt1
      have h_half_pos : 0 < (q + 1) / 2 := by
        have := hq.two_le
        omega
      have hc₁_pos : 0 < c₁ := Nat.pos_of_ne_zero fun hc₁0 => by
        rw [hc₁0, mul_zero, ← h_ordProj_r₁] at h_sig_r₁_eq
        exact hsig_r₁_ne0 h_sig_r₁_eq
      have h_lhs_pos : 0 < ((q + 1) / 2) * c₀ * c₁ :=
        Nat.mul_pos (Nat.mul_pos h_half_pos hc0_odd.pos) hc₁_pos
      by_contra! hle
      have h1 : r₁ ^ (2 * e₁) * B₁ ≤ (((q + 1) / 2) * c₀ * c₁) * B₁ :=
        Nat.mul_le_mul_right B₁ hle
      have h2 : (((q + 1) / 2) * c₀ * c₁) * B₁ < (((q + 1) / 2) * c₀ * c₁) * sigma 1 B₁ :=
        Nat.mul_lt_mul_of_pos_left hB₁_lt_sig h_lhs_pos
      linarith
    exact ⟨r₁, hr₁_B, hr₀_pow_dvd_r₁, hsig_r₁_fact, hcop_r0_sigB₁,
      h_ordProj_r₁, h_sig_r₁_eq, hcop_c₁_r₁, h_peel_bal, h_strict_peel⟩

/-- **5. Peeling-Step Non-Termination Obstruction**:
At any coprime peeling step `Y * sigma 1 B' = r ^ (2 * e) * B'` with `r.Prime`, `0 < e`, `1 < Y`,
`0 < B'`, `¬ r ∣ B'`, and `Nat.Coprime r Y`, the cofactor `B'` cannot be `1`, forcing `1 < B'`,
`Y < r ^ (2 * e)`, `r ^ (2 * e) ∣ sigma 1 B'`, `(sigma 1 B').factorization r = 2 * e`, and
`B' = Y * (sigma 1 B' / r ^ (2 * e))`. -/
theorem peeling_step_no_terminal_unit_of_coprime {r e Y B' : ℕ}
    (hr : r.Prime) (he : 0 < e) (hY : 1 < Y) (hB' : 0 < B')
    (hnotdvd : ¬ r ∣ B') (hcop : Nat.Coprime r Y) (hbal : Y * sigma 1 B' = r ^ (2 * e) * B') :
    1 < B' ∧
    Y < r ^ (2 * e) ∧
    r ^ (2 * e) ∣ sigma 1 B' ∧
    (sigma 1 B').factorization r = 2 * e ∧
    B' = Y * (sigma 1 B' / r ^ (2 * e)) := by
  have hB'_gt1 : 1 < B' := by
    by_contra hle
    have hB'1 : B' = 1 := by omega
    have hY_eq : Y = r ^ (2 * e) := by
      rw [hB'1, sigma_one 1, mul_one, mul_one] at hbal
      exact hbal
    have hr_dvd_Y : r ∣ Y := by
      rw [hY_eq]
      exact dvd_pow_self r (by omega)
    exact hr.not_dvd_one (hcop ▸ Nat.dvd_gcd (dvd_refl r) hr_dvd_Y)
  have hB'_lt_sig : B' < sigma 1 B' := self_lt_sigma_of_one_lt hB'_gt1
  have hY_pos : 0 < Y := by omega
  have hY_lt : Y < r ^ (2 * e) := by
    by_contra! hle
    have h1 : r ^ (2 * e) * B' ≤ Y * B' := Nat.mul_le_mul_right B' hle
    have h2 : Y * B' < Y * sigma 1 B' := Nat.mul_lt_mul_of_pos_left hB'_lt_sig hY_pos
    linarith
  have hcop_pow : Nat.Coprime (r ^ (2 * e)) Y := hcop.pow_left (2 * e)
  have hpow_dvd_sigB' : r ^ (2 * e) ∣ sigma 1 B' :=
    hcop_pow.dvd_of_dvd_mul_left ⟨B', hbal⟩
  have hY_ne0 : Y ≠ 0 := hY_pos.ne'
  have hB'_ne0 : B' ≠ 0 := hB'.ne'
  have hsigB'_ne0 : sigma 1 B' ≠ 0 := (sigma_pos 1 B' hB'_ne0).ne'
  have hr_pow_pos : 0 < r ^ (2 * e) := pow_pos hr.pos _
  have hr_pow_ne0 : r ^ (2 * e) ≠ 0 := hr_pow_pos.ne'
  have hr_ndvd_Y : ¬ r ∣ Y := hr.coprime_iff_not_dvd.mp hcop
  have hY_fact : Y.factorization r = 0 := Nat.factorization_eq_zero_of_not_dvd hr_ndvd_Y
  have hB'_fact : B'.factorization r = 0 := Nat.factorization_eq_zero_of_not_dvd hnotdvd
  have h_pow_fact : (r ^ (2 * e)).factorization r = 2 * e := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hr.factorization_self, mul_one]
  have h_sigB'_fact : (sigma 1 B').factorization r = 2 * e := by
    have h := congrArg (fun x => x.factorization r) hbal
    rw [Nat.factorization_mul hY_ne0 hsigB'_ne0, Nat.factorization_mul hr_pow_ne0 hB'_ne0,
      Finsupp.add_apply, Finsupp.add_apply, hY_fact, hB'_fact, h_pow_fact, zero_add, add_zero] at h
    exact h
  have h_sigB'_eq : sigma 1 B' = r ^ (2 * e) * (sigma 1 B' / r ^ (2 * e)) :=
    (Nat.mul_div_cancel' hpow_dvd_sigB').symm
  have hB'_eq : B' = Y * (sigma 1 B' / r ^ (2 * e)) := by
    apply Nat.mul_left_cancel hr_pow_pos
    calc
      r ^ (2 * e) * B' = Y * sigma 1 B' := hbal.symm
      _ = Y * (r ^ (2 * e) * (sigma 1 B' / r ^ (2 * e))) := by rw [← h_sigB'_eq]
      _ = r ^ (2 * e) * (Y * (sigma 1 B' / r ^ (2 * e))) := by ring
  exact ⟨hB'_gt1, hY_lt, hpow_dvd_sigB', h_sigB'_fact, hB'_eq⟩

end OddPerfect
