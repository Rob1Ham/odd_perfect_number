module

public import OddPerfect.LinearEulerSquareDescent
public import OddPerfect.ZsqrtTwoFermatDescent
public import OddPerfect.TotientOrderTower
public import OddPerfect.ValuationMatrixLinearAlgebra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Tier 2 Priority Wave A Global Synthesis (`OddPerfect.GlobalTier2WaveAObstruction`)

Unifies the four Priority Wave A resolution fronts:
1. `OddPerfect.LinearEulerSquareDescent`: `((q + 1) / 2) * i_q = m ^ 2`,
   `DeficientPerfectWith (m ^ 2) i_q`, `r₀`-valuation conservation, 3-divisor square descent
   `B = ((q + 1) / 2) * c₀ * D₀`, and composite-square splitting vs. iterated cofactor peeling.
2. `OddPerfect.ZsqrtTwoFermatDescent`: `EuclideanDomain (ℤ√2)`, full unit classification via
   `silverUnit = 1 + √2`, reduced `d`-th power descent, `k ≠ 0` elimination, and mod-`d`
   Frobenius collapse `α ≡ silverUnit ^ (-k) [ZMOD d]` on `I = l * t ^ 2` (`a > 1`).
3. `OddPerfect.TotientOrderTower`: global radical–totient–Möbius identities, sharp two-sided
   totient envelope `3N < 8φ(N) < 4N` (`27N < 64φ(N)` when `¬ 3 ∣ N`), Carmichael divisibility
   `lcm_p (e_p + 1) ∣ carmichael N`, and the extremal `(r - 1)`-valuation trap.
4. `OddPerfect.ValuationMatrixLinearAlgebra`: `𝔽₂` odd-valuation operator `oddSigmaMatrix N`,
   cokernel identity `1 ᵥ* A = e_q`, odd global target sum, right-kernel orthogonality `w_q = 0`,
   left-kernel Jacobi reciprocity, and off-diagonal component-index second moment.
-/

public section

namespace OddPerfect

open ArithmeticFunction Finset
open scoped Matrix

/-- Global totient-deficiency gap, Carmichael divisor-length envelope, and off-diagonal
component-index valuation conservation across all odd perfect numbers. -/
theorem odd_perfect_totient_gap_and_carmichael_envelope {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) :
    0 < N - 2 * N.totient ∧
    (4 * N.primeFactors.card + 5) * (N - 2 * N.totient) < N.primeFactors.card * N ∧
    4 * (N - 2 * N.totient) < N ∧
    (¬ 3 ∣ N → 32 * (N - 2 * N.totient) < 5 * N) ∧
    (N.primeFactors.lcm fun p => N.factorization p + 1) ∣ ArithmeticFunction.carmichael N ∧
    (∑ p ∈ N.primeFactors, ∑ r ∈ N.primeFactors.erase p, (componentIndex N p).factorization r) =
      (N.primeFactors.card - 2) * cardFactors N := by
  obtain ⟨h2lt, hω_pinch, h38, h3free⟩ := odd_perfect_totient_two_sided_bounds ho hN
  obtain ⟨_, _, hcarm, _⟩ := odd_perfect_length_lcm_dvd_carmichael ho hN
  have hoff := sum_offDiag_componentIndex_factorization ho hN
  have hle : 2 * N.totient ≤ N := h2lt.le
  have hgap_pos : 0 < N - 2 * N.totient := Nat.sub_pos_of_lt h2lt
  have hω_gap : (4 * N.primeFactors.card + 5) * (N - 2 * N.totient) < N.primeFactors.card * N := by
    zify [hle] at hω_pinch ⊢
    nlinarith
  have h4_gap : 4 * (N - 2 * N.totient) < N := by
    zify [hle] at h38 ⊢
    linarith
  refine ⟨hgap_pos, hω_gap, h4_gap, ?_, hcarm, hoff⟩
  intro h3
  have h27 := h3free h3
  zify [hle] at h27 ⊢
  linarith

/-- Cross-coupled linear Euler (`N = q * m ^ 2`) square descent and Carmichael length export:
couples `DeficientPerfectWith (m ^ 2) i_q`, `r₀`-valuation conservation, and the 3-divisor
square split/peeling dichotomy with `2 * e₀ + 1 ∣ lcm_r (r - 1) ∣ carmichael N`. -/
theorem linear_euler_square_descent_and_carmichael_export {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2) :
    let i_q := sigma 1 (m ^ 2) / q
    ((q + 1) / 2) * i_q = m ^ 2 ∧
    oddValuationPrimes ((q + 1) / 2) = oddValuationPrimes i_q ∧
    DeficientPerfectWith (m ^ 2) i_q ∧
    ∃ r₀ ∈ m.primeFactors,
      q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀)) ∧
      let e₀ := m.factorization r₀
      let B := ordCompl[r₀] (m ^ 2)
      2 * e₀ + 1 ∣ (N.primeFactors.lcm fun r => r - 1) ∧
      2 * e₀ + 1 ∣ ArithmeticFunction.carmichael N ∧
      ((q + 1) / 2).factorization r₀ + (sigma 1 B).factorization r₀ = 2 * e₀ ∧
      (r₀ ∣ (q + 1) / 2 ∨
        ((∃ B₁ B₂ : ℕ, B = B₁ * B₂ ∧ B₁.Coprime B₂ ∧
            r₀ ∣ Nat.gcd (sigma 1 B₁) (sigma 1 B₂) ∧
            1 < Nat.gcd (r₀ ^ (2 * e₀)) (sigma 1 B₁) ∧
            Nat.gcd (r₀ ^ (2 * e₀)) (sigma 1 B₁) < r₀ ^ (2 * e₀)) ∨
         (∃ r₁ ∈ B.primeFactors,
            r₀ ^ (2 * e₀) ∣ sigma 1 (ordProj[r₁] B) ∧
            (sigma 1 (ordProj[r₁] B)).factorization r₀ = 2 * e₀ ∧
            Nat.Coprime r₀ (sigma 1 (ordCompl[r₁] B))))) := by
  obtain ⟨hmul, hoddV, hdef⟩ :=
    linear_euler_half_succ_mul_index_and_deficient_square ho hN hq hqm hform
  obtain ⟨_, r₀, hr₀_m, hq_dvd, _, _, _, _⟩ :=
    linear_euler_unique_q_source_and_bound ho hN hq hqm hform
  have hval := linear_euler_r0_valuation_conservation ho hN hq hqm hform hr₀_m hq_dvd
  obtain ⟨hlcm_sub, _, _, hcarm_all⟩ := odd_perfect_length_lcm_dvd_carmichael ho hN
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀_m
  have hm_ne0 : m ≠ 0 := (Nat.mem_primeFactors.mp hr₀_m).2.2
  have hr₀_N : r₀ ∈ N.primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨hr₀_prime, ?_, hN.2.ne'⟩
    have hdvd_m : r₀ ∣ m := Nat.dvd_of_mem_primeFactors hr₀_m
    exact (hdvd_m.trans (dvd_pow_self m (by decide : 2 ≠ 0))).trans (hform ▸ dvd_mul_left _ _)
  have hfac_r₀ : N.factorization r₀ = 2 * m.factorization r₀ := by
    have hq_ne_r₀ : q ≠ r₀ := fun h => hqm (h ▸ Nat.dvd_of_mem_primeFactors hr₀_m)
    have hq_r0_zero : q.factorization r₀ = 0 :=
      Nat.factorization_eq_zero_of_not_dvd fun hd =>
        hq_ne_r₀ ((Nat.prime_dvd_prime_iff_eq hr₀_prime hq).mp hd).symm
    rw [hform, Nat.factorization_mul hq.ne_zero (pow_ne_zero 2 hm_ne0), Finsupp.add_apply,
      hq_r0_zero, zero_add, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have hdvd_lcm_len : 2 * m.factorization r₀ + 1 ∣
      (N.primeFactors.lcm fun p => N.factorization p + 1) := by
    rw [← hfac_r₀]
    exact Finset.dvd_lcm hr₀_N
  have hdvd_sub : 2 * m.factorization r₀ + 1 ∣ (N.primeFactors.lcm fun r => r - 1) :=
    hdvd_lcm_len.trans hlcm_sub
  have hdvd_carm : 2 * m.factorization r₀ + 1 ∣ ArithmeticFunction.carmichael N := by
    rw [← hfac_r₀]
    exact hcarm_all r₀ hr₀_N
  refine ⟨hmul, hoddV, hdef, r₀, hr₀_m, hq_dvd, hdvd_sub, hdvd_carm, hval, ?_⟩
  by_cases hr₀_half : r₀ ∣ (q + 1) / 2
  · exact Or.inl hr₀_half
  · right
    have hcop : Nat.Coprime r₀ ((q + 1) / 2) := hr₀_prime.coprime_iff_not_dvd.mpr hr₀_half
    rcases linear_euler_composite_square_split_or_single_absorber
        ho hN hq hqm hform hr₀_m hq_dvd hcop with hsplit | ⟨r₁, hr₁B, hdvd1, hfac1, hcop1, _⟩
    · exact Or.inl hsplit
    · exact Or.inr ⟨r₁, hr₁B, hdvd1, hfac1, hcop1⟩

/-- **Tier 2 Priority Wave A Master Profile**:
Unconditionally couples linear-Euler square descent (`a = 1`), `ℤ√2` Frobenius descent (`a > 1`),
`𝔽₂` valuation-matrix cokernel/kernel constraints, and the totient–Carmichael–order tower. -/
theorem odd_perfect_tier2_waveA_master_profile {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    (0 < N - 2 * N.totient ∧
      4 * (N - 2 * N.totient) < N ∧
      (N.primeFactors.lcm fun p => N.factorization p + 1) ∣ ArithmeticFunction.carmichael N ∧
      ∀ l r : ℕ, l.Prime → r ∈ N.primeFactors →
        (N.factorization r + 1).factorization l ≤
          (N.primeFactors.erase r).sup (fun s => (s - 1).factorization l)) ∧
    ∃ (q a m : ℕ) (hq_mem : q ∈ N.primeFactors),
      q % 4 = 1 ∧ a % 4 = 1 ∧ ¬ q ∣ m ∧ N = q ^ a * m ^ 2 ∧
      ((fun _ : ↥N.primeFactors => (1 : ZMod 2)) ᵥ* oddSigmaMatrix N =
          Pi.single ⟨q, hq_mem⟩ (1 : ZMod 2)) ∧
      Odd (∑ p ∈ N.primeFactors, (oddSigmaTargets N p).card) ∧
      (∀ w : ↥N.primeFactors → ZMod 2,
        oddSigmaMatrix N *ᵥ w = 0 → w ⟨q, hq_mem⟩ = 0) ∧
      ((a = 1 ∧ DeficientPerfectWith (m ^ 2) (sigma 1 (m ^ 2) / q) ∧
          ((q + 1) / 2) * (sigma 1 (m ^ 2) / q) = m ^ 2) ∨
       (1 < a ∧ ∀ l t : ℕ, l.Prime → sigma 1 (m ^ 2) / q ^ a = l * t ^ 2 →
          ∃ (y : ℕ) (k : ℤ) (α : ℤ√2),
            1 ≤ |k| ∧ 2 * |k| ≤ ((a + 1) / 2 : ℤ) - 1 ∧
            (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ ((a + 1) / 2) ∧
            α.re ≡ ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2).re [ZMOD ((a + 1) / 2 : ℤ)] ∧
            α.im ≡ ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2).im [ZMOD ((a + 1) / 2 : ℤ)])) := by
  obtain ⟨hgap0, _, h4gap, _, hcarm, _⟩ := odd_perfect_totient_gap_and_carmichael_envelope ho hN
  refine ⟨⟨hgap0, h4gap, hcarm, fun l r hl hr =>
    extremal_sub_one_valuation_trap ho hN l hl r hr⟩, ?_⟩
  obtain ⟨q, a, m, hqp, hq4, ha4, hqm, hform⟩ := euler_form ho hN
  have ha_pos : 0 < a := by omega
  have hq_mem : q ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hqp, (dvd_pow_self q ha_pos.ne').trans (hform ▸ dvd_mul_right _ _),
      hN.2.ne'⟩
  have hm_ne0 : m ≠ 0 := by
    intro hm0
    apply hN.2.ne'
    rw [hform, hm0, zero_pow (by decide : 2 ≠ 0), mul_zero]
  have hfac_q : N.factorization q = a := by
    rw [hform, Nat.factorization_mul (pow_ne_zero a hqp.ne_zero) (pow_ne_zero 2 hm_ne0),
      Finsupp.add_apply, hqp.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_eq_zero_of_not_dvd hqm, mul_zero, add_zero]
  have he : N.factorization q % 4 = 1 := hfac_q ▸ ha4
  have hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r) := by
    intro r hrq
    rw [hform, Nat.factorization_mul (pow_ne_zero a hqp.ne_zero) (pow_ne_zero 2 hm_ne0),
      Finsupp.add_apply, hqp.factorization_pow, Finsupp.single_eq_of_ne hrq, zero_add,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    exact even_two_mul _
  have hcok := vecMul_ones_oddSigmaMatrix_eq_single ho hN hq_mem hq4 he hev
  obtain ⟨hodd_sum, _⟩ := sum_oddSigmaTargets_card_odd ho hN hq_mem hq4 he hev
  have hker : ∀ w : ↥N.primeFactors → ZMod 2, oddSigmaMatrix N *ᵥ w = 0 → w ⟨q, hq_mem⟩ = 0 :=
    fun w hw => oddSigmaMatrix_right_kernel_avoids_euler ho hN hq_mem hq4 he hev hw
  refine ⟨q, a, m, hq_mem, hq4, ha4, hqm, hform, hcok, hodd_sum, hker, ?_⟩
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt ha_pos) with ha1 | ha_gt1
  · left
    have ha1' : a = 1 := ha1.symm
    have hform1 : N = q * m ^ 2 := by simpa [ha1'] using hform
    obtain ⟨hmul, _, hdef⟩ :=
      linear_euler_half_succ_mul_index_and_deficient_square ho hN hqp hqm hform1
    exact ⟨ha1', hdef, hmul⟩
  · right
    refine ⟨ha_gt1, fun l t hlp hi => ?_⟩
    obtain ⟨y, k, α, _, _, _, hk1, h2k, hz_eq, _, hre, him⟩ :=
      exceptional_euler_zsqrtTwo_frobenius_descent hN ho hqp hq4 ha4 ha_gt1 hqm hform hlp hi
    exact ⟨y, k, α, hk1, h2k, hz_eq, hre, him⟩

end OddPerfect
