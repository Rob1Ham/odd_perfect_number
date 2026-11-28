module

public import OddPerfect.CyclotomicIrreducibleAndZetaDivisorLaws
public import OddPerfect.FactorialStirlingSupportObstruction
public import OddPerfect.LinearEulerCoprimeTwoStepChainObstruction
public import OddPerfect.SixthPowerFreeS51CollisionDensityPinch
public import OddPerfect.GlobalTier2WaveLObstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Global Tier 2 Wave M Synthesis (`OddPerfect.GlobalTier2WaveMObstruction`)

Unifies all four Priority Wave M structural modules (crossing the `900`-module public audit
milestone) into cross-module global theorems with 100% preservation of every component invariant:
1. **Zeta Convolution, Factorization-Lattice, Cyclotomic Irreducibility, & Stirling Superlinear
   Envelope** (`odd_perfect_zeta_cyclotomic_and_stirling_envelope`):
   unifies `(ζ * id) N = 2 * N`, `N.properDivisors = (Iio N.factorization).image (·.prod (· ^ ·))`,
   `(Iio N.factorization).card = N.divisors.card - 1`, `N.divisors.card % 4 = 2`,
   `ℤ`/`ℚ`-irreducibility & `ℚ`-coprimality of component cyclotomic factors `Φ_d`,
   `2 ^ ω * ω! < rad(N)` (`2 * ω + 1 ≤ P_max`), `rad(N) ^ 6 < 3 * N ^ 4`, and the superlinear
   Stirling bound `6 * ω * (log (2 * ω) - 1) < log 3 + 4 * log N`.
2. **Tier 2 Wave M Master Profile** (`odd_perfect_tier2_waveM_master_profile`):
   unifies all global envelope invariants with the sixth-power-free `mod 8` divisor-count
   parity law (`N.divisors.card % 8 = 2 ↔ Even |squareSources N|`), Ljunggren non-squareness
   and `S₅₁_col` quartic-target forcing (`|largeSources N q| ≤ 2 * |S₅₁_col| + 1`,
   `73 ≤ |S₅₁_col|`), and the coprime half-successor two-step chain dichotomy
   (`13845841 ≤ r₀ ^ (2 * e₀)` vs. `3721 ≤ U₀ ∧ 13849563 ≤ W ∧ 1648097997 ≤ 2 * u ^ 2 - σ(u ^ 2)`).
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- **1. Global Zeta, Factorization-Lattice, Cyclotomic Irreducibility, & Stirling Envelope**:
Unconditionally preserves every global invariant from `CyclotomicIrreducibleAndZetaDivisorLaws`
and `FactorialStirlingSupportObstruction`. -/
theorem odd_perfect_zeta_cyclotomic_and_stirling_envelope {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    let ω : ℝ := (N.primeFactors.card : ℝ)
    let rad := ∏ p ∈ N.primeFactors, p
    (ArithmeticFunction.zeta * ArithmeticFunction.id) N = 2 * N ∧
    N.properDivisors = (Finset.Iio N.factorization).image (·.prod (· ^ ·)) ∧
    (Finset.Iio N.factorization).card = N.divisors.card - 1 ∧
    N.divisors.card % 4 = 2 ∧
    N.properDivisors.card % 4 = 1 ∧
    (Finset.Iio N.factorization).card % 4 = 1 ∧
    (∀ p ∈ N.primeFactors,
      (∀ d ∈ (N.factorization p + 1).divisors,
        Irreducible (Polynomial.cyclotomic d ℤ) ∧ Irreducible (Polynomial.cyclotomic d ℚ)) ∧
      (∀ d₁ ∈ (N.factorization p + 1).divisors, ∀ d₂ ∈ (N.factorization p + 1).divisors,
        d₁ ≠ d₂ → IsCoprime (Polynomial.cyclotomic d₁ ℚ) (Polynomial.cyclotomic d₂ ℚ))) ∧
    (∃ P_max ∈ N.primeFactors, 2 * N.primeFactors.card + 1 ≤ P_max) ∧
    2 ^ N.primeFactors.card * N.primeFactors.card.factorial < rad ∧
    rad ^ 6 < 3 * N ^ 4 ∧
    ω * (Real.log (2 * ω) - 1) < Real.log (rad : ℝ) ∧
    6 * ω * (Real.log (2 * ω) - 1) < Real.log 3 + 4 * Real.log (N : ℝ) := by
  intro ω rad
  obtain ⟨hzeta, himg, hcard_iio, hdiv4, hprop4, hiio4⟩ :=
    odd_perfect_zeta_divisor_and_lattice_laws ho hN
  have hcyc : ∀ p ∈ N.primeFactors,
      (∀ d ∈ (N.factorization p + 1).divisors,
        Irreducible (Polynomial.cyclotomic d ℤ) ∧ Irreducible (Polynomial.cyclotomic d ℚ)) ∧
      (∀ d₁ ∈ (N.factorization p + 1).divisors, ∀ d₂ ∈ (N.factorization p + 1).divisors,
        d₁ ≠ d₂ → IsCoprime (Polynomial.cyclotomic d₁ ℚ) (Polynomial.cyclotomic d₂ ℚ)) :=
    fun p hp => odd_perfect_component_cyclotomic_irreducible_and_coprime ho hN hp
  obtain ⟨q, a, m, hq, _, ha4, hqm, hform⟩ := euler_form ho hN
  have ha_pos : 0 < a := by omega
  have hq_dvd : q ∣ N := by
    rw [hform]
    exact dvd_mul_of_dvd_left (dvd_pow_self q ha_pos.ne') _
  have hq_mem : q ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hq_dvd, hN.2.ne'⟩
  have hne : N.primeFactors.Nonempty := ⟨q, hq_mem⟩
  have hodd_pf : ∀ p ∈ N.primeFactors, p.Prime ∧ Odd p := fun p hp =>
    ⟨Nat.prime_of_mem_primeFactors hp, ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)⟩
  obtain ⟨hmax_ge, _⟩ := two_pow_mul_factorial_lt_prod_odd_primes hne hodd_pf
  have hpmax_ex : ∃ P_max ∈ N.primeFactors, 2 * N.primeFactors.card + 1 ≤ P_max :=
    ⟨N.primeFactors.max' hne, Finset.max'_mem N.primeFactors hne, hmax_ge⟩
  obtain ⟨h2fac_lt, _, hrad6_lt⟩ :=
    odd_perfect_radical_sq_le_euler_mul_and_pow_six_lt ho hN hq ha_pos hqm hform
  obtain ⟨hstir1, hstir2⟩ := odd_perfect_stirling_superlinear_log_bound ho hN
  exact ⟨hzeta, himg, hcard_iio, hdiv4, hprop4, hiio4, hcyc,
    hpmax_ex, h2fac_lt, hrad6_lt, hstir1, hstir2⟩

/-- **2. Tier 2 Wave M Master Profile**:
Unconditionally synthesizes all four Wave M component modules with 100% invariant preservation. -/
theorem odd_perfect_tier2_waveM_master_profile {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    let ω : ℝ := (N.primeFactors.card : ℝ)
    let rad := ∏ p ∈ N.primeFactors, p
    (ArithmeticFunction.zeta * ArithmeticFunction.id) N = 2 * N ∧
    N.properDivisors = (Finset.Iio N.factorization).image (·.prod (· ^ ·)) ∧
    (Finset.Iio N.factorization).card = N.divisors.card - 1 ∧
    N.divisors.card % 4 = 2 ∧
    N.properDivisors.card % 4 = 1 ∧
    (Finset.Iio N.factorization).card % 4 = 1 ∧
    (∀ p ∈ N.primeFactors,
      (∀ d ∈ (N.factorization p + 1).divisors,
        Irreducible (Polynomial.cyclotomic d ℤ) ∧ Irreducible (Polynomial.cyclotomic d ℚ)) ∧
      (∀ d₁ ∈ (N.factorization p + 1).divisors, ∀ d₂ ∈ (N.factorization p + 1).divisors,
        d₁ ≠ d₂ → IsCoprime (Polynomial.cyclotomic d₁ ℚ) (Polynomial.cyclotomic d₂ ℚ))) ∧
    (∃ P_max ∈ N.primeFactors, 2 * N.primeFactors.card + 1 ≤ P_max) ∧
    2 ^ N.primeFactors.card * N.primeFactors.card.factorial < rad ∧
    rad ^ 6 < 3 * N ^ 4 ∧
    ω * (Real.log (2 * ω) - 1) < Real.log (rad : ℝ) ∧
    6 * ω * (Real.log (2 * ω) - 1) < Real.log 3 + 4 * Real.log (N : ℝ) ∧
    ∃ q a m : ℕ,
      q.Prime ∧ q ∈ N.primeFactors ∧ q % 4 = 1 ∧ a % 4 = 1 ∧ 0 < a ∧ ¬ q ∣ m ∧
      N = q ^ a * m ^ 2 ∧
      rad ^ 2 ≤ q * N ∧
      ((∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) →
        let S₅₁ := (squareSources N).filter (· % 5 = 1)
        let S₅₁_col := S₅₁.filter (fun r => indegAt N q r = 2)
        (N.divisors.card % 8 = 2 ∨ N.divisors.card % 8 = 6) ∧
        (N.divisors.card % 8 = 2 ↔ Even (squareSources N).card) ∧
        (N.divisors.card % 8 = 6 ↔ Odd (squareSources N).card) ∧
        (∀ p ∈ N.primeFactors.erase q,
          ¬ IsSquare (sigma 1 (p ^ N.factorization p)) ∧
          ∃ r ∈ N.primeFactors,
            Odd ((sigma 1 (p ^ N.factorization p)).factorization r) ∧
            (r = q ∨ 2 ≤ indegAt N q r)) ∧
        (∀ u ∈ largeSources N q, ¬ q ∣ sigma 1 (u ^ 4) →
          ∃ r ∈ S₅₁_col, r ∣ sigma 1 (u ^ 4)) ∧
        ((largeSources N q).filter (fun u => q ∣ sigma 1 (u ^ 4))).card ≤ 1 ∧
        (largeSources N q).card ≤ 2 * S₅₁_col.card + 1 ∧
        73 ≤ S₅₁_col.card) ∧
      ((∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) → Nat.Coprime ((q + 1) / 2) (componentIndex N q) →
        ∃ h u W r₀ e₀ U₀ c₀_u V₀ s : ℕ,
          W = sigma 1 (u ^ 2) / q ∧
          59 ≤ h ∧ 6961 ≤ q ∧ 71 ≤ U₀ ∧ 5113 ≤ W ∧
          ¬ IsPrimePow u ∧
          N = q * (h * u) ^ 2 ∧ componentIndex N q = u ^ 2 ∧
          u = r₀ ^ e₀ * U₀ ∧ W = c₀_u * sigma 1 (U₀ ^ 2) ∧ U₀ ^ 2 = c₀_u * V₀ ∧
          r₀ ^ (2 * e₀) * V₀ = sigma 1 (U₀ ^ 2) * sigma 1 (h ^ 2) ∧
          Nat.Coprime (r₀ ^ (2 * e₀)) V₀ ∧
          r₀.Prime ∧ s.Prime ∧ s ∈ U₀.primeFactors ∧ s ≠ r₀ ∧
          61 ≤ r₀ ∧ 61 ≤ s ∧
          e₀ ∈ ({1, 2} : Finset ℕ) ∧ U₀.factorization s ∈ ({1, 2} : Finset ℕ) ∧
          r₀ ∣ sigma 1 (s ^ (2 * U₀.factorization s)) ∧
          ((U₀.factorization s = 1 ∧
              s % 5 = 1 ∧ 71 ≤ s ∧
              r₀ ∣ s ^ 2 + s + 1 ∧ r₀ % 3 = 1 ∧
              e₀ = 2 ∧ r₀ ∈ oneModThreeLargeSources N q ∧
              13845841 ≤ r₀ ^ (2 * e₀)) ∨
           (U₀.factorization s = 2 ∧
              s ∈ largeSources N q ∧
              r₀ ∣ s ^ 4 + s ^ 3 + s ^ 2 + s + 1 ∧ r₀ % 5 = 1 ∧
              3721 ≤ U₀ ∧ 13849563 ≤ W ∧
              1648097997 ≤ 2 * u ^ 2 - sigma 1 (u ^ 2))) ∧
          (13845841 ≤ r₀ ^ (2 * e₀) ∨
            (3721 ≤ U₀ ∧ 13849563 ≤ W ∧ 1648097997 ≤ 2 * u ^ 2 - sigma 1 (u ^ 2)))) := by
  intro ω rad
  obtain ⟨hzeta, himg, hcard_iio, hdiv4, hprop4, hiio4, hcyc,
    hpmax_ex, h2fac_lt, hrad6_lt, hstir1, hstir2⟩ :=
    odd_perfect_zeta_cyclotomic_and_stirling_envelope ho hN
  obtain ⟨_, _, q, a, m, hq, hq_mem, hq4, ha4, ha_pos, hqm, hform, _, _, _⟩ :=
    odd_perfect_tier2_waveL_master_profile ho hN
  obtain ⟨_, hrad2_le, _⟩ :=
    odd_perfect_radical_sq_le_euler_mul_and_pow_six_lt ho hN hq ha_pos hqm hform
  have hm0 : m ≠ 0 := by
    intro hm
    rw [hm] at hform
    simp at hform
    exact hN.2.ne' hform
  have hfact_q : N.factorization q = a := by
    rw [hform, Nat.factorization_mul (pow_ne_zero a hq.ne_zero) (pow_ne_zero 2 hm0),
      Finsupp.add_apply, hq.factorization_pow, Finsupp.single_eq_same]
    have hqm2 : ¬ q ∣ m ^ 2 := fun hd => hqm (hq.dvd_of_dvd_pow hd)
    rw [Nat.factorization_eq_zero_of_not_dvd hqm2]
    omega
  have he_q : N.factorization q % 4 = 1 := by omega
  have hev_N : ∀ r : ℕ, r ≠ q → Even (N.factorization r) := by
    intro r hr_ne
    by_cases hr_prime : r.Prime
    · rw [hform, Nat.factorization_mul (pow_ne_zero a hq.ne_zero) (pow_ne_zero 2 hm0),
        Finsupp.add_apply, hq.factorization_pow, Finsupp.single_eq_of_ne hr_ne, zero_add,
        Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
      exact ⟨m.factorization r, by ring⟩
    · rw [Nat.factorization_eq_zero_of_not_prime N hr_prime]
      exact ⟨0, rfl⟩
  refine ⟨hzeta, himg, hcard_iio, hdiv4, hprop4, hiio4, hcyc,
    hpmax_ex, h2fac_lt, hrad6_lt, hstir1, hstir2,
    q, a, m, hq, hq_mem, hq4, ha4, ha_pos, hqm, hform, hrad2_le, ?_, ?_⟩
  · intro hfree
    obtain ⟨hmod8_or, hmod8_2, hmod8_6⟩ :=
      sixth_power_free_divisor_count_mod_eight_iff ho hN hq_mem hq4 he_q hev_N hfree
    have hlj :=
      sixth_power_free_non_euler_has_odd_valuation_target ho hN hq_mem hq4 he_q hev_N hfree
    obtain ⟨hq_hit, hq_src_le1⟩ :=
      sixth_power_free_largeSources_hit_S51_col ho hN hq_mem hq4 he_q hev_N hfree
    obtain ⟨hq_le_2col, h73⟩ :=
      sixth_power_free_S51_col_ge_73 ho hN hq_mem hq4 he_q hev_N hfree
    exact ⟨hmod8_or, hmod8_2, hmod8_6, hlj, hq_hit, hq_src_le1, hq_le_2col, h73⟩
  · intro hfree hcop
    obtain ⟨h, u, W, r₀, e₀, U₀, c₀_u, V₀, s,
      hW_def, hh_ge, hq_ge, hU₀_ge, hW_ge, hnpp,
      hform_hu, hci_eq, hu_split, hW_eq, hU₀2_eq, hbal_V₀, hcop_V₀,
      hr₀_p, hs_p, hs_U₀, hs_ne, hr₀_ge61, hs_ge61, he₀_mem, hks_mem,
      hr₀_dvd_s, hcase⟩ :=
      sixth_power_free_coprime_half_succ_two_step_dichotomy ho hN hq_mem hq4 he_q hev_N hfree hcop
    have hfloor :
        13845841 ≤ r₀ ^ (2 * e₀) ∨
          (3721 ≤ U₀ ∧ 13849563 ≤ W ∧ 1648097997 ≤ 2 * u ^ 2 - sigma 1 (u ^ 2)) := by
      rcases hcase with ⟨_, _, _, _, _, _, _, hr₀_ge⟩ | ⟨_, _, _, _, hU_ge, hW8, hdiff⟩
      · exact Or.inl hr₀_ge
      · exact Or.inr ⟨hU_ge, hW8, hdiff⟩
    exact ⟨h, u, W, r₀, e₀, U₀, c₀_u, V₀, s,
      hW_def, hh_ge, hq_ge, hU₀_ge, hW_ge, hnpp,
      hform_hu, hci_eq, hu_split, hW_eq, hU₀2_eq, hbal_V₀, hcop_V₀,
      hr₀_p, hs_p, hs_U₀, hs_ne, hr₀_ge61, hs_ge61, he₀_mem, hks_mem,
      hr₀_dvd_s, hcase, hfloor⟩

end OddPerfect
