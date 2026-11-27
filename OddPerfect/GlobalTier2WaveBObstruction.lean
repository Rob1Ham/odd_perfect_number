module

public import OddPerfect.GlobalTier2WaveAObstruction
public import OddPerfect.EvenIndexPrimorialObstruction
public import OddPerfect.TenFactorDropObstruction
public import OddPerfect.SixthPowerFreeNineDropPinch
public import OddPerfect.RestrainedSquareSourcesOneObstruction
public import OddPerfect.PadicEvenIndexObstruction
public import OddPerfect.GaussSumCyclotomicForms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Tier 2 Priority Wave B & Wave 12 Harvest Synthesis (`OddPerfect.GlobalTier2WaveBObstruction`)

Unifies the four harvested Wave 12 modules and the two Priority Wave B modules:
1. `OddPerfect.EvenIndexPrimorialObstruction` + `OddPerfect.PadicEvenIndexObstruction`:
   couples the symbolic all-`k` primorial confinement `min S₁ ∈ {3, 5, 7, 11, 13}` with the
   exact `p`-adic Hensel root distance `‖s - σ_p‖ = p ^ (-(2 * u + 1))` and universal
   fourth-order congruence `128 * (s - 1) ≡ 32 * p + 28 * p ^ 2 + 25 * p ^ 3 [MOD p ^ 4]`.
2. `OddPerfect.GaussSumCyclotomicForms`: couples `signed_prime_isSquare_of_dvd_geometricBlock`
   with repunit prime-length `geometricBlock r l = p` on even prime-power indices to force
   `l ∣ p - 1 ∧ IsSquare ((-1 : ZMod p) ^ (l / 2) * (l : ZMod p))`.
3. `OddPerfect.TenFactorDropObstruction`, `OddPerfect.SixthPowerFreeNineDropPinch`, and
   `OddPerfect.RestrainedSquareSourcesOneObstruction`: consolidates `N.factorization 5 % 6 ≠ 5`,
   tenth-power-free no-10-drop dichotomy, sixth-power-free 9/11-drop vacuum pinches, and
   restrained `v₃(N) = 2` square-source confinement `1 ≤ (squareSourcesOne N).card ≤ 2`.
-/

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- Cross-couples `EvenIndexPrimorialObstruction`, `PadicEvenIndexObstruction`, and
`GaussSumCyclotomicForms` on any even prime-power component index `i = p ^ (2 * u)`:
1. `N` contains `r ^ 2` for some `r ∈ {3, 5, 7, 11, 13}` with `geometricBlock r l = p` (`l.Prime`, `2 < l`),
   and by Gauss-sum cyclotomic reciprocity `IsSquare ((-1 : ZMod p) ^ (l / 2) * (l : ZMod p))`;
2. The cofactor `s` satisfies `2 * (p - 1) * s ^ 2 = (p - 2) + p ^ (2 * u + 1)`,
   `32 * (s - 1) ≡ 8 * p + 7 * p ^ 2 [MOD p ^ 3]`,
   `128 * (s - 1) ≡ 32 * p + 28 * p ^ 2 + 25 * p ^ 3 [MOD p ^ 4]`,
   and lies at exact `p`-adic distance `p ^ (-(2 * u + 1))` from the Hensel root `σ_p ∈ ℤ_[p]`. -/
theorem even_prime_power_primorial_padic_and_gauss_reciprocity
    {N q a b i p u : ℕ} [Fact p.Prime]
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b) (hl : sigma 1 b = q ^ a * i)
    (hr : sigma 1 (q ^ a) * i = 2 * b) (hp : p.Prime) (hu : 0 < u) (hi : i = p ^ (2 * u)) :
    (∃ r ∈ ({3, 5, 7, 11, 13} : Finset ℕ),
      r ^ 2 ∣ N ∧ ∃ l : ℕ, l.Prime ∧ 2 < l ∧ geometricBlock r l = p ∧
        IsSquare ((-1 : ZMod p) ^ (l / 2) * (l : ZMod p))) ∧
    ∃ s : ℕ, Odd s ∧
      2 * (p - 1) * s ^ 2 = (p - 2) + p ^ (2 * u + 1) ∧
      32 * (s - 1) ≡ 8 * p + 7 * p ^ 2 [MOD p ^ 3] ∧
      128 * (s - 1) ≡ 32 * p + 28 * p ^ 2 + 25 * p ^ 3 [MOD p ^ 4] ∧
      ∃ σ_p : ℤ_[p],
        2 * ((p : ℤ_[p]) - 1) * σ_p ^ 2 = (p : ℤ_[p]) - 2 ∧
        ‖(s : ℤ_[p]) - σ_p‖ = (p : ℝ) ^ (-(2 * u + 1 : ℤ)) ∧
        ((s : ℤ_[p]) - σ_p).valuation = 2 * u + 1 := by
  obtain ⟨⟨r, hr5, hr2N, l, hlp, hl2, hgb⟩, _⟩ :=
    even_prime_power_component_forces_small_repunit_base hN ho hq ha hform hqb hl hr hp hu hi
  have hbo := ho.of_dvd_nat (hform ▸ dvd_mul_left b _)
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h4 : 4 ∣ 2 * b := hr ▸ hi ▸ (pow_dvd_pow 2 (by omega : 2 ≤ 2 * u)).trans (dvd_mul_left _ _)
    have := hbo.not_two_dvd_nat
    omega
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hl_ne2 : l ≠ 2 := by omega
  have hr_ge1 : 1 ≤ r := by
    have hpos : ∀ x ∈ ({3, 5, 7, 11, 13} : Finset ℕ), 1 ≤ x := by decide
    exact hpos r hr5
  have hr_ge3 : 3 ≤ r := by
    have hpos : ∀ x ∈ ({3, 5, 7, 11, 13} : Finset ℕ), 3 ≤ x := by decide
    exact hpos r hr5
  have hp_gt_l : l < p := by
    rw [← hgb]
    have hsum : l < ∑ j ∈ Finset.range l, r ^ j := by
      calc
        l = ∑ _j ∈ Finset.range l, 1 := by simp
        _ < ∑ j ∈ Finset.range l, r ^ j := by
          refine Finset.sum_lt_sum (fun j _ => Nat.one_le_pow j r hr_ge1) ?_
          exact ⟨1, Finset.mem_range.mpr (by omega), by simpa using (by omega : 1 < r)⟩
    exact hsum
  have hpl : p ≠ l := (ne_of_lt hp_gt_l).symm
  have hdvd_gb : p ∣ geometricBlock r l := hgb ▸ dvd_rfl
  have hgauss :=
    (signed_prime_isSquare_of_dvd_geometricBlock hlp hl_ne2 hp hp2 hpl hr_ge1 hdvd_gb).2.1
  obtain ⟨ha1, hσq⟩ :=
    even_prime_power_index_eq_selected_sigma hN ho hq ha hform hqb hl hr hp hu hi
  obtain ⟨m, _, _, _, rfl⟩ :=
    euler_form_of_odd_component_index hN ho hq ha hform hqb hl hr (hi ▸ hpo.pow)
  have hmo := ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2 ≠ 0)) _)
  rw [ha1, pow_one] at hform hl hr
  rw [hi] at hl hr
  obtain ⟨s, hso, _, _, _, hplus, hσs⟩ := even_prime_power_cofactor_split hq hp hmo hpo hu hl hr
  have hclosed := even_index_twice_pred_mul_cofactor_sq hp hσq hplus
  obtain ⟨hmod3, hmod4⟩ := even_index_cofactor_mod_p_cube_and_fourth hp hpo hso hu hσq hplus hσs
  obtain ⟨σ_p, hroot, _, _, hnorm, hval, _, _⟩ :=
    even_index_cofactor_padic_distance_to_hensel_root hp hpo hso hu hσq hplus hσs
  exact ⟨⟨r, hr5, hr2N, l, hlp, hl2, hgb, hgauss⟩,
    ⟨s, hso, hclosed, hmod3, hmod4, σ_p, hroot, hnorm, hval⟩⟩

/-- **Tier 2 Priority Wave B & Wave 12 Master Profile**:
Unconditionally packages Sylvester's `v₅(N) % 6 ≠ 5` obstruction, the tenth-power / three-free
10-factor drop dichotomy, restrained `v₃(N) = 2` confinement, and sixth-power-free 9-drop pinch. -/
theorem odd_perfect_tier2_waveB_and_wave12_master_profile {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) :
    N.factorization 5 % 6 ≠ 5 ∧
    ((∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 10 ≤ cardFactors N) ∨
      ((∀ p : ℕ, p.Prime → ¬ p ^ 10 ∣ N) ∧
        2 * cardFactors N + 1 ≤ 10 * N.primeFactors.card)) ∧
    ∀ q ∈ N.primeFactors, q % 4 = 1 → N.factorization q % 4 = 1 →
      (∀ r : ℕ, r ≠ q → Even (N.factorization r)) →
      ((largeSources N q).card ≤ 1 → N.factorization 3 = 2 →
        q % 12 = 1 ∧ 13 ≤ q ∧ 1 ≤ (squareSourcesOne N).card ∧ (squareSourcesOne N).card ≤ 2) ∧
      ((∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) →
        (∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 9 ≤ cardFactors N) ∨
        ((twoModThreeLargeSources N q).card ≤ 1 ∧
          ((squareSources N).filter (· % 5 ≠ 1)).card ≤ 3 ∧
          147 ≤ (oneModThreeLargeSources N q).card)) := by
  have h5 := five_factorization_mod_six_ne_five ho hN
  obtain ⟨q₀, hq₀, hq₀4, he₀, hev₀⟩ := euler_exponents ho hN
  have h10_or :
      (∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 10 ≤ cardFactors N) ∨
      ((∀ p : ℕ, p.Prime → ¬ p ^ 10 ∣ N) ∧
        2 * cardFactors N + 1 ≤ 10 * N.primeFactors.card) := by
    by_cases hex10 : ∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 10 ≤ cardFactors N
    · exact Or.inl hex10
    · right
      have hno10 : ∀ p ∈ N.primeFactors, cardFactors N < cardFactors (componentIndex N p) + 10 := by
        intro p hp
        have hnot : ¬ (cardFactors (componentIndex N p) + 10 ≤ cardFactors N) :=
          fun hle => hex10 ⟨p, hp, hle⟩
        omega
      obtain ⟨_, _, h10free, _, hdens⟩ :=
        no_ten_factor_drop_profile ho hN hq₀ hq₀4 he₀ hev₀ hno10
      exact ⟨h10free, hdens⟩
  refine ⟨h5, h10_or, fun q hq hq4 he hev => ⟨?_, ?_⟩⟩
  · intro hle h3_2
    obtain ⟨hq12, h13, _, h1, h2⟩ := restrained_exact_nine_profile ho hN hq hq4 he hev hle h3_2
    exact ⟨hq12, h13, h1, h2⟩
  · intro hfree
    by_cases hex9 : ∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 9 ≤ cardFactors N
    · exact Or.inl hex9
    · right
      have hno9 : ∀ p ∈ N.primeFactors, cardFactors N < cardFactors (componentIndex N p) + 9 := by
        intro p hp
        have hnot : ¬ (cardFactors (componentIndex N p) + 9 ≤ cardFactors N) :=
          fun hle => hex9 ⟨p, hp, hle⟩
        omega
      obtain ⟨⟨hq23, hs50, _⟩, ⟨hq13, _⟩, _, _⟩ :=
        sixth_power_free_no_nine_drop_pinch ho hN hq hq4 he hev hfree hno9
      exact ⟨hq23, hs50, hq13⟩

end OddPerfect
