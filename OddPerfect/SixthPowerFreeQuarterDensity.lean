module

public import OddPerfect.GlobalWave8Obstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sixth-Power-Free Quarter-Density Obstruction (`OddPerfect.SixthPowerFreeQuarterDensity`)

Combines Wave 8's sharpened bipartite capacity bound
`3 * |Q₁₃| + 2 * |Q₂₃| ≤ 4 * |S₅₁| + 3` (`sixth_power_free_sharpened_quartic_to_S51_bound`),
the three-free sharpened cyclotomic slope `8 * ω(N) + 4 * |Q₂₃| ≤ 3 * Ω(N) + 7`
(`sharpened_cyclotomic_slope_three_free`), and the Fletcher–Nielsen–Ochem sixth-power-free
support bound `443 ≤ ω(N)` (`sixth_power_or_large_support`) to upgrade the sixth-power-free
`S₅₁` density lower bound from `92` and `5 * ω(N) ≤ 24 * |S₅₁| + 28` to the quarter-density
threshold:

1. `sixth_power_free_omega_and_total_identities`:
   Exact rank/multiplicity identities and the bound `ω(N) ≤ 3 * |Q₁₃| + |Q₂₃| + 2`.
2. `sixth_power_free_square_sources_quarter_density`:
   Unconditional `110 ≤ |S₅₁|`, `438 + |Q₂₃| ≤ 4 * |S₅₁|`, `|S| ≤ 2 * |Q₁₃| + 1`,
   and `ω(N) ≤ 4 * |S₅₁| + 5`.
3. `sixth_power_dichotomy_on_S51_quarter_density`:
   Every odd perfect number with `|S₅₁| < 110 ∨ 4 * |S₅₁| + 6 ≤ ω(N)` must be divisible by a
   sixth power of a prime.
-/

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- Exact prime-support and prime-factor multiplicity identities on a sixth-power-free odd perfect
number, together with the slope consequence `N.primeFactors.card ≤ 3 * |Q₁₃| + |Q₂₃| + 2`. -/
theorem sixth_power_free_omega_and_total_identities {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    let S := squareSources N
    let S₅₁ := S.filter (· % 5 = 1)
    let S₅₀ := S.filter (· % 5 ≠ 1)
    let Q₁₃ := oneModThreeLargeSources N q
    let Q₂₃ := twoModThreeLargeSources N q
    N.primeFactors.card = 1 + S₅₁.card + S₅₀.card + Q₁₃.card + Q₂₃.card ∧
    cardFactors N = 1 + 2 * (S₅₁.card + S₅₀.card) + 4 * (Q₁₃.card + Q₂₃.card) ∧
    N.primeFactors.card ≤ 3 * Q₁₃.card + Q₂₃.card + 2 := by
  intro S S₅₁ S₅₀ Q₁₃ Q₂₃
  have h3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  have hq1 : N.factorization q = 1 := sixth_power_free_euler_exponent_one ho hN hq he hfree
  have hfour : ∀ r ∈ largeSources N q, N.factorization r = 4 :=
    (three_free_sixthPowerFree_forces_147_largeSources ho hN hq hq4 he hev h3 hfree).1
  have hparts : N.primeFactors = insert q (S ∪ largeSources N q) := by
    ext r
    simp only [Finset.mem_insert, Finset.mem_union, S, squareSources, largeSources, Finset.mem_filter]
    constructor
    · intro hr
      by_cases hrq : r = q
      · exact Or.inl hrq
      · right
        have hr_prime := Nat.prime_of_mem_primeFactors hr
        have hr3 : r ≠ 3 := fun h => h3 (h ▸ Nat.dvd_of_mem_primeFactors hr)
        have hr_pos : 0 < N.factorization r := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr)
        have hr_lt6 : ¬ 6 ≤ N.factorization r := fun hge =>
          hfree r hr_prime ((hr_prime.pow_dvd_iff_le_factorization hN.2.ne').2 hge)
        obtain ⟨k, hk⟩ := hev r hrq
        by_cases htwo : N.factorization r = 2
        · exact Or.inl ⟨hr, hr3, htwo⟩
        · exact Or.inr ⟨hr, hr3, hrq, by omega⟩
    · rintro (rfl | ⟨hr, _, _⟩ | ⟨hr, _, _, _⟩) <;> assumption
  have hq_notin : q ∉ S ∪ largeSources N q := by
    intro hmem
    rcases Finset.mem_union.mp hmem with hsq | hlg
    · have htwo := (Finset.mem_filter.mp hsq).2.2
      omega
    · exact (Finset.mem_filter.mp hlg).2.2.1 rfl
  have hdisj : Disjoint S (largeSources N q) := by
    apply Finset.disjoint_left.mpr
    intro r hs hl
    have htwo := (Finset.mem_filter.mp hs).2.2
    have hlarge := (Finset.mem_filter.mp hl).2.2.2
    omega
  have hS_parts : S = S₅₁ ∪ S₅₀ := by
    ext r
    simp only [S₅₁, S₅₀, Finset.mem_union, Finset.mem_filter]
    by_cases h : r % 5 = 1 <;> tauto
  have hS_disj : Disjoint S₅₁ S₅₀ := by
    apply Finset.disjoint_left.mpr
    intro r h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hS_card : S.card = S₅₁.card + S₅₀.card := by
    rw [hS_parts, Finset.card_union_of_disjoint hS_disj]
  have hQ_parts : largeSources N q = Q₁₃ ∪ Q₂₃ := by
    ext r
    simp only [Q₁₃, Q₂₃, oneModThreeLargeSources, twoModThreeLargeSources,
      Finset.mem_union, Finset.mem_filter]
    by_cases h : r % 3 = 1 <;> tauto
  have hQ_disj : Disjoint Q₁₃ Q₂₃ := by
    apply Finset.disjoint_left.mpr
    intro r h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hQ_card : (largeSources N q).card = Q₁₃.card + Q₂₃.card := by
    rw [hQ_parts, Finset.card_union_of_disjoint hQ_disj]
  have hω : N.primeFactors.card = 1 + S₅₁.card + S₅₀.card + Q₁₃.card + Q₂₃.card := by
    rw [hparts, Finset.card_insert_of_notMem hq_notin, Finset.card_union_of_disjoint hdisj,
      hS_card, hQ_card]
    omega
  have hΩ : cardFactors N = 1 + 2 * (S₅₁.card + S₅₀.card) + 4 * (Q₁₃.card + Q₂₃.card) := by
    have hcf : cardFactors N = ∑ r ∈ N.primeFactors, N.factorization r := by
      rw [cardFactors_eq_sum_factorization]
      rfl
    have hsum_S : (∑ r ∈ S, N.factorization r) = 2 * S.card := by
      calc
        (∑ r ∈ S, N.factorization r) = ∑ _r ∈ S, (2 : ℕ) :=
          Finset.sum_congr rfl fun r hr => (Finset.mem_filter.mp hr).2.2
        _ = 2 * S.card := by simp [Finset.sum_const, Nat.mul_comm]
    have hsum_L : (∑ r ∈ largeSources N q, N.factorization r) = 4 * (largeSources N q).card := by
      calc
        (∑ r ∈ largeSources N q, N.factorization r) = ∑ _r ∈ largeSources N q, (4 : ℕ) :=
          Finset.sum_congr rfl fun r hr => hfour r hr
        _ = 4 * (largeSources N q).card := by simp [Finset.sum_const, Nat.mul_comm]
    rw [hcf, hparts, Finset.sum_insert hq_notin, Finset.sum_union hdisj, hq1, hsum_S, hsum_L,
      hS_card, hQ_card]
    ring
  have hslope : 8 * N.primeFactors.card + 4 * Q₂₃.card ≤ 3 * cardFactors N + 7 := by
    have h : 8 * N.primeFactors.card + 4 * Q₂₃.card ≤ 3 * N.primeFactorsList.length + 7 :=
      (sharpened_cyclotomic_slope_three_free ho hN hq hq4 he hev h3).2
    have hlen : cardFactors N = N.primeFactorsList.length := cardFactors_apply
    omega
  refine ⟨hω, hΩ, by omega⟩

/-- Quarter-density lower bound on `S₅₁ := (squareSources N).filter (· % 5 = 1)` and upper bound on
`(squareSources N).card` for any sixth-power-free odd perfect number `N`. -/
theorem sixth_power_free_square_sources_quarter_density {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    110 ≤ ((squareSources N).filter (· % 5 = 1)).card ∧
    438 + (twoModThreeLargeSources N q).card ≤ 4 * ((squareSources N).filter (· % 5 = 1)).card ∧
    (squareSources N).card ≤ 2 * (oneModThreeLargeSources N q).card + 1 ∧
    N.primeFactors.card ≤ 4 * ((squareSources N).filter (· % 5 = 1)).card + 5 := by
  obtain ⟨hω_eq, _, hω_le⟩ :=
    sixth_power_free_omega_and_total_identities ho hN hq hq4 he hev hfree
  have hcap := sixth_power_free_sharpened_quartic_to_S51_bound ho hN hq hq4 he hev hfree
  have h443 : 443 ≤ N.primeFactors.card :=
    ((sixth_power_or_large_support ho hN).resolve_left fun ⟨p, hp, hpow⟩ => hfree p hp hpow).1
  have hS_parts :
      squareSources N =
        (squareSources N).filter (· % 5 = 1) ∪ (squareSources N).filter (· % 5 ≠ 1) := by
    ext r
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases h : r % 5 = 1 <;> tauto
  have hS_disj :
      Disjoint ((squareSources N).filter (· % 5 = 1)) ((squareSources N).filter (· % 5 ≠ 1)) := by
    apply Finset.disjoint_left.mpr
    intro r h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hS_card :
      (squareSources N).card =
        ((squareSources N).filter (· % 5 = 1)).card +
          ((squareSources N).filter (· % 5 ≠ 1)).card := by
    conv_lhs => rw [hS_parts]
    rw [Finset.card_union_of_disjoint hS_disj]
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- Every odd perfect number failing the quarter-density `S₅₁` lower bound must be divisible by a
sixth power of a prime. -/
theorem sixth_power_dichotomy_on_S51_quarter_density {N : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (h : ((squareSources N).filter (· % 5 = 1)).card < 110 ∨
      4 * ((squareSources N).filter (· % 5 = 1)).card + 6 ≤ N.primeFactors.card) :
    ∃ p : ℕ, p.Prime ∧ p ^ 6 ∣ N := by
  by_contra hno6
  have hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N := fun p hp hpow => hno6 ⟨p, hp, hpow⟩
  obtain ⟨q, hq, hq4, he, hev⟩ := euler_exponents ho hN
  obtain ⟨h110, _, _, hquarter⟩ :=
    sixth_power_free_square_sources_quarter_density ho hN hq hq4 he hev hfree
  omega

end OddPerfect
