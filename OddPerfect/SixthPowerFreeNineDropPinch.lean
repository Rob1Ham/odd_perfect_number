module

public import OddPerfect.GlobalWave11Obstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sixth-Power-Free Nine-Factor Drop Pinch (`OddPerfect.SixthPowerFreeNineDropPinch`)

Connects the sixth-power-free incoming-source vacuum (`OddPerfect.sixth_power_free_incoming_source_vacuum`)
and quartic divisor-sum mod-3 parity dichotomy (`OddPerfect.sixth_power_free_quartic_cardFactors_mod_three_dichotomy`)
to the nine-factor component-index drop obstruction (`OddPerfect.no_nine_factor_drop_profile`):

1. `sixth_power_free_euler_nine_drop_of_vacuum_excess`:
   Because `N.factorization q = 1` on any sixth-power-free odd perfect number,
   `cardFactors_componentIndex_add_eq` gives
   `cardFactors (componentIndex N q) + cardFactors (sigma 1 (ordProj[q] N)) = cardFactors N`.
   Hence `2 ≤ Q₂₃.card ∨ 4 ≤ S₅₀.card` forces `9 ≤ cardFactors (sigma 1 (ordProj[q] N))` and an
   explicit `+ 9` drop at the Euler prime `q`.
2. `sixth_power_free_euler_eleven_drop_of_vacuum_excess`:
   Under `(2 ≤ Q₂₃.card ∧ 1 ≤ S₅₀.card) ∨ 3 ≤ Q₂₃.card ∨ 5 ≤ S₅₀.card`, the vacuum lower bound
   reaches `11 ≤ cardFactors (sigma 1 (ordProj[q] N))`, forcing an explicit `+ 11` drop at `q`.
3. `sixth_power_free_no_nine_drop_pinch`:
   Under `∀ p ∈ N.primeFactors, cardFactors N < cardFactors (componentIndex N p) + 9`,
   mod-2 parity preserves the exact tight vacuum and support bounds:
   - `Q₂₃.card ≤ 1 ∧ S₅₀.card ≤ 3 ∧ 2 * S₅₀.card + 4 * Q₂₃.card ≤ 6`
   - `147 ≤ Q₁₃.card ∧ 439 ≤ S₅₁.card + Q₁₃.card`
   - `∀ u ∈ Q₂₃, cardFactors (sigma 1 (u ^ 4)) = 2 ∨ cardFactors (sigma 1 (u ^ 4)) = 4`
   - `∀ u ∈ Q₁₃, ¬ q ∣ sigma 1 (u ^ 4) → cardFactors (sigma 1 (u ^ 4)) ∈ {1, 3, 5}`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private theorem sixth_power_free_euler_drop_of_vacuum_bound {N q k : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N)
    (hvac_lb : k ≤ 2 * ((squareSources N).filter (· % 5 ≠ 1)).card +
      4 * (twoModThreeLargeSources N q).card) :
    cardFactors (componentIndex N q) + (k + 1) ≤ cardFactors N := by
  have hq1 : N.factorization q = 1 :=
    sixth_power_free_euler_exponent_one ho hN hq he hfree
  obtain ⟨_, _, hvac_card, _⟩ :=
    sixth_power_free_incoming_source_vacuum ho hN hq hq4 he hev hfree
  change 1 + 2 * ((squareSources N).filter (· % 5 ≠ 1)).card +
    4 * (twoModThreeLargeSources N q).card ≤ cardFactors (sigma 1 (ordProj[q] N)) at hvac_card
  have hbal := cardFactors_componentIndex_add_eq hN hq
  omega

/-- **Euler Nine-Factor Drop from Incoming-Source Vacuum Excess**:
on any sixth-power-free odd perfect number `N`, if `2 ≤ Q₂₃.card ∨ 4 ≤ S₅₀.card`, then the
Euler prime `q` itself incurs an explicit nine-factor component-index drop:
`cardFactors (componentIndex N q) + 9 ≤ cardFactors N`. -/
theorem sixth_power_free_euler_nine_drop_of_vacuum_excess {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N)
    (hex : 2 ≤ (twoModThreeLargeSources N q).card ∨
      4 ≤ ((squareSources N).filter (· % 5 ≠ 1)).card) :
    cardFactors (componentIndex N q) + 9 ≤ cardFactors N := by
  apply sixth_power_free_euler_drop_of_vacuum_bound (k := 8) ho hN hq hq4 he hev hfree
  omega

/-- **Euler Eleven-Factor Drop from Strong Incoming-Source Vacuum Excess**:
on any sixth-power-free odd perfect number `N`, if
`(2 ≤ Q₂₃.card ∧ 1 ≤ S₅₀.card) ∨ 3 ≤ Q₂₃.card ∨ 5 ≤ S₅₀.card`, then the Euler prime `q`
incurs an explicit eleven-factor component-index drop:
`cardFactors (componentIndex N q) + 11 ≤ cardFactors N`. -/
theorem sixth_power_free_euler_eleven_drop_of_vacuum_excess {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N)
    (hex : (2 ≤ (twoModThreeLargeSources N q).card ∧
        1 ≤ ((squareSources N).filter (· % 5 ≠ 1)).card) ∨
      3 ≤ (twoModThreeLargeSources N q).card ∨
      5 ≤ ((squareSources N).filter (· % 5 ≠ 1)).card) :
    cardFactors (componentIndex N q) + 11 ≤ cardFactors N := by
  apply sixth_power_free_euler_drop_of_vacuum_bound (k := 10) ho hN hq hq4 he hev hfree
  omega

/-- **Sixth-Power-Free No-Nine-Drop Pinch**: on a sixth-power-free odd perfect number `N`
lacking a nine-factor component-index drop, mod-2 parity preserves the tight incoming-vacuum
and support bounds while pinning `Q₂₃` and `Q₁₃` quartic prime-factor multiplicities:
1. `Q₂₃.card ≤ 1 ∧ S₅₀.card ≤ 3 ∧ 2 * S₅₀.card + 4 * Q₂₃.card ≤ 6`
2. `147 ≤ Q₁₃.card ∧ 439 ≤ S₅₁.card + Q₁₃.card`
3. `∀ u ∈ Q₂₃, cardFactors (sigma 1 (u ^ 4)) = 2 ∨ cardFactors (sigma 1 (u ^ 4)) = 4`
4. `∀ u ∈ Q₁₃, ¬ q ∣ sigma 1 (u ^ 4) → cardFactors (sigma 1 (u ^ 4)) = 1 ∨ cardFactors (sigma 1 (u ^ 4)) = 3 ∨ cardFactors (sigma 1 (u ^ 4)) = 5`. -/
theorem sixth_power_free_no_nine_drop_pinch {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N)
    (hno9 : ∀ p ∈ N.primeFactors, cardFactors N < cardFactors (componentIndex N p) + 9) :
    let S := squareSources N
    let S₅₁ := S.filter (· % 5 = 1)
    let S₅₀ := S.filter (· % 5 ≠ 1)
    let Q₁₃ := oneModThreeLargeSources N q
    let Q₂₃ := twoModThreeLargeSources N q
    (Q₂₃.card ≤ 1 ∧ S₅₀.card ≤ 3 ∧ 2 * S₅₀.card + 4 * Q₂₃.card ≤ 6) ∧
    (147 ≤ Q₁₃.card ∧ 439 ≤ S₅₁.card + Q₁₃.card) ∧
    (∀ u ∈ Q₂₃,
      cardFactors (sigma 1 (u ^ 4)) = 2 ∨ cardFactors (sigma 1 (u ^ 4)) = 4) ∧
    (∀ u ∈ Q₁₃, ¬ q ∣ sigma 1 (u ^ 4) →
      cardFactors (sigma 1 (u ^ 4)) = 1 ∨
      cardFactors (sigma 1 (u ^ 4)) = 3 ∨
      cardFactors (sigma 1 (u ^ 4)) = 5) := by
  intro S S₅₁ S₅₀ Q₁₃ Q₂₃
  have h3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  have hfour : ∀ r ∈ largeSources N q, N.factorization r = 4 :=
    (three_free_sixthPowerFree_forces_147_largeSources ho hN hq hq4 he hev h3 hfree).1
  obtain ⟨hcap, hq1, _, _, _⟩ :=
    no_nine_factor_drop_profile ho hN hq hq4 he hev hno9
  obtain ⟨_, _, hvac_card, _⟩ :=
    sixth_power_free_incoming_source_vacuum ho hN hq hq4 he hev hfree
  change 1 + 2 * S₅₀.card + 4 * Q₂₃.card ≤ cardFactors (sigma 1 (ordProj[q] N)) at hvac_card
  have hq_cap : N.factorization q + cardFactors (sigma 1 (ordProj[q] N)) ≤ 9 := hcap q hq
  have hvac_le : 2 * S₅₀.card + 4 * Q₂₃.card ≤ 6 := by omega
  have hQ23_le1 : Q₂₃.card ≤ 1 := by omega
  have hS50_le3 : S₅₀.card ≤ 3 := by omega
  obtain ⟨hω_eq, _, hω_le⟩ :=
    sixth_power_free_omega_and_total_identities ho hN hq hq4 he hev hfree
  change N.primeFactors.card = 1 + S₅₁.card + S₅₀.card + Q₁₃.card + Q₂₃.card at hω_eq
  change N.primeFactors.card ≤ 3 * Q₁₃.card + Q₂₃.card + 2 at hω_le
  have h443 : 443 ≤ N.primeFactors.card :=
    ((sixth_power_or_large_support ho hN).resolve_left fun ⟨p, hp, hpow⟩ => hfree p hp hpow).1
  have hQ13_lb : 147 ≤ Q₁₃.card := by omega
  have hsum_lb : 439 ≤ S₅₁.card + Q₁₃.card := by omega
  obtain ⟨hQ13_dich, hQ23_dich⟩ :=
    sixth_power_free_quartic_cardFactors_mod_three_dichotomy ho hN hq hq4 he hev hfree
  have h24 : ∀ u ∈ Q₂₃,
      cardFactors (sigma 1 (u ^ 4)) = 2 ∨ cardFactors (sigma 1 (u ^ 4)) = 4 := by
    intro u hu
    have hu_lg := (Finset.mem_filter.mp hu).1
    have hu_mem := (Finset.mem_filter.mp hu_lg).1
    have hu_exp := hfour u hu_lg
    have hu_cap : N.factorization u + cardFactors (sigma 1 (ordProj[u] N)) ≤ 9 := hcap u hu_mem
    rw [hu_exp] at hu_cap
    obtain ⟨_, _, heven, _, h2_le⟩ := hQ23_dich u hu
    obtain ⟨k, hk⟩ := heven
    omega
  have h135 : ∀ u ∈ Q₁₃, ¬ q ∣ sigma 1 (u ^ 4) →
      cardFactors (sigma 1 (u ^ 4)) = 1 ∨
      cardFactors (sigma 1 (u ^ 4)) = 3 ∨
      cardFactors (sigma 1 (u ^ 4)) = 5 := by
    intro u hu hnq
    have hu_lg := (Finset.mem_filter.mp hu).1
    have hu_mem := (Finset.mem_filter.mp hu_lg).1
    have hu_exp := hfour u hu_lg
    have hu_cap : N.factorization u + cardFactors (sigma 1 (ordProj[u] N)) ≤ 9 := hcap u hu_mem
    rw [hu_exp] at hu_cap
    obtain ⟨_, hodd, _⟩ := hQ13_dich u hu hnq
    have hodd_val := Nat.odd_iff.mp hodd
    omega
  exact ⟨⟨hQ23_le1, hS50_le3, hvac_le⟩, ⟨hQ13_lb, hsum_lb⟩, h24, h135⟩

end OddPerfect
