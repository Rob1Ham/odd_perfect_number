module

public import OddPerfect.SixthPowerFreeQ13CompCollisionPinch
public import OddPerfect.SixthPowerFreeQuarterDensity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sixth-Power-Free Pure Collision Rank Cap (`OddPerfect.SixthPowerFreePureCollisionRankCap`)

Combines the `Q₁₃` composite-free/repeat fiber bound
`Q₁₃.card + 2 * Q₁₃_comp_free.card + 2 * Q₂₃.card ≤ 2 * S₅₁_col.card + 1`
(`sixth_power_free_Q13_comp_free_and_rep_bounds`) with the square-source density bound
`S.card ≤ 2 * Q₁₃.card + 1` (`sixth_power_free_square_sources_quarter_density`), the support slope
`N.primeFactors.card ≤ 3 * Q₁₃.card + Q₂₃.card + 2`
(`sixth_power_free_omega_and_total_identities`), and the sixth-power-free support bound
`443 ≤ N.primeFactors.card` (`sixth_power_or_large_support`) to eliminate `Q₁₃.card` completely and
isolate pure `S₅₁_col.card` caps:

1. `sixth_power_free_pure_collision_repeat_and_rank_bounds`:
   `S₅₀.card + S₅₁_rep.card + 4 * Q₁₃_comp_free.card + 4 * Q₂₃.card ≤ 3 * S₅₁_col.card + 3`,
   `S.card + 4 * Q₁₃_comp_free.card + 4 * Q₂₃.card ≤ 4 * S₅₁_col.card + 3`,
   `N.primeFactors.card + 6 * Q₁₃_comp_free.card + 5 * Q₂₃.card ≤ 6 * S₅₁_col.card + 5`,
   `438 + 6 * Q₁₃_comp_free.card + 5 * Q₂₃.card ≤ 6 * S₅₁_col.card`,
   `73 + Q₁₃_comp_free.card ≤ S₅₁_col.card`, and
   `Q₁₃_comp_free.Nonempty ∨ Q₂₃.Nonempty → 74 ≤ S₅₁_col.card`.
2. `sixth_power_dichotomy_on_pure_S51_col_cap`:
   Global unconditional dichotomy showing that for the Euler prime `q`, any odd perfect number
   satisfying `S₅₁_col.card < 73 ∨ 6 * S₅₁_col.card + 6 ≤ N.primeFactors.card` must be divisible
   by a sixth power of a prime.
-/

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- Pure `S₅₁_col`-cap repeat, square-source, and prime-support bounds for any sixth-power-free
odd perfect number. -/
theorem sixth_power_free_pure_collision_repeat_and_rank_bounds {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    let S := squareSources N
    let S₅₀ := S.filter (· % 5 ≠ 1)
    let S₅₁ := S.filter (· % 5 = 1)
    let S₅₁_col := S₅₁.filter (fun r => indegAt N q r = 2)
    let S₅₁_rep := S₅₁.filter (fun r => indegAt N q r = 1)
    let S₅₁_rep_q := S₅₁_rep.filter (fun r => r ∣ (q + 1) / 2)
    let S₅₁_rep_src := S₅₁_rep.filter (fun r => ¬ r ∣ (q + 1) / 2)
    let Q₁₃ := oneModThreeLargeSources N q
    let Q₂₃ := twoModThreeLargeSources N q
    let repFib := fun u => S₅₁_rep_src.filter (fun r => r ∣ sigma 1 (u ^ 4))
    let Q₁₃_comp := Q₁₃.filter (fun u => ¬ q ∣ sigma 1 (u ^ 4) ∧ ¬ (sigma 1 (u ^ 4)).Prime)
    let Q₁₃_comp_free := Q₁₃_comp.filter (fun u => repFib u = ∅)
    S₅₀.card + S₅₁_rep.card + 4 * Q₁₃_comp_free.card + 4 * Q₂₃.card ≤ 3 * S₅₁_col.card + 3 ∧
    S₅₀.card + S₅₁_rep_q.card + S₅₁_rep_src.card + 4 * Q₁₃_comp_free.card + 4 * Q₂₃.card ≤
      3 * S₅₁_col.card + 3 ∧
    S.card + 4 * Q₁₃_comp_free.card + 4 * Q₂₃.card ≤ 4 * S₅₁_col.card + 3 ∧
    N.primeFactors.card + 6 * Q₁₃_comp_free.card + 5 * Q₂₃.card ≤ 6 * S₅₁_col.card + 5 ∧
    N.primeFactors.card ≤ 6 * S₅₁_col.card + 5 ∧
    438 + 6 * Q₁₃_comp_free.card + 5 * Q₂₃.card ≤ 6 * S₅₁_col.card ∧
    73 + Q₁₃_comp_free.card ≤ S₅₁_col.card ∧
    (Q₁₃_comp_free.Nonempty ∨ Q₂₃.Nonempty → 74 ≤ S₅₁_col.card) := by
  intro S S₅₀ S₅₁ S₅₁_col S₅₁_rep S₅₁_rep_q S₅₁_rep_src Q₁₃ Q₂₃ repFib Q₁₃_comp Q₁₃_comp_free
  obtain ⟨_, _, hω_le⟩ :=
    sixth_power_free_omega_and_total_identities ho hN hq hq4 he hev hfree
  change N.primeFactors.card ≤ 3 * Q₁₃.card + Q₂₃.card + 2 at hω_le
  have hS_le : S.card ≤ 2 * Q₁₃.card + 1 :=
    (sixth_power_free_square_sources_quarter_density ho hN hq hq4 he hev hfree).2.2.1
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
  have hS51_split : S₅₁.card = S₅₁_col.card + S₅₁_rep.card :=
    (sixth_power_free_S51_collision_repeat_split ho hN hq hq4 he hev hfree).2.2.1
  have hrep_split : S₅₁_rep.card = S₅₁_rep_q.card + S₅₁_rep_src.card :=
    (sixth_power_free_S51_rep_source_partition ho hN hq hq4 he hev hfree).2.2.1
  have hcap : Q₁₃.card + 2 * Q₁₃_comp_free.card + 2 * Q₂₃.card ≤ 2 * S₅₁_col.card + 1 :=
    (sixth_power_free_Q13_comp_free_and_rep_bounds ho hN hq hq4 he hev hfree).2.2.2.2.1
  have h443 : 443 ≤ N.primeFactors.card :=
    ((sixth_power_or_large_support ho hN).resolve_left fun ⟨p, hp, hpow⟩ => hfree p hp hpow).1
  have h1 : S₅₀.card + S₅₁_rep.card + 4 * Q₁₃_comp_free.card + 4 * Q₂₃.card ≤
      3 * S₅₁_col.card + 3 := by
    omega
  have h2 : S₅₀.card + S₅₁_rep_q.card + S₅₁_rep_src.card + 4 * Q₁₃_comp_free.card + 4 * Q₂₃.card ≤
      3 * S₅₁_col.card + 3 := by
    omega
  have h3 : S.card + 4 * Q₁₃_comp_free.card + 4 * Q₂₃.card ≤ 4 * S₅₁_col.card + 3 := by
    omega
  have h4 : N.primeFactors.card + 6 * Q₁₃_comp_free.card + 5 * Q₂₃.card ≤
      6 * S₅₁_col.card + 5 := by
    omega
  have h5 : N.primeFactors.card ≤ 6 * S₅₁_col.card + 5 := by
    omega
  have h6 : 438 + 6 * Q₁₃_comp_free.card + 5 * Q₂₃.card ≤ 6 * S₅₁_col.card := by
    omega
  have h7 : 73 + Q₁₃_comp_free.card ≤ S₅₁_col.card := by
    omega
  have h8 : Q₁₃_comp_free.Nonempty ∨ Q₂₃.Nonempty → 74 ≤ S₅₁_col.card := by
    rintro (hne | hne)
    · have hpos : 1 ≤ Q₁₃_comp_free.card := Finset.card_pos.mpr hne
      omega
    · have hpos : 1 ≤ Q₂₃.card := Finset.card_pos.mpr hne
      omega
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- Global unconditional dichotomy: for the Euler prime `q`, any odd perfect number satisfying
`S₅₁_col.card < 73 ∨ 6 * S₅₁_col.card + 6 ≤ N.primeFactors.card` must be divisible by a sixth
power of a prime. -/
theorem sixth_power_dichotomy_on_pure_S51_col_cap {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) :
    ∃ q ∈ N.primeFactors,
      q % 4 = 1 ∧ N.factorization q % 4 = 1 ∧
      (let S₅₁ := (squareSources N).filter (· % 5 = 1)
       let S₅₁_col := S₅₁.filter (fun r => indegAt N q r = 2)
       (S₅₁_col.card < 73 ∨ 6 * S₅₁_col.card + 6 ≤ N.primeFactors.card) →
         ∃ p : ℕ, p.Prime ∧ p ^ 6 ∣ N) := by
  obtain ⟨q, hq, hq4, he, hev⟩ := euler_exponents ho hN
  refine ⟨q, hq, hq4, he, ?_⟩
  dsimp only
  intro h
  by_contra hno6
  have hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N := fun p hp hpow => hno6 ⟨p, hp, hpow⟩
  obtain ⟨_, _, _, _, hrank, _, h73, _⟩ :=
    sixth_power_free_pure_collision_repeat_and_rank_bounds ho hN hq hq4 he hev hfree
  omega

end OddPerfect
