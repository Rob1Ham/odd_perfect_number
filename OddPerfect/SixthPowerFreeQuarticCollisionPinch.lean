module

public import OddPerfect.SixthPowerFreeDropExcessPinch
public import OddPerfect.SixthPowerFreeQuarterDensity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sixth-Power-Free Quartic-Collision Pinch (`OddPerfect.SixthPowerFreeQuarticCollisionPinch`)

Formalizes:
1. `sixth_power_free_S51_collision_repeat_split`: Exact `S₅₁` collision vs. square-repeat
   split (`S₅₁_col` vs. `S₅₁_rep`), exact conservation formulas for both `collisionExcess N q`
   and `localRepeatExcess N q`, and `221 ≤ S₅₁_col.card + 3 * Q₁₃.card`.
2. `sixth_power_free_oneModThreeLarge_ge_80`: Unconditional bounds
   `2 * |Q₂₃| ≤ 5 * |Q₁₃| + 7`, `2 * ω(N) ≤ 11 * |Q₁₃| + 11`, and `80 ≤ |Q₁₃|`.
3. `sixth_power_free_half_rank_bipartite_pinch`: Half-rank bipartite excess pinch
   `ω(N) ≤ 2 * S₅₁_col.card + 6 * Q₁₃.card + 2` and
   `S₅₀.card + S₅₁_rep.card + Q₂₃.card ≤ S₅₁_col.card + 5 * Q₁₃.card + 1`.
-/

public section

namespace OddPerfect

open ArithmeticFunction Finset

private theorem sixth_power_free_partition_invariants_local {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    ¬ 3 ∣ N ∧
    N.factorization q = 1 ∧
    (∀ s ∈ squareSources N, N.factorization s = 2) ∧
    (∀ u ∈ largeSources N q, N.factorization u = 4) ∧
    N.primeFactors = insert q (squareSources N ∪ largeSources N q) ∧
    q ∉ squareSources N ∪ largeSources N q ∧
    Disjoint (squareSources N) (largeSources N q) := by
  have h3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  have hq1 : N.factorization q = 1 := sixth_power_free_euler_exponent_one ho hN hq he hfree
  have hsq2 : ∀ s ∈ squareSources N, N.factorization s = 2 := fun s hs =>
    (Finset.mem_filter.mp hs).2.2
  have hlg4 : ∀ u ∈ largeSources N q, N.factorization u = 4 :=
    (three_free_sixthPowerFree_forces_147_largeSources ho hN hq hq4 he hev h3 hfree).1
  have hparts : N.primeFactors = insert q (squareSources N ∪ largeSources N q) := by
    ext r
    simp only [Finset.mem_insert, Finset.mem_union, squareSources, largeSources, Finset.mem_filter]
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
  have hq_notin : q ∉ squareSources N ∪ largeSources N q := by
    intro hmem
    rcases Finset.mem_union.mp hmem with hsq | hlg
    · have := (Finset.mem_filter.mp hsq).2.2
      omega
    · exact (Finset.mem_filter.mp hlg).2.2.1 rfl
  have hdisj : Disjoint (squareSources N) (largeSources N q) := by
    apply Finset.disjoint_left.mpr
    intro r hs hl
    have htwo := (Finset.mem_filter.mp hs).2.2
    have hlarge := (Finset.mem_filter.mp hl).2.2.2
    omega
  exact ⟨h3, hq1, hsq2, hlg4, hparts, hq_notin, hdisj⟩

/-- **1. Sixth-Power-Free `S₅₁` Collision/Repeat Split**:
Splits `S₅₁ := (squareSources N).filter (· % 5 = 1)` into `S₅₁_col` (`indegAt = 2`) and
`S₅₁_rep` (`indegAt = 1`), gives exact formulas for `collisionExcess N q` and
`localRepeatExcess N q`, and proves `221 ≤ S₅₁_col.card + 3 * Q₁₃.card`. -/
theorem sixth_power_free_S51_collision_repeat_split {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1)
    (he : N.factorization q % 4 = 1) (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    let S₅₀ := (squareSources N).filter (· % 5 ≠ 1)
    let S₅₁ := (squareSources N).filter (· % 5 = 1)
    let S₅₁_col := S₅₁.filter (fun r => indegAt N q r = 2)
    let S₅₁_rep := S₅₁.filter (fun r => indegAt N q r = 1)
    let Q₁₃ := oneModThreeLargeSources N q
    let Q₂₃ := twoModThreeLargeSources N q
    S₅₁ = S₅₁_col ∪ S₅₁_rep ∧
    Disjoint S₅₁_col S₅₁_rep ∧
    S₅₁.card = S₅₁_col.card + S₅₁_rep.card ∧
    collisionExcess N q = S₅₁_col.card + ∑ r ∈ Q₁₃, (indegAt N q r - 1) ∧
    localRepeatExcess N q =
      S₅₀.card + S₅₁_rep.card + 3 * Q₂₃.card + ∑ r ∈ Q₁₃, localRepeatAt N q r ∧
    221 ≤ S₅₁_col.card + 3 * Q₁₃.card := by
  intro S₅₀ S₅₁ S₅₁_col S₅₁_rep Q₁₃ Q₂₃
  obtain ⟨_, _, hsq2, hlg4, hparts, hq_notin, hdisj⟩ :=
    sixth_power_free_partition_invariants_local ho hN hq hq4 he hev hfree
  obtain ⟨hcons, hsum_loc, _⟩ :=
    factorization_eq_indegAt_add_localRepeatAt ho hN hq hq4 he hev
  have hmut2 := (euler_linear_and_exponent_two_mutual_exclusion ho hN hq hq4 he hev).2
  obtain ⟨hq_vac, hS50_vac, hQ23_vac⟩ :=
    sixth_power_free_vacuum_indegAt_and_localRepeatAt ho hN hq hq4 he hev hfree
  obtain ⟨_, _, hcol_eq, h221, _, _⟩ :=
    sixth_power_free_excess_and_drop_partition ho hN hq hq4 he hev hfree
  have hS51_dich : ∀ r ∈ S₅₁,
      (indegAt N q r = 2 ∧ localRepeatAt N q r = 0) ∨
      (indegAt N q r = 1 ∧ localRepeatAt N q r = 1) := by
    intro r hr
    have hr_sq : r ∈ squareSources N := (Finset.mem_filter.mp hr).1
    have hr_mem : r ∈ N.primeFactors := (Finset.mem_filter.mp hr_sq).1
    have hr2 : N.factorization r = 2 := hsq2 r hr_sq
    rcases hmut2 r hr_mem hr2 with ⟨hi2, hl0, _⟩ | ⟨hi1, hl1, _⟩
    · exact Or.inl ⟨hi2, hl0⟩
    · exact Or.inr ⟨hi1, hl1⟩
  have hS51_parts : S₅₁ = S₅₁_col ∪ S₅₁_rep := by
    ext r
    simp only [S₅₁_col, S₅₁_rep, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hr
      rcases hS51_dich r hr with ⟨hi2, _⟩ | ⟨hi1, _⟩
      · exact Or.inl ⟨hr, hi2⟩
      · exact Or.inr ⟨hr, hi1⟩
    · rintro (⟨hr, _⟩ | ⟨hr, _⟩) <;> exact hr
  have hS51_disj : Disjoint S₅₁_col S₅₁_rep := by
    apply Finset.disjoint_left.mpr
    intro r h1 h2
    have hi2 := (Finset.mem_filter.mp h1).2
    have hi1 := (Finset.mem_filter.mp h2).2
    omega
  have hS51_card : S₅₁.card = S₅₁_col.card + S₅₁_rep.card := by
    conv_lhs => rw [hS51_parts]
    exact Finset.card_union_of_disjoint hS51_disj
  have hS_parts : squareSources N = S₅₀ ∪ S₅₁ := by
    ext r
    simp only [S₅₀, S₅₁, Finset.mem_union, Finset.mem_filter]
    by_cases h : r % 5 = 1 <;> tauto
  have hS_disj : Disjoint S₅₀ S₅₁ := by
    apply Finset.disjoint_left.mpr
    intro r h1 h2
    exact (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
  have hQ_parts : largeSources N q = Q₂₃ ∪ Q₁₃ := by
    ext r
    simp only [Q₂₃, Q₁₃, twoModThreeLargeSources, oneModThreeLargeSources,
      Finset.mem_union, Finset.mem_filter]
    by_cases h : r % 3 = 1 <;> tauto
  have hQ_disj : Disjoint Q₂₃ Q₁₃ := by
    apply Finset.disjoint_left.mpr
    intro r h1 h2
    exact (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
  have hS51_Q13_disj : Disjoint S₅₁ Q₁₃ :=
    hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hcol_split : collisionExcess N q = S₅₁_col.card + ∑ r ∈ Q₁₃, (indegAt N q r - 1) := by
    change collisionExcess N q = ∑ r ∈ S₅₁ ∪ Q₁₃, (indegAt N q r - 1) at hcol_eq
    rw [hcol_eq, Finset.sum_union hS51_Q13_disj]
    have hsum_S51 : (∑ r ∈ S₅₁, (indegAt N q r - 1)) = S₅₁_col.card := by
      conv_lhs => rw [hS51_parts]
      rw [Finset.sum_union hS51_disj]
      have hcol : (∑ r ∈ S₅₁_col, (indegAt N q r - 1)) = S₅₁_col.card := by
        calc
          ∑ r ∈ S₅₁_col, (indegAt N q r - 1)
              = ∑ _r ∈ S₅₁_col, 1 := by
                refine Finset.sum_congr rfl fun r hr => ?_
                have hi2 := (Finset.mem_filter.mp hr).2
                omega
          _ = S₅₁_col.card := by simp [Finset.sum_const]
      have hrep : (∑ r ∈ S₅₁_rep, (indegAt N q r - 1)) = 0 := by
        refine Finset.sum_eq_zero fun r hr => ?_
        have hi1 := (Finset.mem_filter.mp hr).2
        omega
      omega
    omega
  have hloc_split :
      localRepeatExcess N q =
        S₅₀.card + S₅₁_rep.card + 3 * Q₂₃.card + ∑ r ∈ Q₁₃, localRepeatAt N q r := by
    rw [← hsum_loc, hparts, Finset.sum_insert hq_notin, Finset.sum_union hdisj,
      hS_parts, Finset.sum_union hS_disj, hS51_parts, Finset.sum_union hS51_disj,
      hQ_parts, Finset.sum_union hQ_disj]
    have hsum_S50 : (∑ r ∈ S₅₀, localRepeatAt N q r) = S₅₀.card := by
      calc
        ∑ r ∈ S₅₀, localRepeatAt N q r
            = ∑ _r ∈ S₅₀, 1 := Finset.sum_congr rfl fun r hr => (hS50_vac r hr).2
        _ = S₅₀.card := by simp [Finset.sum_const]
    have hsum_S51_col : (∑ r ∈ S₅₁_col, localRepeatAt N q r) = 0 := by
      refine Finset.sum_eq_zero fun r hr => ?_
      obtain ⟨hr_S51, hi2⟩ := Finset.mem_filter.mp hr
      rcases hS51_dich r hr_S51 with ⟨_, hl0⟩ | ⟨hi1, _⟩
      · exact hl0
      · omega
    have hsum_S51_rep : (∑ r ∈ S₅₁_rep, localRepeatAt N q r) = S₅₁_rep.card := by
      calc
        ∑ r ∈ S₅₁_rep, localRepeatAt N q r
            = ∑ _r ∈ S₅₁_rep, 1 := by
              refine Finset.sum_congr rfl fun r hr => ?_
              obtain ⟨hr_S51, hi1⟩ := Finset.mem_filter.mp hr
              rcases hS51_dich r hr_S51 with ⟨hi2, _⟩ | ⟨_, hl1⟩
              · omega
              · exact hl1
        _ = S₅₁_rep.card := by simp [Finset.sum_const]
    have hsum_Q23 : (∑ r ∈ Q₂₃, localRepeatAt N q r) = 3 * Q₂₃.card := by
      calc
        ∑ r ∈ Q₂₃, localRepeatAt N q r
            = ∑ _r ∈ Q₂₃, 3 := Finset.sum_congr rfl fun r hr => (hQ23_vac r hr).2
        _ = 3 * Q₂₃.card := by simp [Finset.sum_const, Nat.mul_comm]
    rw [hq_vac.2, hsum_S50, hsum_S51_col, hsum_S51_rep, hsum_Q23]
    omega
  have hQ13_le : (∑ r ∈ Q₁₃, (indegAt N q r - 1)) ≤ 3 * Q₁₃.card := by
    calc
      ∑ r ∈ Q₁₃, (indegAt N q r - 1)
          ≤ ∑ _r ∈ Q₁₃, 3 := by
            refine Finset.sum_le_sum fun r hr => ?_
            have hr_lg : r ∈ largeSources N q := (Finset.mem_filter.mp hr).1
            have hr_mem : r ∈ N.primeFactors := (Finset.mem_filter.mp hr_lg).1
            have hle := (hcons r hr_mem).2.2
            have hexp := hlg4 r hr_lg
            omega
      _ = 3 * Q₁₃.card := by simp [Finset.sum_const, Nat.mul_comm]
  have h221_split : 221 ≤ S₅₁_col.card + 3 * Q₁₃.card := by omega
  exact ⟨hS51_parts, hS51_disj, hS51_card, hcol_split, hloc_split, h221_split⟩

/-- **2. Unconditional `|Q₁₃| ≥ 80` Floor**:
Combines `sixth_power_free_sharpened_quartic_to_S51_bound`,
`sixth_power_free_square_sources_quarter_density`, `sixth_power_free_omega_and_total_identities`,
and `443 ≤ N.primeFactors.card` to prove `2 * |Q₂₃| ≤ 5 * |Q₁₃| + 7`,
`2 * ω(N) ≤ 11 * |Q₁₃| + 11`, and `80 ≤ |Q₁₃|`. -/
theorem sixth_power_free_oneModThreeLarge_ge_80 {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1)
    (he : N.factorization q % 4 = 1) (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    2 * (twoModThreeLargeSources N q).card ≤ 5 * (oneModThreeLargeSources N q).card + 7 ∧
    2 * N.primeFactors.card ≤ 11 * (oneModThreeLargeSources N q).card + 11 ∧
    80 ≤ (oneModThreeLargeSources N q).card := by
  have hcap := sixth_power_free_sharpened_quartic_to_S51_bound ho hN hq hq4 he hev hfree
  have hsq_le :=
    (sixth_power_free_square_sources_quarter_density ho hN hq hq4 he hev hfree).2.2.1
  have hS51_le : ((squareSources N).filter (· % 5 = 1)).card ≤ (squareSources N).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hQ23_bound :
      2 * (twoModThreeLargeSources N q).card ≤ 5 * (oneModThreeLargeSources N q).card + 7 := by
    omega
  obtain ⟨hω_eq, _, _⟩ :=
    sixth_power_free_omega_and_total_identities ho hN hq hq4 he hev hfree
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
    exact Finset.card_union_of_disjoint hS_disj
  have hω_bound : 2 * N.primeFactors.card ≤ 11 * (oneModThreeLargeSources N q).card + 11 := by
    omega
  have h443 : 443 ≤ N.primeFactors.card :=
    (sixth_power_free_collision_excess_ge_221 ho hN hq hq4 he hev hfree).1
  have h80 : 80 ≤ (oneModThreeLargeSources N q).card := by omega
  exact ⟨hQ23_bound, hω_bound, h80⟩

/-- **3. Half-Rank Bipartite Excess Pinch**:
Couples `odd_perfect_half_rank_collision_excess_bound` (for `¬ 3 ∣ N`) with
`sixth_power_free_S51_collision_repeat_split` to prove
`ω(N) ≤ 2 * S₅₁_col.card + 6 * Q₁₃.card + 2` and
`S₅₀.card + S₅₁_rep.card + Q₂₃.card ≤ S₅₁_col.card + 5 * Q₁₃.card + 1`. -/
theorem sixth_power_free_half_rank_bipartite_pinch {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1)
    (he : N.factorization q % 4 = 1) (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    let S₅₀ := (squareSources N).filter (· % 5 ≠ 1)
    let S₅₁ := (squareSources N).filter (· % 5 = 1)
    let S₅₁_col := S₅₁.filter (fun r => indegAt N q r = 2)
    let S₅₁_rep := S₅₁.filter (fun r => indegAt N q r = 1)
    let Q₁₃ := oneModThreeLargeSources N q
    let Q₂₃ := twoModThreeLargeSources N q
    N.primeFactors.card ≤ 2 * S₅₁_col.card + 6 * Q₁₃.card + 2 ∧
    S₅₀.card + S₅₁_rep.card + Q₂₃.card ≤ S₅₁_col.card + 5 * Q₁₃.card + 1 := by
  intro S₅₀ S₅₁ S₅₁_col S₅₁_rep Q₁₃ Q₂₃
  have h3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  have hhalf : N.primeFactors.card ≤ 2 * collisionExcess N q + 2 :=
    (odd_perfect_half_rank_collision_excess_bound ho hN hq hq4 he hev).2.2 h3
  obtain ⟨_, _, hS51_card, hcol_split, _, _⟩ :=
    sixth_power_free_S51_collision_repeat_split ho hN hq hq4 he hev hfree
  change S₅₁.card = S₅₁_col.card + S₅₁_rep.card at hS51_card
  change collisionExcess N q = S₅₁_col.card + ∑ r ∈ Q₁₃, (indegAt N q r - 1) at hcol_split
  obtain ⟨_, _, _, hlg4, _, _, _⟩ :=
    sixth_power_free_partition_invariants_local ho hN hq hq4 he hev hfree
  have hcons := (factorization_eq_indegAt_add_localRepeatAt ho hN hq hq4 he hev).1
  have hQ13_le : (∑ r ∈ Q₁₃, (indegAt N q r - 1)) ≤ 3 * Q₁₃.card := by
    calc
      ∑ r ∈ Q₁₃, (indegAt N q r - 1)
          ≤ ∑ _r ∈ Q₁₃, 3 := by
            refine Finset.sum_le_sum fun r hr => ?_
            have hr_lg : r ∈ largeSources N q := (Finset.mem_filter.mp hr).1
            have hr_mem : r ∈ N.primeFactors := (Finset.mem_filter.mp hr_lg).1
            have hle := (hcons r hr_mem).2.2
            have hexp := hlg4 r hr_lg
            omega
      _ = 3 * Q₁₃.card := by simp [Finset.sum_const, Nat.mul_comm]
  have hcol_ub : collisionExcess N q ≤ S₅₁_col.card + 3 * Q₁₃.card := by omega
  have hω_ub : N.primeFactors.card ≤ 2 * S₅₁_col.card + 6 * Q₁₃.card + 2 := by omega
  obtain ⟨hω_eq, _, _⟩ :=
    sixth_power_free_omega_and_total_identities ho hN hq hq4 he hev hfree
  change N.primeFactors.card = 1 + S₅₁.card + S₅₀.card + Q₁₃.card + Q₂₃.card at hω_eq
  have hpinch : S₅₀.card + S₅₁_rep.card + Q₂₃.card ≤ S₅₁_col.card + 5 * Q₁₃.card + 1 := by
    omega
  exact ⟨hω_ub, hpinch⟩

end OddPerfect
