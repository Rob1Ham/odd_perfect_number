module

public import OddPerfect.LocalRepeatDropConservation
public import OddPerfect.QuarticTargetCapacity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sixth-Power-Free Drop-Excess Pinch (`OddPerfect.SixthPowerFreeDropExcessPinch`)

Couples global component-index drop conservation (`∑ (Ω(N) - Ω(i_p)) = ω(N) + 2 * (M + E) + 1`)
with `cyclotomic_slope_excess_bounds`, `factorization_eq_indegAt_add_localRepeatAt`, and
`sixth_power_free_incoming_source_vacuum`:

1. `componentIndex_drop_sum_cyclotomic_slope_lower_bounds`:
   Unconditional and `3`-free linear lower bounds relating `ω(N)`, `|L₂|`, and
   `∑ p ∈ N.primeFactors, (Ω(N) - Ω(i_p))`.
2. `sixth_power_free_vacuum_indegAt_and_localRepeatAt`:
   On a sixth-power-free odd perfect number `N`, `indegAt N q r = 1` on `{q} ∪ S₅₀ ∪ Q₂₃`,
   forcing `localRepeatAt N q q = 0`, `localRepeatAt N q r = 1` on `S₅₀`, and
   `localRepeatAt N q r = 3` on `Q₂₃`.
3. `sixth_power_free_excess_and_drop_partition`:
   Partitions `localRepeatExcess` and `collisionExcess` across `{q} ∪ S₅₀ ∪ Q₂₃` and
   `S₅₁ ∪ Q₁₃`, yielding `221 ≤ E ≤ |S₅₁| + 3 * |Q₁₃|`, `|S₅₀| + 3 * |Q₂₃| ≤ M`,
   `M + E = |S| + 3 * |Q|`, and `1916 ≤ ∑ p ∈ N.primeFactors, (Ω(N) - Ω(i_p))`.
4. `sixth_power_free_pigeonhole_drop_with_largeSources_bonus`:
   Exact identity `(∑ drop) + 1 = 3 * ω(N) + 4 * |Q|` and existence of a component prime
   achieving the pigeonhole drop bound with `4 ≤ drop_p` (and `5 ≤ drop_p` when
   `|S| + 2 ≤ 3 * |Q|`).
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private theorem sixth_power_free_partition_invariants {N q : ℕ}
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

/-- **1. Component-Index Drop Sum Cyclotomic Slope Lower Bounds**:
Couples `sum_componentIndex_drop_eq_primeFactors_add_two_mul_excess` with
`cyclotomic_slope_excess_bounds`. -/
theorem componentIndex_drop_sum_cyclotomic_slope_lower_bounds {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1)
    (he : N.factorization q % 4 = 1) (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) :
    17 * N.primeFactors.card + 11 * (twoModThreeLargeSources N q).card ≤
      4 * (∑ p ∈ N.primeFactors, (cardFactors N - cardFactors (componentIndex N p))) + 35 ∧
    (¬ 3 ∣ N →
      13 * N.primeFactors.card + 8 * (twoModThreeLargeSources N q).card ≤
        3 * (∑ p ∈ N.primeFactors, (cardFactors N - cardFactors (componentIndex N p))) + 11) := by
  have hsum := sum_componentIndex_drop_eq_primeFactors_add_two_mul_excess ho hN hq hq4 he hev
  obtain ⟨h13, h3free, _⟩ := cyclotomic_slope_excess_bounds ho hN hq hq4 he hev
  refine ⟨by omega, fun h3 => ?_⟩
  have h5 := h3free h3
  omega

/-- **2. Sixth-Power-Free Vacuum Incoming Degrees and Local Repeats**:
On a sixth-power-free odd perfect number `N`, `indegAt N q r = 1` for every `r ∈ {q} ∪ S₅₀ ∪ Q₂₃`,
forcing `localRepeatAt N q q = 0`, `localRepeatAt N q r = 1` on `S₅₀`, and
`localRepeatAt N q r = 3` on `Q₂₃`. -/
theorem sixth_power_free_vacuum_indegAt_and_localRepeatAt {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1)
    (he : N.factorization q % 4 = 1) (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    let S₅₀ := (squareSources N).filter (· % 5 ≠ 1)
    let Q₂₃ := twoModThreeLargeSources N q
    (indegAt N q q = 1 ∧ localRepeatAt N q q = 0) ∧
    (∀ r ∈ S₅₀, indegAt N q r = 1 ∧ localRepeatAt N q r = 1) ∧
    (∀ r ∈ Q₂₃, indegAt N q r = 1 ∧ localRepeatAt N q r = 3) := by
  intro S₅₀ Q₂₃
  obtain ⟨_, hq1, hsq2, hlg4, hparts, _, _⟩ :=
    sixth_power_free_partition_invariants ho hN hq hq4 he hev hfree
  have hq_mut := (euler_linear_and_exponent_two_mutual_exclusion ho hN hq hq4 he hev).1 hq1
  have hq_pair : indegAt N q q = 1 ∧ localRepeatAt N q q = 0 := ⟨hq_mut.1, hq_mut.2.1⟩
  have hcons := (factorization_eq_indegAt_add_localRepeatAt ho hN hq hq4 he hev).1
  have hvac := (sixth_power_free_incoming_source_vacuum ho hN hq hq4 he hev hfree).1
  have hindeg_one : ∀ r ∈ S₅₀ ∪ Q₂₃, indegAt N q r = 1 := by
    intro r hr
    have hr_mem : r ∈ N.primeFactors := by
      rcases Finset.mem_union.mp hr with hrS | hrQ
      · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hrS).1).1
      · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hrQ).1).1
    have h1 : 1 ≤ indegAt N q r := (hcons r hr_mem).1
    have hnot_sq := (hvac r hr).2.2.2.2.2.2.1
    have hnot_lg := (hvac r hr).2.2.2.2.2.2.2.1
    have hsub :
        N.primeFactors.filter (fun p => r ∈ (oddComponentSigma N q p).primeFactors) ⊆ {q} := by
      intro p hp
      obtain ⟨hp_mem, hrp⟩ := Finset.mem_filter.mp hp
      rw [Finset.mem_singleton]
      by_contra hpq
      have hcomp_eq : oddComponentSigma N q p = sigma 1 (ordProj[p] N) := by
        simp [oddComponentSigma, hpq]
      have hdvd : r ∣ sigma 1 (p ^ N.factorization p) := by
        rw [← hcomp_eq]
        exact Nat.dvd_of_mem_primeFactors hrp
      have hp_mem' := hp_mem
      rw [hparts, Finset.mem_insert, Finset.mem_union] at hp_mem'
      rcases hp_mem' with rfl | hp_sq | hp_lg
      · exact hpq rfl
      · rw [hsq2 p hp_sq] at hdvd
        exact hnot_sq p hp_sq hdvd
      · rw [hlg4 p hp_lg] at hdvd
        exact hnot_lg p hp_lg hdvd
    have hle1 : indegAt N q r ≤ 1 := by
      unfold indegAt
      calc
        (N.primeFactors.filter (fun p => r ∈ (oddComponentSigma N q p).primeFactors)).card
            ≤ ({q} : Finset ℕ).card := Finset.card_le_card hsub
        _ = 1 := Finset.card_singleton q
    omega
  refine ⟨hq_pair, fun r hr => ?_, fun r hr => ?_⟩
  · have hr_sq : r ∈ squareSources N := (Finset.mem_filter.mp hr).1
    have hr_mem : r ∈ N.primeFactors := (Finset.mem_filter.mp hr_sq).1
    have hi : indegAt N q r = 1 := hindeg_one r (Finset.mem_union.mpr (Or.inl hr))
    have hadd := (hcons r hr_mem).2.1
    have hexp := hsq2 r hr_sq
    omega
  · have hr_lg : r ∈ largeSources N q := (Finset.mem_filter.mp hr).1
    have hr_mem : r ∈ N.primeFactors := (Finset.mem_filter.mp hr_lg).1
    have hi : indegAt N q r = 1 := hindeg_one r (Finset.mem_union.mpr (Or.inr hr))
    have hadd := (hcons r hr_mem).2.1
    have hexp := hlg4 r hr_lg
    omega

/-- **3. Sixth-Power-Free Excess and Drop Partition**:
Partitions `localRepeatExcess` and `collisionExcess` across `{q} ∪ S₅₀ ∪ Q₂₃` and `S₅₁ ∪ Q₁₃`,
and establishes the lower bound `1916 ≤ ∑ p ∈ N.primeFactors, (Ω(N) - Ω(i_p))`. -/
theorem sixth_power_free_excess_and_drop_partition {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1)
    (he : N.factorization q % 4 = 1) (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    let S₅₀ := (squareSources N).filter (· % 5 ≠ 1)
    let S₅₁ := (squareSources N).filter (· % 5 = 1)
    let Q₁₃ := oneModThreeLargeSources N q
    let Q₂₃ := twoModThreeLargeSources N q
    localRepeatExcess N q + collisionExcess N q =
      (squareSources N).card + 3 * (largeSources N q).card ∧
    S₅₀.card + 3 * Q₂₃.card ≤ localRepeatExcess N q ∧
    collisionExcess N q = ∑ r ∈ S₅₁ ∪ Q₁₃, (indegAt N q r - 1) ∧
    221 ≤ collisionExcess N q ∧
    collisionExcess N q ≤ S₅₁.card + 3 * Q₁₃.card ∧
    1916 ≤ ∑ p ∈ N.primeFactors, (cardFactors N - cardFactors (componentIndex N p)) := by
  intro S₅₀ S₅₁ Q₁₃ Q₂₃
  obtain ⟨_, hq1, hsq2, hlg4, hparts, hq_notin, hdisj⟩ :=
    sixth_power_free_partition_invariants ho hN hq hq4 he hev hfree
  obtain ⟨hcons, hsum_loc, hsum_col⟩ :=
    factorization_eq_indegAt_add_localRepeatAt ho hN hq hq4 he hev
  obtain ⟨hq_vac, hS50_vac, hQ23_vac⟩ :=
    sixth_power_free_vacuum_indegAt_and_localRepeatAt ho hN hq hq4 he hev hfree
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
  have hS50_sub_S : S₅₀ ⊆ squareSources N := Finset.filter_subset _ _
  have hS51_sub_S : S₅₁ ⊆ squareSources N := Finset.filter_subset _ _
  have hQ23_sub_Q : Q₂₃ ⊆ largeSources N q := Finset.filter_subset _ _
  have hQ13_sub_Q : Q₁₃ ⊆ largeSources N q := Finset.filter_subset _ _
  have hS50_Q23_disj : Disjoint S₅₀ Q₂₃ := hdisj.mono hS50_sub_S hQ23_sub_Q
  have hS51_Q13_disj : Disjoint S₅₁ Q₁₃ := hdisj.mono hS51_sub_S hQ13_sub_Q
  have hS_sub_N : squareSources N ⊆ N.primeFactors := by
    intro r hr
    exact (Finset.mem_filter.mp hr).1
  have hQ_sub_N : largeSources N q ⊆ N.primeFactors := by
    intro r hr
    exact (Finset.mem_filter.mp hr).1
  have hcard_N : N.primeFactors.card = 1 + (squareSources N).card + (largeSources N q).card := by
    rw [hparts, Finset.card_insert_of_notMem hq_notin, Finset.card_union_of_disjoint hdisj]
    omega
  have hΩ_N : cardFactors N = 1 + 2 * (squareSources N).card + 4 * (largeSources N q).card := by
    have hcf : cardFactors N = ∑ r ∈ N.primeFactors, N.factorization r := by
      rw [cardFactors_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
    have hsum_sq : (∑ s ∈ squareSources N, N.factorization s) = 2 * (squareSources N).card := by
      calc
        ∑ s ∈ squareSources N, N.factorization s
            = ∑ _s ∈ squareSources N, 2 := Finset.sum_congr rfl fun s hs => hsq2 s hs
        _ = 2 * (squareSources N).card := by simp [Finset.sum_const, Nat.mul_comm]
    have hsum_lg : (∑ u ∈ largeSources N q, N.factorization u) = 4 * (largeSources N q).card := by
      calc
        ∑ u ∈ largeSources N q, N.factorization u
            = ∑ _u ∈ largeSources N q, 4 := Finset.sum_congr rfl fun u hu => hlg4 u hu
        _ = 4 * (largeSources N q).card := by simp [Finset.sum_const, Nat.mul_comm]
    rw [hcf, hparts, Finset.sum_insert hq_notin, Finset.sum_union hdisj, hq1, hsum_sq, hsum_lg]
    omega
  have hdecomp := cardFactors_eq_primeFactors_add_localRepeat_add_collisionExcess ho hN hq hq4 he hev
  have hME_eq : localRepeatExcess N q + collisionExcess N q =
      (squareSources N).card + 3 * (largeSources N q).card := by
    omega
  have hloc_bound : S₅₀.card + 3 * Q₂₃.card ≤ localRepeatExcess N q := by
    have hsub : S₅₀ ∪ Q₂₃ ⊆ N.primeFactors :=
      Finset.union_subset (hS50_sub_S.trans hS_sub_N) (hQ23_sub_Q.trans hQ_sub_N)
    have hsum_le :
        (∑ r ∈ S₅₀ ∪ Q₂₃, localRepeatAt N q r) ≤ ∑ r ∈ N.primeFactors, localRepeatAt N q r :=
      Finset.sum_le_sum_of_subset hsub
    have hsum_S50 : (∑ r ∈ S₅₀, localRepeatAt N q r) = S₅₀.card := by
      calc
        ∑ r ∈ S₅₀, localRepeatAt N q r
            = ∑ _r ∈ S₅₀, 1 := Finset.sum_congr rfl fun r hr => (hS50_vac r hr).2
        _ = S₅₀.card := by simp [Finset.sum_const]
    have hsum_Q23 : (∑ r ∈ Q₂₃, localRepeatAt N q r) = 3 * Q₂₃.card := by
      calc
        ∑ r ∈ Q₂₃, localRepeatAt N q r
            = ∑ _r ∈ Q₂₃, 3 := Finset.sum_congr rfl fun r hr => (hQ23_vac r hr).2
        _ = 3 * Q₂₃.card := by simp [Finset.sum_const, Nat.mul_comm]
    rw [Finset.sum_union hS50_Q23_disj, hsum_S50, hsum_Q23, hsum_loc] at hsum_le
    exact hsum_le
  have hcol_eq : collisionExcess N q = ∑ r ∈ S₅₁ ∪ Q₁₃, (indegAt N q r - 1) := by
    have hsub : S₅₁ ∪ Q₁₃ ⊆ N.primeFactors :=
      Finset.union_subset (hS51_sub_S.trans hS_sub_N) (hQ13_sub_Q.trans hQ_sub_N)
    rw [← hsum_col]
    refine (Finset.sum_subset hsub fun r hrN hrnot => ?_).symm
    have hr_not_S51 : r ∉ S₅₁ := fun h => hrnot (Finset.mem_union.mpr (Or.inl h))
    have hr_not_Q13 : r ∉ Q₁₃ := fun h => hrnot (Finset.mem_union.mpr (Or.inr h))
    have hrN' := hrN
    rw [hparts, Finset.mem_insert, Finset.mem_union] at hrN'
    rcases hrN' with rfl | hrS | hrQ
    · rw [hq_vac.1]
      rfl
    · have hr_S50 : r ∈ S₅₀ := by
        rw [hS_parts, Finset.mem_union] at hrS
        exact hrS.resolve_right hr_not_S51
      rw [(hS50_vac r hr_S50).1]
      rfl
    · have hr_Q23 : r ∈ Q₂₃ := by
        rw [hQ_parts, Finset.mem_union] at hrQ
        exact hrQ.resolve_right hr_not_Q13
      rw [(hQ23_vac r hr_Q23).1]
      rfl
  have h221 : 221 ≤ collisionExcess N q :=
    (sixth_power_free_collision_excess_ge_221 ho hN hq hq4 he hev hfree).2.1
  have hcol_le : collisionExcess N q ≤ S₅₁.card + 3 * Q₁₃.card := by
    rw [hcol_eq, Finset.sum_union hS51_Q13_disj]
    have h1 : (∑ r ∈ S₅₁, (indegAt N q r - 1)) ≤ S₅₁.card := by
      calc
        ∑ r ∈ S₅₁, (indegAt N q r - 1)
            ≤ ∑ _r ∈ S₅₁, 1 := by
              refine Finset.sum_le_sum fun r hr => ?_
              have hr_sq := hS51_sub_S hr
              have hr_mem := hS_sub_N hr_sq
              have hle := (hcons r hr_mem).2.2
              have hexp := hsq2 r hr_sq
              omega
        _ = S₅₁.card := by simp [Finset.sum_const]
    have h2 : (∑ r ∈ Q₁₃, (indegAt N q r - 1)) ≤ 3 * Q₁₃.card := by
      calc
        ∑ r ∈ Q₁₃, (indegAt N q r - 1)
            ≤ ∑ _r ∈ Q₁₃, 3 := by
              refine Finset.sum_le_sum fun r hr => ?_
              have hr_lg := hQ13_sub_Q hr
              have hr_mem := hQ_sub_N hr_lg
              have hle := (hcons r hr_mem).2.2
              have hexp := hlg4 r hr_lg
              omega
        _ = 3 * Q₁₃.card := by simp [Finset.sum_const, Nat.mul_comm]
    omega
  have hdrop_1916 :
      1916 ≤ ∑ p ∈ N.primeFactors, (cardFactors N - cardFactors (componentIndex N p)) := by
    have hdrop_eq := sum_componentIndex_drop_eq_primeFactors_add_two_mul_excess ho hN hq hq4 he hev
    have h443 := (sixth_power_free_collision_excess_ge_221 ho hN hq hq4 he hev hfree).1
    have h736 := (cyclotomic_slope_excess_bounds ho hN hq hq4 he hev).2.2 hfree
    omega
  exact ⟨hME_eq, hloc_bound, hcol_eq, h221, hcol_le, hdrop_1916⟩

/-- **4. Sixth-Power-Free Pigeonhole Drop with Large-Sources Bonus**:
Proves `(∑ drop) + 1 = 3 * ω(N) + 4 * |Q|` and exhibits a prime factor `p ∈ N.primeFactors`
satisfying the pigeonhole drop inequality with `4 ≤ drop_p` (and `5 ≤ drop_p` when
`|S| + 2 ≤ 3 * |Q|`). -/
theorem sixth_power_free_pigeonhole_drop_with_largeSources_bonus {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1)
    (he : N.factorization q % 4 = 1) (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    (∑ p ∈ N.primeFactors, (cardFactors N - cardFactors (componentIndex N p))) + 1 =
      3 * N.primeFactors.card + 4 * (largeSources N q).card ∧
    ∃ p ∈ N.primeFactors,
      3 * N.primeFactors.card + 4 * (largeSources N q).card ≤
        N.primeFactors.card * (cardFactors N - cardFactors (componentIndex N p)) + 1 ∧
      4 ≤ cardFactors N - cardFactors (componentIndex N p) ∧
      ((squareSources N).card + 2 ≤ 3 * (largeSources N q).card →
        5 ≤ cardFactors N - cardFactors (componentIndex N p)) := by
  obtain ⟨_, _, _, _, hparts, hq_notin, hdisj⟩ :=
    sixth_power_free_partition_invariants ho hN hq hq4 he hev hfree
  have hcard_N : N.primeFactors.card = 1 + (squareSources N).card + (largeSources N q).card := by
    rw [hparts, Finset.card_insert_of_notMem hq_notin, Finset.card_union_of_disjoint hdisj]
    omega
  have hME_eq :=
    (sixth_power_free_excess_and_drop_partition ho hN hq hq4 he hev hfree).1
  have hdrop_eq := sum_componentIndex_drop_eq_primeFactors_add_two_mul_excess ho hN hq hq4 he hev
  have hsum_id :
      (∑ p ∈ N.primeFactors, (cardFactors N - cardFactors (componentIndex N p))) + 1 =
        3 * N.primeFactors.card + 4 * (largeSources N q).card := by
    omega
  obtain ⟨p, hp, hp_max⟩ :=
    Finset.exists_max_image N.primeFactors
      (fun x => cardFactors N - cardFactors (componentIndex N x)) ⟨q, hq⟩
  have hsum_le :
      (∑ x ∈ N.primeFactors, (cardFactors N - cardFactors (componentIndex N x))) ≤
        N.primeFactors.card * (cardFactors N - cardFactors (componentIndex N p)) := by
    calc
      ∑ x ∈ N.primeFactors, (cardFactors N - cardFactors (componentIndex N x))
          ≤ ∑ _x ∈ N.primeFactors, (cardFactors N - cardFactors (componentIndex N p)) :=
            Finset.sum_le_sum fun x hx => hp_max x hx
      _ = N.primeFactors.card * (cardFactors N - cardFactors (componentIndex N p)) := by
            simp [Finset.sum_const, smul_eq_mul]
  obtain ⟨p₀, hp₀, h6⟩ := exists_componentIndex_cardFactors_add_six_le ho hN
  have hp0_le :
      cardFactors N - cardFactors (componentIndex N p₀) ≤
        cardFactors N - cardFactors (componentIndex N p) :=
    hp_max p₀ hp₀
  have h6_drop : 6 ≤ cardFactors N - cardFactors (componentIndex N p) := by omega
  refine ⟨hsum_id, p, hp, by omega, by omega, fun _ => by omega⟩

end OddPerfect
