module

public import OddPerfect.SixthPowerFreeRepSourceDecomposition
import OddPerfect.SixthPowerFreeBipartiteSlackPinch
import OddPerfect.SixthPowerFreeS51CollisionDensityPinch
import OddPerfect.SixthPowerFreeBipartiteParity
import OddPerfect.SixthPowerFreeQuarterDensity
import OddPerfect.SixthPowerFreeEuler
import OddPerfect.SteuerwaldFree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Sixth-Power-Free `Q₁₃` Composite Fiber & Collision Pinch (`OddPerfect.SixthPowerFreeQ13CompCollisionPinch`)

Refines the `Q₁₃` composite fiber decomposition by partitioning
`Q₁₃_comp := Q₁₃.filter (fun u => ¬ q ∣ sigma 1 (u ^ 4) ∧ ¬ (sigma 1 (u ^ 4)).Prime)` into:
- `Q₁₃_comp_free := Q₁₃_comp.filter (fun u => repFib u = ∅)` (each contributing `3` instead of `1`
  to `∑ cardFactors (sigma 1 (u ^ 4))` with zero `repFib` overlap), and
- `Q₁₃_comp_rep := Q₁₃_comp.filter (fun u => (repFib u).Nonempty)` (bounded by `S₅₁_rep_src.card`).

This eliminates `S₅₁_rep_q` completely from the quartic-to-`S₅₁` pinch and strengthens the
collision lower bound to `110 ≤ S₅₁_col.card` whenever `S₅₁_rep_src = ∅`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private theorem sigma_one_prime_local {p : ℕ} (hp : p.Prime) :
    sigma 1 p = p + 1 := by
  rw [← pow_one p, sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

/-- **1. `Q₁₃` Composite Free/Repeat Fiber Bounds**:
Partitions `Q₁₃_comp` into `Q₁₃_comp_free` (`repFib u = ∅`) and `Q₁₃_comp_rep`
(`(repFib u).Nonempty`), proves `Q₁₃_comp_rep.card ≤ S₅₁_rep_src.card`, and sharpens the
`2 * S₅₁_col.card` bound by `2 * Q₁₃_comp_free.card`. -/
theorem sixth_power_free_Q13_comp_free_and_rep_bounds {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    let S₅₁ := (squareSources N).filter (· % 5 = 1)
    let S₅₁_col := S₅₁.filter (fun r => indegAt N q r = 2)
    let S₅₁_rep := S₅₁.filter (fun r => indegAt N q r = 1)
    let S₅₁_rep_src := S₅₁_rep.filter (fun r => ¬ r ∣ (q + 1) / 2)
    let Q₁₃ := oneModThreeLargeSources N q
    let Q₂₃ := twoModThreeLargeSources N q
    let repFib := fun u => S₅₁_rep_src.filter (fun r => r ∣ sigma 1 (u ^ 4))
    let Q₁₃_comp := Q₁₃.filter (fun u => ¬ q ∣ sigma 1 (u ^ 4) ∧ ¬ (sigma 1 (u ^ 4)).Prime)
    let Q₁₃_comp_free := Q₁₃_comp.filter (fun u => repFib u = ∅)
    let Q₁₃_comp_rep := Q₁₃_comp.filter (fun u => (repFib u).Nonempty)
    Q₁₃_comp = Q₁₃_comp_free ∪ Q₁₃_comp_rep ∧
    Disjoint Q₁₃_comp_free Q₁₃_comp_rep ∧
    Q₁₃_comp.card = Q₁₃_comp_free.card + Q₁₃_comp_rep.card ∧
    Q₁₃_comp_rep.card ≤ S₅₁_rep_src.card ∧
    Q₁₃.card + 2 * Q₁₃_comp_free.card + 2 * Q₂₃.card ≤ 2 * S₅₁_col.card + 1 ∧
    146 + 2 * Q₁₃_comp_free.card + Q₂₃.card ≤ 2 * S₅₁_col.card := by
  intro S₅₁ S₅₁_col S₅₁_rep S₅₁_rep_src Q₁₃ Q₂₃ repFib Q₁₃_comp Q₁₃_comp_free Q₁₃_comp_rep
  let S₅₁_rep_q := S₅₁_rep.filter (fun r => r ∣ (q + 1) / 2)
  have hpart : Q₁₃_comp = Q₁₃_comp_free ∪ Q₁₃_comp_rep := by
    ext u
    simp only [Q₁₃_comp_free, Q₁₃_comp_rep, Finset.mem_union, Finset.mem_filter]
    rcases Finset.eq_empty_or_nonempty (repFib u) with h | h <;> tauto
  have hdisj : Disjoint Q₁₃_comp_free Q₁₃_comp_rep := by
    apply Finset.disjoint_left.mpr
    intro u h1 h2
    exact (Finset.mem_filter.mp h2).2.ne_empty (Finset.mem_filter.mp h1).2
  have hcard : Q₁₃_comp.card = Q₁₃_comp_free.card + Q₁₃_comp_rep.card := by
    rw [hpart, Finset.card_union_of_disjoint hdisj]
  obtain ⟨hfib_sum, hlb_all, hlb_Q23, _, _, _, _⟩ :=
    sixth_power_free_quartic_double_Q23_collision_pinch ho hN hq hq4 he hev hfree
  change (∑ u ∈ largeSources N q, (repFib u).card) = S₅₁_rep_src.card at hfib_sum
  have hcomp_rep_sub : Q₁₃_comp_rep ⊆ largeSources N q := by
    intro u hu
    have hu_comp : u ∈ Q₁₃_comp := (Finset.mem_filter.mp hu).1
    have hu_Q13 : u ∈ Q₁₃ := (Finset.mem_filter.mp hu_comp).1
    exact (Finset.mem_filter.mp hu_Q13).1
  have hcomp_rep_le : Q₁₃_comp_rep.card ≤ S₅₁_rep_src.card := by
    calc
      Q₁₃_comp_rep.card = ∑ _u ∈ Q₁₃_comp_rep, 1 := by simp [Finset.sum_const]
      _ ≤ ∑ u ∈ Q₁₃_comp_rep, (repFib u).card := by
            refine Finset.sum_le_sum fun u hu => ?_
            exact Finset.card_pos.mpr (Finset.mem_filter.mp hu).2
      _ ≤ ∑ u ∈ largeSources N q, (repFib u).card :=
            Finset.sum_le_sum_of_subset hcomp_rep_sub
      _ = S₅₁_rep_src.card := hfib_sum
  have hfree_sub : Q₁₃_comp_free ⊆ Q₁₃ :=
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  let Q₁₃_other := Q₁₃ \ Q₁₃_comp_free
  have hQ13_split_set : Q₁₃ = Q₁₃_comp_free ∪ Q₁₃_other :=
    (Finset.union_sdiff_of_subset hfree_sub).symm
  have hQ13_split_disj : Disjoint Q₁₃_comp_free Q₁₃_other :=
    Finset.disjoint_left.mpr fun _ h1 h2 => (Finset.mem_sdiff.mp h2).2 h1
  have hQ13_split_card : Q₁₃.card = Q₁₃_comp_free.card + Q₁₃_other.card := by
    rw [hQ13_split_set, Finset.card_union_of_disjoint hQ13_split_disj]
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
  have hfib_split :
      (∑ u ∈ largeSources N q, (repFib u).card) =
        (∑ u ∈ Q₁₃_comp_free, (repFib u).card) +
          (∑ u ∈ Q₁₃_other, (repFib u).card) +
          ∑ u ∈ Q₂₃, (repFib u).card := by
    rw [hQ_parts, Finset.sum_union hQ_disj, hQ13_split_set, Finset.sum_union hQ13_split_disj]
  have hcf_split :
      (∑ u ∈ largeSources N q, cardFactors (sigma 1 (u ^ 4))) =
        (∑ u ∈ Q₁₃_comp_free, cardFactors (sigma 1 (u ^ 4))) +
          (∑ u ∈ Q₁₃_other, cardFactors (sigma 1 (u ^ 4))) +
          ∑ u ∈ Q₂₃, cardFactors (sigma 1 (u ^ 4)) := by
    rw [hQ_parts, Finset.sum_union hQ_disj, hQ13_split_set, Finset.sum_union hQ13_split_disj]
  have hQ13_dich :=
    (sixth_power_free_quartic_cardFactors_mod_three_dichotomy ho hN hq hq4 he hev hfree).1
  have hlb_free : ∀ u ∈ Q₁₃_comp_free,
      2 * (repFib u).card + 3 ≤ cardFactors (sigma 1 (u ^ 4)) := by
    intro u hu
    obtain ⟨hu_comp, hu_empty⟩ := Finset.mem_filter.mp hu
    obtain ⟨hu_Q13, hnq, hnprime⟩ := Finset.mem_filter.mp hu_comp
    have hcard0 : (repFib u).card = 0 := Finset.card_eq_zero.mpr hu_empty
    have h3le : 3 ≤ cardFactors (sigma 1 (u ^ 4)) :=
      ((hQ13_dich u hu_Q13 hnq).2.2).resolve_left hnprime
    omega
  have hsum_free :
      2 * (∑ u ∈ Q₁₃_comp_free, (repFib u).card) + 3 * Q₁₃_comp_free.card ≤
        ∑ u ∈ Q₁₃_comp_free, cardFactors (sigma 1 (u ^ 4)) := by
    calc
      2 * (∑ u ∈ Q₁₃_comp_free, (repFib u).card) + 3 * Q₁₃_comp_free.card
          = (∑ u ∈ Q₁₃_comp_free, 2 * (repFib u).card) + ∑ _u ∈ Q₁₃_comp_free, 3 := by
              rw [Finset.mul_sum, Finset.sum_const, smul_eq_mul, mul_comm]
      _ = ∑ u ∈ Q₁₃_comp_free, (2 * (repFib u).card + 3) := Finset.sum_add_distrib.symm
      _ ≤ ∑ u ∈ Q₁₃_comp_free, cardFactors (sigma 1 (u ^ 4)) := Finset.sum_le_sum hlb_free
  have hsum_other :
      2 * (∑ u ∈ Q₁₃_other, (repFib u).card) + Q₁₃_other.card ≤
        ∑ u ∈ Q₁₃_other, cardFactors (sigma 1 (u ^ 4)) := by
    calc
      2 * (∑ u ∈ Q₁₃_other, (repFib u).card) + Q₁₃_other.card
          = (∑ u ∈ Q₁₃_other, 2 * (repFib u).card) + ∑ _u ∈ Q₁₃_other, 1 := by
              rw [Finset.mul_sum, Finset.sum_const, smul_eq_mul, mul_one]
      _ = ∑ u ∈ Q₁₃_other, (2 * (repFib u).card + 1) := Finset.sum_add_distrib.symm
      _ ≤ ∑ u ∈ Q₁₃_other, cardFactors (sigma 1 (u ^ 4)) := by
            refine Finset.sum_le_sum fun u hu => ?_
            have hu_Q13 : u ∈ Q₁₃ := (Finset.mem_sdiff.mp hu).1
            exact hlb_all u (Finset.mem_filter.mp hu_Q13).1
  have hsum_Q23 :
      2 * (∑ u ∈ Q₂₃, (repFib u).card) + 2 * Q₂₃.card ≤
        ∑ u ∈ Q₂₃, cardFactors (sigma 1 (u ^ 4)) := by
    calc
      2 * (∑ u ∈ Q₂₃, (repFib u).card) + 2 * Q₂₃.card
          = (∑ u ∈ Q₂₃, 2 * (repFib u).card) + ∑ _u ∈ Q₂₃, 2 := by
              rw [Finset.mul_sum, Finset.sum_const, smul_eq_mul, mul_comm]
      _ = ∑ u ∈ Q₂₃, (2 * (repFib u).card + 2) := Finset.sum_add_distrib.symm
      _ ≤ ∑ u ∈ Q₂₃, cardFactors (sigma 1 (u ^ 4)) := Finset.sum_le_sum hlb_Q23
  have hcf_lb :
      2 * S₅₁_rep_src.card + Q₁₃.card + 2 * Q₁₃_comp_free.card + 2 * Q₂₃.card ≤
        ∑ u ∈ largeSources N q, cardFactors (sigma 1 (u ^ 4)) := by
    omega
  have h3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  have hq1 : N.factorization q = 1 := sixth_power_free_euler_exponent_one ho hN hq he hfree
  have hq_prime := Nat.prime_of_mem_primeFactors hq
  have hq_odd : Odd q := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hq)
  obtain ⟨hlg4, h147, _⟩ :=
    three_free_sixthPowerFree_forces_147_largeSources ho hN hq hq4 he hev h3 hfree
  obtain ⟨_, _, hrep_split, _, _⟩ :=
    sixth_power_free_S51_rep_source_partition ho hN hq hq4 he hev hfree
  change S₅₁_rep.card = S₅₁_rep_q.card + S₅₁_rep_src.card at hrep_split
  have hid1 :=
    (sixth_power_free_bipartite_multiplicity_identities ho hN hq hq4 he hev hfree).1
  change (∑ u ∈ largeSources N q, cardFactors (sigma 1 (u ^ 4))) +
      (∑ p ∈ S₅₁, ((q + 1) / 2).factorization p) =
      2 * S₅₁.card + ∑ u ∈ largeSources N q, (sigma 1 (u ^ 4)).factorization q at hid1
  have hS51_split : S₅₁.card = S₅₁_col.card + S₅₁_rep.card :=
    (sixth_power_free_S51_collision_repeat_split ho hN hq hq4 he hev hfree).2.2.1
  have hhalf_ne0 : (q + 1) / 2 ≠ 0 := by
    have := hq_prime.two_le
    omega
  have hcomp_q : oddComponentSigma N q q = (q + 1) / 2 := by
    unfold oddComponentSigma
    simp only [ite_true]
    rw [hq1, pow_one, sigma_one_prime_local hq_prime]
  have hrep_q_fac : ∀ r ∈ S₅₁_rep_q, ((q + 1) / 2).factorization r = 2 := by
    intro r hr
    obtain ⟨hr_rep, hr_dvd_half⟩ := Finset.mem_filter.mp hr
    obtain ⟨hr_S51, hr_ind1⟩ := Finset.mem_filter.mp hr_rep
    have hr_sq : r ∈ squareSources N := (Finset.mem_filter.mp hr_S51).1
    obtain ⟨hr_N, _, hr_exp2⟩ := Finset.mem_filter.mp hr_sq
    have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr_N
    have hmut := (euler_linear_and_exponent_two_mutual_exclusion ho hN hq hq4 he hev).2 r hr_N hr_exp2
    obtain ⟨_, _, p, hp_N, hr2_dvd_p, hnot_other⟩ := hmut.resolve_left (fun h => by omega)
    have hr_dvd_q : r ∣ oddComponentSigma N q q := by
      rw [hcomp_q]
      exact hr_dvd_half
    have hqp : q = p := by
      by_contra hne
      exact hnot_other q hq hne hr_dvd_q
    have hr2_dvd_half : r ^ 2 ∣ (q + 1) / 2 := by
      rw [← hcomp_q]
      rw [← hqp] at hr2_dvd_p
      exact hr2_dvd_p
    have hle2 : 2 ≤ ((q + 1) / 2).factorization r :=
      (hr_prime.pow_dvd_iff_le_factorization hhalf_ne0).mp hr2_dvd_half
    have hle_N : ((q + 1) / 2).factorization r ≤ 2 := by
      have hsum := factorization_eq_sum_sigma_factorizations hN
        (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr_N)) hr_prime
      have hq_le := Finset.single_le_sum
        (f := fun x => (sigma 1 (x ^ N.factorization x)).factorization r)
        (fun _ _ => Nat.zero_le _) hq
      have hsig_q : sigma 1 (q ^ N.factorization q) = 2 * ((q + 1) / 2) := by
        rw [hq1, pow_one, sigma_one_prime_local hq_prime]
        omega
      have hr_ne2 : r ≠ 2 := by
        intro h2
        have hodd_r : Odd r := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr_N)
        rw [h2] at hodd_r
        exact (by decide : ¬ Odd 2) hodd_r
      have hq_term : (sigma 1 (q ^ N.factorization q)).factorization r =
          ((q + 1) / 2).factorization r := by
        rw [hsig_q, Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) hhalf_ne0, Finsupp.add_apply]
        have hnot2 : ¬ r ∣ 2 := fun h =>
          hr_ne2 (((Nat.dvd_prime Nat.prime_two).mp h).resolve_left hr_prime.ne_one)
        rw [Nat.factorization_eq_zero_of_not_dvd hnot2, zero_add]
      omega
    omega
  have hrep_q_sum : 2 * S₅₁_rep_q.card ≤ ∑ p ∈ S₅₁, ((q + 1) / 2).factorization p := by
    have hsub : S₅₁_rep_q ⊆ S₅₁ :=
      (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    calc
      2 * S₅₁_rep_q.card = ∑ _r ∈ S₅₁_rep_q, 2 := by simp [Finset.sum_const, Nat.mul_comm]
      _ = ∑ r ∈ S₅₁_rep_q, ((q + 1) / 2).factorization r :=
            Finset.sum_congr rfl fun r hr => (hrep_q_fac r hr).symm
      _ ≤ ∑ p ∈ S₅₁, ((q + 1) / 2).factorization p := Finset.sum_le_sum_of_subset hsub
  have hq_sum_le1 : ∑ u ∈ largeSources N q, (sigma 1 (u ^ 4)).factorization q ≤ 1 := by
    have hsum := factorization_eq_sum_sigma_factorizations hN hq_odd hq_prime
    have hsub : largeSources N q ⊆ N.primeFactors := Finset.filter_subset _ _
    have hle1 :
        ∑ u ∈ largeSources N q, (sigma 1 (u ^ 4)).factorization q ≤
          ∑ r ∈ largeSources N q, (sigma 1 (r ^ N.factorization r)).factorization q := by
      refine Finset.sum_le_sum fun u hu => ?_
      rw [hlg4 u hu]
    have hle2 :
        ∑ r ∈ largeSources N q, (sigma 1 (r ^ N.factorization r)).factorization q ≤
          ∑ r ∈ N.primeFactors, (sigma 1 (r ^ N.factorization r)).factorization q :=
      Finset.sum_le_sum_of_subset hsub
    omega
  have hmain : Q₁₃.card + 2 * Q₁₃_comp_free.card + 2 * Q₂₃.card ≤ 2 * S₅₁_col.card + 1 := by
    omega
  have h146 : 146 + 2 * Q₁₃_comp_free.card + Q₂₃.card ≤ 2 * S₅₁_col.card := by
    omega
  exact ⟨hpart, hdisj, hcard, hcomp_rep_le, hmain, h146⟩

/-- **2. Collision + `S₅₁_rep_src` Pinch and `110` Bound**:
Eliminates `S₅₁_rep_q` completely from Wave N4's collision/repeat inequality, proving
`3 * Q₁₃.card + 2 * Q₂₃.card ≤ 4 * S₅₁_col.card + 2 * S₅₁_rep_src.card + 3`,
`438 + Q₂₃.card ≤ 4 * S₅₁_col.card + 2 * S₅₁_rep_src.card`,
`219 ≤ 2 * S₅₁_col.card + S₅₁_rep_src.card`,
`N.primeFactors.card ≤ 4 * S₅₁_col.card + 2 * S₅₁_rep_src.card + 5`, and
`S₅₁_rep_src = ∅ → 110 ≤ S₅₁_col.card`. -/
theorem sixth_power_free_col_rep_src_pinch_and_110_bound {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    let S₅₁ := (squareSources N).filter (· % 5 = 1)
    let S₅₁_col := S₅₁.filter (fun r => indegAt N q r = 2)
    let S₅₁_rep := S₅₁.filter (fun r => indegAt N q r = 1)
    let S₅₁_rep_src := S₅₁_rep.filter (fun r => ¬ r ∣ (q + 1) / 2)
    let Q₁₃ := oneModThreeLargeSources N q
    let Q₂₃ := twoModThreeLargeSources N q
    3 * Q₁₃.card + 2 * Q₂₃.card ≤ 4 * S₅₁_col.card + 2 * S₅₁_rep_src.card + 3 ∧
    438 + Q₂₃.card ≤ 4 * S₅₁_col.card + 2 * S₅₁_rep_src.card ∧
    219 ≤ 2 * S₅₁_col.card + S₅₁_rep_src.card ∧
    N.primeFactors.card ≤ 4 * S₅₁_col.card + 2 * S₅₁_rep_src.card + 5 ∧
    (S₅₁_rep_src = ∅ → 110 ≤ S₅₁_col.card) := by
  intro S₅₁ S₅₁_col S₅₁_rep S₅₁_rep_src Q₁₃ Q₂₃
  let repFib := fun u => S₅₁_rep_src.filter (fun r => r ∣ sigma 1 (u ^ 4))
  let Q₁₃_q := Q₁₃.filter (fun u => q ∣ sigma 1 (u ^ 4))
  let Q₁₃_nq := Q₁₃.filter (fun u => ¬ q ∣ sigma 1 (u ^ 4))
  let Q₁₃_prime := Q₁₃.filter (fun u => ¬ q ∣ sigma 1 (u ^ 4) ∧ (sigma 1 (u ^ 4)).Prime)
  let Q₁₃_comp := Q₁₃.filter (fun u => ¬ q ∣ sigma 1 (u ^ 4) ∧ ¬ (sigma 1 (u ^ 4)).Prime)
  let Q₁₃_comp_free := Q₁₃_comp.filter (fun u => repFib u = ∅)
  let Q₁₃_comp_rep := Q₁₃_comp.filter (fun u => (repFib u).Nonempty)
  obtain ⟨_, _, hcomp_card, hcomp_rep_le, hmain, _⟩ :=
    sixth_power_free_Q13_comp_free_and_rep_bounds ho hN hq hq4 he hev hfree
  change Q₁₃_comp.card = Q₁₃_comp_free.card + Q₁₃_comp_rep.card at hcomp_card
  change Q₁₃_comp_rep.card ≤ S₅₁_rep_src.card at hcomp_rep_le
  change Q₁₃.card + 2 * Q₁₃_comp_free.card + 2 * Q₂₃.card ≤ 2 * S₅₁_col.card + 1 at hmain
  have hQ13_parts : Q₁₃ = Q₁₃_q ∪ Q₁₃_nq := by
    ext u
    simp only [Q₁₃_q, Q₁₃_nq, Finset.mem_union, Finset.mem_filter]
    by_cases h : q ∣ sigma 1 (u ^ 4) <;> tauto
  have hQ13_disj : Disjoint Q₁₃_q Q₁₃_nq := by
    apply Finset.disjoint_left.mpr
    intro u h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hQ13_nq_parts : Q₁₃_nq = Q₁₃_prime ∪ Q₁₃_comp := by
    ext u
    simp only [Q₁₃_nq, Q₁₃_prime, Q₁₃_comp, Finset.mem_union, Finset.mem_filter]
    by_cases h : (sigma 1 (u ^ 4)).Prime <;> tauto
  have hQ13_nq_disj : Disjoint Q₁₃_prime Q₁₃_comp := by
    apply Finset.disjoint_left.mpr
    intro u h1 h2
    exact (Finset.mem_filter.mp h2).2.2 (Finset.mem_filter.mp h1).2.2
  have hQ13_card : Q₁₃.card = Q₁₃_q.card + Q₁₃_prime.card + Q₁₃_comp.card := by
    rw [hQ13_parts, Finset.card_union_of_disjoint hQ13_disj,
      hQ13_nq_parts, Finset.card_union_of_disjoint hQ13_nq_disj]
    omega
  have hQ13_q_le1 : Q₁₃_q.card ≤ 1 := by
    have hhit_q := (sixth_power_free_largeSources_hit_S51_col ho hN hq hq4 he hev hfree).2
    have hsub : Q₁₃_q ⊆ (largeSources N q).filter (fun u => q ∣ sigma 1 (u ^ 4)) := by
      intro u hu
      obtain ⟨hu_Q13, hu_q⟩ := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu_Q13).1, hu_q⟩
    exact (Finset.card_le_card hsub).trans hhit_q
  have hQ13_prime_le : Q₁₃_prime.card ≤ S₅₁_col.card :=
    sixth_power_free_Q13_prime_inj_into_S51_col ho hN hq hq4 he hev hfree
  have h443 : 443 ≤ N.primeFactors.card :=
    (sixth_power_free_collision_excess_ge_221 ho hN hq hq4 he hev hfree).1
  have hω_le : N.primeFactors.card ≤ 3 * Q₁₃.card + Q₂₃.card + 2 :=
    (sixth_power_free_omega_and_total_identities ho hN hq hq4 he hev hfree).2.2
  have h1 : 3 * Q₁₃.card + 2 * Q₂₃.card ≤ 4 * S₅₁_col.card + 2 * S₅₁_rep_src.card + 3 := by
    omega
  have h2 : 438 + Q₂₃.card ≤ 4 * S₅₁_col.card + 2 * S₅₁_rep_src.card := by
    omega
  have h3 : 219 ≤ 2 * S₅₁_col.card + S₅₁_rep_src.card := by
    omega
  have h4 : N.primeFactors.card ≤ 4 * S₅₁_col.card + 2 * S₅₁_rep_src.card + 5 := by
    omega
  have h5 : S₅₁_rep_src = ∅ → 110 ≤ S₅₁_col.card := by
    intro hemp
    have hzero : S₅₁_rep_src.card = 0 := Finset.card_eq_zero.mpr hemp
    omega
  exact ⟨h1, h2, h3, h4, h5⟩

end OddPerfect
