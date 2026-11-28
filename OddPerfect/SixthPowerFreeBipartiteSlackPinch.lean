module

public import OddPerfect.SixthPowerFreeS51CollisionDensityPinch
import OddPerfect.SixthPowerFreeBipartiteParity
import OddPerfect.SixthPowerFreeQuarterDensity
import OddPerfect.SixthPowerFreeEuler
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Sixth-Power-Free Bipartite Slack Pinch (`OddPerfect.SixthPowerFreeBipartiteSlackPinch`)

Refines the sixth-power-free quartic-to-`S₅₁` bipartite capacity bound by splitting
`S₅₁ := (squareSources N).filter (· % 5 = 1)` into colliding (`indegAt = 2`) and
square-repeat (`indegAt = 1`) primes:

1. `sixth_power_free_Q13_prime_inj_into_S51_col`:
   Every `u ∈ Q₁₃_prime` maps injectively via `u ↦ σ(u^4)` into `S₅₁_col`, giving
   `Q₁₃_prime.card ≤ S₅₁_col.card`.
2. `sixth_power_free_sharpened_col_rep_bipartite_bound`:
   Accounts for both `Q₁₃_prime ↪ S₅₁_col` and the exact `((q + 1) / 2).factorization r = 2`
   contribution on `S₅₁_rep_q := S₅₁_rep.filter (fun r => r ∣ (q + 1) / 2)` to prove
   `3 * Q₁₃.card + 2 * Q₂₃.card + 2 * S₅₁_rep_q.card ≤ 4 * S₅₁_col.card + 2 * S₅₁_rep.card + 3`.
3. `sixth_power_free_omega_le_four_col_add_two_rep`:
   Combines (2) with the sixth-power-free slope and support lower bound `443 ≤ ω(N)` to deduce
   `438 + Q₂₃.card + 2 * S₅₁_rep_q.card ≤ 4 * S₅₁_col.card + 2 * S₅₁_rep.card`,
   `219 ≤ 2 * S₅₁_col.card + S₅₁_rep.card`,
   `N.primeFactors.card + 2 * S₅₁_rep_q.card ≤ 4 * S₅₁_col.card + 2 * S₅₁_rep.card + 5`, and
   `S₅₀.card + Q₁₃.card + Q₂₃.card + 2 * S₅₁_rep_q.card ≤ 3 * S₅₁_col.card + S₅₁_rep.card + 4`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private theorem sigma_one_four_local {p : ℕ} (hp : p.Prime) :
    sigma 1 (p ^ 4) = p ^ 4 + p ^ 3 + p ^ 2 + p + 1 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

private theorem sigma_one_prime_local {p : ℕ} (hp : p.Prime) :
    sigma 1 p = p + 1 := by
  rw [← pow_one p, sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

/-- **1. `Q₁₃_prime` Injects into `S₅₁_col`**:
Every prime `u ∈ oneModThreeLargeSources N q` with `¬ q ∣ σ(u^4)` and `(σ(u^4)).Prime`
sends `σ(u^4)` into `S₅₁_col`, and the map `u ↦ σ(u^4)` is strictly increasing on primes,
giving `Q₁₃_prime.card ≤ S₅₁_col.card`. -/
theorem sixth_power_free_Q13_prime_inj_into_S51_col {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    let S₅₁ := (squareSources N).filter (· % 5 = 1)
    let S₅₁_col := S₅₁.filter (fun r => indegAt N q r = 2)
    let Q₁₃_prime := (oneModThreeLargeSources N q).filter
      (fun u => ¬ q ∣ sigma 1 (u ^ 4) ∧ (sigma 1 (u ^ 4)).Prime)
    Q₁₃_prime.card ≤ S₅₁_col.card := by
  intro S₅₁ S₅₁_col Q₁₃_prime
  have hhit := (sixth_power_free_largeSources_hit_S51_col ho hN hq hq4 he hev hfree).1
  refine Finset.card_le_card_of_injOn (fun u => sigma 1 (u ^ 4)) ?_ ?_
  · intro u hu
    obtain ⟨hu_Q13, hnq, hu_sig_prime⟩ := Finset.mem_filter.mp hu
    have hu_lg : u ∈ largeSources N q := (Finset.mem_filter.mp hu_Q13).1
    obtain ⟨r, hr_col, hr_dvd⟩ := hhit u hu_lg hnq
    have hr_S51 : r ∈ S₅₁ := (Finset.mem_filter.mp hr_col).1
    have hr_sq : r ∈ squareSources N := (Finset.mem_filter.mp hr_S51).1
    have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hr_sq).1
    have hr_eq : r = sigma 1 (u ^ 4) := (Nat.prime_dvd_prime_iff_eq hr_prime hu_sig_prime).mp hr_dvd
    dsimp only
    rwa [← hr_eq]
  · intro u₁ hu₁ u₂ hu₂ heq
    dsimp only at heq
    have hu₁_prime : u₁.Prime :=
      Nat.prime_of_mem_primeFactors
        (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hu₁).1).1).1
    have hu₂_prime : u₂.Prime :=
      Nat.prime_of_mem_primeFactors
        (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hu₂).1).1).1
    rw [sigma_one_four_local hu₁_prime, sigma_one_four_local hu₂_prime] at heq
    rcases lt_trichotomy u₁ u₂ with hlt | rfl | hgt
    · have h2 : u₁ ^ 2 < u₂ ^ 2 := Nat.pow_lt_pow_left hlt (by decide)
      have h3 : u₁ ^ 3 < u₂ ^ 3 := Nat.pow_lt_pow_left hlt (by decide)
      have h4 : u₁ ^ 4 < u₂ ^ 4 := Nat.pow_lt_pow_left hlt (by decide)
      omega
    · rfl
    · have h2 : u₂ ^ 2 < u₁ ^ 2 := Nat.pow_lt_pow_left hgt (by decide)
      have h3 : u₂ ^ 3 < u₁ ^ 3 := Nat.pow_lt_pow_left hgt (by decide)
      have h4 : u₂ ^ 4 < u₁ ^ 4 := Nat.pow_lt_pow_left hgt (by decide)
      omega

/-- **2. Sharpened Collision/Repeat Bipartite Capacity Bound**:
Splits `S₅₁` into `S₅₁_col` (`indegAt = 2`) and `S₅₁_rep` (`indegAt = 1`), tracks the
`r ∣ (q + 1) / 2` repeat subset `S₅₁_rep_q` (each contributing `2` to the `(q + 1) / 2`
multiplicity sum), and injects `Q₁₃_prime` into `S₅₁_col` to prove
`3 * Q₁₃.card + 2 * Q₂₃.card + 2 * S₅₁_rep_q.card ≤ 4 * S₅₁_col.card + 2 * S₅₁_rep.card + 3`. -/
theorem sixth_power_free_sharpened_col_rep_bipartite_bound {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    let S₅₁ := (squareSources N).filter (· % 5 = 1)
    let S₅₁_col := S₅₁.filter (fun r => indegAt N q r = 2)
    let S₅₁_rep := S₅₁.filter (fun r => indegAt N q r = 1)
    let S₅₁_rep_q := S₅₁_rep.filter (fun r => r ∣ (q + 1) / 2)
    let Q₁₃ := oneModThreeLargeSources N q
    let Q₂₃ := twoModThreeLargeSources N q
    3 * Q₁₃.card + 2 * Q₂₃.card + 2 * S₅₁_rep_q.card ≤
      4 * S₅₁_col.card + 2 * S₅₁_rep.card + 3 := by
  intro S₅₁ S₅₁_col S₅₁_rep S₅₁_rep_q Q₁₃ Q₂₃
  have hq_prime := Nat.prime_of_mem_primeFactors hq
  have hq_odd : Odd q := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hq)
  have hq1 : N.factorization q = 1 := sixth_power_free_euler_exponent_one ho hN hq he hfree
  have h3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  have hlg4 : ∀ u ∈ largeSources N q, N.factorization u = 4 :=
    (three_free_sixthPowerFree_forces_147_largeSources ho hN hq hq4 he hev h3 hfree).1
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
  obtain ⟨hQ13_dich, hQ23_dich⟩ :=
    sixth_power_free_quartic_cardFactors_mod_three_dichotomy ho hN hq hq4 he hev hfree
  let Q₁₃_q := Q₁₃.filter (fun u => q ∣ sigma 1 (u ^ 4))
  let Q₁₃_nq := Q₁₃.filter (fun u => ¬ q ∣ sigma 1 (u ^ 4))
  let Q₁₃_prime := Q₁₃_nq.filter (fun u => (sigma 1 (u ^ 4)).Prime)
  let Q₁₃_comp := Q₁₃_nq.filter (fun u => ¬ (sigma 1 (u ^ 4)).Prime)
  have hQ_parts : largeSources N q = Q₁₃ ∪ Q₂₃ := by
    ext r
    simp only [Q₁₃, Q₂₃, oneModThreeLargeSources, twoModThreeLargeSources,
      Finset.mem_union, Finset.mem_filter]
    by_cases h : r % 3 = 1 <;> tauto
  have hQ_disj : Disjoint Q₁₃ Q₂₃ := by
    apply Finset.disjoint_left.mpr
    intro r h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
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
    simp only [Q₁₃_prime, Q₁₃_comp, Finset.mem_union, Finset.mem_filter]
    by_cases h : (sigma 1 (u ^ 4)).Prime <;> tauto
  have hQ13_nq_disj : Disjoint Q₁₃_prime Q₁₃_comp := by
    apply Finset.disjoint_left.mpr
    intro u h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
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
  have hQ13_prime_le : Q₁₃_prime.card ≤ S₅₁_col.card := by
    have hinj := sixth_power_free_Q13_prime_inj_into_S51_col ho hN hq hq4 he hev hfree
    have heq_set :
        Q₁₃_prime =
          (oneModThreeLargeSources N q).filter
            (fun u => ¬ q ∣ sigma 1 (u ^ 4) ∧ (sigma 1 (u ^ 4)).Prime) := by
      ext u
      simp only [Q₁₃_prime, Q₁₃_nq, Q₁₃, Finset.mem_filter]
      tauto
    rw [heq_set]
    exact hinj
  have hsum_split :
      (∑ u ∈ largeSources N q, cardFactors (sigma 1 (u ^ 4))) =
        (∑ u ∈ Q₁₃_q, cardFactors (sigma 1 (u ^ 4))) +
          (∑ u ∈ Q₁₃_prime, cardFactors (sigma 1 (u ^ 4))) +
          (∑ u ∈ Q₁₃_comp, cardFactors (sigma 1 (u ^ 4))) +
          ∑ u ∈ Q₂₃, cardFactors (sigma 1 (u ^ 4)) := by
    rw [hQ_parts, Finset.sum_union hQ_disj,
      hQ13_parts, Finset.sum_union hQ13_disj,
      hQ13_nq_parts, Finset.sum_union hQ13_nq_disj]
    ring
  have hlb_q : Q₁₃_q.card ≤ ∑ u ∈ Q₁₃_q, cardFactors (sigma 1 (u ^ 4)) := by
    calc
      Q₁₃_q.card = ∑ _u ∈ Q₁₃_q, 1 := by simp [Finset.sum_const]
      _ ≤ ∑ u ∈ Q₁₃_q, cardFactors (sigma 1 (u ^ 4)) := by
            refine Finset.sum_le_sum fun u hu => ?_
            have hu_lg := (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).1
            have hu_prime : u.Prime :=
              Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hu_lg).1
            have hu2 : 2 ≤ u := hu_prime.two_le
            have hgt1 : 1 < sigma 1 (u ^ 4) := by
              rw [sigma_one_four_local hu_prime]
              have h4 : 2 ^ 4 ≤ u ^ 4 := Nat.pow_le_pow_left hu2 4
              omega
            exact cardFactors_pos_iff_one_lt.mpr hgt1
  have hlb_prime : Q₁₃_prime.card ≤ ∑ u ∈ Q₁₃_prime, cardFactors (sigma 1 (u ^ 4)) := by
    calc
      Q₁₃_prime.card = ∑ _u ∈ Q₁₃_prime, 1 := by simp [Finset.sum_const]
      _ ≤ ∑ u ∈ Q₁₃_prime, cardFactors (sigma 1 (u ^ 4)) := by
            refine Finset.sum_le_sum fun u hu => ?_
            have hu_sig_prime := (Finset.mem_filter.mp hu).2
            rw [cardFactors_apply_prime hu_sig_prime]
  have hlb_comp : 3 * Q₁₃_comp.card ≤ ∑ u ∈ Q₁₃_comp, cardFactors (sigma 1 (u ^ 4)) := by
    calc
      3 * Q₁₃_comp.card = ∑ _u ∈ Q₁₃_comp, 3 := by simp [Finset.sum_const, Nat.mul_comm]
      _ ≤ ∑ u ∈ Q₁₃_comp, cardFactors (sigma 1 (u ^ 4)) := by
            refine Finset.sum_le_sum fun u hu => ?_
            obtain ⟨hu_nq, hu_not_prime⟩ := Finset.mem_filter.mp hu
            obtain ⟨hu_Q13, hu_nq_dvd⟩ := Finset.mem_filter.mp hu_nq
            have hbranch := (hQ13_dich u hu_Q13 hu_nq_dvd).2.2
            exact hbranch.resolve_left hu_not_prime
  have hlb_Q23 : 2 * Q₂₃.card ≤ ∑ u ∈ Q₂₃, cardFactors (sigma 1 (u ^ 4)) := by
    calc
      2 * Q₂₃.card = ∑ _u ∈ Q₂₃, 2 := by simp [Finset.sum_const, Nat.mul_comm]
      _ ≤ ∑ u ∈ Q₂₃, cardFactors (sigma 1 (u ^ 4)) := by
            refine Finset.sum_le_sum fun u hu => (hQ23_dich u hu).2.2.2.2
  omega

/-- **3. Sixth-Power-Free `ω(N)` and Slack Pinch on `4 * S₅₁_col + 2 * S₅₁_rep`**:
Combines Theorem 2 with `ω(N) ≤ 3 * Q₁₃ + Q₂₃ + 2`, `ω(N) = 1 + S₅₁ + S₅₀ + Q₁₃ + Q₂₃`,
`S₅₁ = S₅₁_col + S₅₁_rep`, and `443 ≤ ω(N)` to pinch the collision/repeat slack. -/
theorem sixth_power_free_omega_le_four_col_add_two_rep {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    let S₅₀ := (squareSources N).filter (· % 5 ≠ 1)
    let S₅₁ := (squareSources N).filter (· % 5 = 1)
    let S₅₁_col := S₅₁.filter (fun r => indegAt N q r = 2)
    let S₅₁_rep := S₅₁.filter (fun r => indegAt N q r = 1)
    let S₅₁_rep_q := S₅₁_rep.filter (fun r => r ∣ (q + 1) / 2)
    let Q₁₃ := oneModThreeLargeSources N q
    let Q₂₃ := twoModThreeLargeSources N q
    438 + Q₂₃.card + 2 * S₅₁_rep_q.card ≤ 4 * S₅₁_col.card + 2 * S₅₁_rep.card ∧
    219 ≤ 2 * S₅₁_col.card + S₅₁_rep.card ∧
    N.primeFactors.card + 2 * S₅₁_rep_q.card ≤ 4 * S₅₁_col.card + 2 * S₅₁_rep.card + 5 ∧
    S₅₀.card + Q₁₃.card + Q₂₃.card + 2 * S₅₁_rep_q.card ≤
      3 * S₅₁_col.card + S₅₁_rep.card + 4 := by
  intro S₅₀ S₅₁ S₅₁_col S₅₁_rep S₅₁_rep_q Q₁₃ Q₂₃
  have hcap :=
    sixth_power_free_sharpened_col_rep_bipartite_bound ho hN hq hq4 he hev hfree
  obtain ⟨hω_eq, _, hω_le⟩ :=
    sixth_power_free_omega_and_total_identities ho hN hq hq4 he hev hfree
  have hS51_split : S₅₁.card = S₅₁_col.card + S₅₁_rep.card :=
    (sixth_power_free_S51_collision_repeat_split ho hN hq hq4 he hev hfree).2.2.1
  have h443 : 443 ≤ N.primeFactors.card :=
    (sixth_power_free_collision_excess_ge_221 ho hN hq hq4 he hev hfree).1
  dsimp only [S₅₀, S₅₁, S₅₁_col, S₅₁_rep, S₅₁_rep_q, Q₁₃, Q₂₃] at *
  change 3 * (oneModThreeLargeSources N q).card + 2 * (twoModThreeLargeSources N q).card +
      2 * (((squareSources N).filter (· % 5 = 1)).filter (fun r => indegAt N q r = 1) |>.filter
        (fun r => r ∣ (q + 1) / 2)).card ≤
    4 * (((squareSources N).filter (· % 5 = 1)).filter (fun r => indegAt N q r = 2)).card +
      2 * (((squareSources N).filter (· % 5 = 1)).filter (fun r => indegAt N q r = 1)).card + 3 at hcap
  change N.primeFactors.card =
    1 + ((squareSources N).filter (· % 5 = 1)).card + ((squareSources N).filter (· % 5 ≠ 1)).card +
      (oneModThreeLargeSources N q).card + (twoModThreeLargeSources N q).card at hω_eq
  change N.primeFactors.card ≤
    3 * (oneModThreeLargeSources N q).card + (twoModThreeLargeSources N q).card + 2 at hω_le
  refine ⟨by omega, by omega, by omega, by omega⟩

end OddPerfect
