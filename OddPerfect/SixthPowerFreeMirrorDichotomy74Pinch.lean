module

public import OddPerfect.SixthPowerFreePureCollisionRankCap
public import OddPerfect.SixthPowerFreeDropExcessPinch
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sixth-Power-Free Mirror Dichotomy & Unconditional `74 ≤ |S₅₁_col|` Pinch (`OddPerfect.SixthPowerFreeMirrorDichotomy74Pinch`)

Combines the pure-collision rank/excess caps (`SixthPowerFreePureCollisionRankCap`,
`SixthPowerFreeDropExcessPinch`) with the Euler-prime split on `∑ u ∈ Q, v_q(σ(u⁴)) ∈ {0, 1}` to
prove:

1. `sixth_power_free_pure_collision_total_and_drop_caps`:
   Pure `S₅₁_col` caps on `cardFactors N`, `localRepeatExcess N q + collisionExcess N q`, and
   `∑ p ∈ N.primeFactors, (cardFactors N - cardFactors (componentIndex N p))`, together with the
   `Q₁₃_comp_free` and `Q₂₃` bonus terms.
2. `sixth_power_free_unconditional_74_S51_col_and_dichotomy`:
   Eliminates the `S₅₁_col.card = 73` extremal boundary unconditionally in the sixth-power-free
   regime (`74 ≤ S₅₁_col.card` and `148 ≤ 2 * S₅₁_col.card`), and establishes the global
   unconditional dichotomy: every odd perfect number failing `74 ≤ S₅₁_col.card`,
   `N.primeFactors.card ≤ 6 * S₅₁_col.card + 5`, or `cardFactors N ≤ 16 * S₅₁_col.card + 11`
   is divisible by a sixth power of a prime.
-/

public section

namespace OddPerfect

open ArithmeticFunction Finset

private theorem sigma_one_prime_local {p : ℕ} (hp : p.Prime) :
    sigma 1 p = p + 1 := by
  rw [← pow_one p, sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

private theorem sigma_one_sq_local {p : ℕ} (hp : p.Prime) :
    sigma 1 (p ^ 2) = p ^ 2 + p + 1 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

/-- **1. Pure Collision Total-Multiplicity and Component-Drop Caps**:
Isolates pure `S₅₁_col` upper bounds (with `Q₁₃_comp_free` and `Q₂₃` bonus slack) on
`cardFactors N`, `localRepeatExcess N q + collisionExcess N q`, and the total component-index
drop `∑ p ∈ N.primeFactors, (cardFactors N - cardFactors (componentIndex N p))`. -/
theorem sixth_power_free_pure_collision_total_and_drop_caps {N q : ℕ}
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
    cardFactors N + 16 * Q₁₃_comp_free.card + 12 * Q₂₃.card ≤ 16 * S₅₁_col.card + 11 ∧
    cardFactors N ≤ 16 * S₅₁_col.card + 11 ∧
    localRepeatExcess N q + collisionExcess N q + 10 * Q₁₃_comp_free.card + 7 * Q₂₃.card ≤
      10 * S₅₁_col.card + 6 ∧
    localRepeatExcess N q + collisionExcess N q ≤ 10 * S₅₁_col.card + 6 ∧
    (∑ p ∈ N.primeFactors, (cardFactors N - cardFactors (componentIndex N p))) +
      26 * Q₁₃_comp_free.card + 19 * Q₂₃.card ≤ 26 * S₅₁_col.card + 18 ∧
    (∑ p ∈ N.primeFactors, (cardFactors N - cardFactors (componentIndex N p))) ≤
      26 * S₅₁_col.card + 18 := by
  intro S₅₁ S₅₁_col S₅₁_rep S₅₁_rep_src Q₁₃ Q₂₃ repFib Q₁₃_comp Q₁₃_comp_free
  let S := squareSources N
  let S₅₀ := S.filter (· % 5 ≠ 1)
  have hS_parts : S = S₅₁ ∪ S₅₀ := by
    ext r
    simp only [S, S₅₁, S₅₀, Finset.mem_union, Finset.mem_filter]
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
  obtain ⟨_, hΩ_eq, _⟩ :=
    sixth_power_free_omega_and_total_identities ho hN hq hq4 he hev hfree
  change cardFactors N = 1 + 2 * (S₅₁.card + S₅₀.card) + 4 * (Q₁₃.card + Q₂₃.card) at hΩ_eq
  obtain ⟨_, _, hS_cap, hω_cap, _, _, _, _⟩ :=
    sixth_power_free_pure_collision_repeat_and_rank_bounds ho hN hq hq4 he hev hfree
  change S.card + 4 * Q₁₃_comp_free.card + 4 * Q₂₃.card ≤ 4 * S₅₁_col.card + 3 at hS_cap
  change N.primeFactors.card + 6 * Q₁₃_comp_free.card + 5 * Q₂₃.card ≤ 6 * S₅₁_col.card + 5 at hω_cap
  have hQ_cap : Q₁₃.card + 2 * Q₁₃_comp_free.card + 2 * Q₂₃.card ≤ 2 * S₅₁_col.card + 1 :=
    (sixth_power_free_Q13_comp_free_and_rep_bounds ho hN hq hq4 he hev hfree).2.2.2.2.1
  have hME_eq : localRepeatExcess N q + collisionExcess N q = S.card + 3 * (largeSources N q).card :=
    (sixth_power_free_excess_and_drop_partition ho hN hq hq4 he hev hfree).1
  have hdrop_eq := sum_componentIndex_drop_eq_primeFactors_add_two_mul_excess ho hN hq hq4 he hev
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- **2. Unconditional Sixth-Power-Free `74 ≤ |S₅₁_col|` and Mirror Dichotomy**:
Eliminates the extremal `S₅₁_col.card = 73` case via the Euler-prime dichotomy on
`∑ u ∈ largeSources N q, (sigma 1 (u ^ 4)).factorization q ∈ {0, 1}`:
- If `0`, no `+ 1` Euler correction enters the bipartite `S₅₁` multiplicity identity, giving
  `Q₁₃.card + 2 * Q₂₃.card ≤ 2 * S₅₁_col.card` and hence `147 ≤ 2 * S₅₁_col.card`.
- If `1`, `q` divides no `sigma 1 (s ^ 2)` for `s ∈ squareSources N`, so the Vieta mod-3 root-slot
  target set collapses from `insert q Q₁₃` to `Q₁₃`, sharpening `|S| ≤ 2 * |Q₁₃| + 1` to
  `|S| ≤ 2 * |Q₁₃|` and yielding `439 ≤ 6 * S₅₁_col.card`. -/
theorem sixth_power_free_unconditional_74_S51_col_and_dichotomy {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) :
    ∃ q ∈ N.primeFactors,
      q % 4 = 1 ∧ N.factorization q % 4 = 1 ∧
      (let S₅₁ := (squareSources N).filter (· % 5 = 1)
       let S₅₁_col := S₅₁.filter (fun r => indegAt N q r = 2)
       ((∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) →
         74 ≤ S₅₁_col.card ∧ 148 ≤ 2 * S₅₁_col.card) ∧
       ((S₅₁_col.card < 74 ∨
         6 * S₅₁_col.card + 6 ≤ N.primeFactors.card ∨
         16 * S₅₁_col.card + 12 ≤ cardFactors N) →
         ∃ p : ℕ, p.Prime ∧ p ^ 6 ∣ N)) := by
  obtain ⟨q, hq, hq4, he, hev⟩ := euler_exponents ho hN
  refine ⟨q, hq, hq4, he, ?_⟩
  dsimp only
  have h74_impl :
      (∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) →
        74 ≤ ((squareSources N).filter (· % 5 = 1) |>.filter (fun r => indegAt N q r = 2)).card ∧
        148 ≤ 2 * ((squareSources N).filter (· % 5 = 1) |>.filter (fun r => indegAt N q r = 2)).card := by
    intro hfree
    let S := squareSources N
    let S₅₁ := S.filter (· % 5 = 1)
    let S₅₀ := S.filter (· % 5 ≠ 1)
    let S₅₁_col := S₅₁.filter (fun r => indegAt N q r = 2)
    let S₅₁_rep := S₅₁.filter (fun r => indegAt N q r = 1)
    let S₅₁_rep_q := S₅₁_rep.filter (fun r => r ∣ (q + 1) / 2)
    let S₅₁_rep_src := S₅₁_rep.filter (fun r => ¬ r ∣ (q + 1) / 2)
    let Q₁₃ := oneModThreeLargeSources N q
    let Q₂₃ := twoModThreeLargeSources N q
    let repFib := fun u => S₅₁_rep_src.filter (fun r => r ∣ sigma 1 (u ^ 4))
    have h3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
    have hq1 : N.factorization q = 1 := sixth_power_free_euler_exponent_one ho hN hq he hfree
    have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hq_odd : Odd q := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hq)
    obtain ⟨hlg4, h147, _⟩ :=
      three_free_sixthPowerFree_forces_147_largeSources ho hN hq hq4 he hev h3 hfree
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
    have h74_core : 74 ≤ S₅₁_col.card := by
      by_cases hq_lg : ∑ u ∈ largeSources N q, (sigma 1 (u ^ 4)).factorization q = 0
      · obtain ⟨hfib_sum, hlb_all, hlb_Q23, _, _, _, _⟩ :=
          sixth_power_free_quartic_double_Q23_collision_pinch ho hN hq hq4 he hev hfree
        change (∑ u ∈ largeSources N q, (repFib u).card) = S₅₁_rep_src.card at hfib_sum
        have hfib_split :
            (∑ u ∈ largeSources N q, (repFib u).card) =
              (∑ u ∈ Q₁₃, (repFib u).card) + ∑ u ∈ Q₂₃, (repFib u).card := by
          rw [hQ_parts, Finset.sum_union hQ_disj]
        have hcf_split :
            (∑ u ∈ largeSources N q, cardFactors (sigma 1 (u ^ 4))) =
              (∑ u ∈ Q₁₃, cardFactors (sigma 1 (u ^ 4))) +
                ∑ u ∈ Q₂₃, cardFactors (sigma 1 (u ^ 4)) := by
          rw [hQ_parts, Finset.sum_union hQ_disj]
        have hsum_Q13 :
            2 * (∑ u ∈ Q₁₃, (repFib u).card) + Q₁₃.card ≤
              ∑ u ∈ Q₁₃, cardFactors (sigma 1 (u ^ 4)) := by
          calc
            2 * (∑ u ∈ Q₁₃, (repFib u).card) + Q₁₃.card
                = (∑ u ∈ Q₁₃, 2 * (repFib u).card) + ∑ _u ∈ Q₁₃, 1 := by
                    rw [Finset.mul_sum, Finset.sum_const, smul_eq_mul, mul_one]
            _ = ∑ u ∈ Q₁₃, (2 * (repFib u).card + 1) := Finset.sum_add_distrib.symm
            _ ≤ ∑ u ∈ Q₁₃, cardFactors (sigma 1 (u ^ 4)) := by
                  refine Finset.sum_le_sum fun u hu => hlb_all u (Finset.mem_filter.mp hu).1
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
            2 * S₅₁_rep_src.card + Q₁₃.card + 2 * Q₂₃.card ≤
              ∑ u ∈ largeSources N q, cardFactors (sigma 1 (u ^ 4)) := by
          omega
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
          obtain ⟨hr_S51, _⟩ := Finset.mem_filter.mp hr_rep
          have hr_sq : r ∈ squareSources N := (Finset.mem_filter.mp hr_S51).1
          obtain ⟨hr_N, _, hr_exp2⟩ := Finset.mem_filter.mp hr_sq
          have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr_N
          have hmut :=
            (euler_linear_and_exponent_two_mutual_exclusion ho hN hq hq4 he hev).2 r hr_N hr_exp2
          obtain ⟨_, _, p, _, hr2_dvd_p, hnot_other⟩ := hmut.resolve_left (fun h => by omega)
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
              rw [hsig_q, Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) hhalf_ne0,
                Finsupp.add_apply]
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
        omega
      · have hparts : N.primeFactors = insert q (S ∪ largeSources N q) := by
          ext r
          simp only [Finset.mem_insert, Finset.mem_union, S, squareSources, largeSources,
            Finset.mem_filter]
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
          · have := (Finset.mem_filter.mp hsq).2.2
            omega
          · exact (Finset.mem_filter.mp hlg).2.2.1 rfl
        have hdisj : Disjoint S (largeSources N q) := by
          apply Finset.disjoint_left.mpr
          intro r hs hl
          have htwo := (Finset.mem_filter.mp hs).2.2
          have hlarge := (Finset.mem_filter.mp hl).2.2.2
          omega
        have hsum_q := factorization_eq_sum_sigma_factorizations hN hq_odd hq_prime
        have hsum_lg_eq :
            ∑ u ∈ largeSources N q, (sigma 1 (u ^ 4)).factorization q =
              ∑ r ∈ largeSources N q, (sigma 1 (r ^ N.factorization r)).factorization q := by
          refine Finset.sum_congr rfl fun u hu => ?_
          rw [hlg4 u hu]
        have hsum_split :
            ∑ r ∈ N.primeFactors, (sigma 1 (r ^ N.factorization r)).factorization q =
              (sigma 1 (q ^ N.factorization q)).factorization q +
                (∑ s ∈ S, (sigma 1 (s ^ N.factorization s)).factorization q) +
                ∑ u ∈ largeSources N q, (sigma 1 (u ^ N.factorization u)).factorization q := by
          rw [hparts, Finset.sum_insert hq_notin, Finset.sum_union hdisj]
          ring
        have hS_sum_q0 : ∑ s ∈ S, (sigma 1 (s ^ N.factorization s)).factorization q = 0 := by
          omega
        have hsq_not_dvd_q : ∀ s ∈ S, ¬ q ∣ sigma 1 (s ^ 2) := by
          intro s hs hd
          have hs_mem : s ∈ N.primeFactors := (Finset.mem_filter.mp hs).1
          have hs_prime : s.Prime := Nat.prime_of_mem_primeFactors hs_mem
          have hs_exp2 : N.factorization s = 2 := (Finset.mem_filter.mp hs).2.2
          have hsig_ne0 : sigma 1 (s ^ 2) ≠ 0 := by
            rw [sigma_one_sq_local hs_prime]
            positivity
          have hpos : 1 ≤ (sigma 1 (s ^ 2)).factorization q :=
            (hq_prime.pow_dvd_iff_le_factorization hsig_ne0).mp (by simpa using hd)
          have hterm_le :
              (sigma 1 (s ^ N.factorization s)).factorization q ≤
                ∑ x ∈ S, (sigma 1 (x ^ N.factorization x)).factorization q :=
            Finset.single_le_sum
              (f := fun x => (sigma 1 (x ^ N.factorization x)).factorization q)
              (fun _ _ => Nat.zero_le _) hs
          rw [hs_exp2] at hterm_le
          omega
        have hS1_empty : squareSourcesOne N = ∅ := by
          have hb := squareSourcesOne_card_le_three_exponent hN
          have hz : N.factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd h3
          exact Finset.card_eq_zero.mp (by omega)
        have hs_props : ∀ s ∈ S, s.Prime ∧ 3 < s ∧ N.factorization s = 2 ∧ s % 3 = 2 := by
          intro s hs
          obtain ⟨hs_mem, hs3, hs_exp2⟩ := Finset.mem_filter.mp hs
          have hs_prime : s.Prime := Nat.prime_of_mem_primeFactors hs_mem
          have hs_odd : Odd s := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hs_mem)
          have hs_gt3 : 3 < s := by
            have := hs_prime.two_le
            have := Nat.odd_iff.mp hs_odd
            omega
          have hs_mod0 : s % 3 ≠ 0 := fun h0 =>
            h3 ((Nat.dvd_of_mod_eq_zero h0).trans (Nat.dvd_of_mem_primeFactors hs_mem))
          have hs_mod1 : s % 3 ≠ 1 := by
            intro h1
            have hmem1 : s ∈ squareSourcesOne N := Finset.mem_filter.mpr ⟨hs, h1⟩
            simp [hS1_empty] at hmem1
          exact ⟨hs_prime, hs_gt3, hs_exp2, by omega⟩
        have hs_sub : S ⊆ N.primeFactors := Finset.filter_subset _ _
        have localDiv : ∀ s ∈ S, normalizedSquareSum s ∣ sigma 1 (s ^ N.factorization s) := by
          intro s hs
          obtain ⟨hs_prime, hs_gt3, hs_exp2, _⟩ := hs_props s hs
          rw [hs_exp2]
          exact normalizedSquareSum_dvd_sigma hs_prime hs_gt3
        have cover : ∀ s ∈ S, (normalizedSquareSum s).primeFactors ⊆ Q₁₃ := by
          intro s hs w hw
          obtain ⟨hs_prime, hs_gt3, hs_exp2, _⟩ := hs_props s hs
          obtain ⟨hw_prime, hw_dvd, _⟩ := Nat.mem_primeFactors.mp hw
          have hd := hw_dvd.trans (localDiv s hs)
          have hpoly := hd
          rw [hs_exp2, sigma_one_sq_local hs_prime] at hpoly
          have hmod := (prime_dvd_sq_add_self_add_one hw_prime hpoly).resolve_left
            (fun h => three_not_dvd_normalizedSquareSum hs_prime hs_gt3 (h ▸ hw_dvd))
          have hw_odd : Odd w := hw_prime.odd_of_ne_two (by omega)
          have hwN : w ∣ N := by
            apply dvd_perfect_of_exact_prime_pow hN hs_prime (Nat.ordProj_dvd _ _) _ hw_prime hw_odd
            · rwa [← sigma_one_apply]
            · rw [hs_prime.pow_dvd_iff_le_factorization hN.2.ne']
              omega
          have hw_mem := Nat.mem_primeFactors.mpr ⟨hw_prime, hwN, hN.2.ne'⟩
          have hwq : w ≠ q := by
            intro hEq
            subst hEq
            exact hsq_not_dvd_q s hs (hs_exp2 ▸ hd)
          have hw3 : w ≠ 3 := by omega
          have hw_ne2 : N.factorization w ≠ 2 := by
            intro hex
            have hmem1 : w ∈ squareSourcesOne N :=
              Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hw_mem, hw3, hex⟩, hmod⟩
            simp [hS1_empty] at hmem1
          have hw_pos : 0 < N.factorization w :=
            (hw_prime.dvd_iff_one_le_factorization hN.2.ne').mp hwN
          obtain ⟨k, hk⟩ := hev w hwq
          exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hw_mem, hw3, hwq, by omega⟩, hmod⟩
        have hQ13_sub : Q₁₃ ⊆ N.primeFactors :=
          (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
        have upper := sum_cardFactors_le_target_exponents hN S Q₁₃ normalizedSquareSum
          hs_sub localDiv cover (fun _ hw => ⟨Nat.prime_of_mem_primeFactors (hQ13_sub hw),
            ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors (hQ13_sub hw))⟩)
        have hQ13_sum : ∑ w ∈ Q₁₃, N.factorization w = 4 * Q₁₃.card := by
          calc
            ∑ w ∈ Q₁₃, N.factorization w = ∑ _w ∈ Q₁₃, (4 : ℕ) :=
              Finset.sum_congr rfl fun w hw => hlg4 w (Finset.mem_filter.mp hw).1
            _ = 4 * Q₁₃.card := by simp [Finset.sum_const, Nat.mul_comm]
        rw [hQ13_sum] at upper
        let A₁ := S.filter fun u => (normalizedSquareSum u).Prime
        let A₂ := S.filter fun u => cardFactors (normalizedSquareSum u) = 2
        let A₃ := S.filter fun u => 3 ≤ cardFactors (normalizedSquareSum u)
        have hS_part3 : S = A₁ ∪ A₂ ∪ A₃ := by
          ext u
          simp only [A₁, A₂, A₃, Finset.mem_union, Finset.mem_filter]
          constructor
          · intro hu
            obtain ⟨hup, hu3, _, _⟩ := hs_props u hu
            have hpos := cardFactors_pos_iff_one_lt.mpr (normalizedSquareSum_one_lt hup hu3)
            by_cases h1 : cardFactors (normalizedSquareSum u) = 1
            · exact Or.inl (Or.inl ⟨hu, cardFactors_eq_one_iff_prime.mp h1⟩)
            · by_cases h2 : cardFactors (normalizedSquareSum u) = 2
              · exact Or.inl (Or.inr ⟨hu, h2⟩)
              · exact Or.inr ⟨hu, by omega⟩
          · rintro ((⟨hu, _⟩ | ⟨hu, _⟩) | ⟨hu, _⟩) <;> exact hu
        have hdis_1_2 : Disjoint A₁ A₂ := by
          apply Finset.disjoint_left.mpr
          intro u h1 h2
          have hp1 := cardFactors_eq_one_iff_prime.mpr (Finset.mem_filter.mp h1).2
          have hp2 := (Finset.mem_filter.mp h2).2
          omega
        have hdis_12_3 : Disjoint (A₁ ∪ A₂) A₃ := by
          apply Finset.disjoint_left.mpr
          intro u h12 h3_mem
          have hge3 := (Finset.mem_filter.mp h3_mem).2
          rcases Finset.mem_union.mp h12 with h1 | h2
          · have hp1 := cardFactors_eq_one_iff_prime.mpr (Finset.mem_filter.mp h1).2
            omega
          · have hp2 := (Finset.mem_filter.mp h2).2
            omega
        have hS_card3 : S.card = A₁.card + A₂.card + A₃.card := by
          rw [hS_part3, Finset.card_union_of_disjoint hdis_12_3, Finset.card_union_of_disjoint hdis_1_2]
        have hsum_S_lb : A₁.card + 2 * A₂.card + 3 * A₃.card ≤
            ∑ u ∈ S, cardFactors (normalizedSquareSum u) := by
          rw [hS_part3, Finset.sum_union hdis_12_3, Finset.sum_union hdis_1_2]
          have h1 : A₁.card ≤ ∑ u ∈ A₁, cardFactors (normalizedSquareSum u) := by
            calc
              A₁.card = ∑ _u ∈ A₁, 1 := by simp
              _ ≤ ∑ u ∈ A₁, cardFactors (normalizedSquareSum u) := by
                    refine Finset.sum_le_sum fun u hu => ?_
                    rw [cardFactors_eq_one_iff_prime.mpr (Finset.mem_filter.mp hu).2]
          have h2 : 2 * A₂.card ≤ ∑ u ∈ A₂, cardFactors (normalizedSquareSum u) := by
            calc
              2 * A₂.card = ∑ _u ∈ A₂, 2 := by simp [Nat.mul_comm]
              _ ≤ ∑ u ∈ A₂, cardFactors (normalizedSquareSum u) := by
                    refine Finset.sum_le_sum fun u hu => ?_
                    rw [(Finset.mem_filter.mp hu).2]
          have h3_lb : 3 * A₃.card ≤ ∑ u ∈ A₃, cardFactors (normalizedSquareSum u) := by
            calc
              3 * A₃.card = ∑ _u ∈ A₃, 3 := by simp [Nat.mul_comm]
              _ ≤ ∑ u ∈ A₃, cardFactors (normalizedSquareSum u) :=
                    Finset.sum_le_sum fun u hu => (Finset.mem_filter.mp hu).2
          omega
        let Up := (S ×ˢ Q₁₃).filter fun uw => uw.1 < uw.2 ∧ uw.2 ∣ normalizedSquareSum uw.1
        have hA12_sub : A₁ ∪ A₂ ⊆ Up.image Prod.fst := by
          intro u hu
          rw [Finset.mem_image]
          rcases Finset.mem_union.mp hu with hu1 | hu2
          · obtain ⟨huS, hwp⟩ := Finset.mem_filter.mp hu1
            obtain ⟨hup, _, _, hu_mod⟩ := hs_props u huS
            let w := normalizedSquareSum u
            have hwT : w ∈ Q₁₃ := cover u huS (Nat.mem_primeFactors.mpr ⟨hwp, dvd_rfl, hwp.ne_zero⟩)
            have hu_ne1 : u % 3 ≠ 1 := by omega
            have hlt : u < w := by
              have hnorm : w = u ^ 2 + u + 1 := by simp [w, normalizedSquareSum, hu_ne1]
              rw [hnorm]
              nlinarith [hup.one_lt]
            exact ⟨(u, w), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huS, hwT⟩, hlt, dvd_rfl⟩, rfl⟩
          · obtain ⟨huS, hcard2⟩ := Finset.mem_filter.mp hu2
            obtain ⟨_, _, _, hu_mod⟩ := hs_props u huS
            have hu_ne1 : u % 3 ≠ 1 := by omega
            obtain ⟨w, hw_pf, huw⟩ := squareSourcesTwo_semiprime_exists_gt hu_ne1 hcard2
            have hwT : w ∈ Q₁₃ := cover u huS hw_pf
            have hwdvd : w ∣ normalizedSquareSum u := Nat.dvd_of_mem_primeFactors hw_pf
            exact ⟨(u, w), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huS, hwT⟩, huw, hwdvd⟩, rfl⟩
        have hUp_lower : A₁.card + A₂.card ≤ Up.card := by
          rw [← Finset.card_union_of_disjoint hdis_1_2]
          exact (Finset.card_le_card hA12_sub).trans Finset.card_image_le
        have hUp_fiber : Up.card = ∑ w ∈ Q₁₃, (Up.filter fun uw => uw.2 = w).card := by
          apply Finset.card_eq_sum_card_fiberwise
          intro uw huw
          exact (Finset.mem_product.mp (Finset.mem_filter.mp huw).1).2
        have hfiber_le : ∀ w ∈ Q₁₃, (Up.filter fun uw => uw.2 = w).card ≤ 1 := by
          intro w hw
          have hw_prime : w.Prime := Nat.prime_of_mem_primeFactors (hQ13_sub hw)
          have hw1 : w % 3 = 1 := (Finset.mem_filter.mp hw).2
          have h1 :
              (Up.filter fun uw => uw.2 = w).card ≤
                (S.filter fun v => v < w ∧ w ∣ normalizedSquareSum v).card := by
            apply Finset.card_le_card_of_injOn Prod.fst
            · intro uw huw
              obtain ⟨huw_Up, rfl⟩ := Finset.mem_filter.mp huw
              obtain ⟨huw_prod, hlt, hdvd⟩ := Finset.mem_filter.mp huw_Up
              exact Finset.mem_filter.mpr ⟨(Finset.mem_product.mp huw_prod).1, hlt, hdvd⟩
            · intro x hx y hy hxy
              obtain ⟨_, hx2⟩ := Finset.mem_filter.mp hx
              obtain ⟨_, hy2⟩ := Finset.mem_filter.mp hy
              exact Prod.ext hxy (hx2.trans hy2.symm)
          have hsub :
              (S.filter fun v => v < w ∧ w ∣ normalizedSquareSum v) ⊆
                (Finset.range w).filter (fun x => x % 3 = 2 ∧ w ∣ x ^ 2 + x + 1) := by
            intro v hv
            obtain ⟨hvS, hvw, hdvd⟩ := Finset.mem_filter.mp hv
            obtain ⟨_, _, _, hv_mod⟩ := hs_props v hvS
            have hv_ne1 : v % 3 ≠ 1 := by omega
            have hnorm : normalizedSquareSum v = v ^ 2 + v + 1 := by
              simp [normalizedSquareSum, hv_ne1]
            rw [hnorm] at hdvd
            exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hvw, hv_mod, hdvd⟩
          exact h1.trans
            ((Finset.card_le_card hsub).trans (card_twoModThree_dvd_sq_add_self_add_one_le_one hw_prime hw1))
        have hUp_upper : Up.card ≤ Q₁₃.card := by
          rw [hUp_fiber]
          calc
            ∑ w ∈ Q₁₃, (Up.filter fun uw => uw.2 = w).card ≤ ∑ _w ∈ Q₁₃, 1 :=
              Finset.sum_le_sum hfiber_le
            _ = Q₁₃.card := by simp
        have hS_le_two_Q13 : S.card ≤ 2 * Q₁₃.card := by
          omega
        have h443 : 443 ≤ N.primeFactors.card :=
          ((sixth_power_or_large_support ho hN).resolve_left fun ⟨p, hp, hpow⟩ => hfree p hp hpow).1
        have hS_parts : S = S₅₁ ∪ S₅₀ := by
          ext r
          simp only [S, S₅₁, S₅₀, Finset.mem_union, Finset.mem_filter]
          by_cases h : r % 5 = 1 <;> tauto
        have hS_disj : Disjoint S₅₁ S₅₀ := by
          apply Finset.disjoint_left.mpr
          intro r h1 h2
          exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
        have hS_card : S.card = S₅₁.card + S₅₀.card := by
          rw [hS_parts, Finset.card_union_of_disjoint hS_disj]
        obtain ⟨hω_eq, _, _⟩ :=
          sixth_power_free_omega_and_total_identities ho hN hq hq4 he hev hfree
        change N.primeFactors.card = 1 + S₅₁.card + S₅₀.card + Q₁₃.card + Q₂₃.card at hω_eq
        have hQ_cap : Q₁₃.card + 2 * Q₂₃.card ≤ 2 * S₅₁_col.card + 1 :=
          (sixth_power_free_quartic_double_Q23_collision_pinch ho hN hq hq4 he hev hfree).2.2.2.1
        omega
    change 74 ≤ S₅₁_col.card ∧ 148 ≤ 2 * S₅₁_col.card
    exact ⟨h74_core, by omega⟩
  refine ⟨h74_impl, fun h => ?_⟩
  by_contra hno6
  have hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N := fun p hp hpow => hno6 ⟨p, hp, hpow⟩
  have h74 := (h74_impl hfree).1
  have hω :=
    (sixth_power_free_pure_collision_repeat_and_rank_bounds ho hN hq hq4 he hev hfree).2.2.2.2.1
  have hΩ :=
    (sixth_power_free_pure_collision_total_and_drop_caps ho hN hq hq4 he hev hfree).2.1
  omega

end OddPerfect
