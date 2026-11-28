module

public import OddPerfect.SixthPowerFreeBipartiteSlackPinch
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
# Sixth-Power-Free `S₅₁_rep` Source Decomposition (`OddPerfect.SixthPowerFreeRepSourceDecomposition`)

Decomposes `S₅₁_rep := S₅₁.filter (fun r => indegAt N q r = 1)` into:
- `S₅₁_rep_q := S₅₁_rep.filter (fun r => r ∣ (q + 1) / 2)` (Euler repeat targets), and
- `S₅₁_rep_src := S₅₁_rep.filter (fun r => ¬ r ∣ (q + 1) / 2)` (quartic repeat targets),

and proves that every `r ∈ S₅₁_rep_src` comes with multiplicity `2` from a unique quartic source
`u ∈ largeSources N q` (since no `p ∈ squareSources N` has `r ∣ σ(p^2)`). This cancels
`2 * S₅₁_rep.card` completely from the quartic-to-`S₅₁` bipartite capacity bound, doubling the
`Q₂₃` coefficient to `Q₁₃.card + 2 * Q₂₃.card ≤ 2 * S₅₁_col.card + 1`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private theorem sigma_one_sq_local {p : ℕ} (hp : p.Prime) :
    sigma 1 (p ^ 2) = p ^ 2 + p + 1 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

private theorem sigma_one_prime_local {p : ℕ} (hp : p.Prime) :
    sigma 1 p = p + 1 := by
  rw [← pow_one p, sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

private theorem sigma_one_four_local {p : ℕ} (hp : p.Prime) :
    sigma 1 (p ^ 4) = p ^ 4 + p ^ 3 + p ^ 2 + p + 1 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

/-- **1. `S₅₁_rep` Euler/Quartic Source Partition**:
Splits `S₅₁_rep` into `S₅₁_rep_q` (`r ∣ (q + 1) / 2`) and `S₅₁_rep_src` (`¬ r ∣ (q + 1) / 2`),
shows that no `r ∈ S₅₁` divides `σ(p^2)` for `p ∈ squareSources N`, and proves that every
`r ∈ S₅₁_rep_src` satisfies `(σ(u^4)).factorization r = 2` and `r ^ 2 ∣ σ(u^4)` for a unique
`u ∈ largeSources N q`. -/
theorem sixth_power_free_S51_rep_source_partition {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    let S₅₁ := (squareSources N).filter (· % 5 = 1)
    let S₅₁_rep := S₅₁.filter (fun r => indegAt N q r = 1)
    let S₅₁_rep_q := S₅₁_rep.filter (fun r => r ∣ (q + 1) / 2)
    let S₅₁_rep_src := S₅₁_rep.filter (fun r => ¬ r ∣ (q + 1) / 2)
    S₅₁_rep = S₅₁_rep_q ∪ S₅₁_rep_src ∧
    Disjoint S₅₁_rep_q S₅₁_rep_src ∧
    S₅₁_rep.card = S₅₁_rep_q.card + S₅₁_rep_src.card ∧
    (∀ p ∈ squareSources N, ∀ r ∈ S₅₁, ¬ r ∣ sigma 1 (p ^ 2)) ∧
    (∀ r ∈ S₅₁_rep_src,
      ∃ u ∈ largeSources N q,
        (sigma 1 (u ^ 4)).factorization r = 2 ∧
        r ^ 2 ∣ sigma 1 (u ^ 4) ∧
        ∀ v ∈ (largeSources N q).erase u, ¬ r ∣ sigma 1 (v ^ 4)) := by
  intro S₅₁ S₅₁_rep S₅₁_rep_q S₅₁_rep_src
  have hpart : S₅₁_rep = S₅₁_rep_q ∪ S₅₁_rep_src := by
    ext r
    simp only [S₅₁_rep_q, S₅₁_rep_src, Finset.mem_union, Finset.mem_filter]
    by_cases h : r ∣ (q + 1) / 2 <;> tauto
  have hdisj : Disjoint S₅₁_rep_q S₅₁_rep_src := by
    apply Finset.disjoint_left.mpr
    intro r h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hcard : S₅₁_rep.card = S₅₁_rep_q.card + S₅₁_rep_src.card := by
    rw [hpart, Finset.card_union_of_disjoint hdisj]
  have h3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  have hq1 : N.factorization q = 1 := sixth_power_free_euler_exponent_one ho hN hq he hfree
  have hS1_empty : squareSourcesOne N = ∅ := by
    have hb := squareSourcesOne_card_le_three_exponent hN
    have hz : N.factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd h3
    exact Finset.card_eq_zero.mp (by omega)
  have hsq_mod3 : ∀ r ∈ squareSources N, r % 3 = 2 := by
    intro r hr
    obtain ⟨hr_mem, _, _⟩ := Finset.mem_filter.mp hr
    have hr_dvd := Nat.dvd_of_mem_primeFactors hr_mem
    have hr_not0 : r % 3 ≠ 0 := fun h0 => h3 ((Nat.dvd_of_mod_eq_zero h0).trans hr_dvd)
    have hr_not1 : r % 3 ≠ 1 := by
      intro h1
      have hmem1 : r ∈ squareSourcesOne N := Finset.mem_filter.mpr ⟨hr, h1⟩
      simp [hS1_empty] at hmem1
    omega
  have hnot_sq_dvd : ∀ p ∈ squareSources N, ∀ r ∈ S₅₁, ¬ r ∣ sigma 1 (p ^ 2) := by
    intro p hp r hr hd
    have hp_prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
    have hr_sq : r ∈ squareSources N := (Finset.mem_filter.mp hr).1
    have hr_prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hr_sq).1
    have hr_mod3 := hsq_mod3 r hr_sq
    rw [sigma_one_sq_local hp_prime] at hd
    rcases prime_dvd_sq_add_self_add_one hr_prime hd with rfl | h1
    · exact (by decide : 3 % 3 ≠ 2) hr_mod3
    · omega
  have hq_prime := Nat.prime_of_mem_primeFactors hq
  have hcomp_q : oddComponentSigma N q q = (q + 1) / 2 := by
    unfold oddComponentSigma
    simp only [ite_true]
    rw [hq1, pow_one, sigma_one_prime_local hq_prime]
  have hlg4 : ∀ u ∈ largeSources N q, N.factorization u = 4 :=
    (three_free_sixthPowerFree_forces_147_largeSources ho hN hq hq4 he hev h3 hfree).1
  have hsrc : ∀ r ∈ S₅₁_rep_src,
      ∃ u ∈ largeSources N q,
        (sigma 1 (u ^ 4)).factorization r = 2 ∧
        r ^ 2 ∣ sigma 1 (u ^ 4) ∧
        ∀ v ∈ (largeSources N q).erase u, ¬ r ∣ sigma 1 (v ^ 4) := by
    intro r hr
    obtain ⟨hr_rep, hr_ndvd_half⟩ := Finset.mem_filter.mp hr
    obtain ⟨hr_S51, hr_ind1⟩ := Finset.mem_filter.mp hr_rep
    have hr_sq : r ∈ squareSources N := (Finset.mem_filter.mp hr_S51).1
    obtain ⟨hr_N, _, hr_exp2⟩ := Finset.mem_filter.mp hr_sq
    have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr_N
    have hr_odd : Odd r := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr_N)
    have hmut := (euler_linear_and_exponent_two_mutual_exclusion ho hN hq hq4 he hev).2 r hr_N hr_exp2
    obtain ⟨_, _, u, hu_N, hr2_dvd_comp, hnot_other⟩ := hmut.resolve_left (fun h => by omega)
    have huq : u ≠ q := by
      intro hEq
      rw [hEq, hcomp_q] at hr2_dvd_comp
      exact hr_ndvd_half ((dvd_pow_self r (by decide : 2 ≠ 0)).trans hr2_dvd_comp)
    have hu_prime : u.Prime := Nat.prime_of_mem_primeFactors hu_N
    have hu_pos : 0 < N.factorization u :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hu_N)
    have hu_lt6 : ¬ 6 ≤ N.factorization u := fun hge =>
      hfree u hu_prime ((hu_prime.pow_dvd_iff_le_factorization hN.2.ne').2 hge)
    have hu_even : Even (N.factorization u) := hev u huq
    have hu_ne2 : N.factorization u ≠ 2 := by
      intro h2
      have hu3 : u ≠ 3 := fun h3eq => h3 (h3eq ▸ Nat.dvd_of_mem_primeFactors hu_N)
      have hu_sq : u ∈ squareSources N := Finset.mem_filter.mpr ⟨hu_N, hu3, h2⟩
      have hcomp_u : oddComponentSigma N q u = sigma 1 (u ^ 2) := by
        unfold oddComponentSigma
        simp only [huq, ite_false]
        rw [h2]
      rw [hcomp_u] at hr2_dvd_comp
      exact hnot_sq_dvd u hu_sq r hr_S51 ((dvd_pow_self r (by decide : 2 ≠ 0)).trans hr2_dvd_comp)
    have hu_exp4 : N.factorization u = 4 := by
      obtain ⟨k, hk⟩ := hu_even
      omega
    have hu3 : u ≠ 3 := fun h3eq => h3 (h3eq ▸ Nat.dvd_of_mem_primeFactors hu_N)
    have hu_lg : u ∈ largeSources N q :=
      Finset.mem_filter.mpr ⟨hu_N, hu3, huq, by omega⟩
    have hcomp_u : oddComponentSigma N q u = sigma 1 (u ^ 4) := by
      unfold oddComponentSigma
      simp only [huq, ite_false]
      rw [hu_exp4]
    have hr2_dvd_sig : r ^ 2 ∣ sigma 1 (u ^ 4) := hcomp_u ▸ hr2_dvd_comp
    have hsig_ne0 : sigma 1 (u ^ 4) ≠ 0 := by
      rw [sigma_one_four_local hu_prime]
      omega
    have hge2 : 2 ≤ (sigma 1 (u ^ 4)).factorization r :=
      (hr_prime.pow_dvd_iff_le_factorization hsig_ne0).mp hr2_dvd_sig
    have hle2 : (sigma 1 (u ^ 4)).factorization r ≤ 2 := by
      have hsum := factorization_eq_sum_sigma_factorizations hN hr_odd hr_prime
      have hu_le := Finset.single_le_sum
        (f := fun x => (sigma 1 (x ^ N.factorization x)).factorization r)
        (fun _ _ => Nat.zero_le _) hu_N
      rw [hu_exp4] at hu_le
      omega
    have hfac2 : (sigma 1 (u ^ 4)).factorization r = 2 := by omega
    refine ⟨u, hu_lg, hfac2, hr2_dvd_sig, fun v hv => ?_⟩
    obtain ⟨hv_ne, hv_lg⟩ := Finset.mem_erase.mp hv
    obtain ⟨hv_N, _, hv_neq, _⟩ := Finset.mem_filter.mp hv_lg
    have hv_exp4 : N.factorization v = 4 := hlg4 v hv_lg
    have hcomp_v : oddComponentSigma N q v = sigma 1 (v ^ 4) := by
      unfold oddComponentSigma
      simp only [hv_neq, ite_false]
      rw [hv_exp4]
    rw [← hcomp_v]
    exact hnot_other v hv_N hv_ne
  exact ⟨hpart, hdisj, hcard, hnot_sq_dvd, hsrc⟩

/-- **2. Quartic Double-`Q₂₃` Collision Pinch**:
Using the unique quartic source decomposition on `S₅₁_rep_src` together with the non-Euler
odd-valuation target theorem and the mod-3 parity dichotomy on `Q₂₃`, proves:
- `(∑ u ∈ largeSources N q, (repFib u).card) = S₅₁_rep_src.card`,
- `2 * (repFib u).card + 1 ≤ cardFactors (sigma 1 (u ^ 4))` for all `u ∈ largeSources N q`,
- `2 * (repFib u).card + 2 ≤ cardFactors (sigma 1 (u ^ 4))` for all `u ∈ Q₂₃`,
- `Q₁₃.card + 2 * Q₂₃.card ≤ 2 * S₅₁_col.card + 1`,
- `146 + Q₂₃.card ≤ 2 * S₅₁_col.card`,
- `438 + 5 * Q₂₃.card ≤ 6 * S₅₁_col.card`, and
- `Q₂₃.Nonempty → 74 ≤ S₅₁_col.card`. -/
theorem sixth_power_free_quartic_double_Q23_collision_pinch {N q : ℕ}
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
    (∑ u ∈ largeSources N q, (repFib u).card) = S₅₁_rep_src.card ∧
    (∀ u ∈ largeSources N q, 2 * (repFib u).card + 1 ≤ cardFactors (sigma 1 (u ^ 4))) ∧
    (∀ u ∈ Q₂₃, 2 * (repFib u).card + 2 ≤ cardFactors (sigma 1 (u ^ 4))) ∧
    Q₁₃.card + 2 * Q₂₃.card ≤ 2 * S₅₁_col.card + 1 ∧
    146 + Q₂₃.card ≤ 2 * S₅₁_col.card ∧
    438 + 5 * Q₂₃.card ≤ 6 * S₅₁_col.card ∧
    (Q₂₃.Nonempty → 74 ≤ S₅₁_col.card) := by
  intro S₅₁ S₅₁_col S₅₁_rep S₅₁_rep_src Q₁₃ Q₂₃ repFib
  let S₅₁_rep_q := S₅₁_rep.filter (fun r => r ∣ (q + 1) / 2)
  have h3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  have hq1 : N.factorization q = 1 := sixth_power_free_euler_exponent_one ho hN hq he hfree
  have hq_prime := Nat.prime_of_mem_primeFactors hq
  have hq_odd : Odd q := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hq)
  obtain ⟨hlg4, h147, _⟩ :=
    three_free_sixthPowerFree_forces_147_largeSources ho hN hq hq4 he hev h3 hfree
  obtain ⟨_, _, hrep_split, _, hsrc⟩ :=
    sixth_power_free_S51_rep_source_partition ho hN hq hq4 he hev hfree
  change S₅₁_rep.card = S₅₁_rep_q.card + S₅₁_rep_src.card at hrep_split
  have hfib_sum : (∑ u ∈ largeSources N q, (repFib u).card) = S₅₁_rep_src.card := by
    have h1 : ∀ u ∈ largeSources N q, (repFib u).card =
        ∑ r ∈ S₅₁_rep_src, if r ∣ sigma 1 (u ^ 4) then 1 else 0 := fun u _ => by
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    have h2 : ∀ r ∈ S₅₁_rep_src, ((largeSources N q).filter (fun u => r ∣ sigma 1 (u ^ 4))).card =
        ∑ u ∈ largeSources N q, if r ∣ sigma 1 (u ^ 4) then 1 else 0 := fun r _ => by
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm, ← Finset.sum_congr rfl h2]
    calc
      ∑ r ∈ S₅₁_rep_src, ((largeSources N q).filter (fun u => r ∣ sigma 1 (u ^ 4))).card
          = ∑ _r ∈ S₅₁_rep_src, 1 := by
              refine Finset.sum_congr rfl fun r hr => ?_
              obtain ⟨u₀, hu₀_lg, _, hr2_dvd, hnot_other⟩ := hsrc r hr
              have heq_sing :
                  (largeSources N q).filter (fun u => r ∣ sigma 1 (u ^ 4)) = {u₀} := by
                ext v
                simp only [Finset.mem_filter, Finset.mem_singleton]
                constructor
                · rintro ⟨hv_lg, hv_dvd⟩
                  by_contra hv_ne
                  exact hnot_other v (Finset.mem_erase.mpr ⟨hv_ne, hv_lg⟩) hv_dvd
                · rintro rfl
                  exact ⟨hu₀_lg, (dvd_pow_self r (by decide : 2 ≠ 0)).trans hr2_dvd⟩
              rw [heq_sing, Finset.card_singleton]
      _ = S₅₁_rep_src.card := by simp [Finset.sum_const]
  have htarget := sixth_power_free_non_euler_has_odd_valuation_target ho hN hq hq4 he hev hfree
  have hfib_fac2 : ∀ u ∈ largeSources N q, ∀ r ∈ repFib u,
      (sigma 1 (u ^ 4)).factorization r = 2 := by
    intro u hu r hr
    obtain ⟨hr_src, hr_dvd⟩ := Finset.mem_filter.mp hr
    obtain ⟨u₀, _, hfac2, _, hnot_other⟩ := hsrc r hr_src
    have hu_eq : u = u₀ := by
      by_contra hu_ne
      exact hnot_other u (Finset.mem_erase.mpr ⟨hu_ne, hu⟩) hr_dvd
    rwa [hu_eq]
  have hlb_all : ∀ u ∈ largeSources N q, 2 * (repFib u).card + 1 ≤ cardFactors (sigma 1 (u ^ 4)) := by
    intro u hu
    obtain ⟨hu_N, _, hu_neq, _⟩ := Finset.mem_filter.mp hu
    have hu_prime : u.Prime := Nat.prime_of_mem_primeFactors hu_N
    have hu_exp4 : N.factorization u = 4 := hlg4 u hu
    have hsig_ne0 : sigma 1 (u ^ 4) ≠ 0 := by
      rw [sigma_one_four_local hu_prime]
      omega
    obtain ⟨_, w, _, hw_odd, _⟩ := htarget u (Finset.mem_erase.mpr ⟨hu_neq, hu_N⟩)
    rw [hu_exp4] at hw_odd
    have hw_pos : 1 ≤ (sigma 1 (u ^ 4)).factorization w := by
      obtain ⟨k, hk⟩ := hw_odd
      omega
    have hw_mem : w ∈ (sigma 1 (u ^ 4)).primeFactors :=
      Finsupp.mem_support_iff.mpr (Nat.ne_of_gt hw_pos)
    have hw_notin : w ∉ repFib u := by
      intro hw_rep
      have hw2 := hfib_fac2 u hu w hw_rep
      rw [hw2] at hw_odd
      exact (by decide : ¬ Odd 2) hw_odd
    have hsub : insert w (repFib u) ⊆ (sigma 1 (u ^ 4)).primeFactors := by
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp_rep
      · exact hw_mem
      · obtain ⟨hp_src, hp_dvd⟩ := Finset.mem_filter.mp hp_rep
        have hp_S51 := (Finset.mem_filter.mp (Finset.mem_filter.mp hp_src).1).1
        have hp_sq := (Finset.mem_filter.mp hp_S51).1
        have hp_prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp_sq).1
        exact Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd, hsig_ne0⟩
    have hcard_eq :
        cardFactors (sigma 1 (u ^ 4)) =
          ∑ p ∈ (sigma 1 (u ^ 4)).primeFactors, (sigma 1 (u ^ 4)).factorization p := by
      rw [cardFactors_eq_sum_factorization]
      rfl
    have hsum_le :
        ∑ p ∈ insert w (repFib u), (sigma 1 (u ^ 4)).factorization p ≤
          cardFactors (sigma 1 (u ^ 4)) := by
      rw [hcard_eq]
      exact Finset.sum_le_sum_of_subset hsub
    have hsum_ins :
        ∑ p ∈ insert w (repFib u), (sigma 1 (u ^ 4)).factorization p =
          (sigma 1 (u ^ 4)).factorization w + ∑ r ∈ repFib u, (sigma 1 (u ^ 4)).factorization r :=
      Finset.sum_insert hw_notin
    have hsum_rep :
        ∑ r ∈ repFib u, (sigma 1 (u ^ 4)).factorization r = 2 * (repFib u).card := by
      calc
        ∑ r ∈ repFib u, (sigma 1 (u ^ 4)).factorization r
            = ∑ _r ∈ repFib u, 2 := Finset.sum_congr rfl (hfib_fac2 u hu)
        _ = 2 * (repFib u).card := by simp [Finset.sum_const, Nat.mul_comm]
    omega
  have hQ23_dich :=
    (sixth_power_free_quartic_cardFactors_mod_three_dichotomy ho hN hq hq4 he hev hfree).2
  have hlb_Q23 : ∀ u ∈ Q₂₃, 2 * (repFib u).card + 2 ≤ cardFactors (sigma 1 (u ^ 4)) := by
    intro u hu
    have hu_lg : u ∈ largeSources N q := (Finset.mem_filter.mp hu).1
    have h1 := hlb_all u hu_lg
    have heven := (hQ23_dich u hu).2.2.1
    obtain ⟨k, hk⟩ := heven
    omega
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
  have hmain : Q₁₃.card + 2 * Q₂₃.card ≤ 2 * S₅₁_col.card + 1 := by omega
  have h146 : 146 + Q₂₃.card ≤ 2 * S₅₁_col.card := by omega
  have h443 : 443 ≤ N.primeFactors.card :=
    (sixth_power_free_collision_excess_ge_221 ho hN hq hq4 he hev hfree).1
  have hω_le : N.primeFactors.card ≤ 3 * Q₁₃.card + Q₂₃.card + 2 :=
    (sixth_power_free_omega_and_total_identities ho hN hq hq4 he hev hfree).2.2
  have h438 : 438 + 5 * Q₂₃.card ≤ 6 * S₅₁_col.card := by omega
  have h74 : Q₂₃.Nonempty → 74 ≤ S₅₁_col.card := by
    intro hne
    have hpos : 1 ≤ Q₂₃.card := Finset.card_pos.mpr hne
    omega
  exact ⟨hfib_sum, hlb_all, hlb_Q23, hmain, h146, h438, h74⟩

end OddPerfect
