module

public import OddPerfect.ComponentIndexDrop
public import OddPerfect.SixthPowerFreeEuler
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Sixth-Power-Free Incoming-Source Vacuum and Unconditional Six-Factor Drop

Formalizes:
1. `sixth_power_free_incoming_source_vacuum`: On a sixth-power-free odd perfect number `N`,
   incoming square sources `S₅₀ := (squareSources N).filter (· % 5 ≠ 1)` and incoming quartic
   sources `Q₂₃ := twoModThreeLargeSources N q` cannot receive any prime factor from
   `sigma 1 (s ^ 2)` (`s ∈ squareSources N`) or `sigma 1 (u ^ 4)` (`u ∈ largeSources N q`),
   forcing `(∏ p ∈ S₅₀, p ^ 2) * (∏ u ∈ Q₂₃, u ^ 4) ∣ (q + 1) / 2`,
   `1 + 2 * S₅₀.card + 4 * Q₂₃.card ≤ cardFactors (sigma 1 (ordProj[q] N))`, and
   `∀ p ∈ S₅₀ ∪ Q₂₃, ¬ p ∣ componentIndex N q`.
2. `quartic_oneModThree_prime_sigma_of_le_two`: On a sixth-power-free odd perfect number `N`,
   any `u ∈ oneModThreeLargeSources N q` with `cardFactors (sigma 1 (u ^ 4)) ≤ 2` and
   `¬ q ∣ sigma 1 (u ^ 4)` has prime `sigma 1 (u ^ 4) ∈ (squareSources N).filter (· % 5 = 1)`.
3. `exists_componentIndex_cardFactors_add_six_le` and `all_componentIndex_lt_six_drop_eq_empty`:
   Unconditional proof that every odd perfect number admits a prime component `p ∈ N.primeFactors`
   with `cardFactors (componentIndex N p) + 6 ≤ cardFactors N`.
-/

public section

namespace OddPerfect

open ArithmeticFunction Finset

private theorem cardFactors_finset_prod {s : Finset ℕ} (f : ℕ → ℕ) (h : ∀ p ∈ s, 0 < f p) :
    cardFactors (∏ p ∈ s, f p) = ∑ p ∈ s, cardFactors (f p) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    have hpos : ∀ p ∈ s, 0 < f p := fun p hp => h p (Finset.mem_insert_of_mem hp)
    rw [Finset.prod_insert hx, Finset.sum_insert hx,
      cardFactors_mul (h x (Finset.mem_insert_self ..)).ne' (Finset.prod_pos hpos).ne', ih hpos]

private theorem sum_factorization_le_cardFactors (S : Finset ℕ) (m : ℕ) :
    ∑ p ∈ S, m.factorization p ≤ cardFactors m := by
  have hsub : ∑ p ∈ S, m.factorization p = ∑ p ∈ S ∩ m.primeFactors, m.factorization p := by
    refine (Finset.sum_subset Finset.inter_subset_left fun p hpS hpI => ?_).symm
    have hnot : p ∉ m.primeFactors := fun hm => hpI (Finset.mem_inter.mpr ⟨hpS, hm⟩)
    exact Finsupp.notMem_support_iff.mp hnot
  rw [hsub]
  calc
    ∑ p ∈ S ∩ m.primeFactors, m.factorization p
        ≤ ∑ p ∈ m.primeFactors, m.factorization p :=
          Finset.sum_le_sum_of_subset Finset.inter_subset_right
    _ = cardFactors m := by
          rw [cardFactors_eq_sum_factorization]
          rfl

private theorem sigma_one_prime {p : ℕ} (hp : p.Prime) : sigma 1 p = p + 1 := by
  rw [← pow_one p, sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

private theorem sigma_one_sq {p : ℕ} (hp : p.Prime) : sigma 1 (p ^ 2) = p ^ 2 + p + 1 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

private theorem sigma_one_four {p : ℕ} (hp : p.Prime) :
    sigma 1 (p ^ 4) = p ^ 4 + p ^ 3 + p ^ 2 + p + 1 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

private theorem sixth_power_free_source_invariants {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    ¬ 3 ∣ N ∧
    ¬ 5 ∣ N ∧
    N.factorization q = 1 ∧
    squareSourcesOne N = ∅ ∧
    (∀ s ∈ squareSources N, s.Prime ∧ s % 3 = 2 ∧ s ≠ 2 ∧ s ≠ 3 ∧ s ≠ 5 ∧ s ≠ q ∧
      N.factorization s = 2) ∧
    (∀ u ∈ largeSources N q, u.Prime ∧ u % 5 ≠ 1 ∧ u ≠ 2 ∧ u ≠ 3 ∧ u ≠ 5 ∧ u ≠ q ∧
      N.factorization u = 4) ∧
    N.primeFactors = insert q (squareSources N ∪ largeSources N q) ∧
    q ∉ squareSources N ∪ largeSources N q ∧
    Disjoint (squareSources N) (largeSources N q) := by
  have h3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  have h5 : ¬ 5 ∣ N := sixth_power_free_five_not_dvd ho hN hfree
  have hq1 : N.factorization q = 1 := sixth_power_free_euler_exponent_one ho hN hq he hfree
  have hfour : ∀ r ∈ largeSources N q, N.factorization r = 4 :=
    (three_free_sixthPowerFree_forces_147_largeSources ho hN hq hq4 he hev h3 hfree).1
  have hS1_empty : squareSourcesOne N = ∅ := by
    have hb := squareSourcesOne_card_le_three_exponent hN
    have hz : N.factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd h3
    exact Finset.card_eq_zero.mp (by omega)
  have hsq_prop : ∀ s ∈ squareSources N,
      s.Prime ∧ s % 3 = 2 ∧ s ≠ 2 ∧ s ≠ 3 ∧ s ≠ 5 ∧ s ≠ q ∧ N.factorization s = 2 := by
    intro s hs
    obtain ⟨hs_mem, hs_ne3, hs_exp⟩ := Finset.mem_filter.mp hs
    have hs_prime := Nat.prime_of_mem_primeFactors hs_mem
    have hs_dvd := Nat.dvd_of_mem_primeFactors hs_mem
    have hs_odd := ho.of_dvd_nat hs_dvd
    have hs_ne2 : s ≠ 2 := fun h => by subst s; exact (by decide : ¬ Odd 2) hs_odd
    have hs_ne5 : s ≠ 5 := fun h => h5 (h ▸ hs_dvd)
    have hs_neq : s ≠ q := fun h => by subst s; omega
    have hs_not1 : s % 3 ≠ 1 := by
      intro h1
      have hmem1 : s ∈ squareSourcesOne N := Finset.mem_filter.mpr ⟨hs, h1⟩
      simp [hS1_empty] at hmem1
    have hs_not0 : s % 3 ≠ 0 := fun h0 => h3 ((Nat.dvd_of_mod_eq_zero h0).trans hs_dvd)
    exact ⟨hs_prime, by omega, hs_ne2, hs_ne3, hs_ne5, hs_neq, hs_exp⟩
  have hlg_prop : ∀ u ∈ largeSources N q,
      u.Prime ∧ u % 5 ≠ 1 ∧ u ≠ 2 ∧ u ≠ 3 ∧ u ≠ 5 ∧ u ≠ q ∧ N.factorization u = 4 := by
    intro u hu
    obtain ⟨hu_mem, hu_ne3, hu_neq, _⟩ := Finset.mem_filter.mp hu
    have hu_exp := hfour u hu
    have hu_prime := Nat.prime_of_mem_primeFactors hu_mem
    have hu_dvd := Nat.dvd_of_mem_primeFactors hu_mem
    have hu_odd := ho.of_dvd_nat hu_dvd
    have hu_ne2 : u ≠ 2 := fun h => by subst u; exact (by decide : ¬ Odd 2) hu_odd
    have hu_ne5 : u ≠ 5 := fun h => h5 (h ▸ hu_dvd)
    have hu_not5 : u % 5 ≠ 1 := by
      intro hmod5
      have hmem5 : u ∈ quarticSourcesOne N q :=
        Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hu_neq, hu_mem⟩, hu_exp, hmod5⟩
      have hpos := Finset.card_pos.mpr ⟨u, hmem5⟩
      have hle := quarticSourcesOne_card_le_five_exponent (q := q) hN
      have hz : N.factorization 5 = 0 := Nat.factorization_eq_zero_of_not_dvd h5
      omega
    exact ⟨hu_prime, hu_not5, hu_ne2, hu_ne3, hu_ne5, hu_neq, hu_exp⟩
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
  exact ⟨h3, h5, hq1, hS1_empty, hsq_prop, hlg_prop, hparts, hq_notin, hdisj⟩

/-- **Sixth-Power-Free Incoming-Source Vacuum**: on a sixth-power-free odd perfect number `N`,
every prime `p ∈ S₅₀ ∪ Q₂₃` (with `S₅₀ := (squareSources N).filter (· % 5 ≠ 1)` and
`Q₂₃ := twoModThreeLargeSources N q`) satisfies `p % 3 = 2`, `p % 5 ≠ 1`, `p ≠ 2, 3, 5`, cannot
divide `sigma 1 (s ^ 2)` for `s ∈ squareSources N` or `sigma 1 (u ^ 4)` for `u ∈ largeSources N q`,
forces `(sigma 1 (ordProj[q] N)).factorization p = N.factorization p`, divides `(q + 1) / 2` to its
exact prime-power in `N`, satisfies `1 + 2 * S₅₀.card + 4 * Q₂₃.card ≤ cardFactors (sigma 1 (ordProj[q] N))`,
and cannot divide `componentIndex N q`. -/
theorem sixth_power_free_incoming_source_vacuum {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    let S₅₀ := (squareSources N).filter (· % 5 ≠ 1)
    let Q₂₃ := twoModThreeLargeSources N q
    (∀ p ∈ S₅₀ ∪ Q₂₃, p.Prime ∧ p % 3 = 2 ∧ p % 5 ≠ 1 ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧
      (∀ s ∈ squareSources N, ¬ p ∣ sigma 1 (s ^ 2)) ∧
      (∀ u ∈ largeSources N q, ¬ p ∣ sigma 1 (u ^ 4)) ∧
      (sigma 1 (ordProj[q] N)).factorization p = N.factorization p) ∧
    (∏ p ∈ S₅₀, p ^ 2) * (∏ u ∈ Q₂₃, u ^ 4) ∣ (q + 1) / 2 ∧
    1 + 2 * S₅₀.card + 4 * Q₂₃.card ≤ cardFactors (sigma 1 (ordProj[q] N)) ∧
    (∀ p ∈ S₅₀ ∪ Q₂₃, ¬ p ∣ componentIndex N q) := by
  intro S₅₀ Q₂₃
  obtain ⟨h3, _, hq1, _, hsq_prop, hlg_prop, hparts, hq_notin, hdisj⟩ :=
    sixth_power_free_source_invariants ho hN hq hq4 he hev hfree
  have hq_prime := Nat.prime_of_mem_primeFactors hq
  have hS50_sub : S₅₀ ⊆ squareSources N := Finset.filter_subset _ _
  have hQ23_sub : Q₂₃ ⊆ largeSources N q := Finset.filter_subset _ _
  have hS50_Q23_disj : Disjoint S₅₀ Q₂₃ := hdisj.mono hS50_sub hQ23_sub
  have hmem_info : ∀ p ∈ S₅₀ ∪ Q₂₃,
      p.Prime ∧ p % 3 = 2 ∧ p % 5 ≠ 1 ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ q ∧ Odd p := by
    intro p hp
    rcases Finset.mem_union.mp hp with hpS | hpQ
    · obtain ⟨hp_sq, hp5⟩ := Finset.mem_filter.mp hpS
      obtain ⟨hp_prime, hp3, hp2, hp3', hp5', hpq, _⟩ := hsq_prop p hp_sq
      have hp_dvd := Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp_sq).1
      exact ⟨hp_prime, hp3, hp5, hp2, hp3', hp5', hpq, ho.of_dvd_nat hp_dvd⟩
    · obtain ⟨hp_lg, hp3⟩ := Finset.mem_filter.mp hpQ
      obtain ⟨hp_prime, hp5, hp2, hp3', hp5', hpq, _⟩ := hlg_prop p hp_lg
      have hp_dvd := Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp_lg).1
      have hp3_not0 : p % 3 ≠ 0 := fun h0 => h3 ((Nat.dvd_of_mod_eq_zero h0).trans hp_dvd)
      exact ⟨hp_prime, by omega, hp5, hp2, hp3', hp5', hpq, ho.of_dvd_nat hp_dvd⟩
  have hpoint : ∀ p ∈ S₅₀ ∪ Q₂₃,
      p.Prime ∧ p % 3 = 2 ∧ p % 5 ≠ 1 ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧
        (∀ s ∈ squareSources N, ¬ p ∣ sigma 1 (s ^ 2)) ∧
        (∀ u ∈ largeSources N q, ¬ p ∣ sigma 1 (u ^ 4)) ∧
        (sigma 1 (ordProj[q] N)).factorization p = N.factorization p := by
    intro p hp
    obtain ⟨hp_prime, hp3, hp5, hp2, hp3', hp5', _, hp_odd⟩ := hmem_info p hp
    have hnot_sq : ∀ s ∈ squareSources N, ¬ p ∣ sigma 1 (s ^ 2) := by
      intro s hs hd
      have hs_prime := (hsq_prop s hs).1
      rw [sigma_one_sq hs_prime] at hd
      rcases prime_dvd_sq_add_self_add_one hp_prime hd with rfl | hmod
      · exact hp3' rfl
      · omega
    have hnot_lg : ∀ u ∈ largeSources N q, ¬ p ∣ sigma 1 (u ^ 4) := by
      intro u hu hd
      obtain ⟨hu_prime, hu5, hu2, hu3, _, _, _⟩ := hlg_prop u hu
      have hu_ge3 : 3 ≤ u := by have := hu_prime.two_le; omega
      have hnorm_eq : normalizedQuarticSum u = sigma 1 (u ^ 4) := by
        rw [normalizedQuarticSum, ite_eq_right hu5, ← sigma_one_four hu_prime]
      have hd_norm : p ∣ normalizedQuarticSum u := hnorm_eq ▸ hd
      have hp_mod5 := (quartic_sigma_properties hu_prime hu_ge3).2.2.2 p hp_prime hd_norm
      exact hp5 hp_mod5
    have hfac_eq : (sigma 1 (ordProj[q] N)).factorization p = N.factorization p := by
      have hsum := factorization_eq_sum_sigma_factorizations hN hp_odd hp_prime
      rw [hparts, Finset.sum_insert hq_notin, Finset.sum_union hdisj] at hsum
      have hsum_sq : (∑ s ∈ squareSources N, (sigma 1 (s ^ N.factorization s)).factorization p) = 0 := by
        refine Finset.sum_eq_zero fun s hs => ?_
        rw [(hsq_prop s hs).2.2.2.2.2.2]
        exact Nat.factorization_eq_zero_of_not_dvd (hnot_sq s hs)
      have hsum_lg : (∑ u ∈ largeSources N q, (sigma 1 (u ^ N.factorization u)).factorization p) = 0 := by
        refine Finset.sum_eq_zero fun u hu => ?_
        rw [(hlg_prop u hu).2.2.2.2.2.2]
        exact Nat.factorization_eq_zero_of_not_dvd (hnot_lg u hu)
      rw [hsum_sq, hsum_lg] at hsum
      omega
    exact ⟨hp_prime, hp3, hp5, hp2, hp3', hp5', hnot_sq, hnot_lg, hfac_eq⟩
  have hsig_eq : sigma 1 (ordProj[q] N) = 2 * ((q + 1) / 2) := by
    rw [hq1, pow_one, sigma_one_prime hq_prime]
    omega
  have hhalf_ne0 : (q + 1) / 2 ≠ 0 := by
    have := hq_prime.two_le
    omega
  have hhalf_fac : ∀ p ∈ S₅₀ ∪ Q₂₃, ((q + 1) / 2).factorization p = N.factorization p := by
    intro p hp
    have hp_prime := (hpoint p hp).1
    have hp_ne2 := (hpoint p hp).2.2.2.1
    have hfac := (hpoint p hp).2.2.2.2.2.2.2.2
    rw [hsig_eq, Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) hhalf_ne0, Finsupp.add_apply] at hfac
    have hnot2 : ¬ p ∣ 2 := fun h =>
      hp_ne2 (((Nat.dvd_prime Nat.prime_two).mp h).resolve_left hp_prime.ne_one)
    rw [Nat.factorization_eq_zero_of_not_dvd hnot2, zero_add] at hfac
    exact hfac
  have hS50_ne0 : ∀ p ∈ S₅₀, p ^ 2 ≠ 0 := fun p hp =>
    pow_ne_zero 2 (hpoint p (Finset.mem_union.mpr (Or.inl hp))).1.ne_zero
  have hQ23_ne0 : ∀ u ∈ Q₂₃, u ^ 4 ≠ 0 := fun u hu =>
    pow_ne_zero 4 (hpoint u (Finset.mem_union.mpr (Or.inr hu))).1.ne_zero
  have hprod1_ne0 : (∏ p ∈ S₅₀, p ^ 2) ≠ 0 := Finset.prod_ne_zero_iff.mpr hS50_ne0
  have hprod2_ne0 : (∏ u ∈ Q₂₃, u ^ 4) ≠ 0 := Finset.prod_ne_zero_iff.mpr hQ23_ne0
  have hD_ne0 : (∏ p ∈ S₅₀, p ^ 2) * (∏ u ∈ Q₂₃, u ^ 4) ≠ 0 :=
    mul_ne_zero hprod1_ne0 hprod2_ne0
  have hD_dvd : (∏ p ∈ S₅₀, p ^ 2) * (∏ u ∈ Q₂₃, u ^ 4) ∣ (q + 1) / 2 := by
    rw [← Nat.factorization_le_iff_dvd hD_ne0 hhalf_ne0]
    intro r
    rw [Nat.factorization_mul hprod1_ne0 hprod2_ne0, Finsupp.add_apply,
      Nat.factorization_prod_apply hS50_ne0, Nat.factorization_prod_apply hQ23_ne0]
    by_cases hrS : r ∈ S₅₀
    · have hrQ : r ∉ Q₂₃ := Finset.disjoint_left.mp hS50_Q23_disj hrS
      have hsum1 : (∑ p ∈ S₅₀, (p ^ 2).factorization r) = 2 := by
        rw [Finset.sum_eq_single_of_mem r hrS]
        · exact Nat.factorization_pow_self (hpoint r (Finset.mem_union.mpr (Or.inl hrS))).1
        · intro p hp hpr
          have hp_prime := (hpoint p (Finset.mem_union.mpr (Or.inl hp))).1
          simp [hp_prime.factorization_pow, hpr.symm]
      have hsum2 : (∑ u ∈ Q₂₃, (u ^ 4).factorization r) = 0 := by
        refine Finset.sum_eq_zero fun u hu => ?_
        have hu_prime := (hpoint u (Finset.mem_union.mpr (Or.inr hu))).1
        have hur : u ≠ r := fun h => hrQ (h ▸ hu)
        simp [hu_prime.factorization_pow, hur.symm]
      have hfac_r := hhalf_fac r (Finset.mem_union.mpr (Or.inl hrS))
      have hN_r : N.factorization r = 2 := (hsq_prop r (hS50_sub hrS)).2.2.2.2.2.2
      rw [hsum1, hsum2, hfac_r, hN_r]
    · have hsum1 : (∑ p ∈ S₅₀, (p ^ 2).factorization r) = 0 := by
        refine Finset.sum_eq_zero fun p hp => ?_
        have hp_prime := (hpoint p (Finset.mem_union.mpr (Or.inl hp))).1
        have hpr : p ≠ r := fun h => hrS (h ▸ hp)
        simp [hp_prime.factorization_pow, hpr.symm]
      by_cases hrQ : r ∈ Q₂₃
      · have hsum2 : (∑ u ∈ Q₂₃, (u ^ 4).factorization r) = 4 := by
          rw [Finset.sum_eq_single_of_mem r hrQ]
          · exact Nat.factorization_pow_self (hpoint r (Finset.mem_union.mpr (Or.inr hrQ))).1
          · intro u hu hur
            have hu_prime := (hpoint u (Finset.mem_union.mpr (Or.inr hu))).1
            simp [hu_prime.factorization_pow, hur.symm]
        have hfac_r := hhalf_fac r (Finset.mem_union.mpr (Or.inr hrQ))
        have hN_r : N.factorization r = 4 := (hlg_prop r (hQ23_sub hrQ)).2.2.2.2.2.2
        rw [hsum1, hsum2, hfac_r, hN_r]
      · have hsum2 : (∑ u ∈ Q₂₃, (u ^ 4).factorization r) = 0 := by
          refine Finset.sum_eq_zero fun u hu => ?_
          have hu_prime := (hpoint u (Finset.mem_union.mpr (Or.inr hu))).1
          have hur : u ≠ r := fun h => hrQ (h ▸ hu)
          simp [hu_prime.factorization_pow, hur.symm]
        rw [hsum1, hsum2]
        exact Nat.zero_le _
  have hcard_le : 1 + 2 * S₅₀.card + 4 * Q₂₃.card ≤ cardFactors (sigma 1 (ordProj[q] N)) := by
    obtain ⟨m, hm⟩ := hD_dvd
    have hm_ne0 : m ≠ 0 := by
      intro hm0
      rw [hm0, mul_zero] at hm
      exact hhalf_ne0 hm
    have hprod1_card : cardFactors (∏ p ∈ S₅₀, p ^ 2) = 2 * S₅₀.card := by
      rw [cardFactors_finset_prod _ fun p hp => Nat.pos_of_ne_zero (hS50_ne0 p hp)]
      calc
        ∑ p ∈ S₅₀, cardFactors (p ^ 2)
            = ∑ _p ∈ S₅₀, 2 :=
              Finset.sum_congr rfl fun p hp =>
                cardFactors_apply_prime_pow (hpoint p (Finset.mem_union.mpr (Or.inl hp))).1
        _ = 2 * S₅₀.card := by simp [Finset.sum_const, Nat.mul_comm]
    have hprod2_card : cardFactors (∏ u ∈ Q₂₃, u ^ 4) = 4 * Q₂₃.card := by
      rw [cardFactors_finset_prod _ fun u hu => Nat.pos_of_ne_zero (hQ23_ne0 u hu)]
      calc
        ∑ u ∈ Q₂₃, cardFactors (u ^ 4)
            = ∑ _u ∈ Q₂₃, 4 :=
              Finset.sum_congr rfl fun u hu =>
                cardFactors_apply_prime_pow (hpoint u (Finset.mem_union.mpr (Or.inr hu))).1
        _ = 4 * Q₂₃.card := by simp [Finset.sum_const, Nat.mul_comm]
    rw [hsig_eq, hm, cardFactors_mul (by decide : (2 : ℕ) ≠ 0) (mul_ne_zero hD_ne0 hm_ne0),
      cardFactors_apply_prime Nat.prime_two,
      cardFactors_mul hD_ne0 hm_ne0,
      cardFactors_mul hprod1_ne0 hprod2_ne0,
      hprod1_card, hprod2_card]
    omega
  have hci_not_dvd : ∀ p ∈ S₅₀ ∪ Q₂₃, ¬ p ∣ componentIndex N q := by
    intro p hp hdvd
    obtain ⟨hmul, hci_pos⟩ := componentIndex_mul_eq_two_mul hN hq
    have hp_prime := (hmem_info p hp).1
    have hp_ne2 := (hmem_info p hp).2.2.2.1
    have hp_neq := (hmem_info p hp).2.2.2.2.2.2.1
    have hord_ne0 : ordProj[q] N ≠ 0 := pow_ne_zero _ hq_prime.ne_zero
    have hsig_ne0 : sigma 1 (ordProj[q] N) ≠ 0 := (sigma_pos 1 _ hord_ne0).ne'
    have hfac := congrArg (fun n => n.factorization p) hmul
    rw [Nat.factorization_mul (mul_ne_zero hci_pos.ne' hord_ne0) hsig_ne0, Finsupp.add_apply,
      Nat.factorization_mul hci_pos.ne' hord_ne0, Finsupp.add_apply,
      Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) hN.2.ne', Finsupp.add_apply] at hfac
    have hord_fac : (ordProj[q] N).factorization p = 0 := by
      simp [hq_prime.factorization_pow, hp_neq]
    have hnot2 : ¬ p ∣ 2 := fun h =>
      hp_ne2 (((Nat.dvd_prime Nat.prime_two).mp h).resolve_left hp_prime.ne_one)
    have h2_fac : (2 : ℕ).factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hnot2
    have hsig_fac := (hpoint p hp).2.2.2.2.2.2.2.2
    have hci_ge1 : 1 ≤ (componentIndex N q).factorization p :=
      (hp_prime.dvd_iff_one_le_factorization hci_pos.ne').mp hdvd
    omega
  exact ⟨hpoint, hD_dvd, hcard_le, hci_not_dvd⟩

/-- On a sixth-power-free odd perfect number `N`, if `u ∈ oneModThreeLargeSources N q`
has `cardFactors (sigma 1 (u ^ 4)) ≤ 2` and `¬ q ∣ sigma 1 (u ^ 4)`, then `sigma 1 (u ^ 4)`
is prime and belongs to `(squareSources N).filter (· % 5 = 1)`. -/
theorem quartic_oneModThree_prime_sigma_of_le_two {N q u : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N)
    (hu : u ∈ oneModThreeLargeSources N q)
    (hcard : cardFactors (sigma 1 (u ^ 4)) ≤ 2)
    (hnq : ¬ q ∣ sigma 1 (u ^ 4)) :
    (sigma 1 (u ^ 4)).Prime ∧ sigma 1 (u ^ 4) ∈ (squareSources N).filter (· % 5 = 1) := by
  obtain ⟨h3, _, _, hS1_empty, _, hlg_prop, _, _, _⟩ :=
    sixth_power_free_source_invariants ho hN hq hq4 he hev hfree
  obtain ⟨hu_lg, hu3⟩ := Finset.mem_filter.mp hu
  obtain ⟨hu_prime, hu5, hu2, _, _, _, hu_exp⟩ := hlg_prop u hu_lg
  have hu_ge3 : 3 ≤ u := by have := hu_prime.two_le; omega
  have hu_odd : Odd u := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hu_lg).1)
  have hsig_eq : sigma 1 (u ^ 4) = u ^ 4 + u ^ 3 + u ^ 2 + u + 1 := sigma_one_four hu_prime
  have hnorm_eq : normalizedQuarticSum u = sigma 1 (u ^ 4) := by
    rw [normalizedQuarticSum, ite_eq_right hu5, ← hsig_eq]
  have hsig_gt1 : 1 < sigma 1 (u ^ 4) := by
    have := hu_prime.two_le
    rw [hsig_eq]
    omega
  have hsig_odd : Odd (sigma 1 (u ^ 4)) := by
    have hmod4 := normalizedQuarticSum_mod_four hu_odd
    rw [hnorm_eq] at hmod4
    exact Nat.odd_iff.mpr (by omega)
  have hsig_mod3 : sigma 1 (u ^ 4) % 3 = 2 := by
    rw [hsig_eq]
    have hc : u ≡ 1 [MOD 3] := hu3
    have hpoly : u ^ 4 + u ^ 3 + u ^ 2 + u + 1 ≡
        1 ^ 4 + 1 ^ 3 + 1 ^ 2 + 1 + 1 [MOD 3] :=
      ((((hc.pow 4).add (hc.pow 3)).add (hc.pow 2)).add hc).add (Nat.ModEq.refl 1)
    change (u ^ 4 + u ^ 3 + u ^ 2 + u + 1) % 3 = (1 ^ 4 + 1 ^ 3 + 1 ^ 2 + 1 + 1) % 3 at hpoly
    omega
  have hw_prop : ∀ w : ℕ, w.Prime → w ∣ sigma 1 (u ^ 4) →
      w ∈ (squareSources N).filter (· % 5 = 1) ∧ w % 3 = 2 := by
    intro w hw_prime hw_dvd
    have hw_odd : Odd w := hsig_odd.of_dvd_nat hw_dvd
    have hw_mod5 : w % 5 = 1 :=
      (quartic_sigma_properties hu_prime hu_ge3).2.2.2 w hw_prime (hnorm_eq ▸ hw_dvd)
    have hw_N : w ∣ N := by
      apply dvd_perfect_of_exact_prime_pow hN hu_prime (hu_exp ▸ Nat.ordProj_dvd N u)
        ((hu_prime.pow_dvd_iff_le_factorization hN.2.ne').not.mpr (by omega))
        hw_prime hw_odd
      rw [← sigma_one_apply]
      exact hw_dvd
    have hw_mem : w ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hw_prime, hw_N, hN.2.ne'⟩
    have hw_ne3 : w ≠ 3 := fun h => h3 (h ▸ hw_N)
    have hw_neq : w ≠ q := fun h => hnq (h ▸ hw_dvd)
    have hw_exp : N.factorization w = 2 := by
      obtain ⟨k, hk⟩ := hev w hw_neq
      have hw_pos : 0 < N.factorization w := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hw_mem)
      have hw_lt6 : ¬ 6 ≤ N.factorization w := fun hge =>
        hfree w hw_prime ((hw_prime.pow_dvd_iff_le_factorization hN.2.ne').2 hge)
      by_cases h4 : N.factorization w = 4
      · have hw_lg : w ∈ largeSources N q :=
          Finset.mem_filter.mpr ⟨hw_mem, hw_ne3, hw_neq, by omega⟩
        exact ((hlg_prop w hw_lg).2.1 hw_mod5).elim
      · omega
    have hw_sq : w ∈ squareSources N := Finset.mem_filter.mpr ⟨hw_mem, hw_ne3, hw_exp⟩
    have hw_not1 : w % 3 ≠ 1 := by
      intro h1
      have hmem1 : w ∈ squareSourcesOne N := Finset.mem_filter.mpr ⟨hw_sq, h1⟩
      simp [hS1_empty] at hmem1
    have hw_not0 : w % 3 ≠ 0 := fun h0 => h3 ((Nat.dvd_of_mod_eq_zero h0).trans hw_N)
    exact ⟨Finset.mem_filter.mpr ⟨hw_sq, hw_mod5⟩, by omega⟩
  have hcard_pos : 0 < cardFactors (sigma 1 (u ^ 4)) := cardFactors_pos_iff_one_lt.mpr hsig_gt1
  have hcard_one : cardFactors (sigma 1 (u ^ 4)) = 1 := by
    by_contra hne1
    have hcard_two : cardFactors (sigma 1 (u ^ 4)) = 2 := by omega
    let s := sigma 1 (u ^ 4)
    let w₁ := s.minFac
    have hw₁_prime : w₁.Prime := Nat.minFac_prime (by omega : s ≠ 1)
    have hw₁_dvd : w₁ ∣ s := Nat.minFac_dvd s
    let w₂ := s / w₁
    have hs_eq : s = w₁ * w₂ := (Nat.mul_div_cancel' hw₁_dvd).symm
    have hw₂_ne0 : w₂ ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hs_eq
      omega
    have hw₂_card : cardFactors w₂ = 1 := by
      have hmul_card : cardFactors s = cardFactors w₁ + cardFactors w₂ := by
        rw [hs_eq, cardFactors_mul hw₁_prime.ne_zero hw₂_ne0]
      rw [cardFactors_apply_prime hw₁_prime] at hmul_card
      exact Nat.add_left_cancel (hmul_card.symm.trans hcard_two)
    have hw₂_prime : w₂.Prime := cardFactors_eq_one_iff_prime.mp hw₂_card
    have hw₂_dvd : w₂ ∣ s := hs_eq ▸ dvd_mul_left w₂ w₁
    have hw₁_mod3 : w₁ % 3 = 2 := (hw_prop w₁ hw₁_prime hw₁_dvd).2
    have hw₂_mod3 : w₂ % 3 = 2 := (hw_prop w₂ hw₂_prime hw₂_dvd).2
    have hs_mod3 : s % 3 = 1 := by
      rw [hs_eq, Nat.mul_mod, hw₁_mod3, hw₂_mod3]
    change s % 3 = 2 at hsig_mod3
    omega
  have hsig_prime : (sigma 1 (u ^ 4)).Prime := cardFactors_eq_one_iff_prime.mp hcard_one
  exact ⟨hsig_prime, (hw_prop (sigma 1 (u ^ 4)) hsig_prime dvd_rfl).1⟩

/-- **Unconditional Six-Factor Component-Index Drop**: every odd perfect number `N` admits a prime
factor `p ∈ N.primeFactors` such that `cardFactors (componentIndex N p) + 6 ≤ cardFactors N`. -/
theorem exists_componentIndex_cardFactors_add_six_le {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    ∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 6 ≤ cardFactors N := by
  by_contra! hnot
  have hneg :
      ¬ ((∃ p : ℕ, p.Prime ∧ p ^ 6 ∣ N) ∨
        ∃ p ∈ N.primeFactors,
          (N.factorization p = 1 ∧ 6 ≤ cardFactors (sigma 1 (ordProj[p] N))) ∨
          (N.factorization p = 2 ∧ 5 ≤ cardFactors (sigma 1 (ordProj[p] N))) ∨
          (N.factorization p = 4 ∧ 3 ≤ cardFactors (sigma 1 (ordProj[p] N)))) := by
    rw [← exists_componentIndex_cardFactors_add_six_le_iff ho hN]
    rintro ⟨p, hp, hle⟩
    exact (hnot p hp).not_ge hle
  have hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N := fun p hp hd => hneg (Or.inl ⟨p, hp, hd⟩)
  obtain ⟨q, hq, hq4, he, hev⟩ := euler_exponents ho hN
  have hq_prime := Nat.prime_of_mem_primeFactors hq
  have hq_odd := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hq)
  obtain ⟨_, _, hq1, hS1_empty, hsq_prop, hlg_prop, hparts, hq_notin, hdisj⟩ :=
    sixth_power_free_source_invariants ho hN hq hq4 he hev hfree
  obtain ⟨h443, _, _⟩ :=
    (sixth_power_or_large_support ho hN).resolve_left fun ⟨p, hp, hd⟩ => hfree p hp hd
  have hq_sig_le5 : cardFactors (sigma 1 (ordProj[q] N)) ≤ 5 := by
    by_contra! hgt
    exact hneg (Or.inr ⟨q, hq, Or.inl ⟨hq1, by omega⟩⟩)
  have hu_sig_le2 : ∀ u ∈ largeSources N q, cardFactors (sigma 1 (u ^ 4)) ≤ 2 := by
    intro u hu
    have hu_mem := (Finset.mem_filter.mp hu).1
    have hu4 := (hlg_prop u hu).2.2.2.2.2.2
    by_contra! hgt
    exact hneg (Or.inr ⟨u, hu_mem, Or.inr (Or.inr ⟨hu4, by rw [hu4]; omega⟩)⟩)
  let S₅₀ := (squareSources N).filter (· % 5 ≠ 1)
  let S₅₁ := (squareSources N).filter (· % 5 = 1)
  let Q₁₃ := oneModThreeLargeSources N q
  let Q₂₃ := twoModThreeLargeSources N q
  let P₂ := N.primeFactors.filter (· % 3 = 2)
  have hvac := sixth_power_free_incoming_source_vacuum ho hN hq hq4 he hev hfree
  dsimp only at hvac
  have hvac_card : 1 + 2 * S₅₀.card + 4 * Q₂₃.card ≤ cardFactors (sigma 1 (ordProj[q] N)) :=
    hvac.2.2.1
  have hS50_le2 : S₅₀.card ≤ 2 := by omega
  have hQ23_le1 : Q₂₃.card ≤ 1 := by omega
  let Q₁₃_q := Q₁₃.filter (fun u => q ∣ sigma 1 (u ^ 4))
  let Q₁₃_nq := Q₁₃.filter (fun u => ¬ q ∣ sigma 1 (u ^ 4))
  have hQ13_parts : Q₁₃ = Q₁₃_q ∪ Q₁₃_nq := by
    ext u
    simp only [Q₁₃_q, Q₁₃_nq, Finset.mem_union, Finset.mem_filter]
    by_cases h : q ∣ sigma 1 (u ^ 4) <;> tauto
  have hQ13_disj : Disjoint Q₁₃_q Q₁₃_nq := by
    apply Finset.disjoint_left.mpr
    intro u h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hQ13_card : Q₁₃.card = Q₁₃_q.card + Q₁₃_nq.card := by
    rw [hQ13_parts, Finset.card_union_of_disjoint hQ13_disj]
  have hQ13_q_le1 : Q₁₃_q.card ≤ 1 := by
    have hle : Q₁₃_q.card ≤ N.factorization q := by
      apply card_le_factorization_of_sigma_sources hN hq_odd hq_prime Q₁₃_q
      · exact (Finset.filter_subset _ _).trans
          ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
      · intro u hu
        obtain ⟨hu_Q13, hu_q⟩ := Finset.mem_filter.mp hu
        have hu_lg := (Finset.mem_filter.mp hu_Q13).1
        rw [(hlg_prop u hu_lg).2.2.2.2.2.2]
        exact hu_q
    omega
  have hQ13_nq_le : Q₁₃_nq.card ≤ S₅₁.card := by
    refine Finset.card_le_card_of_injOn (fun u => sigma 1 (u ^ 4)) ?_ ?_
    · intro u hu
      obtain ⟨hu_Q13, hu_nq⟩ := Finset.mem_filter.mp hu
      have hu_lg := (Finset.mem_filter.mp hu_Q13).1
      exact (quartic_oneModThree_prime_sigma_of_le_two ho hN hq hq4 he hev hfree
        hu_Q13 (hu_sig_le2 u hu_lg) hu_nq).2
    · intro u₁ hu₁ u₂ hu₂ heq
      have hu₁_prime := (hlg_prop u₁ (Finset.mem_filter.mp (Finset.mem_filter.mp hu₁).1).1).1
      have hu₂_prime := (hlg_prop u₂ (Finset.mem_filter.mp (Finset.mem_filter.mp hu₂).1).1).1
      dsimp only at heq
      rw [sigma_one_four hu₁_prime, sigma_one_four hu₂_prime] at heq
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
  have hS51_sub_P2 : S₅₁ ⊆ P₂ := by
    intro p hp
    have hp_sq := (Finset.mem_filter.mp hp).1
    have hp_mem := (Finset.mem_filter.mp hp_sq).1
    have hp3 := (hsq_prop p hp_sq).2.1
    exact Finset.mem_filter.mpr ⟨hp_mem, hp3⟩
  have hLHS : 2 * S₅₁.card ≤ ∑ p ∈ P₂, N.factorization p := by
    calc
      2 * S₅₁.card
          = ∑ _p ∈ S₅₁, 2 := by simp [Finset.sum_const, Nat.mul_comm]
      _ = ∑ p ∈ S₅₁, N.factorization p := by
            refine Finset.sum_congr rfl fun p hp => ?_
            exact (hsq_prop p (Finset.mem_filter.mp hp).1).2.2.2.2.2.2.symm
      _ ≤ ∑ p ∈ P₂, N.factorization p := Finset.sum_le_sum_of_subset hS51_sub_P2
  let g : ℕ → ℕ := fun r => ∑ p ∈ P₂, (sigma 1 (r ^ N.factorization r)).factorization p
  have hP2_eq_sum : (∑ p ∈ P₂, N.factorization p) = ∑ r ∈ N.primeFactors, g r := by
    calc
      ∑ p ∈ P₂, N.factorization p
          = ∑ p ∈ P₂, ∑ r ∈ N.primeFactors, (sigma 1 (r ^ N.factorization r)).factorization p := by
            refine Finset.sum_congr rfl fun p hp => ?_
            have hp_mem := (Finset.mem_filter.mp hp).1
            have hp_prime := Nat.prime_of_mem_primeFactors hp_mem
            have hp_odd := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp_mem)
            exact factorization_eq_sum_sigma_factorizations hN hp_odd hp_prime
      _ = ∑ r ∈ N.primeFactors, g r := Finset.sum_comm
  have hQ_parts : largeSources N q = Q₁₃ ∪ Q₂₃ := by
    ext r
    simp only [Q₁₃, Q₂₃, oneModThreeLargeSources, twoModThreeLargeSources,
      Finset.mem_union, Finset.mem_filter]
    by_cases h : r % 3 = 1 <;> tauto
  have hQ_disj : Disjoint Q₁₃ Q₂₃ := by
    apply Finset.disjoint_left.mpr
    intro r h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hS_parts : squareSources N = S₅₁ ∪ S₅₀ := by
    ext r
    simp only [S₅₁, S₅₀, Finset.mem_union, Finset.mem_filter]
    by_cases h : r % 5 = 1 <;> tauto
  have hS_disj : Disjoint S₅₁ S₅₀ := by
    apply Finset.disjoint_left.mpr
    intro r h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hsum_split :
      (∑ r ∈ N.primeFactors, g r) =
        g q + (∑ s ∈ squareSources N, g s) + (∑ u ∈ Q₁₃, g u) + ∑ u ∈ Q₂₃, g u := by
    rw [hparts, Finset.sum_insert hq_notin, Finset.sum_union hdisj, hQ_parts,
      Finset.sum_union hQ_disj]
    ring
  have hg_q : g q ≤ 5 :=
    (sum_factorization_le_cardFactors P₂ (sigma 1 (ordProj[q] N))).trans hq_sig_le5
  have hg_sq : (∑ s ∈ squareSources N, g s) = 0 := by
    refine Finset.sum_eq_zero fun s hs => Finset.sum_eq_zero fun p hp => ?_
    have hs_prime := (hsq_prop s hs).1
    have hs_exp := (hsq_prop s hs).2.2.2.2.2.2
    obtain ⟨hp_mem, hp3⟩ := Finset.mem_filter.mp hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp_mem
    have hnot : ¬ p ∣ sigma 1 (s ^ 2) := by
      intro hd
      rw [sigma_one_sq hs_prime] at hd
      rcases prime_dvd_sq_add_self_add_one hp_prime hd with rfl | hmod
      · exact (by decide : 3 % 3 ≠ 2) hp3
      · omega
    rw [hs_exp]
    exact Nat.factorization_eq_zero_of_not_dvd hnot
  have hg_Q23 : (∑ u ∈ Q₂₃, g u) ≤ 2 * Q₂₃.card := by
    calc
      ∑ u ∈ Q₂₃, g u
          ≤ ∑ _u ∈ Q₂₃, 2 := by
            refine Finset.sum_le_sum fun u hu => ?_
            have hu_lg := (Finset.mem_filter.mp hu).1
            have hu_exp := (hlg_prop u hu_lg).2.2.2.2.2.2
            dsimp only [g]
            rw [hu_exp]
            exact (sum_factorization_le_cardFactors P₂ _).trans (hu_sig_le2 u hu_lg)
      _ = 2 * Q₂₃.card := by simp [Finset.sum_const, Nat.mul_comm]
  have hg_Q13 : (∑ u ∈ Q₁₃, g u) ≤ Q₁₃_q.card + Q₁₃.card := by
    have hsum_Q13 : (∑ u ∈ Q₁₃, g u) = (∑ u ∈ Q₁₃_q, g u) + ∑ u ∈ Q₁₃_nq, g u := by
      rw [hQ13_parts, Finset.sum_union hQ13_disj]
    have h1 : (∑ u ∈ Q₁₃_q, g u) ≤ 2 * Q₁₃_q.card := by
      calc
        ∑ u ∈ Q₁₃_q, g u
            ≤ ∑ _u ∈ Q₁₃_q, 2 := by
              refine Finset.sum_le_sum fun u hu => ?_
              have hu_Q13 := (Finset.mem_filter.mp hu).1
              have hu_lg := (Finset.mem_filter.mp hu_Q13).1
              have hu_exp := (hlg_prop u hu_lg).2.2.2.2.2.2
              dsimp only [g]
              rw [hu_exp]
              exact (sum_factorization_le_cardFactors P₂ _).trans (hu_sig_le2 u hu_lg)
        _ = 2 * Q₁₃_q.card := by simp [Finset.sum_const, Nat.mul_comm]
    have h2 : (∑ u ∈ Q₁₃_nq, g u) ≤ Q₁₃_nq.card := by
      calc
        ∑ u ∈ Q₁₃_nq, g u
            ≤ ∑ _u ∈ Q₁₃_nq, 1 := by
              refine Finset.sum_le_sum fun u hu => ?_
              obtain ⟨hu_Q13, hu_nq⟩ := Finset.mem_filter.mp hu
              have hu_lg := (Finset.mem_filter.mp hu_Q13).1
              have hu_exp := (hlg_prop u hu_lg).2.2.2.2.2.2
              have hsig_prime := (quartic_oneModThree_prime_sigma_of_le_two ho hN hq hq4 he hev
                hfree hu_Q13 (hu_sig_le2 u hu_lg) hu_nq).1
              dsimp only [g]
              rw [hu_exp]
              exact (sum_factorization_le_cardFactors P₂ _).trans
                (cardFactors_apply_prime hsig_prime).le
        _ = Q₁₃_nq.card := by simp [Finset.sum_const]
    omega
  have hS51_le9 : S₅₁.card ≤ 9 := by
    rw [hP2_eq_sum, hsum_split, hg_sq] at hLHS
    omega
  have hcard_total :
      N.primeFactors.card = 1 + S₅₁.card + S₅₀.card + Q₁₃.card + Q₂₃.card := by
    rw [hparts, Finset.card_insert_of_notMem hq_notin, Finset.card_union_of_disjoint hdisj,
      hS_parts, Finset.card_union_of_disjoint hS_disj,
      hQ_parts, Finset.card_union_of_disjoint hQ_disj]
    omega
  omega

/-- The candidate set of odd perfect numbers with no six-factor component-index drop is empty. -/
theorem all_componentIndex_lt_six_drop_eq_empty :
    {N : ℕ | Odd N ∧ N.Perfect ∧
      ∀ p ∈ N.primeFactors, cardFactors N < cardFactors (componentIndex N p) + 6} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro N ⟨ho, hN, hnear⟩
  obtain ⟨p, hp, hdrop⟩ := exists_componentIndex_cardFactors_add_six_le ho hN
  exact (hnear p hp).not_ge hdrop

end OddPerfect
