module

public import OddPerfect.GlobalWave7Obstruction
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sixth-Power-Free Bipartite Parity and Exact Multiplicity Identities

Formalizes:
1. `mod_three_of_all_prime_divisors_two_mod_three`: Pure `ℕ` parity invariant relating `n % 3`
   to `cardFactors n` when every prime divisor of `n` satisfies `w % 3 = 2`.
2. `sixth_power_free_quartic_cardFactors_mod_three_dichotomy`: On a sixth-power-free odd perfect
   number `N`:
   - every `u ∈ oneModThreeLargeSources N q` with `¬ q ∣ sigma 1 (u ^ 4)` has all prime factors of
     `sigma 1 (u ^ 4)` in `S₅₁ := (squareSources N).filter (· % 5 = 1)` (with `% 3 = 2`),
     `Odd (cardFactors (sigma 1 (u ^ 4)))`, and `(sigma 1 (u ^ 4)).Prime ∨ 3 ≤ cardFactors (sigma 1 (u ^ 4))`;
   - every `u ∈ twoModThreeLargeSources N q` automatically satisfies `¬ q ∣ sigma 1 (u ^ 4)`, has all
     prime factors of `sigma 1 (u ^ 4)` in `S₅₁`, `Even (cardFactors (sigma 1 (u ^ 4)))`,
     `¬ (sigma 1 (u ^ 4)).Prime`, and `2 ≤ cardFactors (sigma 1 (u ^ 4))`.
3. `sixth_power_free_bipartite_multiplicity_identities`: The two exact bipartite prime-factor
   conservation identities between `largeSources N q`, `S₅₁`, `squareSources N`, and `Q₁₃`.
4. `sixth_power_free_sharpened_quartic_to_S51_bound`: Unconditional sharpened inequality
   `3 * (oneModThreeLargeSources N q).card + 2 * (twoModThreeLargeSources N q).card ≤
    4 * ((squareSources N).filter (· % 5 = 1)).card + 3`.
-/

public section

namespace OddPerfect

open ArithmeticFunction Finset

private theorem sigma_one_prime_local {p : ℕ} (hp : p.Prime) : sigma 1 p = p + 1 := by
  rw [← pow_one p, sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

private theorem sigma_one_sq_local {p : ℕ} (hp : p.Prime) : sigma 1 (p ^ 2) = p ^ 2 + p + 1 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

private theorem sigma_one_four_local {p : ℕ} (hp : p.Prime) :
    sigma 1 (p ^ 4) = p ^ 4 + p ^ 3 + p ^ 2 + p + 1 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

private theorem cardFactors_eq_sum_factorization_of_subset {n : ℕ} {S : Finset ℕ}
    (hsub : n.primeFactors ⊆ S) :
    cardFactors n = ∑ p ∈ S, n.factorization p := by
  have h1 : cardFactors n = ∑ p ∈ n.primeFactors, n.factorization p := by
    rw [cardFactors_eq_sum_factorization]
    rfl
  rw [h1]
  refine Finset.sum_subset hsub fun p _ hp_not => ?_
  exact Finsupp.notMem_support_iff.mp hp_not

private theorem sixth_power_free_source_invariants_local {N q : ℕ}
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

/-- **Pure `ℕ` Parity Lemma**: if every prime divisor `w` of `n` (`0 < n`) satisfies `w % 3 = 2`,
then `n % 3 = 1` when `cardFactors n` is even, and `n % 3 = 2` when `cardFactors n` is odd. -/
theorem mod_three_of_all_prime_divisors_two_mod_three {n : ℕ}
    (hn : 0 < n) (hw : ∀ w : ℕ, w.Prime → w ∣ n → w % 3 = 2) :
    (Even (cardFactors n) → n % 3 = 1) ∧ (Odd (cardFactors n) → n % 3 = 2) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hn) with h1 | hn_gt1
    · have hn1 : n = 1 := h1.symm
      subst hn1
      constructor
      · intro _
        norm_num
      · intro hodd
        rw [cardFactors_one] at hodd
        exact absurd hodd (by decide)
    · let w := n.minFac
      have hw_prime : w.Prime := Nat.minFac_prime (by omega)
      have hw_dvd : w ∣ n := Nat.minFac_dvd n
      let m := n / w
      have hn_eq : n = w * m := (Nat.mul_div_cancel' hw_dvd).symm
      have hm_pos : 0 < m := Nat.div_pos (Nat.le_of_dvd hn hw_dvd) hw_prime.pos
      have hm_lt : m < n := Nat.div_lt_self hn hw_prime.one_lt
      have hm_hw : ∀ v : ℕ, v.Prime → v ∣ m → v % 3 = 2 := fun v hv hvm =>
        hw v hv (hn_eq ▸ hvm.trans (dvd_mul_left m w))
      obtain ⟨ih_even, ih_odd⟩ := ih m hm_lt hm_pos hm_hw
      have hcard : cardFactors n = 1 + cardFactors m := by
        rw [hn_eq, cardFactors_mul hw_prime.ne_zero hm_pos.ne', cardFactors_apply_prime hw_prime]
      have hw_mod3 : w % 3 = 2 := hw w hw_prime hw_dvd
      have hn_mod3 : n % 3 = (2 * (m % 3)) % 3 := by
        rw [hn_eq, Nat.mul_mod, hw_mod3]
      constructor
      · intro heven
        have hm_odd : Odd (cardFactors m) := by
          have h1 := Nat.even_iff.mp heven
          rw [hcard] at h1
          exact Nat.odd_iff.mpr (by omega)
        have hm3 := ih_odd hm_odd
        omega
      · intro hodd
        have hm_even : Even (cardFactors m) := by
          have h1 := Nat.odd_iff.mp hodd
          rw [hcard] at h1
          exact Nat.even_iff.mpr (by omega)
        have hm3 := ih_even hm_even
        omega

private theorem quartic_sigma_prime_factor_classification {N q u : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N)
    (hu : u ∈ largeSources N q) :
    1 < sigma 1 (u ^ 4) ∧
    (∀ w ∈ (sigma 1 (u ^ 4)).primeFactors,
      w = q ∨ (w ∈ (squareSources N).filter (· % 5 = 1) ∧ w % 3 = 2)) := by
  obtain ⟨h3, _, _, _, hsq_prop, hlg_prop, hparts, _, _⟩ :=
    sixth_power_free_source_invariants_local ho hN hq hq4 he hev hfree
  obtain ⟨hu_prime, hu5, _, _, _, _, hu_exp⟩ := hlg_prop u hu
  have hu_ge3 : 3 ≤ u := by
    have := hu_prime.two_le
    omega
  have hu_odd : Odd u := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hu).1)
  have hsig_eq : sigma 1 (u ^ 4) = u ^ 4 + u ^ 3 + u ^ 2 + u + 1 := sigma_one_four_local hu_prime
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
  refine ⟨hsig_gt1, fun w hw => ?_⟩
  have hw_prime := Nat.prime_of_mem_primeFactors hw
  have hw_dvd := Nat.dvd_of_mem_primeFactors hw
  by_cases hwq : w = q
  · exact Or.inl hwq
  · right
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
    have hw_union : w ∈ squareSources N ∪ largeSources N q := by
      rcases Finset.mem_insert.mp (hparts ▸ hw_mem) with hq_eq | hmem
      · exact (hwq hq_eq).elim
      · exact hmem
    have hw_sq : w ∈ squareSources N := by
      rcases Finset.mem_union.mp hw_union with hw_sq | hw_lg
      · exact hw_sq
      · exact ((hlg_prop w hw_lg).2.1 hw_mod5).elim
    have hw_mod3 : w % 3 = 2 := (hsq_prop w hw_sq).2.1
    exact ⟨Finset.mem_filter.mpr ⟨hw_sq, hw_mod5⟩, hw_mod3⟩

/-- **Sixth-Power-Free Quartic `cardFactors` Mod-3 Dichotomy**: on a sixth-power-free odd perfect
number `N`,
1. every `u ∈ oneModThreeLargeSources N q` with `¬ q ∣ sigma 1 (u ^ 4)` sends all prime factors of
   `sigma 1 (u ^ 4)` into `S₅₁ := (squareSources N).filter (· % 5 = 1)`, has
   `Odd (cardFactors (sigma 1 (u ^ 4)))`, and satisfies
   `(sigma 1 (u ^ 4)).Prime ∨ 3 ≤ cardFactors (sigma 1 (u ^ 4))`;
2. every `u ∈ twoModThreeLargeSources N q` automatically satisfies `¬ q ∣ sigma 1 (u ^ 4)`, sends
   all prime factors of `sigma 1 (u ^ 4)` into `S₅₁`, has `Even (cardFactors (sigma 1 (u ^ 4)))`,
   is not prime, and satisfies `2 ≤ cardFactors (sigma 1 (u ^ 4))`. -/
theorem sixth_power_free_quartic_cardFactors_mod_three_dichotomy {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    (∀ u ∈ oneModThreeLargeSources N q, ¬ q ∣ sigma 1 (u ^ 4) →
      (∀ w ∈ (sigma 1 (u ^ 4)).primeFactors,
        w ∈ (squareSources N).filter (· % 5 = 1) ∧ w % 3 = 2) ∧
      Odd (cardFactors (sigma 1 (u ^ 4))) ∧
      ((sigma 1 (u ^ 4)).Prime ∨ 3 ≤ cardFactors (sigma 1 (u ^ 4)))) ∧
    (∀ u ∈ twoModThreeLargeSources N q,
      ¬ q ∣ sigma 1 (u ^ 4) ∧
      (∀ w ∈ (sigma 1 (u ^ 4)).primeFactors,
        w ∈ (squareSources N).filter (· % 5 = 1) ∧ w % 3 = 2) ∧
      Even (cardFactors (sigma 1 (u ^ 4))) ∧
      ¬ (sigma 1 (u ^ 4)).Prime ∧
      2 ≤ cardFactors (sigma 1 (u ^ 4))) := by
  obtain ⟨h3, _, _, _, _, hlg_prop, _, _, hdisj⟩ :=
    sixth_power_free_source_invariants_local ho hN hq hq4 he hev hfree
  constructor
  · intro u hu hnq
    obtain ⟨hu_lg, hu3⟩ := Finset.mem_filter.mp hu
    have hu_prime := (hlg_prop u hu_lg).1
    obtain ⟨hsig_gt1, hclass⟩ :=
      quartic_sigma_prime_factor_classification ho hN hq hq4 he hev hfree hu_lg
    have hw_prop : ∀ w ∈ (sigma 1 (u ^ 4)).primeFactors,
        w ∈ (squareSources N).filter (· % 5 = 1) ∧ w % 3 = 2 := by
      intro w hw
      rcases hclass w hw with rfl | hmem
      · exact (hnq (Nat.dvd_of_mem_primeFactors hw)).elim
      · exact hmem
    have hw_div_mod3 : ∀ w : ℕ, w.Prime → w ∣ sigma 1 (u ^ 4) → w % 3 = 2 := by
      intro w hw_prime hw_dvd
      have hw_mem : w ∈ (sigma 1 (u ^ 4)).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hw_prime, hw_dvd, by omega⟩
      exact (hw_prop w hw_mem).2
    have hsig_mod3 : sigma 1 (u ^ 4) % 3 = 2 := by
      rw [sigma_one_four_local hu_prime]
      have hc : u ≡ 1 [MOD 3] := hu3
      have hp : u ^ 4 + u ^ 3 + u ^ 2 + u + 1 ≡
          1 ^ 4 + 1 ^ 3 + 1 ^ 2 + 1 + 1 [MOD 3] :=
        ((((hc.pow 4).add (hc.pow 3)).add (hc.pow 2)).add hc).add (Nat.ModEq.refl 1)
      change (u ^ 4 + u ^ 3 + u ^ 2 + u + 1) % 3 = (1 ^ 4 + 1 ^ 3 + 1 ^ 2 + 1 + 1) % 3 at hp
      omega
    have hparity := mod_three_of_all_prime_divisors_two_mod_three (by omega : 0 < sigma 1 (u ^ 4)) hw_div_mod3
    have hodd : Odd (cardFactors (sigma 1 (u ^ 4))) := by
      by_contra hnot_odd
      have heven : Even (cardFactors (sigma 1 (u ^ 4))) := Nat.not_odd_iff_even.mp hnot_odd
      have h1 := hparity.1 heven
      omega
    have hcard_pos : 0 < cardFactors (sigma 1 (u ^ 4)) :=
      cardFactors_pos_iff_one_lt.mpr hsig_gt1
    have hodd_val := Nat.odd_iff.mp hodd
    have hbranch : (sigma 1 (u ^ 4)).Prime ∨ 3 ≤ cardFactors (sigma 1 (u ^ 4)) := by
      by_cases h1 : cardFactors (sigma 1 (u ^ 4)) = 1
      · exact Or.inl (cardFactors_eq_one_iff_prime.mp h1)
      · right
        omega
    exact ⟨hw_prop, hodd, hbranch⟩
  · obtain ⟨m, r₀, hm_odd, hqm, hform, _, _, _, _, _, _, _, huniq, hmirror⟩ :=
      sixth_power_free_unique_q_source_mirror_dichotomy ho hN hq hq4 he hev hfree
    have hq_prime := Nat.prime_of_mem_primeFactors hq
    have hm0 : m ≠ 0 := hm_odd.pos.ne'
    have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
    intro u hu
    obtain ⟨hu_lg, hu_not3⟩ := Finset.mem_filter.mp hu
    obtain ⟨hu_prime, _, _, hu3, _, huq, hu_exp⟩ := hlg_prop u hu_lg
    have hu_mem := (Finset.mem_filter.mp hu_lg).1
    have hu_dvd_N : u ∣ N := Nat.dvd_of_mem_primeFactors hu_mem
    have hu_dvd_m : u ∣ m := by
      have hu_m2 : u ∣ m ^ 2 := by
        have h1 : u ∣ q * m ^ 2 := hform ▸ hu_dvd_N
        exact (hu_prime.dvd_mul.mp h1).resolve_left fun hu_q =>
          huq (((Nat.dvd_prime hq_prime).mp hu_q).resolve_left hu_prime.ne_one)
      exact hu_prime.dvd_of_dvd_pow hu_m2
    have hu_m : u ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hu_prime, hu_dvd_m, hm0⟩
    have hu_m_fac : 2 * m.factorization u = 4 := by
      have hfac : N.factorization u = 2 * m.factorization u := by
        rw [hform, Nat.factorization_mul hq_prime.ne_zero hm20, Finsupp.add_apply]
        have hnotq : ¬ u ∣ q := fun h =>
          huq (((Nat.dvd_prime hq_prime).mp h).resolve_left hu_prime.ne_one)
        rw [Nat.factorization_eq_zero_of_not_dvd hnotq, zero_add, pow_two,
          Nat.factorization_mul hm0 hm0, Finsupp.add_apply, ← two_mul]
      omega
    have hnq : ¬ q ∣ sigma 1 (u ^ 4) := by
      intro hd
      have hd' : q ∣ sigma 1 (u ^ (2 * m.factorization u)) := by
        rw [hu_m_fac]
        exact hd
      have hur0 : u = r₀ := huniq u hu_m hd'
      subst hur0
      rcases hmirror with ⟨hr₀_sq, _⟩ | ⟨_, hr₀_3, _⟩
      · exact Finset.disjoint_left.mp hdisj hr₀_sq hu_lg
      · exact hu_not3 hr₀_3
    obtain ⟨hsig_gt1, hclass⟩ :=
      quartic_sigma_prime_factor_classification ho hN hq hq4 he hev hfree hu_lg
    have hw_prop : ∀ w ∈ (sigma 1 (u ^ 4)).primeFactors,
        w ∈ (squareSources N).filter (· % 5 = 1) ∧ w % 3 = 2 := by
      intro w hw
      rcases hclass w hw with rfl | hmem
      · exact (hnq (Nat.dvd_of_mem_primeFactors hw)).elim
      · exact hmem
    have hw_div_mod3 : ∀ w : ℕ, w.Prime → w ∣ sigma 1 (u ^ 4) → w % 3 = 2 := by
      intro w hw_prime hw_dvd
      have hw_mem : w ∈ (sigma 1 (u ^ 4)).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hw_prime, hw_dvd, by omega⟩
      exact (hw_prop w hw_mem).2
    have hu_mod3 : u % 3 = 2 := by
      have hnot0 : u % 3 ≠ 0 := fun h0 => h3 ((Nat.dvd_of_mod_eq_zero h0).trans hu_dvd_N)
      omega
    have hsig_mod3 : sigma 1 (u ^ 4) % 3 = 1 := by
      rw [sigma_one_four_local hu_prime]
      have hc : u ≡ 2 [MOD 3] := hu_mod3
      have hp : u ^ 4 + u ^ 3 + u ^ 2 + u + 1 ≡
          2 ^ 4 + 2 ^ 3 + 2 ^ 2 + 2 + 1 [MOD 3] :=
        ((((hc.pow 4).add (hc.pow 3)).add (hc.pow 2)).add hc).add (Nat.ModEq.refl 1)
      change (u ^ 4 + u ^ 3 + u ^ 2 + u + 1) % 3 = (2 ^ 4 + 2 ^ 3 + 2 ^ 2 + 2 + 1) % 3 at hp
      omega
    have hparity := mod_three_of_all_prime_divisors_two_mod_three (by omega : 0 < sigma 1 (u ^ 4)) hw_div_mod3
    have heven : Even (cardFactors (sigma 1 (u ^ 4))) := by
      by_contra hnot_even
      have hodd : Odd (cardFactors (sigma 1 (u ^ 4))) := Nat.not_even_iff_odd.mp hnot_even
      have h2 := hparity.2 hodd
      omega
    have hcard_pos : 0 < cardFactors (sigma 1 (u ^ 4)) :=
      cardFactors_pos_iff_one_lt.mpr hsig_gt1
    have heven_val := Nat.even_iff.mp heven
    have hge2 : 2 ≤ cardFactors (sigma 1 (u ^ 4)) := by omega
    have hnot_prime : ¬ (sigma 1 (u ^ 4)).Prime := by
      intro hp
      have := cardFactors_apply_prime hp
      omega
    exact ⟨hnq, hw_prop, heven, hnot_prime, hge2⟩

/-- **Bipartite Prime-Factor Multiplicity Conservation Identities**: on any sixth-power-free odd
perfect number `N`,
1. `(∑ u ∈ largeSources N q, cardFactors (sigma 1 (u ^ 4))) + (∑ p ∈ S₅₁, ((q + 1) / 2).factorization p) = 2 * S₅₁.card + ∑ u ∈ largeSources N q, (sigma 1 (u ^ 4)).factorization q`
2. `(∑ s ∈ squareSources N, cardFactors (sigma 1 (s ^ 2))) + (∑ u ∈ Q₁₃, ((q + 1) / 2).factorization u) = 4 * Q₁₃.card + ∑ s ∈ squareSources N, (sigma 1 (s ^ 2)).factorization q`
where `S₅₁ := (squareSources N).filter (· % 5 = 1)` and `Q₁₃ := oneModThreeLargeSources N q`. -/
theorem sixth_power_free_bipartite_multiplicity_identities {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    let S₅₁ := (squareSources N).filter (· % 5 = 1)
    let Q₁₃ := oneModThreeLargeSources N q
    ((∑ u ∈ largeSources N q, cardFactors (sigma 1 (u ^ 4))) +
      (∑ p ∈ S₅₁, ((q + 1) / 2).factorization p) =
      2 * S₅₁.card + ∑ u ∈ largeSources N q, (sigma 1 (u ^ 4)).factorization q) ∧
    ((∑ s ∈ squareSources N, cardFactors (sigma 1 (s ^ 2))) +
      (∑ u ∈ Q₁₃, ((q + 1) / 2).factorization u) =
      4 * Q₁₃.card + ∑ s ∈ squareSources N, (sigma 1 (s ^ 2)).factorization q) := by
  intro S₅₁ Q₁₃
  obtain ⟨h3, _, hq1, _, hsq_prop, hlg_prop, hparts, hq_notin, hdisj⟩ :=
    sixth_power_free_source_invariants_local ho hN hq hq4 he hev hfree
  have hq_prime := Nat.prime_of_mem_primeFactors hq
  have hq_odd : Odd q := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hq)
  have hhalf_ne0 : (q + 1) / 2 ≠ 0 := by
    have := hq_prime.two_le
    omega
  have hsig_q : sigma 1 (q ^ N.factorization q) = 2 * ((q + 1) / 2) := by
    rw [hq1, pow_one, sigma_one_prime_local hq_prime]
    omega
  have hq_notin_S51 : q ∉ S₅₁ := fun h =>
    hq_notin (Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mp h).1))
  have hq_notin_Q13 : q ∉ Q₁₃ := fun h =>
    hq_notin (Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mp h).1))
  have hsq_not_dvd_two_mod3 :
      ∀ p : ℕ, p.Prime → p % 3 = 2 → ∀ s ∈ squareSources N, ¬ p ∣ sigma 1 (s ^ 2) := by
    intro p hp_prime hp3 s hs hd
    have hs_prime := (hsq_prop s hs).1
    rw [sigma_one_sq_local hs_prime] at hd
    rcases prime_dvd_sq_add_self_add_one hp_prime hd with rfl | hmod
    · exact (by decide : 3 % 3 ≠ 2) hp3
    · omega
  constructor
  · have hcard_u : ∀ u ∈ largeSources N q,
        cardFactors (sigma 1 (u ^ 4)) =
          (sigma 1 (u ^ 4)).factorization q + ∑ p ∈ S₅₁, (sigma 1 (u ^ 4)).factorization p := by
      intro u hu
      have hclass := (quartic_sigma_prime_factor_classification ho hN hq hq4 he hev hfree hu).2
      have hsub : (sigma 1 (u ^ 4)).primeFactors ⊆ insert q S₅₁ := by
        intro w hw
        rcases hclass w hw with hwq | ⟨hw_S51, _⟩
        · rw [hwq]
          exact Finset.mem_insert_self q S₅₁
        · exact Finset.mem_insert_of_mem hw_S51
      rw [cardFactors_eq_sum_factorization_of_subset hsub, Finset.sum_insert hq_notin_S51]
    have hsum_card :
        (∑ u ∈ largeSources N q, cardFactors (sigma 1 (u ^ 4))) =
          (∑ u ∈ largeSources N q, (sigma 1 (u ^ 4)).factorization q) +
            ∑ p ∈ S₅₁, ∑ u ∈ largeSources N q, (sigma 1 (u ^ 4)).factorization p := by
      calc
        ∑ u ∈ largeSources N q, cardFactors (sigma 1 (u ^ 4))
            = ∑ u ∈ largeSources N q,
                ((sigma 1 (u ^ 4)).factorization q +
                  ∑ p ∈ S₅₁, (sigma 1 (u ^ 4)).factorization p) :=
              Finset.sum_congr rfl hcard_u
        _ = (∑ u ∈ largeSources N q, (sigma 1 (u ^ 4)).factorization q) +
              ∑ u ∈ largeSources N q, ∑ p ∈ S₅₁, (sigma 1 (u ^ 4)).factorization p :=
            Finset.sum_add_distrib
        _ = (∑ u ∈ largeSources N q, (sigma 1 (u ^ 4)).factorization q) +
              ∑ p ∈ S₅₁, ∑ u ∈ largeSources N q, (sigma 1 (u ^ 4)).factorization p := by
            rw [Finset.sum_comm]
    have hpoint_p : ∀ p ∈ S₅₁,
        ((q + 1) / 2).factorization p +
          ∑ u ∈ largeSources N q, (sigma 1 (u ^ 4)).factorization p = 2 := by
      intro p hp
      have hp_sq := (Finset.mem_filter.mp hp).1
      obtain ⟨hp_prime, hp3, hp2, _, _, _, hp_exp⟩ := hsq_prop p hp_sq
      have hp_odd : Odd p := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp_sq).1)
      have hsum := factorization_eq_sum_sigma_factorizations hN hp_odd hp_prime
      rw [hparts, Finset.sum_insert hq_notin, Finset.sum_union hdisj] at hsum
      have hq_term : (sigma 1 (q ^ N.factorization q)).factorization p =
          ((q + 1) / 2).factorization p := by
        rw [hsig_q, Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) hhalf_ne0, Finsupp.add_apply]
        have hnot2 : ¬ p ∣ 2 := fun h =>
          hp2 (((Nat.dvd_prime Nat.prime_two).mp h).resolve_left hp_prime.ne_one)
        rw [Nat.factorization_eq_zero_of_not_dvd hnot2, zero_add]
      have hsq_term :
          (∑ s ∈ squareSources N, (sigma 1 (s ^ N.factorization s)).factorization p) = 0 := by
        refine Finset.sum_eq_zero fun s hs => ?_
        rw [(hsq_prop s hs).2.2.2.2.2.2]
        exact Nat.factorization_eq_zero_of_not_dvd (hsq_not_dvd_two_mod3 p hp_prime hp3 s hs)
      have hlg_term :
          (∑ u ∈ largeSources N q, (sigma 1 (u ^ N.factorization u)).factorization p) =
            ∑ u ∈ largeSources N q, (sigma 1 (u ^ 4)).factorization p := by
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [(hlg_prop u hu).2.2.2.2.2.2]
      rw [hp_exp, hq_term, hsq_term, hlg_term, zero_add] at hsum
      exact hsum.symm
    have hsum_p :
        (∑ p ∈ S₅₁, ((q + 1) / 2).factorization p) +
          (∑ p ∈ S₅₁, ∑ u ∈ largeSources N q, (sigma 1 (u ^ 4)).factorization p) =
            2 * S₅₁.card := by
      calc
        (∑ p ∈ S₅₁, ((q + 1) / 2).factorization p) +
            (∑ p ∈ S₅₁, ∑ u ∈ largeSources N q, (sigma 1 (u ^ 4)).factorization p)
            = ∑ p ∈ S₅₁,
                (((q + 1) / 2).factorization p +
                  ∑ u ∈ largeSources N q, (sigma 1 (u ^ 4)).factorization p) :=
              Finset.sum_add_distrib.symm
        _ = ∑ _p ∈ S₅₁, 2 := Finset.sum_congr rfl hpoint_p
        _ = 2 * S₅₁.card := by simp [Finset.sum_const, Nat.mul_comm]
    omega
  · have hcard_s : ∀ s ∈ squareSources N,
        cardFactors (sigma 1 (s ^ 2)) =
          (sigma 1 (s ^ 2)).factorization q + ∑ u ∈ Q₁₃, (sigma 1 (s ^ 2)).factorization u := by
      intro s hs
      obtain ⟨hs_prime, _, _, _, _, _, hs_exp⟩ := hsq_prop s hs
      have hs_odd : Odd s := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hs).1)
      have hsig_sq : sigma 1 (s ^ 2) = s ^ 2 + s + 1 := sigma_one_sq_local hs_prime
      have hsig_odd : Odd (sigma 1 (s ^ 2)) := by
        rw [hsig_sq]
        have hs2 : Odd (s ^ 2) := hs_odd.pow
        have hs1 : Even (s ^ 2 + s) := hs2.add_odd hs_odd
        exact hs1.add_one
      have hsub : (sigma 1 (s ^ 2)).primeFactors ⊆ insert q Q₁₃ := by
        intro w hw
        have hw_prime := Nat.prime_of_mem_primeFactors hw
        have hw_dvd := Nat.dvd_of_mem_primeFactors hw
        by_cases hwq : w = q
        · exact hwq ▸ Finset.mem_insert_self q Q₁₃
        · apply Finset.mem_insert_of_mem
          have hw_odd : Odd w := hsig_odd.of_dvd_nat hw_dvd
          have hw_N : w ∣ N := by
            apply dvd_perfect_of_exact_prime_pow hN hs_prime (hs_exp ▸ Nat.ordProj_dvd N s)
              ((hs_prime.pow_dvd_iff_le_factorization hN.2.ne').not.mpr (by omega))
              hw_prime hw_odd
            rw [← sigma_one_apply]
            exact hw_dvd
          have hw_mem : w ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hw_prime, hw_N, hN.2.ne'⟩
          have hw_mod3 : w % 3 = 1 := by
            rcases prime_dvd_sq_add_self_add_one hw_prime (hsig_sq ▸ hw_dvd) with rfl | h1
            · exact (h3 hw_N).elim
            · exact h1
          have hw_union : w ∈ squareSources N ∪ largeSources N q := by
            rcases Finset.mem_insert.mp (hparts ▸ hw_mem) with hq_eq | hmem
            · exact (hwq hq_eq).elim
            · exact hmem
          have hw_lg : w ∈ largeSources N q := by
            rcases Finset.mem_union.mp hw_union with hw_sq | hw_lg
            · have := (hsq_prop w hw_sq).2.1
              omega
            · exact hw_lg
          exact Finset.mem_filter.mpr ⟨hw_lg, hw_mod3⟩
      rw [cardFactors_eq_sum_factorization_of_subset hsub, Finset.sum_insert hq_notin_Q13]
    have hsum_card :
        (∑ s ∈ squareSources N, cardFactors (sigma 1 (s ^ 2))) =
          (∑ s ∈ squareSources N, (sigma 1 (s ^ 2)).factorization q) +
            ∑ u ∈ Q₁₃, ∑ s ∈ squareSources N, (sigma 1 (s ^ 2)).factorization u := by
      calc
        ∑ s ∈ squareSources N, cardFactors (sigma 1 (s ^ 2))
            = ∑ s ∈ squareSources N,
                ((sigma 1 (s ^ 2)).factorization q +
                  ∑ u ∈ Q₁₃, (sigma 1 (s ^ 2)).factorization u) :=
              Finset.sum_congr rfl hcard_s
        _ = (∑ s ∈ squareSources N, (sigma 1 (s ^ 2)).factorization q) +
              ∑ s ∈ squareSources N, ∑ u ∈ Q₁₃, (sigma 1 (s ^ 2)).factorization u :=
            Finset.sum_add_distrib
        _ = (∑ s ∈ squareSources N, (sigma 1 (s ^ 2)).factorization q) +
              ∑ u ∈ Q₁₃, ∑ s ∈ squareSources N, (sigma 1 (s ^ 2)).factorization u := by
            rw [Finset.sum_comm]
    have hpoint_u : ∀ u ∈ Q₁₃,
        ((q + 1) / 2).factorization u +
          ∑ s ∈ squareSources N, (sigma 1 (s ^ 2)).factorization u = 4 := by
      intro u hu
      have hu_lg := (Finset.mem_filter.mp hu).1
      obtain ⟨hu_prime, _, hu2, _, _, _, hu_exp⟩ := hlg_prop u hu_lg
      have hu_odd : Odd u := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hu_lg).1)
      have hsum := factorization_eq_sum_sigma_factorizations hN hu_odd hu_prime
      rw [hparts, Finset.sum_insert hq_notin, Finset.sum_union hdisj] at hsum
      have hq_term : (sigma 1 (q ^ N.factorization q)).factorization u =
          ((q + 1) / 2).factorization u := by
        rw [hsig_q, Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) hhalf_ne0, Finsupp.add_apply]
        have hnot2 : ¬ u ∣ 2 := fun h =>
          hu2 (((Nat.dvd_prime Nat.prime_two).mp h).resolve_left hu_prime.ne_one)
        rw [Nat.factorization_eq_zero_of_not_dvd hnot2, zero_add]
      have hsq_term :
          (∑ s ∈ squareSources N, (sigma 1 (s ^ N.factorization s)).factorization u) =
            ∑ s ∈ squareSources N, (sigma 1 (s ^ 2)).factorization u := by
        refine Finset.sum_congr rfl fun s hs => ?_
        rw [(hsq_prop s hs).2.2.2.2.2.2]
      have hlg_term :
          (∑ v ∈ largeSources N q, (sigma 1 (v ^ N.factorization v)).factorization u) = 0 := by
        refine Finset.sum_eq_zero fun v hv => ?_
        rw [(hlg_prop v hv).2.2.2.2.2.2]
        exact Nat.factorization_eq_zero_of_not_dvd
          (sixth_power_free_quartic_mutual_exclusion ho hN hq hq4 he hev hfree u hu_lg v hv)
      rw [hu_exp, hq_term, hsq_term, hlg_term, add_zero] at hsum
      exact hsum.symm
    have hsum_u :
        (∑ u ∈ Q₁₃, ((q + 1) / 2).factorization u) +
          (∑ u ∈ Q₁₃, ∑ s ∈ squareSources N, (sigma 1 (s ^ 2)).factorization u) =
            4 * Q₁₃.card := by
      calc
        (∑ u ∈ Q₁₃, ((q + 1) / 2).factorization u) +
            (∑ u ∈ Q₁₃, ∑ s ∈ squareSources N, (sigma 1 (s ^ 2)).factorization u)
            = ∑ u ∈ Q₁₃,
                (((q + 1) / 2).factorization u +
                  ∑ s ∈ squareSources N, (sigma 1 (s ^ 2)).factorization u) :=
              Finset.sum_add_distrib.symm
        _ = ∑ _u ∈ Q₁₃, 4 := Finset.sum_congr rfl hpoint_u
        _ = 4 * Q₁₃.card := by simp [Finset.sum_const, Nat.mul_comm]
    omega

/-- **Sharpened Quartic-to-`S₅₁` Capacity Bound**: on any sixth-power-free odd perfect number `N`,
`3 * (oneModThreeLargeSources N q).card + 2 * (twoModThreeLargeSources N q).card ≤
 4 * ((squareSources N).filter (· % 5 = 1)).card + 3`. -/
theorem sixth_power_free_sharpened_quartic_to_S51_bound {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    3 * (oneModThreeLargeSources N q).card + 2 * (twoModThreeLargeSources N q).card ≤
      4 * ((squareSources N).filter (· % 5 = 1)).card + 3 := by
  let S₅₁ := (squareSources N).filter (· % 5 = 1)
  let Q₁₃ := oneModThreeLargeSources N q
  let Q₂₃ := twoModThreeLargeSources N q
  obtain ⟨_, _, hq1, _, _, hlg_prop, hparts, hq_notin, hdisj⟩ :=
    sixth_power_free_source_invariants_local ho hN hq hq4 he hev hfree
  obtain ⟨hQ13_dich, hQ23_dich⟩ :=
    sixth_power_free_quartic_cardFactors_mod_three_dichotomy ho hN hq hq4 he hev hfree
  have hid1 :=
    (sixth_power_free_bipartite_multiplicity_identities ho hN hq hq4 he hev hfree).1
  change (∑ u ∈ largeSources N q, cardFactors (sigma 1 (u ^ 4))) +
      (∑ p ∈ S₅₁, ((q + 1) / 2).factorization p) =
      2 * S₅₁.card + ∑ u ∈ largeSources N q, (sigma 1 (u ^ 4)).factorization q at hid1
  have hq_prime := Nat.prime_of_mem_primeFactors hq
  have hq_odd : Odd q := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hq)
  have hq_sum_le1 : ∑ u ∈ largeSources N q, (sigma 1 (u ^ 4)).factorization q ≤ 1 := by
    have hsum := factorization_eq_sum_sigma_factorizations hN hq_odd hq_prime
    have hsub : largeSources N q ⊆ N.primeFactors := Finset.filter_subset _ _
    have hle1 :
        ∑ u ∈ largeSources N q, (sigma 1 (u ^ 4)).factorization q ≤
          ∑ r ∈ largeSources N q, (sigma 1 (r ^ N.factorization r)).factorization q := by
      refine Finset.sum_le_sum fun u hu => ?_
      rw [(hlg_prop u hu).2.2.2.2.2.2]
    have hle2 :
        ∑ r ∈ largeSources N q, (sigma 1 (r ^ N.factorization r)).factorization q ≤
          ∑ r ∈ N.primeFactors, (sigma 1 (r ^ N.factorization r)).factorization q :=
      Finset.sum_le_sum_of_subset hsub
    omega
  have htotal_upper : ∑ u ∈ largeSources N q, cardFactors (sigma 1 (u ^ 4)) ≤ 2 * S₅₁.card + 1 := by
    omega
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
  have hQ13_prime_le : Q₁₃_prime.card ≤ S₅₁.card := by
    refine Finset.card_le_card_of_injOn (fun u => sigma 1 (u ^ 4)) ?_ ?_
    · intro u hu
      obtain ⟨hu_nq, hu_sig_prime⟩ := Finset.mem_filter.mp hu
      obtain ⟨hu_Q13, hu_nq_dvd⟩ := Finset.mem_filter.mp hu_nq
      have hw_prop := (hQ13_dich u hu_Q13 hu_nq_dvd).1
      have hself_mem : sigma 1 (u ^ 4) ∈ (sigma 1 (u ^ 4)).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hu_sig_prime, dvd_rfl, hu_sig_prime.ne_zero⟩
      exact (hw_prop (sigma 1 (u ^ 4)) hself_mem).1
    · intro u₁ hu₁ u₂ hu₂ heq
      have hu₁_prime :=
        (hlg_prop u₁ (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hu₁).1).1).1).1
      have hu₂_prime :=
        (hlg_prop u₂ (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hu₂).1).1).1).1
      dsimp only at heq
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
            have hgt1 := (quartic_sigma_prime_factor_classification ho hN hq hq4 he hev hfree hu_lg).1
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
  change 3 * Q₁₃.card + 2 * Q₂₃.card ≤ 4 * S₅₁.card + 3
  omega

end OddPerfect
