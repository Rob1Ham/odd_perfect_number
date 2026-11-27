module

public import OddPerfect.GlobalWave6Obstruction
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Wave 7 Track 3: Sixth-Power-Free Cofactor Obstruction & Mirror Dichotomy

Formalizes:
1. `sixth_power_free_quartic_mutual_exclusion`: On any sixth-power-free odd perfect number `N`,
   no quartic source `u ∈ largeSources N q` can divide `sigma 1 (v ^ 4)` for any
   `v ∈ largeSources N q` (since `u % 5 ≠ 1` while `v % 5 ≠ 1` forces every prime divisor of
   `sigma 1 (v ^ 4)` to satisfy `w % 5 = 1`).
2. `sixth_power_free_quartic_incoming_budget`: All `4 * (largeSources N q).card` quartic prime
   factors (with multiplicity, `≥ 588` via `three_free_sixthPowerFree_forces_147_largeSources`)
   must come exclusively from `(q + 1) / 2` and `squareSources N`.
3. `sixth_power_free_unique_q_source_mirror_dichotomy`: In the linear Euler decomposition
   `N = q * m ^ 2`, the unique `q`-source `r₀ ∈ m.primeFactors` satisfies a strict dual mirror
   dichotomy between `r₀ ∈ squareSources N` (`r₀ % 5 = 1`, `c₀.primeFactors ⊆ oneModThreeLargeSources N q`)
   and `r₀ ∈ largeSources N q` (`r₀ % 3 = 1`, `q % 60 = 1 ∧ 61 ≤ q`,
   `c₀.primeFactors ⊆ (squareSources N).filter (· % 5 = 1)`).
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction
open scoped NumberTheorySymbols

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

private theorem sixth_power_free_partition_invariants {N q : ℕ}
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

/-- **Quartic Mutual Exclusion (Wave 7 Track 3)**: On a sixth-power-free odd perfect number `N`,
no quartic source `u ∈ largeSources N q` can divide `sigma 1 (v ^ 4)` for any
`v ∈ largeSources N q`. -/
theorem sixth_power_free_quartic_mutual_exclusion {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    ∀ u ∈ largeSources N q, ∀ v ∈ largeSources N q, ¬ u ∣ sigma 1 (v ^ 4) := by
  obtain ⟨_, _, _, _, _, hlg_prop, _, _, _⟩ :=
    sixth_power_free_partition_invariants ho hN hq hq4 he hev hfree
  intro u hu v hv hdvd
  obtain ⟨hu_prime, hu5, _, _, _, _, _⟩ := hlg_prop u hu
  obtain ⟨hv_prime, hv5, _, hv3, _, _, _⟩ := hlg_prop v hv
  have hv_ge3 : 3 ≤ v := by
    have := hv_prime.two_le
    omega
  have hnorm_eq : normalizedQuarticSum v = sigma 1 (v ^ 4) := by
    rw [normalizedQuarticSum, ite_eq_right hv5, ← sigma_one_four_local hv_prime]
  have hu_norm : u ∣ normalizedQuarticSum v := hnorm_eq ▸ hdvd
  have hu_mod5 := (quartic_sigma_properties hv_prime hv_ge3).2.2.2 u hu_prime hu_norm
  exact hu5 hu_mod5

/-- **Quartic Incoming Prime-Factor Budget (Wave 7 Track 3)**: On a sixth-power-free odd
perfect number `N`, all `4 * (largeSources N q).card` quartic prime factors (with multiplicity,
at least `588`) come exclusively from `(q + 1) / 2` and `squareSources N`. -/
theorem sixth_power_free_quartic_incoming_budget {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    4 * (largeSources N q).card =
      (∑ u ∈ largeSources N q, ((q + 1) / 2).factorization u) +
        ∑ s ∈ squareSources N, ∑ u ∈ largeSources N q, (s ^ 2 + s + 1).factorization u ∧
    588 ≤
      (∑ u ∈ largeSources N q, ((q + 1) / 2).factorization u) +
        ∑ s ∈ squareSources N, ∑ u ∈ largeSources N q, (s ^ 2 + s + 1).factorization u := by
  obtain ⟨h3, _, hq1, _, hsq_prop, hlg_prop, hparts, hq_notin, hdisj⟩ :=
    sixth_power_free_partition_invariants ho hN hq hq4 he hev hfree
  have hq_prime := Nat.prime_of_mem_primeFactors hq
  have hhalf_ne0 : (q + 1) / 2 ≠ 0 := by
    have := hq_prime.two_le
    omega
  have hsig_q : sigma 1 (q ^ N.factorization q) = 2 * ((q + 1) / 2) := by
    rw [hq1, pow_one, sigma_one_prime_local hq_prime]
    have hq_odd : Odd q := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hq)
    omega
  have hpoint : ∀ u ∈ largeSources N q,
      4 = ((q + 1) / 2).factorization u +
        ∑ s ∈ squareSources N, (s ^ 2 + s + 1).factorization u := by
    intro u hu
    obtain ⟨hu_prime, _, hu2, _, _, _, hu_exp⟩ := hlg_prop u hu
    have hu_dvd : u ∣ N := Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hu).1
    have hu_odd : Odd u := ho.of_dvd_nat hu_dvd
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
          ∑ s ∈ squareSources N, (s ^ 2 + s + 1).factorization u := by
      refine Finset.sum_congr rfl fun s hs => ?_
      have hs_prime := (hsq_prop s hs).1
      have hs_exp := (hsq_prop s hs).2.2.2.2.2.2
      rw [hs_exp, sigma_one_sq_local hs_prime]
    have hlg_term :
        (∑ v ∈ largeSources N q, (sigma 1 (v ^ N.factorization v)).factorization u) = 0 := by
      refine Finset.sum_eq_zero fun v hv => ?_
      have hv_exp := (hlg_prop v hv).2.2.2.2.2.2
      rw [hv_exp]
      exact Nat.factorization_eq_zero_of_not_dvd
        (sixth_power_free_quartic_mutual_exclusion ho hN hq hq4 he hev hfree u hu v hv)
    rw [hu_exp, hq_term, hsq_term, hlg_term, add_zero] at hsum
    exact hsum
  have h1 : 4 * (largeSources N q).card = ∑ _u ∈ largeSources N q, 4 := by
    simp [Finset.sum_const, Nat.mul_comm]
  have h2 : (∑ _u ∈ largeSources N q, 4) =
      ∑ u ∈ largeSources N q,
        (((q + 1) / 2).factorization u +
          ∑ s ∈ squareSources N, (s ^ 2 + s + 1).factorization u) :=
    Finset.sum_congr rfl hpoint
  have h3_sum :
      (∑ u ∈ largeSources N q,
        (((q + 1) / 2).factorization u +
          ∑ s ∈ squareSources N, (s ^ 2 + s + 1).factorization u)) =
      (∑ u ∈ largeSources N q, ((q + 1) / 2).factorization u) +
        ∑ u ∈ largeSources N q, ∑ s ∈ squareSources N, (s ^ 2 + s + 1).factorization u :=
    Finset.sum_add_distrib
  have h4_sum :
      (∑ u ∈ largeSources N q, ∑ s ∈ squareSources N, (s ^ 2 + s + 1).factorization u) =
      ∑ s ∈ squareSources N, ∑ u ∈ largeSources N q, (s ^ 2 + s + 1).factorization u :=
    Finset.sum_comm
  have hsum_eq :
      4 * (largeSources N q).card =
        (∑ u ∈ largeSources N q, ((q + 1) / 2).factorization u) +
          ∑ s ∈ squareSources N, ∑ u ∈ largeSources N q, (s ^ 2 + s + 1).factorization u := by
    rw [h1, h2, h3_sum, h4_sum]
  have h147 : 147 ≤ (largeSources N q).card :=
    (three_free_sixthPowerFree_forces_147_largeSources ho hN hq hq4 he hev h3 hfree).2.1
  exact ⟨hsum_eq, by omega⟩

private lemma odd_sq_add_self_add_one_mod4 {r : ℕ}
    (hr : Odd r) (hmod : (r ^ 2 + r + 1) % 4 = 1) : r % 4 = 3 := by
  have hr2 : r % 2 = 1 := Nat.odd_iff.mp hr
  by_contra hne3
  have h1 : r % 4 = 1 := by omega
  have hk : r = 4 * (r / 4) + 1 := by omega
  have hcalc : r ^ 2 + r + 1 = 4 * (4 * (r / 4) ^ 2 + 3 * (r / 4)) + 3 := by
    conv_lhs => rw [hk]
    ring
  rw [hcalc] at hmod
  omega

private lemma sq_half_bound_absurd {q r : ℕ}
    (hr3 : 3 ≤ r) (hle : r ^ 2 ≤ (q + 1) / 2) (hbound : 2 * q < 3 * r ^ 2) : False := by
  have h9 : 9 ≤ r ^ 2 := by
    calc
      9 = 3 ^ 2 := by norm_num
      _ ≤ r ^ 2 := Nat.pow_le_pow_left hr3 2
  omega

private lemma quartic_half_bound_absurd {q r : ℕ}
    (hr3 : 3 ≤ r) (hle : r ^ 4 ≤ (q + 1) / 2) (hbound : 2 * q < 3 * r ^ 4) : False := by
  have h81 : 81 ≤ r ^ 4 := by
    calc
      81 = 3 ^ 4 := by norm_num
      _ ≤ r ^ 4 := Nat.pow_le_pow_left hr3 4
  omega

private lemma mod12_mod5_to_mod60 {q : ℕ}
    (hq2 : 2 ≤ q) (h12 : q % 12 = 1) (h5 : q % 5 = 1) : q % 60 = 1 ∧ 61 ≤ q := by
  omega

private lemma mod3_mod5_to_mod15 {p : ℕ} (h3 : p % 3 = 2) (h5 : p % 5 = 1) : p % 15 = 11 := by
  omega

private lemma mod3_mod4_to_mod12 {r : ℕ} (h3 : r % 3 = 2) (h4 : r % 4 = 3) : r % 12 = 11 := by
  omega

/-- **Unique `q`-Source Mirror Dichotomy (Wave 7 Track 3)**: On any sixth-power-free odd
perfect number `N`, writing `N = q * m ^ 2` (`Odd m`, `¬ q ∣ m`), the unique `q`-source
`r₀ ∈ m.primeFactors` satisfies a strict dual mirror dichotomy:
- Either `r₀ ∈ squareSources N` (`r₀ % 5 = 1`, `N.factorization r₀ = 2`, `e₀ = 1`,
  `r₀ ^ 2 + r₀ + 1 = q * c₀`, `2 * q < 3 * r₀ ^ 2`, `c₀ = 1 → q = r₀ ^ 2 + r₀ + 1 ∧ r₀ % 12 = 11`,
  and `c₀.primeFactors ⊆ oneModThreeLargeSources N q`),
- Or `r₀ ∈ largeSources N q` (`r₀ % 3 = 1`, `N.factorization r₀ = 4`, `e₀ = 2`,
  `r₀ ^ 4 + r₀ ^ 3 + r₀ ^ 2 + r₀ + 1 = q * c₀`, `2 * q < 3 * r₀ ^ 4`, `q % 60 = 1 ∧ 61 ≤ q`,
  and `c₀.primeFactors ⊆ (squareSources N).filter (· % 5 = 1)`). -/
theorem sixth_power_free_unique_q_source_mirror_dichotomy {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    ∃ m r₀ : ℕ,
      Odd m ∧ ¬ q ∣ m ∧ N = q * m ^ 2 ∧
      r₀ ∈ m.primeFactors ∧
      let e₀ := m.factorization r₀
      let B := ordCompl[r₀] (m ^ 2)
      let c₀ := sigma 1 (r₀ ^ (2 * e₀)) / q
      sigma 1 (r₀ ^ (2 * e₀)) = q * c₀ ∧
      ¬ q ∣ c₀ ∧
      Odd c₀ ∧
      Nat.Coprime c₀ (r₀ ^ (2 * e₀)) ∧
      c₀ ∣ B ∧
      sigma 1 (m ^ 2) / q = c₀ * sigma 1 B ∧
      (∀ r₁ ∈ m.primeFactors, q ∣ sigma 1 (r₁ ^ (2 * m.factorization r₁)) → r₁ = r₀) ∧
      ((r₀ ∈ squareSources N ∧ r₀ % 5 = 1 ∧ N.factorization r₀ = 2 ∧ e₀ = 1 ∧
          r₀ ^ 2 + r₀ + 1 = q * c₀ ∧ 2 * q < 3 * r₀ ^ 2 ∧
          (c₀ = 1 → q = r₀ ^ 2 + r₀ + 1 ∧ r₀ % 12 = 11) ∧
          c₀.primeFactors ⊆ oneModThreeLargeSources N q ∧
          ∀ p ∈ c₀.primeFactors, N.factorization p = 4 ∧ p % 3 = 1 ∧ p % 5 ≠ 1) ∨
        (r₀ ∈ largeSources N q ∧ r₀ % 3 = 1 ∧ N.factorization r₀ = 4 ∧ e₀ = 2 ∧
          r₀ ^ 4 + r₀ ^ 3 + r₀ ^ 2 + r₀ + 1 = q * c₀ ∧ 2 * q < 3 * r₀ ^ 4 ∧
          q % 60 = 1 ∧ 61 ≤ q ∧
          c₀.primeFactors ⊆ (squareSources N).filter (· % 5 = 1) ∧
          ∀ p ∈ c₀.primeFactors, N.factorization p = 2 ∧ p % 15 = 11)) := by
  obtain ⟨h3, h5, hq1, hS1_empty, hsq_prop, hlg_prop, hparts, _, _⟩ :=
    sixth_power_free_partition_invariants ho hN hq hq4 he hev hfree
  obtain ⟨hq12, _⟩ := sixth_power_free_euler_prime_mod_twelve_or_twenty ho hN hq hq4 he hev hfree
  have hq_prime := Nat.prime_of_mem_primeFactors hq
  obtain ⟨q', a', m, hq'_prime, _, ha'_mod4, hq'm, hform'⟩ := euler_form ho hN
  have ha'_pos : 0 < a' := by omega
  have hm_odd : Odd m :=
    ho.of_dvd_nat (hform' ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) (q' ^ a')))
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hq'_fac : N.factorization q' = a' := by
    rw [hform', Nat.factorization_mul (pow_ne_zero a' hq'_prime.ne_zero) hm20, Finsupp.add_apply,
      hq'_prime.factorization_pow, Finsupp.single_eq_same]
    have hnq'm2 : ¬ q' ∣ m ^ 2 := fun h => hq'm (hq'_prime.dvd_of_dvd_pow h)
    rw [Nat.factorization_eq_zero_of_not_dvd hnq'm2, add_zero]
  have hq'_eq : q' = q := by
    by_contra hne
    obtain ⟨k, hk⟩ := hev q' hne
    rw [hq'_fac] at hk
    omega
  rw [hq'_eq] at hq'm hform' hq'_fac
  have ha'_eq1 : a' = 1 := hq'_fac.symm.trans hq1
  have hform : N = q * m ^ 2 := by
    simpa [ha'_eq1] using hform'
  obtain ⟨r₀, hr₀_m, hmul_c0, hnq_c0, hodd_c0, hcop_c0, hiq_eq, _, hc0_dvd_B, _⟩ :=
    linear_euler_cofactor_quotient_structure ho hN hq_prime hq'm hform
  obtain ⟨_, r₁, _, _, _, _, hbound_r1, huniq⟩ :=
    linear_euler_unique_q_source_and_bound ho hN hq_prime hq'm hform
  have hr₀_eq_r1 : r₀ = r₁ := by
    apply huniq r₀ hr₀_m
    rw [hmul_c0]
    exact dvd_mul_right q _
  have huniq₀ : ∀ r₂ ∈ m.primeFactors,
      q ∣ sigma 1 (r₂ ^ (2 * m.factorization r₂)) → r₂ = r₀ :=
    fun r₂ hr₂ hdvd => (huniq r₂ hr₂ hdvd).trans hr₀_eq_r1.symm
  rw [← hr₀_eq_r1] at hbound_r1
  have hr₀_prime := Nat.prime_of_mem_primeFactors hr₀_m
  have hr₀_dvd_m : r₀ ∣ m := Nat.dvd_of_mem_primeFactors hr₀_m
  have hr₀_odd : Odd r₀ := hm_odd.of_dvd_nat hr₀_dvd_m
  have hr₀_neq : r₀ ≠ q := fun h => hq'm (h ▸ hr₀_dvd_m)
  have hr₀_dvd_N : r₀ ∣ N :=
    hform ▸ (hr₀_dvd_m.trans (dvd_pow_self m (by decide : 2 ≠ 0))).trans (dvd_mul_left (m ^ 2) q)
  have hr₀_N : r₀ ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hr₀_prime, hr₀_dvd_N, hN.2.ne'⟩
  have hfac_r0 : N.factorization r₀ = 2 * m.factorization r₀ := by
    rw [hform, Nat.factorization_mul hq_prime.ne_zero hm20, Finsupp.add_apply]
    have hnotq : ¬ r₀ ∣ q := fun h =>
      hr₀_neq (((Nat.dvd_prime hq_prime).mp h).resolve_left hr₀_prime.ne_one)
    rw [Nat.factorization_eq_zero_of_not_dvd hnotq, zero_add, pow_two,
      Nat.factorization_mul hm0 hm0, Finsupp.add_apply, ← two_mul]
  have hr₀_mem_union : r₀ ∈ squareSources N ∪ largeSources N q := by
    have := hparts ▸ hr₀_N
    rcases Finset.mem_insert.mp this with hq_eq | hmem
    · exact (hr₀_neq hq_eq).elim
    · exact hmem
  have hhalf_pos : 0 < (q + 1) / 2 := by
    have := hq_prime.two_le
    omega
  refine ⟨m, r₀, hm_odd, hq'm, hform, hr₀_m, hmul_c0, hnq_c0, hodd_c0, hcop_c0, hc0_dvd_B, hiq_eq,
    huniq₀, ?_⟩
  let e₀ := m.factorization r₀
  let B := ordCompl[r₀] (m ^ 2)
  let c₀ := sigma 1 (r₀ ^ (2 * e₀)) / q
  have hc0_dvd_B' : c₀ ∣ B := hc0_dvd_B
  have hc0_mem_info : ∀ p ∈ c₀.primeFactors,
      p.Prime ∧ p ∣ c₀ ∧ p ∈ N.primeFactors ∧ p ≠ q := by
    intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have hp_c0 := Nat.dvd_of_mem_primeFactors hp
    have hp_B : p ∣ B := hp_c0.trans hc0_dvd_B'
    have hp_m2 : p ∣ m ^ 2 := hp_B.trans (Nat.ordCompl_dvd (m ^ 2) r₀)
    have hp_N : p ∣ N := hp_m2.trans (hform ▸ dvd_mul_left (m ^ 2) q)
    have hp_mem : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hp_prime, hp_N, hN.2.ne'⟩
    have hp_neq : p ≠ q := by
      rintro rfl
      exact hnq_c0 hp_c0
    exact ⟨hp_prime, hp_c0, hp_mem, hp_neq⟩
  rcases Finset.mem_union.mp hr₀_mem_union with hr₀_sq | hr₀_lg
  · left
    obtain ⟨_, hr₀_mod3, hr₀_ne2, _, _, _, hr₀_exp⟩ := hsq_prop r₀ hr₀_sq
    have he₀ : e₀ = 1 := by
      have h2e : 2 = 2 * e₀ := hr₀_exp.symm.trans hfac_r0
      omega
    have hsig_eq : r₀ ^ 2 + r₀ + 1 = q * c₀ := by
      calc
        r₀ ^ 2 + r₀ + 1 = sigma 1 (r₀ ^ 2) := (sigma_one_sq_local hr₀_prime).symm
        _ = sigma 1 (r₀ ^ (2 * e₀)) := by rw [he₀, mul_one]
        _ = q * c₀ := hmul_c0
    have hbound2 : 2 * q < 3 * r₀ ^ 2 := by
      have hm_eq : m.factorization r₀ = 1 := he₀
      simpa [hm_eq] using hbound_r1
    have hr₀_mod5 : r₀ % 5 = 1 := by
      by_contra hr₀_not5
      have hr₀_S50 : r₀ ∈ (squareSources N).filter (· % 5 ≠ 1) :=
        Finset.mem_filter.mpr ⟨hr₀_sq, hr₀_not5⟩
      have hvac_dvd := (sixth_power_free_incoming_source_vacuum ho hN hq hq4 he hev hfree).2.1
      have hdvd_half : r₀ ^ 2 ∣ (q + 1) / 2 :=
        (Finset.dvd_prod_of_mem (fun x => x ^ 2) hr₀_S50).trans ((dvd_mul_right _ _).trans hvac_dvd)
      have hle_half : r₀ ^ 2 ≤ (q + 1) / 2 := Nat.le_of_dvd hhalf_pos hdvd_half
      have hr₀_ge3 : 3 ≤ r₀ := by
        have := hr₀_prime.two_le
        omega
      exact (sq_half_bound_absurd hr₀_ge3 hle_half hbound2).elim
    have hc0_one_imp : c₀ = 1 → q = r₀ ^ 2 + r₀ + 1 ∧ r₀ % 12 = 11 := by
      intro hc1
      have hq_eq : q = r₀ ^ 2 + r₀ + 1 := by
        rw [hsig_eq, hc1, mul_one]
      have hq_mod4 : (r₀ ^ 2 + r₀ + 1) % 4 = 1 := hq_eq ▸ hq4
      have hr₀_mod4 : r₀ % 4 = 3 := odd_sq_add_self_add_one_mod4 hr₀_odd hq_mod4
      exact ⟨hq_eq, mod3_mod4_to_mod12 hr₀_mod3 hr₀_mod4⟩
    have hc0_prop : ∀ p ∈ c₀.primeFactors,
        N.factorization p = 4 ∧ p % 3 = 1 ∧ p % 5 ≠ 1 := by
      intro p hp
      obtain ⟨hp_prime, hp_c0, hp_mem, hp_neq⟩ := hc0_mem_info p hp
      have hp_sq_dvd : p ∣ r₀ ^ 2 + r₀ + 1 := by
        rw [hsig_eq]
        exact hp_c0.trans (dvd_mul_left c₀ q)
      have hp_mod3 : p % 3 = 1 := by
        rcases prime_dvd_sq_add_self_add_one hp_prime hp_sq_dvd with rfl | h1
        · exact (h3 (Nat.dvd_of_mem_primeFactors hp_mem)).elim
        · exact h1
      have hp_union : p ∈ squareSources N ∪ largeSources N q := by
        rcases Finset.mem_insert.mp (hparts ▸ hp_mem) with hq_eq | hmem
        · exact (hp_neq hq_eq).elim
        · exact hmem
      have hp_lg : p ∈ largeSources N q := by
        rcases Finset.mem_union.mp hp_union with hp_sq | hp_lg
        · have hp_m3 := (hsq_prop p hp_sq).2.1
          omega
        · exact hp_lg
      obtain ⟨_, hp_not5, _, _, _, _, hp_exp⟩ := hlg_prop p hp_lg
      exact ⟨hp_exp, hp_mod3, hp_not5⟩
    have hc0_sub : c₀.primeFactors ⊆ oneModThreeLargeSources N q := by
      intro p hp
      obtain ⟨_, _, hp_mem, hp_neq⟩ := hc0_mem_info p hp
      obtain ⟨hp_exp, hp_mod3, _⟩ := hc0_prop p hp
      have hp_ne3 : p ≠ 3 := fun h => h3 (h ▸ Nat.dvd_of_mem_primeFactors hp_mem)
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hp_mem, hp_ne3, hp_neq, by omega⟩, hp_mod3⟩
    exact ⟨hr₀_sq, hr₀_mod5, hr₀_exp, he₀, hsig_eq, hbound2, hc0_one_imp, hc0_sub, hc0_prop⟩
  · right
    obtain ⟨_, hr₀_not5, hr₀_ne2, _, _, _, hr₀_exp⟩ := hlg_prop r₀ hr₀_lg
    have he₀ : e₀ = 2 := by
      have h4e : 4 = 2 * e₀ := hr₀_exp.symm.trans hfac_r0
      omega
    have hsig_eq : r₀ ^ 4 + r₀ ^ 3 + r₀ ^ 2 + r₀ + 1 = q * c₀ := by
      calc
        r₀ ^ 4 + r₀ ^ 3 + r₀ ^ 2 + r₀ + 1 = sigma 1 (r₀ ^ 4) := (sigma_one_four_local hr₀_prime).symm
        _ = sigma 1 (r₀ ^ (2 * e₀)) := by rw [he₀]
        _ = q * c₀ := hmul_c0
    have hbound4 : 2 * q < 3 * r₀ ^ 4 := by
      have hm_eq : m.factorization r₀ = 2 := he₀
      simpa [hm_eq] using hbound_r1
    have hr₀_ge3 : 3 ≤ r₀ := by
      have := hr₀_prime.two_le
      omega
    have hr₀_mod3 : r₀ % 3 = 1 := by
      by_contra hr₀_not3
      have hr₀_Q23 : r₀ ∈ twoModThreeLargeSources N q :=
        Finset.mem_filter.mpr ⟨hr₀_lg, hr₀_not3⟩
      have hvac_dvd := (sixth_power_free_incoming_source_vacuum ho hN hq hq4 he hev hfree).2.1
      have hdvd_half : r₀ ^ 4 ∣ (q + 1) / 2 :=
        (Finset.dvd_prod_of_mem (fun x => x ^ 4) hr₀_Q23).trans ((dvd_mul_left _ _).trans hvac_dvd)
      have hle_half : r₀ ^ 4 ≤ (q + 1) / 2 := Nat.le_of_dvd hhalf_pos hdvd_half
      exact (quartic_half_bound_absurd hr₀_ge3 hle_half hbound4).elim
    have hnorm_eq : normalizedQuarticSum r₀ = q * c₀ := by
      rw [normalizedQuarticSum, ite_eq_right hr₀_not5, hsig_eq]
    have hq_mod5 : q % 5 = 1 :=
      (quartic_sigma_properties hr₀_prime hr₀_ge3).2.2.2 q hq_prime
        (hnorm_eq ▸ dvd_mul_right q c₀)
    obtain ⟨hq_mod60, hq_ge61⟩ := mod12_mod5_to_mod60 hq_prime.two_le hq12 hq_mod5
    have hc0_prop : ∀ p ∈ c₀.primeFactors, N.factorization p = 2 ∧ p % 15 = 11 := by
      intro p hp
      obtain ⟨hp_prime, hp_c0, hp_mem, hp_neq⟩ := hc0_mem_info p hp
      have hp_norm_dvd : p ∣ normalizedQuarticSum r₀ := by
        rw [hnorm_eq]
        exact hp_c0.trans (dvd_mul_left c₀ q)
      have hp_mod5 : p % 5 = 1 :=
        (quartic_sigma_properties hr₀_prime hr₀_ge3).2.2.2 p hp_prime hp_norm_dvd
      have hp_union : p ∈ squareSources N ∪ largeSources N q := by
        rcases Finset.mem_insert.mp (hparts ▸ hp_mem) with hq_eq | hmem
        · exact (hp_neq hq_eq).elim
        · exact hmem
      have hp_sq : p ∈ squareSources N := by
        rcases Finset.mem_union.mp hp_union with hp_sq | hp_lg
        · exact hp_sq
        · exact ((hlg_prop p hp_lg).2.1 hp_mod5).elim
      obtain ⟨_, hp_mod3, _, _, _, _, hp_exp⟩ := hsq_prop p hp_sq
      exact ⟨hp_exp, mod3_mod5_to_mod15 hp_mod3 hp_mod5⟩
    have hc0_sub : c₀.primeFactors ⊆ (squareSources N).filter (· % 5 = 1) := by
      intro p hp
      obtain ⟨_, _, hp_mem, _⟩ := hc0_mem_info p hp
      obtain ⟨hp_exp, hp_mod15⟩ := hc0_prop p hp
      have hp_ne3 : p ≠ 3 := fun h => h3 (h ▸ Nat.dvd_of_mem_primeFactors hp_mem)
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hp_mem, hp_ne3, hp_exp⟩, by omega⟩
    exact ⟨hr₀_lg, hr₀_mod3, hr₀_exp, he₀, hsig_eq, hbound4, hq_mod60, hq_ge61, hc0_sub, hc0_prop⟩

end OddPerfect
