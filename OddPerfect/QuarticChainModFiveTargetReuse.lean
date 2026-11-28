module

public import OddPerfect.QuarticChainBaselineAndReuse
import OddPerfect.SixthPowerSieve
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quartic-Chain Modulo-Five Target-Reuse Bound

BRANCH_MAP: A1_SPF
Closure: Excludes every quartic-reuse count family with 4k > 5 D_all + 2 (sharp over (ℤ/20ℤ)* and (ℤ/40ℤ)*, sharpening 4 D_all ≥ 2k − 1 and 5 D_all ≥ 3k − 2); does not close A1_SPF or reset its pivot clock.

Formalizes the modulo-5 target-reuse sharpening for quartic chains `w ↦ s = Φ₅(w) ↦ σ(s²) = A(w) B(w)`:
1. Every target prime `t ≠ q` dividing `σ(s²)` for `s ∈ K` belongs to `oneModThreeLargeSources N q`
   with `N.factorization t = 4`.
2. Counting prime block factors `A(w) = quarticFirstFactor w` and `B(w) = quarticSecondFactor w`
   by residue class `w % 5 ∈ {2, 3, 4}` yields disjoint residue-class injections into
   `D_r 3 + q_r 3`, `D_r 2 + q_r 2`, `D_r 1 + q_r 1`, and `D_r 4 + q_r 4`, summing to
   `k_A1_24 + k_A1_3 + k_B1_24 + k_B1_3 ≤ allTargets.card + q_tot`.
3. Double-counting `cardFactors (σ(s²))` over `s ∈ K` yields
   `4 * K.card ≤ 5 * allTargets.card + 2 * q_tot ≤ 5 * allTargets.card + 2`.
4. Specialization to `K = quarticChainIntermediates N q` gives
   `4 * (quarticChainSources N q).card ≤ 5 * allTargets.card + 2`.
-/

public section

namespace OddPerfect

open ArithmeticFunction Finset

private theorem sigma_one_sq_local {p : ℕ} (hp : p.Prime) :
    sigma 1 (p ^ 2) = p ^ 2 + p + 1 := by
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

private theorem quarticPoly_strictMono : StrictMono quarticPoly := by
  intro w₁ w₂ hlt
  unfold quarticPoly
  have h2 : w₁ ^ 2 < w₂ ^ 2 := Nat.pow_lt_pow_left hlt (by decide)
  have h3 : w₁ ^ 3 < w₂ ^ 3 := Nat.pow_lt_pow_left hlt (by decide)
  have h4 : w₁ ^ 4 < w₂ ^ 4 := Nat.pow_lt_pow_left hlt (by decide)
  omega

private theorem quarticFirstFactor_strictMonoOn {w₁ w₂ : ℕ}
    (hw₁ : 1 ≤ w₁) (hlt : w₁ < w₂) :
    quarticFirstFactor w₁ < quarticFirstFactor w₂ := by
  unfold quarticFirstFactor
  have h1 : w₁ ≤ w₁ ^ 2 := by nlinarith
  have h2 : w₂ ≤ w₂ ^ 2 := by nlinarith
  have hsq : w₁ ^ 2 + w₂ < w₂ ^ 2 + w₁ := by nlinarith
  omega

private theorem quarticFirstFactor_injOn {w₁ w₂ : ℕ}
    (hw₁ : 1 ≤ w₁) (hw₂ : 1 ≤ w₂)
    (heq : quarticFirstFactor w₁ = quarticFirstFactor w₂) : w₁ = w₂ := by
  rcases lt_trichotomy w₁ w₂ with hlt | rfl | hgt
  · exact absurd heq (quarticFirstFactor_strictMonoOn hw₁ hlt).ne
  · rfl
  · exact absurd heq.symm (quarticFirstFactor_strictMonoOn hw₂ hgt).ne

private theorem quarticSecondFactor_strictMono : StrictMono quarticSecondFactor := by
  intro w₁ w₂ hlt
  unfold quarticSecondFactor
  have h2 : w₁ ^ 2 < w₂ ^ 2 := Nat.pow_lt_pow_left hlt (by decide)
  have h3 : w₁ ^ 3 < w₂ ^ 3 := Nat.pow_lt_pow_left hlt (by decide)
  have h4 : w₁ ^ 4 < w₂ ^ 4 := Nat.pow_lt_pow_left hlt (by decide)
  have h5 : w₁ ^ 5 < w₂ ^ 5 := Nat.pow_lt_pow_left hlt (by decide)
  have h6 : w₁ ^ 6 < w₂ ^ 6 := Nat.pow_lt_pow_left hlt (by decide)
  omega

private theorem quarticFirstFactor_mod_five_of_two_four {w : ℕ}
    (hw1 : 1 ≤ w) (hw5 : w % 5 = 2 ∨ w % 5 = 4) :
    quarticFirstFactor w % 5 = 3 := by
  have hle : w ≤ w ^ 2 := by nlinarith
  have hadd : quarticFirstFactor w + w = w ^ 2 + 1 := by
    unfold quarticFirstFactor
    omega
  rcases hw5 with h | h
  · have hc : w ≡ 2 [MOD 5] := h
    have hsq : w ^ 2 + 1 ≡ 2 ^ 2 + 1 [MOD 5] := (hc.pow 2).add (Nat.ModEq.refl 1)
    change (w ^ 2 + 1) % 5 = (2 ^ 2 + 1) % 5 at hsq
    rw [show (2 ^ 2 + 1) % 5 = 0 by decide] at hsq
    have hmod : (quarticFirstFactor w + w) % 5 = (quarticFirstFactor w % 5 + w % 5) % 5 :=
      Nat.add_mod _ _ 5
    rw [hadd, hsq, h] at hmod
    omega
  · have hc : w ≡ 4 [MOD 5] := h
    have hsq : w ^ 2 + 1 ≡ 4 ^ 2 + 1 [MOD 5] := (hc.pow 2).add (Nat.ModEq.refl 1)
    change (w ^ 2 + 1) % 5 = (4 ^ 2 + 1) % 5 at hsq
    rw [show (4 ^ 2 + 1) % 5 = 2 by decide] at hsq
    have hmod : (quarticFirstFactor w + w) % 5 = (quarticFirstFactor w % 5 + w % 5) % 5 :=
      Nat.add_mod _ _ 5
    rw [hadd, hsq, h] at hmod
    omega

private theorem quarticFirstFactor_mod_five_of_three {w : ℕ}
    (hw1 : 1 ≤ w) (hw5 : w % 5 = 3) :
    quarticFirstFactor w % 5 = 2 := by
  have hle : w ≤ w ^ 2 := by nlinarith
  have hadd : quarticFirstFactor w + w = w ^ 2 + 1 := by
    unfold quarticFirstFactor
    omega
  have hc : w ≡ 3 [MOD 5] := hw5
  have hsq : w ^ 2 + 1 ≡ 3 ^ 2 + 1 [MOD 5] := (hc.pow 2).add (Nat.ModEq.refl 1)
  change (w ^ 2 + 1) % 5 = (3 ^ 2 + 1) % 5 at hsq
  rw [show (3 ^ 2 + 1) % 5 = 0 by decide] at hsq
  have hmod : (quarticFirstFactor w + w) % 5 = (quarticFirstFactor w % 5 + w % 5) % 5 :=
    Nat.add_mod _ _ 5
  rw [hadd, hsq, hw5] at hmod
  omega

private theorem quarticSecondFactor_mod_five_of_two_four {w : ℕ}
    (hw5 : w % 5 = 2 ∨ w % 5 = 4) :
    quarticSecondFactor w % 5 = 1 := by
  rcases hw5 with h | h
  · have hc : w ≡ 2 [MOD 5] := h
    have hp : quarticSecondFactor w ≡
        2 ^ 6 + 3 * 2 ^ 5 + 5 * 2 ^ 4 + 6 * 2 ^ 3 + 7 * 2 ^ 2 + 6 * 2 + 3 [MOD 5] := by
      unfold quarticSecondFactor
      exact ((((((hc.pow 6).add ((Nat.ModEq.refl 3).mul (hc.pow 5))).add
        ((Nat.ModEq.refl 5).mul (hc.pow 4))).add
        ((Nat.ModEq.refl 6).mul (hc.pow 3))).add
        ((Nat.ModEq.refl 7).mul (hc.pow 2))).add
        ((Nat.ModEq.refl 6).mul hc)).add (Nat.ModEq.refl 3)
    change quarticSecondFactor w % 5 =
      (2 ^ 6 + 3 * 2 ^ 5 + 5 * 2 ^ 4 + 6 * 2 ^ 3 + 7 * 2 ^ 2 + 6 * 2 + 3) % 5 at hp
    rw [show (2 ^ 6 + 3 * 2 ^ 5 + 5 * 2 ^ 4 + 6 * 2 ^ 3 + 7 * 2 ^ 2 + 6 * 2 + 3) % 5 = 1 by
      decide] at hp
    exact hp
  · have hc : w ≡ 4 [MOD 5] := h
    have hp : quarticSecondFactor w ≡
        4 ^ 6 + 3 * 4 ^ 5 + 5 * 4 ^ 4 + 6 * 4 ^ 3 + 7 * 4 ^ 2 + 6 * 4 + 3 [MOD 5] := by
      unfold quarticSecondFactor
      exact ((((((hc.pow 6).add ((Nat.ModEq.refl 3).mul (hc.pow 5))).add
        ((Nat.ModEq.refl 5).mul (hc.pow 4))).add
        ((Nat.ModEq.refl 6).mul (hc.pow 3))).add
        ((Nat.ModEq.refl 7).mul (hc.pow 2))).add
        ((Nat.ModEq.refl 6).mul hc)).add (Nat.ModEq.refl 3)
    change quarticSecondFactor w % 5 =
      (4 ^ 6 + 3 * 4 ^ 5 + 5 * 4 ^ 4 + 6 * 4 ^ 3 + 7 * 4 ^ 2 + 6 * 4 + 3) % 5 at hp
    rw [show (4 ^ 6 + 3 * 4 ^ 5 + 5 * 4 ^ 4 + 6 * 4 ^ 3 + 7 * 4 ^ 2 + 6 * 4 + 3) % 5 = 1 by
      decide] at hp
    exact hp

private theorem quarticSecondFactor_mod_five_of_three {w : ℕ}
    (hw5 : w % 5 = 3) :
    quarticSecondFactor w % 5 = 4 := by
  have hc : w ≡ 3 [MOD 5] := hw5
  have hp : quarticSecondFactor w ≡
      3 ^ 6 + 3 * 3 ^ 5 + 5 * 3 ^ 4 + 6 * 3 ^ 3 + 7 * 3 ^ 2 + 6 * 3 + 3 [MOD 5] := by
    unfold quarticSecondFactor
    exact ((((((hc.pow 6).add ((Nat.ModEq.refl 3).mul (hc.pow 5))).add
      ((Nat.ModEq.refl 5).mul (hc.pow 4))).add
      ((Nat.ModEq.refl 6).mul (hc.pow 3))).add
      ((Nat.ModEq.refl 7).mul (hc.pow 2))).add
      ((Nat.ModEq.refl 6).mul hc)).add (Nat.ModEq.refl 3)
  change quarticSecondFactor w % 5 =
    (3 ^ 6 + 3 * 3 ^ 5 + 5 * 3 ^ 4 + 6 * 3 ^ 3 + 7 * 3 ^ 2 + 6 * 3 + 3) % 5 at hp
  rw [show (3 ^ 6 + 3 * 3 ^ 5 + 5 * 3 ^ 4 + 6 * 3 ^ 3 + 7 * 3 ^ 2 + 6 * 3 + 3) % 5 = 4 by
    decide] at hp
  exact hp

private theorem two_le_cardFactors_of_not_prime {n : ℕ} (h1 : 1 < n) (hnp : ¬ n.Prime) :
    2 ≤ cardFactors n := by
  have hpos : 0 < cardFactors n := cardFactors_pos_iff_one_lt.mpr h1
  have hne1 : cardFactors n ≠ 1 := fun h => hnp (cardFactors_eq_one_iff_prime.mp h)
  omega

open Classical in
theorem quartic_chain_mod_five_target_reuse {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N)
    (K : Finset ℕ) (hK_sub : K ⊆ squareSources N)
    (hK_chain : ∀ s ∈ K, ∃ w ∈ N.primeFactors, N.factorization w = 4 ∧
      s = w ^ 4 + w ^ 3 + w ^ 2 + w + 1) :
    let allTargets := (N.primeFactors.erase q).filter (fun t => ∃ s ∈ K, t ∣ sigma 1 (s ^ 2))
    let q_tot := if ∃ s ∈ K, q ∣ sigma 1 (s ^ 2) then 1 else 0
    let q_r (r : ℕ) := if (∃ s ∈ K, q ∣ sigma 1 (s ^ 2)) ∧ q % 5 = r then 1 else 0
    let D_r (r : ℕ) := (allTargets.filter (fun t => t % 5 = r)).card
    let k_A1_24 := (K.filter (fun s => ∃ w ∈ N.primeFactors,
      s = quarticPoly w ∧ (w % 5 = 2 ∨ w % 5 = 4) ∧ (quarticFirstFactor w).Prime)).card
    let k_A1_3 := (K.filter (fun s => ∃ w ∈ N.primeFactors,
      s = quarticPoly w ∧ w % 5 = 3 ∧ (quarticFirstFactor w).Prime)).card
    let k_B1_24 := (K.filter (fun s => ∃ w ∈ N.primeFactors,
      s = quarticPoly w ∧ (w % 5 = 2 ∨ w % 5 = 4) ∧ (quarticSecondFactor w).Prime)).card
    let k_B1_3 := (K.filter (fun s => ∃ w ∈ N.primeFactors,
      s = quarticPoly w ∧ w % 5 = 3 ∧ (quarticSecondFactor w).Prime)).card
    allTargets ⊆ oneModThreeLargeSources N q ∧
    (∀ t ∈ allTargets, N.factorization t = 4) ∧
    k_A1_24 ≤ D_r 3 + q_r 3 ∧
    k_A1_3 ≤ D_r 2 + q_r 2 ∧
    k_B1_24 ≤ D_r 1 + q_r 1 ∧
    k_B1_3 ≤ D_r 4 + q_r 4 ∧
    k_A1_24 + k_A1_3 + k_B1_24 + k_B1_3 ≤ allTargets.card + q_tot ∧
    4 * K.card ≤ 5 * allTargets.card + 2 * q_tot ∧
    4 * K.card ≤ 5 * allTargets.card + 2 ∧
    3 * K.card ≤ 5 * allTargets.card + 2 := by
  intro allTargets q_tot q_r D_r k_A1_24 k_A1_3 k_B1_24 k_B1_3
  have h3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  have h5 : ¬ 5 ∣ N := sixth_power_free_five_not_dvd ho hN hfree
  have hq1 : N.factorization q = 1 := sixth_power_free_euler_exponent_one ho hN hq he hfree
  have hlg4 : ∀ u ∈ largeSources N q, N.factorization u = 4 :=
    (three_free_sixthPowerFree_forces_147_largeSources ho hN hq hq4 he hev h3 hfree).1
  have hs_prime_of : ∀ {s : ℕ}, s ∈ K → s.Prime := fun hsK =>
    Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp (hK_sub hsK)).1
  have hsig_eq : ∀ {s : ℕ}, s ∈ K → sigma 1 (s ^ 2) = s ^ 2 + s + 1 := fun hsK =>
    sigma_one_sq_local (hs_prime_of hsK)
  have hsig_ne0 : ∀ {s : ℕ}, s ∈ K → sigma 1 (s ^ 2) ≠ 0 := by
    intro s hsK
    rw [hsig_eq hsK]
    positivity
  have hsig_dvd_N : ∀ {s : ℕ}, s ∈ K → sigma 1 (s ^ 2) ∣ N := by
    intro s hsK
    obtain ⟨hs_mem, _, hs_exp2⟩ := Finset.mem_filter.mp (hK_sub hsK)
    have hs_prime := Nat.prime_of_mem_primeFactors hs_mem
    have hs_odd : Odd s := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hs_mem)
    have hsig_odd : Odd (sigma 1 (s ^ 2)) := by
      rw [hsig_eq hsK]
      exact (hs_odd.pow.add_odd hs_odd).add_one
    obtain ⟨b, hNb, hcop⟩ := exists_coprime_cofactor_of_exact_prime_pow hs_prime
      (hs_exp2 ▸ Nat.ordProj_dvd N s)
      ((hs_prime.pow_dvd_iff_le_factorization hN.2.ne').not.mpr
        (by omega : ¬ 2 + 1 ≤ N.factorization s))
    apply odd_dvd_perfect_of_dvd_sum_divisors hN hNb hcop hsig_odd
    rw [← sigma_one_apply]
  have hsig_pf_sub : ∀ {s : ℕ}, s ∈ K →
      (sigma 1 (s ^ 2)).primeFactors ⊆ insert q allTargets := by
    intro s hsK p hp
    obtain ⟨hp_prime, hp_dvd, _⟩ := Nat.mem_primeFactors.mp hp
    have hp_N : p ∈ N.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd.trans (hsig_dvd_N hsK), hN.2.ne'⟩
    by_cases hpq : p = q
    · subst hpq
      exact Finset.mem_insert_self p allTargets
    · exact Finset.mem_insert_of_mem
        (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hpq, hp_N⟩, ⟨s, hsK, hp_dvd⟩⟩)
  have htargets_sub : allTargets ⊆ oneModThreeLargeSources N q := by
    intro t ht
    obtain ⟨ht_erase, s, hsK, ht_dvd⟩ := Finset.mem_filter.mp ht
    obtain ⟨htq, ht_mem⟩ := Finset.mem_erase.mp ht_erase
    have ht_prime : t.Prime := Nat.prime_of_mem_primeFactors ht_mem
    have ht3 : t ≠ 3 := fun h => h3 (h ▸ Nat.dvd_of_mem_primeFactors ht_mem)
    rw [hsig_eq hsK] at ht_dvd
    have ht_mod3 : t % 3 = 1 :=
      (prime_dvd_sq_add_self_add_one ht_prime ht_dvd).resolve_left ht3
    have ht_pos : 0 < N.factorization t :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ht_mem)
    have ht_lt6 : ¬ 6 ≤ N.factorization t := fun hge =>
      hfree t ht_prime ((ht_prime.pow_dvd_iff_le_factorization hN.2.ne').2 hge)
    obtain ⟨m, hm⟩ := hev t htq
    have ht_ge4 : 4 ≤ N.factorization t := by
      by_contra hlt4
      have ht_exp2 : N.factorization t = 2 := by omega
      have h3_dvd_sq : 3 ∣ ∑ d ∈ (t ^ 2).divisors, d := by
        rw [← sigma_one_apply, sigma_one_sq_local ht_prime]
        have hc : t ≡ 1 [MOD 3] := ht_mod3
        have hsum : t ^ 2 + t + 1 ≡ 1 ^ 2 + 1 + 1 [MOD 3] :=
          ((hc.pow 2).add hc).add (Nat.ModEq.refl 1)
        change (t ^ 2 + t + 1) % 3 = 0 at hsum
        exact Nat.dvd_of_mod_eq_zero hsum
      have h3_dvd_N : 3 ∣ N := dvd_perfect_of_exact_prime_pow hN ht_prime
        (ht_exp2 ▸ Nat.ordProj_dvd N t)
        ((ht_prime.pow_dvd_iff_le_factorization hN.2.ne').not.mpr (by omega))
        (by decide) (by decide) h3_dvd_sq
      exact h3 h3_dvd_N
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨ht_mem, ht3, htq, ht_ge4⟩, ht_mod3⟩
  have htargets_exp4 : ∀ t ∈ allTargets, N.factorization t = 4 := fun t ht =>
    hlg4 t (Finset.mem_filter.mp (htargets_sub ht)).1
  let wOf (s : ℕ) : ℕ :=
    if hs : s ∈ K then Classical.choose (hK_chain s hs) else 0
  have hwOf_mem : ∀ {s : ℕ}, s ∈ K → wOf s ∈ N.primeFactors := by
    intro s hs
    dsimp only [wOf]
    split
    · exact (Classical.choose_spec (hK_chain s hs)).1
    · contradiction
  have hwOf_eq : ∀ {s : ℕ}, s ∈ K → s = quarticPoly (wOf s) := by
    intro s hs
    dsimp only [wOf]
    split
    · exact (Classical.choose_spec (hK_chain s hs)).2.2
    · contradiction
  have hwOf_unique : ∀ {s w : ℕ}, s ∈ K → s = quarticPoly w → w = wOf s := by
    intro s w hs hsw
    apply quarticPoly_strictMono.injective
    rw [← hsw, ← hwOf_eq hs]
  have hwOf_prime : ∀ {s : ℕ}, s ∈ K → (wOf s).Prime := fun hs =>
    Nat.prime_of_mem_primeFactors (hwOf_mem hs)
  have hwOf_ge1 : ∀ {s : ℕ}, s ∈ K → 1 ≤ wOf s := fun hs =>
    (hwOf_prime hs).one_lt.le
  have hwOf_ge2 : ∀ {s : ℕ}, s ∈ K → 2 ≤ wOf s := fun hs =>
    (hwOf_prime hs).two_le
  have hwOf_mod5 : ∀ {s : ℕ}, s ∈ K →
      wOf s % 5 = 2 ∨ wOf s % 5 = 3 ∨ wOf s % 5 = 4 := by
    intro s hs
    have hne0 : wOf s % 5 ≠ 0 := fun h0 =>
      h5 ((Nat.dvd_of_mod_eq_zero h0).trans (Nat.dvd_of_mem_primeFactors (hwOf_mem hs)))
    have hne1 : wOf s % 5 ≠ 1 := by
      intro h1
      have hc : wOf s ≡ 1 [MOD 5] := h1
      have hp : quarticPoly (wOf s) ≡ 1 ^ 4 + 1 ^ 3 + 1 ^ 2 + 1 + 1 [MOD 5] := by
        unfold quarticPoly
        exact ((((hc.pow 4).add (hc.pow 3)).add (hc.pow 2)).add hc).add (Nat.ModEq.refl 1)
      change quarticPoly (wOf s) % 5 = (1 ^ 4 + 1 ^ 3 + 1 ^ 2 + 1 + 1) % 5 at hp
      rw [show (1 ^ 4 + 1 ^ 3 + 1 ^ 2 + 1 + 1) % 5 = 0 by decide, ← hwOf_eq hs] at hp
      have hs_mem : s ∈ N.primeFactors := (Finset.mem_filter.mp (hK_sub hs)).1
      exact h5 ((Nat.dvd_of_mod_eq_zero hp).trans (Nat.dvd_of_mem_primeFactors hs_mem))
    have hlt5 : wOf s % 5 < 5 := Nat.mod_lt (wOf s) (by decide)
    omega
  have hsig_prod : ∀ {s : ℕ}, s ∈ K →
      sigma 1 (s ^ 2) = quarticFirstFactor (wOf s) * quarticSecondFactor (wOf s) := by
    intro s hsK
    conv_lhs => rw [hsig_eq hsK, hwOf_eq hsK, quartic_phi3_factor_product]
  let T_r (r : ℕ) : Finset ℕ :=
    allTargets.filter (fun t => t % 5 = r) ∪
      (if (∃ s ∈ K, q ∣ sigma 1 (s ^ 2)) ∧ q % 5 = r then {q} else ∅)
  have hTr_card : ∀ r : ℕ, (T_r r).card ≤ D_r r + q_r r := by
    intro r
    dsimp only [T_r, D_r, q_r]
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add_left ?_ _)
    by_cases h : (∃ s ∈ K, q ∣ sigma 1 (s ^ 2)) ∧ q % 5 = r <;> simp [h]
  have hmem_Tr : ∀ {s p r : ℕ}, s ∈ K → p.Prime → p ∣ sigma 1 (s ^ 2) → p % 5 = r →
      p ∈ T_r r := by
    intro s p r hsK hp_prime hp_dvd hp_mod
    have hp_sub : p ∈ insert q allTargets :=
      hsig_pf_sub hsK (Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd, hsig_ne0 hsK⟩)
    rcases Finset.mem_insert.mp hp_sub with hpq | hp_all
    · refine Finset.mem_union_right _ ?_
      have hcond : (∃ s ∈ K, q ∣ sigma 1 (s ^ 2)) ∧ q % 5 = r :=
        ⟨⟨s, hsK, hpq ▸ hp_dvd⟩, hpq ▸ hp_mod⟩
      simp [hpq, hcond]
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp_all, hp_mod⟩)
  have hk_A1_24 : k_A1_24 ≤ D_r 3 + q_r 3 := by
    refine (Finset.card_le_card_of_injOn (fun s => quarticFirstFactor (wOf s)) ?_ ?_).trans
      (hTr_card 3)
    · intro s hs
      obtain ⟨hsK, w, _, hsw, hw5, hAp⟩ := Finset.mem_filter.mp hs
      have hweq : w = wOf s := hwOf_unique hsK hsw
      subst hweq
      have hmod : quarticFirstFactor (wOf s) % 5 = 3 :=
        quarticFirstFactor_mod_five_of_two_four (hwOf_ge1 hsK) hw5
      have hdvd : quarticFirstFactor (wOf s) ∣ sigma 1 (s ^ 2) := by
        rw [hsig_prod hsK]
        exact dvd_mul_right _ _
      exact hmem_Tr hsK hAp hdvd hmod
    · intro s₁ hs₁ s₂ hs₂ heq
      have hs₁K := (Finset.mem_filter.mp hs₁).1
      have hs₂K := (Finset.mem_filter.mp hs₂).1
      have hweq := quarticFirstFactor_injOn (hwOf_ge1 hs₁K) (hwOf_ge1 hs₂K) heq
      rw [hwOf_eq hs₁K, hwOf_eq hs₂K, hweq]
  have hk_A1_3 : k_A1_3 ≤ D_r 2 + q_r 2 := by
    refine (Finset.card_le_card_of_injOn (fun s => quarticFirstFactor (wOf s)) ?_ ?_).trans
      (hTr_card 2)
    · intro s hs
      obtain ⟨hsK, w, _, hsw, hw5, hAp⟩ := Finset.mem_filter.mp hs
      have hweq : w = wOf s := hwOf_unique hsK hsw
      subst hweq
      have hmod : quarticFirstFactor (wOf s) % 5 = 2 :=
        quarticFirstFactor_mod_five_of_three (hwOf_ge1 hsK) hw5
      have hdvd : quarticFirstFactor (wOf s) ∣ sigma 1 (s ^ 2) := by
        rw [hsig_prod hsK]
        exact dvd_mul_right _ _
      exact hmem_Tr hsK hAp hdvd hmod
    · intro s₁ hs₁ s₂ hs₂ heq
      have hs₁K := (Finset.mem_filter.mp hs₁).1
      have hs₂K := (Finset.mem_filter.mp hs₂).1
      have hweq := quarticFirstFactor_injOn (hwOf_ge1 hs₁K) (hwOf_ge1 hs₂K) heq
      rw [hwOf_eq hs₁K, hwOf_eq hs₂K, hweq]
  have hk_B1_24 : k_B1_24 ≤ D_r 1 + q_r 1 := by
    refine (Finset.card_le_card_of_injOn (fun s => quarticSecondFactor (wOf s)) ?_ ?_).trans
      (hTr_card 1)
    · intro s hs
      obtain ⟨hsK, w, _, hsw, hw5, hBp⟩ := Finset.mem_filter.mp hs
      have hweq : w = wOf s := hwOf_unique hsK hsw
      subst hweq
      have hmod : quarticSecondFactor (wOf s) % 5 = 1 :=
        quarticSecondFactor_mod_five_of_two_four hw5
      have hdvd : quarticSecondFactor (wOf s) ∣ sigma 1 (s ^ 2) := by
        rw [hsig_prod hsK]
        exact dvd_mul_left _ _
      exact hmem_Tr hsK hBp hdvd hmod
    · intro s₁ hs₁ s₂ hs₂ heq
      have hs₁K := (Finset.mem_filter.mp hs₁).1
      have hs₂K := (Finset.mem_filter.mp hs₂).1
      have hweq := quarticSecondFactor_strictMono.injective heq
      rw [hwOf_eq hs₁K, hwOf_eq hs₂K, hweq]
  have hk_B1_3 : k_B1_3 ≤ D_r 4 + q_r 4 := by
    refine (Finset.card_le_card_of_injOn (fun s => quarticSecondFactor (wOf s)) ?_ ?_).trans
      (hTr_card 4)
    · intro s hs
      obtain ⟨hsK, w, _, hsw, hw5, hBp⟩ := Finset.mem_filter.mp hs
      have hweq : w = wOf s := hwOf_unique hsK hsw
      subst hweq
      have hmod : quarticSecondFactor (wOf s) % 5 = 4 :=
        quarticSecondFactor_mod_five_of_three hw5
      have hdvd : quarticSecondFactor (wOf s) ∣ sigma 1 (s ^ 2) := by
        rw [hsig_prod hsK]
        exact dvd_mul_left _ _
      exact hmem_Tr hsK hBp hdvd hmod
    · intro s₁ hs₁ s₂ hs₂ heq
      have hs₁K := (Finset.mem_filter.mp hs₁).1
      have hs₂K := (Finset.mem_filter.mp hs₂).1
      have hweq := quarticSecondFactor_strictMono.injective heq
      rw [hwOf_eq hs₁K, hwOf_eq hs₂K, hweq]
  have hDr_sum : D_r 1 + D_r 2 + D_r 3 + D_r 4 = allTargets.card := by
    simp only [D_r, Finset.card_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    trans ∑ _t ∈ allTargets, 1
    · refine Finset.sum_congr rfl fun t ht => ?_
      have ht_mem : t ∈ N.primeFactors := (Finset.mem_erase.mp (Finset.mem_filter.mp ht).1).2
      have ht5 : t % 5 ≠ 0 := fun h0 =>
        h5 ((Nat.dvd_of_mod_eq_zero h0).trans (Nat.dvd_of_mem_primeFactors ht_mem))
      have hlt5 : t % 5 < 5 := Nat.mod_lt t (by decide)
      rcases (by omega : t % 5 = 1 ∨ t % 5 = 2 ∨ t % 5 = 3 ∨ t % 5 = 4) with h | h | h | h <;>
        simp [h]
    · simp
  have hqr_sum : q_r 1 + q_r 2 + q_r 3 + q_r 4 = q_tot := by
    have hq5 : q % 5 ≠ 0 := fun h0 =>
      h5 ((Nat.dvd_of_mod_eq_zero h0).trans (Nat.dvd_of_mem_primeFactors hq))
    have hq_lt5 : q % 5 < 5 := Nat.mod_lt q (by decide)
    dsimp only [q_r, q_tot]
    by_cases hq_ex : ∃ s ∈ K, q ∣ sigma 1 (s ^ 2)
    · rcases (by omega : q % 5 = 1 ∨ q % 5 = 2 ∨ q % 5 = 3 ∨ q % 5 = 4) with h | h | h | h <;>
        simp [hq_ex, h]
    · simp [hq_ex]
  have hk_sum_le : k_A1_24 + k_A1_3 + k_B1_24 + k_B1_3 ≤ allTargets.card + q_tot := by
    omega
  have hkA_sum : k_A1_24 + k_A1_3 =
      ∑ s ∈ K, if (quarticFirstFactor (wOf s)).Prime then 1 else 0 := by
    dsimp only [k_A1_24, k_A1_3]
    simp only [Finset.card_filter]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s hsK => ?_
    by_cases hp : (quarticFirstFactor (wOf s)).Prime
    · rcases hwOf_mod5 hsK with h2 | h3' | h4
      · have hP1 : ∃ w ∈ N.primeFactors, s = quarticPoly w ∧ (w % 5 = 2 ∨ w % 5 = 4) ∧
            (quarticFirstFactor w).Prime :=
          ⟨wOf s, hwOf_mem hsK, hwOf_eq hsK, Or.inl h2, hp⟩
        have hP2 : ¬ ∃ w ∈ N.primeFactors, s = quarticPoly w ∧ w % 5 = 3 ∧
            (quarticFirstFactor w).Prime := by
          rintro ⟨w, _, hsw, hw3, _⟩
          have := hwOf_unique hsK hsw
          omega
        simp only [hp, hP1, hP2, ite_true, ite_false]
      · have hP1 : ¬ ∃ w ∈ N.primeFactors, s = quarticPoly w ∧ (w % 5 = 2 ∨ w % 5 = 4) ∧
            (quarticFirstFactor w).Prime := by
          rintro ⟨w, _, hsw, hw24, _⟩
          have := hwOf_unique hsK hsw
          omega
        have hP2 : ∃ w ∈ N.primeFactors, s = quarticPoly w ∧ w % 5 = 3 ∧
            (quarticFirstFactor w).Prime :=
          ⟨wOf s, hwOf_mem hsK, hwOf_eq hsK, h3', hp⟩
        simp only [hp, hP1, hP2, ite_true, ite_false]
      · have hP1 : ∃ w ∈ N.primeFactors, s = quarticPoly w ∧ (w % 5 = 2 ∨ w % 5 = 4) ∧
            (quarticFirstFactor w).Prime :=
          ⟨wOf s, hwOf_mem hsK, hwOf_eq hsK, Or.inr h4, hp⟩
        have hP2 : ¬ ∃ w ∈ N.primeFactors, s = quarticPoly w ∧ w % 5 = 3 ∧
            (quarticFirstFactor w).Prime := by
          rintro ⟨w, _, hsw, hw3, _⟩
          have := hwOf_unique hsK hsw
          omega
        simp only [hp, hP1, hP2, ite_true, ite_false]
    · have hP1 : ¬ ∃ w ∈ N.primeFactors, s = quarticPoly w ∧ (w % 5 = 2 ∨ w % 5 = 4) ∧
          (quarticFirstFactor w).Prime := by
        rintro ⟨w, _, hsw, _, hwp⟩
        exact hp (hwOf_unique hsK hsw ▸ hwp)
      have hP2 : ¬ ∃ w ∈ N.primeFactors, s = quarticPoly w ∧ w % 5 = 3 ∧
          (quarticFirstFactor w).Prime := by
        rintro ⟨w, _, hsw, _, hwp⟩
        exact hp (hwOf_unique hsK hsw ▸ hwp)
      simp only [hp, hP1, hP2, ite_false]
  have hkB_sum : k_B1_24 + k_B1_3 =
      ∑ s ∈ K, if (quarticSecondFactor (wOf s)).Prime then 1 else 0 := by
    dsimp only [k_B1_24, k_B1_3]
    simp only [Finset.card_filter]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s hsK => ?_
    by_cases hp : (quarticSecondFactor (wOf s)).Prime
    · rcases hwOf_mod5 hsK with h2 | h3' | h4
      · have hP1 : ∃ w ∈ N.primeFactors, s = quarticPoly w ∧ (w % 5 = 2 ∨ w % 5 = 4) ∧
            (quarticSecondFactor w).Prime :=
          ⟨wOf s, hwOf_mem hsK, hwOf_eq hsK, Or.inl h2, hp⟩
        have hP2 : ¬ ∃ w ∈ N.primeFactors, s = quarticPoly w ∧ w % 5 = 3 ∧
            (quarticSecondFactor w).Prime := by
          rintro ⟨w, _, hsw, hw3, _⟩
          have := hwOf_unique hsK hsw
          omega
        simp only [hp, hP1, hP2, ite_true, ite_false]
      · have hP1 : ¬ ∃ w ∈ N.primeFactors, s = quarticPoly w ∧ (w % 5 = 2 ∨ w % 5 = 4) ∧
            (quarticSecondFactor w).Prime := by
          rintro ⟨w, _, hsw, hw24, _⟩
          have := hwOf_unique hsK hsw
          omega
        have hP2 : ∃ w ∈ N.primeFactors, s = quarticPoly w ∧ w % 5 = 3 ∧
            (quarticSecondFactor w).Prime :=
          ⟨wOf s, hwOf_mem hsK, hwOf_eq hsK, h3', hp⟩
        simp only [hp, hP1, hP2, ite_true, ite_false]
      · have hP1 : ∃ w ∈ N.primeFactors, s = quarticPoly w ∧ (w % 5 = 2 ∨ w % 5 = 4) ∧
            (quarticSecondFactor w).Prime :=
          ⟨wOf s, hwOf_mem hsK, hwOf_eq hsK, Or.inr h4, hp⟩
        have hP2 : ¬ ∃ w ∈ N.primeFactors, s = quarticPoly w ∧ w % 5 = 3 ∧
            (quarticSecondFactor w).Prime := by
          rintro ⟨w, _, hsw, hw3, _⟩
          have := hwOf_unique hsK hsw
          omega
        simp only [hp, hP1, hP2, ite_true, ite_false]
    · have hP1 : ¬ ∃ w ∈ N.primeFactors, s = quarticPoly w ∧ (w % 5 = 2 ∨ w % 5 = 4) ∧
          (quarticSecondFactor w).Prime := by
        rintro ⟨w, _, hsw, _, hwp⟩
        exact hp (hwOf_unique hsK hsw ▸ hwp)
      have hP2 : ¬ ∃ w ∈ N.primeFactors, s = quarticPoly w ∧ w % 5 = 3 ∧
          (quarticSecondFactor w).Prime := by
        rintro ⟨w, _, hsw, _, hwp⟩
        exact hp (hwOf_unique hsK hsw ▸ hwp)
      simp only [hp, hP1, hP2, ite_false]
  have hlower_K : 4 * K.card ≤ (∑ s ∈ K, cardFactors (sigma 1 (s ^ 2))) +
      (k_A1_24 + k_A1_3 + k_B1_24 + k_B1_3) := by
    rw [add_assoc (k_A1_24 + k_A1_3), hkA_sum, hkB_sum]
    have h4K : 4 * K.card = ∑ _s ∈ K, 4 := by simp [Finset.sum_const, Nat.mul_comm]
    rw [h4K]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun s hsK => ?_
    have hw2 : 2 ≤ wOf s := hwOf_ge2 hsK
    have hA1 : 1 < quarticFirstFactor (wOf s) := by
      unfold quarticFirstFactor
      have hsq : 2 * wOf s ≤ (wOf s) ^ 2 := by nlinarith
      omega
    have hB1 : 1 < quarticSecondFactor (wOf s) := by
      unfold quarticSecondFactor
      omega
    have hprod : sigma 1 (s ^ 2) = quarticFirstFactor (wOf s) * quarticSecondFactor (wOf s) :=
      hsig_prod hsK
    have hcf_mul : cardFactors (sigma 1 (s ^ 2)) =
        cardFactors (quarticFirstFactor (wOf s)) + cardFactors (quarticSecondFactor (wOf s)) := by
      rw [hprod]
      exact cardFactors_mul (by omega) (by omega)
    have hA_le : 2 ≤ cardFactors (quarticFirstFactor (wOf s)) +
        (if (quarticFirstFactor (wOf s)).Prime then 1 else 0) := by
      by_cases hp : (quarticFirstFactor (wOf s)).Prime
      · simp only [hp, ite_true, cardFactors_apply_prime hp]
        exact le_rfl
      · simp only [hp, ite_false, add_zero]
        exact two_le_cardFactors_of_not_prime hA1 hp
    have hB_le : 2 ≤ cardFactors (quarticSecondFactor (wOf s)) +
        (if (quarticSecondFactor (wOf s)).Prime then 1 else 0) := by
      by_cases hp : (quarticSecondFactor (wOf s)).Prime
      · simp only [hp, ite_true, cardFactors_apply_prime hp]
        exact le_rfl
      · simp only [hp, ite_false, add_zero]
        exact two_le_cardFactors_of_not_prime hB1 hp
    omega
  have hupper_K : ∑ s ∈ K, cardFactors (sigma 1 (s ^ 2)) ≤ 4 * allTargets.card + q_tot := by
    have hq_not_all : q ∉ allTargets := fun h =>
      (Finset.mem_erase.mp (Finset.mem_filter.mp h).1).1 rfl
    have hrewrite : ∑ s ∈ K, cardFactors (sigma 1 (s ^ 2)) =
        (∑ s ∈ K, (sigma 1 (s ^ 2)).factorization q) +
          ∑ t ∈ allTargets, ∑ s ∈ K, (sigma 1 (s ^ 2)).factorization t := by
      have hcongr : ∑ s ∈ K, cardFactors (sigma 1 (s ^ 2)) =
          ∑ s ∈ K, ((sigma 1 (s ^ 2)).factorization q +
            ∑ t ∈ allTargets, (sigma 1 (s ^ 2)).factorization t) := by
        refine Finset.sum_congr rfl fun s hsK => ?_
        rw [cardFactors_eq_sum_factorization_of_subset (hsig_pf_sub hsK),
          Finset.sum_insert hq_not_all]
      rw [hcongr, Finset.sum_add_distrib, Finset.sum_comm]
    have hsum_le_fac : ∀ p ∈ N.primeFactors,
        ∑ s ∈ K, (sigma 1 (s ^ 2)).factorization p ≤ N.factorization p := by
      intro p hp
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      have hp_odd := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
      rw [factorization_eq_sum_sigma_factorizations hN hp_odd hp_prime]
      calc
        ∑ s ∈ K, (sigma 1 (s ^ 2)).factorization p
            = ∑ s ∈ K, (sigma 1 (s ^ N.factorization s)).factorization p := by
                refine Finset.sum_congr rfl fun s hsK => ?_
                rw [(Finset.mem_filter.mp (hK_sub hsK)).2.2]
        _ ≤ ∑ s ∈ N.primeFactors, (sigma 1 (s ^ N.factorization s)).factorization p :=
              Finset.sum_le_sum_of_subset (hK_sub.trans (Finset.filter_subset _ _))
    have hq_le : ∑ s ∈ K, (sigma 1 (s ^ 2)).factorization q ≤ q_tot := by
      dsimp only [q_tot]
      by_cases hq_ex : ∃ s ∈ K, q ∣ sigma 1 (s ^ 2)
      · simp only [hq_ex, ite_true]
        exact (hsum_le_fac q hq).trans hq1.le
      · simp only [hq_ex, ite_false]
        have hzero : ∀ s ∈ K, (sigma 1 (s ^ 2)).factorization q = 0 := fun s hsK =>
          Nat.factorization_eq_zero_of_not_dvd fun hd => hq_ex ⟨s, hsK, hd⟩
        rw [Finset.sum_eq_zero hzero]
    have ht_le : ∑ t ∈ allTargets, ∑ s ∈ K, (sigma 1 (s ^ 2)).factorization t ≤
        4 * allTargets.card := by
      calc
        ∑ t ∈ allTargets, ∑ s ∈ K, (sigma 1 (s ^ 2)).factorization t
            ≤ ∑ _t ∈ allTargets, 4 := by
                refine Finset.sum_le_sum fun t ht => ?_
                have ht_mem : t ∈ N.primeFactors :=
                  (Finset.mem_erase.mp (Finset.mem_filter.mp ht).1).2
                exact (hsum_le_fac t ht_mem).trans (htargets_exp4 t ht).le
        _ = 4 * allTargets.card := by simp [Finset.sum_const, Nat.mul_comm]
    omega
  have hqtot_le1 : q_tot ≤ 1 := by
    dsimp only [q_tot]
    by_cases h : ∃ s ∈ K, q ∣ sigma 1 (s ^ 2) <;> simp [h]
  have h4K_q : 4 * K.card ≤ 5 * allTargets.card + 2 * q_tot := by omega
  have h4K : 4 * K.card ≤ 5 * allTargets.card + 2 := by omega
  have h3K : 3 * K.card ≤ 5 * allTargets.card + 2 := by omega
  exact ⟨htargets_sub, htargets_exp4, hk_A1_24, hk_A1_3, hk_B1_24, hk_B1_3,
    hk_sum_le, h4K_q, h4K, h3K⟩

open Classical in
theorem quarticChainSources_five_mul_allTargets_ge_four_mul_sub_two {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    let K := quarticChainIntermediates N q
    let allTargets := (N.primeFactors.erase q).filter (fun t => ∃ s ∈ K, t ∣ sigma 1 (s ^ 2))
    allTargets ⊆ oneModThreeLargeSources N q ∧
    (∀ t ∈ allTargets, N.factorization t = 4) ∧
    4 * (quarticChainSources N q).card ≤ 5 * allTargets.card + 2 ∧
    3 * (quarticChainSources N q).card ≤ 5 * allTargets.card + 2 := by
  intro K allTargets
  have h3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  have hlg4 : ∀ u ∈ largeSources N q, N.factorization u = 4 :=
    (three_free_sixthPowerFree_forces_147_largeSources ho hN hq hq4 he hev h3 hfree).1
  have hcs := quarticChainSources_eq_oneModThree_prime_and_card ho hN hq hq4 he hev hfree
  have hK_col := hcs.2.2.1
  have hK_card : K.card = (quarticChainSources N q).card := hcs.2.2.2
  have hK_sub : K ⊆ squareSources N := fun s hs =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp (hK_col hs)).1).1
  have hK_chain : ∀ s ∈ K, ∃ w ∈ N.primeFactors, N.factorization w = 4 ∧
      s = w ^ 4 + w ^ 3 + w ^ 2 + w + 1 := by
    intro s hs
    obtain ⟨w, hw_src, rfl⟩ := Finset.mem_image.mp hs
    have hw_lg := (Finset.mem_filter.mp hw_src).1
    have hw_mem := (Finset.mem_filter.mp hw_lg).1
    have hw_prime := Nat.prime_of_mem_primeFactors hw_mem
    exact ⟨w, hw_mem, hlg4 w hw_lg, sigma_one_four_local hw_prime⟩
  obtain ⟨htargets_sub, htargets_exp4, _, _, _, _, _, _, h4le, h3le⟩ :=
    quartic_chain_mod_five_target_reuse ho hN hq hq4 he hev hfree K hK_sub hK_chain
  rw [hK_card] at h4le h3le
  exact ⟨htargets_sub, htargets_exp4, h4le, h3le⟩

end OddPerfect
