module

public import OddPerfect.GlobalWave8Obstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exceptional Valuation Matrix & Factor-Drop Profile (`OddPerfect.ExceptionalValuationProfile`)

Establishes the exact valuation-matrix profile and cyclotomic factor-drop bounds on the
exceptional prime-times-square Euler-index branch (`N = q ^ a * m ^ 2`, `1 < a`,
`sigma 1 (m ^ 2) / q ^ a = l * t ^ 2`, `l.Prime`):
1. `exceptional_euler_componentIndex_eq`: identifies `componentIndex N q = l * t ^ 2`,
   `N.factorization q = a`, `ordCompl[q] N = m ^ 2`, and `l ∈ N.primeFactors` (`l ≠ q`,
   `Odd l`, `Odd t`, `0 < t`).
2. `exceptional_euler_valuation_matrix_profile`: gives the complete prime-by-prime valuation
   conservation profile across `N.primeFactors.erase q` and at `l`, proving
   `oddSigmaTargets N q = {l}` and the `N.factorization l = 2` specialization.
3. `exceptional_euler_thirty_six_and_148_factor_drop`: combines
   `exceptional_euler_pell_fundamental_profile`, `odd_prime_cyclotomic_pair_dvd_sigma`,
   `cardFactors_componentIndex_add_eq`, and `exceptional_euler_three_dvd_dichotomy` to prove
   `cardFactors (componentIndex N q) + 36 ≤ cardFactors N` unconditionally and
   `cardFactors (componentIndex N q) + 148 ≤ cardFactors N` when `¬ 3 ∣ N`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma euler_cofactor_odd {N q a m : ℕ} (ho : Odd N)
    (hform : N = q ^ a * m ^ 2) : Odd m := by
  have hm2 : Odd (m ^ 2) := ho.of_dvd_nat (hform ▸ dvd_mul_left _ _)
  exact hm2.of_dvd_nat (dvd_pow_self m (by decide : 2 ≠ 0))

private lemma euler_cofactor_factorization_eq {N q a m : ℕ} (ho : Odd N) (hq : q.Prime)
    (hform : N = q ^ a * m ^ 2) {r : ℕ} (hrq : r ≠ q) :
    N.factorization r = 2 * m.factorization r := by
  have hm : Odd m := euler_cofactor_odd ho hform
  rw [hform, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hm.pos.ne'),
    Finsupp.add_apply, hq.factorization_pow, Finsupp.single_apply, ite_eq_right hrq.symm,
    zero_add, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]

/-- Exact identification of `componentIndex N q = l * t ^ 2` and basic parity/support data
on the exceptional prime-times-square Euler-index branch (`a > 1`, `l.Prime`). -/
theorem exceptional_euler_componentIndex_eq {N q a m l t : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha1 : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hI : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    q ∈ N.primeFactors ∧ N.factorization q = a ∧ ordCompl[q] N = m ^ 2 ∧
      componentIndex N q = l * t ^ 2 ∧ 0 < t ∧ Odd l ∧ Odd t ∧
      l ≠ q ∧ l ∈ N.primeFactors := by
  have hm : Odd m := euler_cofactor_odd ho hform
  have hqN : q ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr
      ⟨hq, hform ▸ dvd_mul_of_dvd_left (dvd_pow_self q (by omega)) _, hN.2.ne'⟩
  have hval : N.factorization q = a := by
    rw [hform, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hm.pos.ne'),
      Finsupp.add_apply, hq.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_pow, Finsupp.smul_apply,
      Nat.factorization_eq_zero_of_not_dvd hqm, smul_eq_mul, mul_zero, add_zero]
  have hordProj : ordProj[q] N = q ^ a := by rw [hval]
  have hordCompl : ordCompl[q] N = m ^ 2 := by
    have hmul : q ^ a * ordCompl[q] N = q ^ a * m ^ 2 := by
      calc
        q ^ a * ordCompl[q] N = ordProj[q] N * ordCompl[q] N := by rw [hordProj]
        _ = N := Nat.ordProj_mul_ordCompl_eq_self N q
        _ = q ^ a * m ^ 2 := hform
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hq.pos a) hmul
  have hci : componentIndex N q = l * t ^ 2 := by
    rw [componentIndex, hordCompl, hordProj, hI]
  obtain ⟨_, _, _, _, _, ht3⟩ :=
    exceptional_index_parameter_floors hN ho hq hq4 ha4 ha1 hqm hform hl hI
  have ht_pos : 0 < t := by omega
  have hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r) := fun r hr => by
    rw [euler_cofactor_factorization_eq ho hq hform hr]
    exact even_two_mul _
  have he4 : N.factorization q % 4 = 1 := by simpa [hval] using ha4
  have hci_odd : Odd (componentIndex N q) :=
    ((componentIndex_two_valuation_dichotomy ho hN hqN hq4 he4 hev hqN).1 rfl).2
  have hlt2_odd : Odd (l * t ^ 2) := hci ▸ hci_odd
  have hl_odd : Odd l := hlt2_odd.of_dvd_nat (dvd_mul_right l (t ^ 2))
  have ht_odd : Odd t :=
    (hlt2_odd.of_dvd_nat (dvd_mul_left (t ^ 2) l)).of_dvd_nat
      (dvd_pow_self t (by decide : 2 ≠ 0))
  have hq_ndvd : ¬ q ∣ componentIndex N q := componentIndex_not_dvd_self ho hN hqN
  have hlq : l ≠ q := by
    intro h
    apply hq_ndvd
    rw [hci, ← h]
    exact dvd_mul_right l (t ^ 2)
  have hlN : l ∈ N.primeFactors := by
    obtain ⟨hmul, _⟩ := componentIndex_mul_eq_two_mul hN hqN
    have hl_dvd_2N : l ∣ 2 * N := by
      rw [← hmul, hci]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right l (t ^ 2)) _) _
    have hl_ne2 : l ≠ 2 := fun h => (by decide : ¬ Odd 2) (h ▸ hl_odd)
    have hl_ndvd2 : ¬ l ∣ 2 := fun h2 =>
      hl_ne2 (((Nat.dvd_prime Nat.prime_two).mp h2).resolve_left hl.ne_one)
    have hl_dvd_N : l ∣ N := (hl.dvd_mul.mp hl_dvd_2N).resolve_left hl_ndvd2
    exact Nat.mem_primeFactors.mpr ⟨hl, hl_dvd_N, hN.2.ne'⟩
  exact ⟨hqN, hval, hordCompl, hci, ht_pos, hl_odd, ht_odd, hlq, hlN⟩

/-- Valuation matrix profile on the exceptional prime-times-square Euler-index branch:
every cofactor prime `r ≠ l` has even index and `σ(q^a)` valuations, `l` is the unique
odd-valuation target (`oddSigmaTargets N q = {l}`), and `N.factorization l = 2` forces
`¬ l ∣ t` and `(sigma 1 (q ^ a)).factorization l = 1`. -/
theorem exceptional_euler_valuation_matrix_profile {N q a m l t : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha1 : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hI : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    (∀ r ∈ N.primeFactors.erase q, r ≠ l →
      (componentIndex N q).factorization r = 2 * t.factorization r ∧
        Even ((sigma 1 (q ^ a)).factorization r)) ∧
    ((componentIndex N q).factorization l = 1 + 2 * t.factorization l ∧
      Odd ((sigma 1 (q ^ a)).factorization l) ∧
      1 + 2 * t.factorization l + (sigma 1 (q ^ a)).factorization l = N.factorization l) ∧
    oddSigmaTargets N q = {l} ∧
    (N.factorization l = 2 → ¬ l ∣ t ∧ (sigma 1 (q ^ a)).factorization l = 1) := by
  obtain ⟨hqN, hval, _, hci, ht_pos, hl_odd, _, hlq, hlN⟩ :=
    exceptional_euler_componentIndex_eq ho hN hq hq4 ha4 ha1 hqm hform hl hI
  have hordProj : ordProj[q] N = q ^ a := by rw [hval]
  have hci_fac : ∀ r : ℕ,
      (componentIndex N q).factorization r = l.factorization r + 2 * t.factorization r := by
    intro r
    rw [hci, Nat.factorization_mul hl.ne_zero (pow_ne_zero 2 ht_pos.ne'),
      Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have hother : ∀ r ∈ N.primeFactors.erase q, r ≠ l →
      (componentIndex N q).factorization r = 2 * t.factorization r ∧
        Even ((sigma 1 (q ^ a)).factorization r) := by
    intro r hr hrl
    have hrq : r ≠ q := (Finset.mem_erase.mp hr).1
    have hrN : r ∈ N.primeFactors := (Finset.mem_erase.mp hr).2
    have hr_odd : Odd r := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hrN)
    have hr2 : r ≠ 2 := fun h => (by decide : ¬ Odd 2) (h ▸ hr_odd)
    have hci_r : (componentIndex N q).factorization r = 2 * t.factorization r := by
      rw [hci_fac r, hl.factorization, Finsupp.single_apply, ite_eq_right hrl.symm, zero_add]
    have hsub := componentIndex_factorization_eq_sub ho hN hqN hrq hr2
    rw [hordProj, hci_r, euler_cofactor_factorization_eq ho hq hform hrq] at hsub
    have heven : Even ((sigma 1 (q ^ a)).factorization r) := by
      refine ⟨m.factorization r - t.factorization r, ?_⟩
      omega
    exact ⟨hci_r, heven⟩
  have hl2 : l ≠ 2 := fun h => (by decide : ¬ Odd 2) (h ▸ hl_odd)
  have hci_l : (componentIndex N q).factorization l = 1 + 2 * t.factorization l := by
    rw [hci_fac l, hl.factorization, Finsupp.single_eq_same]
  have hsub_l := componentIndex_factorization_eq_sub ho hN hqN hlq hl2
  rw [hordProj, hci_l] at hsub_l
  have hN_l_eq : N.factorization l = 2 * m.factorization l :=
    euler_cofactor_factorization_eq ho hq hform hlq
  have hsig_l_odd : Odd ((sigma 1 (q ^ a)).factorization l) := by
    rw [Nat.odd_iff]
    omega
  have htargets : oddSigmaTargets N q = {l} := by
    rw [euler_oddSigmaTargets_eq_index hN ho hq hq4 ha4 hqm hform, hI]
    ext r
    simp only [mem_oddValuationPrimes, Finset.mem_singleton]
    rw [Nat.factorization_mul hl.ne_zero (pow_ne_zero 2 ht_pos.ne'), Finsupp.add_apply,
      hl.factorization, Finsupp.single_apply, Nat.factorization_pow, Finsupp.smul_apply,
      smul_eq_mul]
    by_cases hrl : r = l
    · subst hrl
      simp
    · simp [hrl, ite_eq_right (Ne.symm hrl), Nat.odd_iff]
  have hvl2 : N.factorization l = 2 → ¬ l ∣ t ∧ (sigma 1 (q ^ a)).factorization l = 1 := by
    intro hN2
    have htl0 : t.factorization l = 0 := by omega
    have hsig1 : (sigma 1 (q ^ a)).factorization l = 1 := by omega
    refine ⟨?_, hsig1⟩
    intro hlt
    have hle1 : 1 ≤ t.factorization l := (hl.dvd_iff_one_le_factorization ht_pos.ne').mp hlt
    omega
  exact ⟨hother, ⟨hci_l, hsig_l_odd, hsub_l⟩, htargets, hvl2⟩

/-- Lower bound `4 ≤ cardFactors (sigma 1 (q ^ a))` from the cyclotomic decomposition
`sigma 1 (q ^ a) = (q + 1) * B₁ * B₂` (`B₁ = geometricBlock q d`, `B₂ = (q ^ d + 1) / (q + 1)`). -/
theorem exceptional_euler_sigma_cardFactors_ge_four {N q a m l t : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha1 : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hI : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    4 ≤ cardFactors (sigma 1 (q ^ a)) := by
  let d := (a + 1) / 2
  obtain ⟨hd_prime, hd17, _, hq193, _, _, _, _⟩ :=
    exceptional_euler_pell_fundamental_profile hN ho hq hq4 ha4 ha1 hqm hform hl hI
  change d.Prime at hd_prime
  change 17 ≤ d at hd17
  change 193 ≤ q at hq193
  have ha_eq : a + 1 = d * 2 := by dsimp [d]; omega
  obtain ⟨hB₂_eq, hB₁_gt1, _, hB₂_gt1, _, _, _⟩ :=
    odd_prime_cyclotomic_pair_dvd_sigma hq hq4 ha4 hd_prime (by omega) dvd_rfl
  let B₁ := geometricBlock q d
  let B₂ := (q ^ d + 1) / (q + 1)
  have hsig_eq : sigma 1 (q ^ a) = (q + 1) * (B₁ * B₂) := by
    rw [sigma_one_apply_prime_pow hq]
    change geometricBlock q (a + 1) = (q + 1) * (B₁ * B₂)
    rw [ha_eq, geometricBlock_mul q d 2]
    have hg2 : geometricBlock (q ^ d) 2 = q ^ d + 1 := by
      rw [geometricBlock, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
      ring
    rw [hg2, ← hB₂_eq]
    change B₁ * ((q + 1) * B₂) = (q + 1) * (B₁ * B₂)
    ring
  have hq1_eq : q + 1 = 2 * ((q + 1) / 2) := by omega
  have hq1_half_gt1 : 1 < (q + 1) / 2 := by omega
  have hcf_q1 : 2 ≤ cardFactors (q + 1) := by
    rw [hq1_eq, cardFactors_mul (by decide : (2 : ℕ) ≠ 0) (by omega),
      cardFactors_apply_prime Nat.prime_two]
    have hpos : 0 < cardFactors ((q + 1) / 2) := cardFactors_pos_iff_one_lt.mpr hq1_half_gt1
    omega
  have hcf_B₁ : 1 ≤ cardFactors B₁ := cardFactors_pos_iff_one_lt.mpr hB₁_gt1
  have hcf_B₂ : 1 ≤ cardFactors B₂ := cardFactors_pos_iff_one_lt.mpr hB₂_gt1
  rw [hsig_eq, cardFactors_mul (by omega) (mul_ne_zero (by omega) (by omega)),
    cardFactors_mul (by omega) (by omega)]
  omega

/-- Unconditional 36-factor drop (`cardFactors (componentIndex N q) + 36 ≤ cardFactors N`)
and conditional 148-factor drop when `¬ 3 ∣ N` on the exceptional prime-times-square
Euler-index branch (`a > 1`, `l.Prime`). -/
theorem exceptional_euler_thirty_six_and_148_factor_drop {N q a m l t : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha1 : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hI : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    cardFactors (componentIndex N q) + 36 ≤ cardFactors N ∧
      (¬ 3 ∣ N → cardFactors (componentIndex N q) + 148 ≤ cardFactors N) := by
  obtain ⟨hqN, hval, _, _, _, _, _, _, _⟩ :=
    exceptional_euler_componentIndex_eq ho hN hq hq4 ha4 ha1 hqm hform hl hI
  have hbalance := cardFactors_componentIndex_add_eq hN hqN
  rw [hval] at hbalance
  have hsig4 : 4 ≤ cardFactors (sigma 1 (q ^ a)) :=
    exceptional_euler_sigma_cardFactors_ge_four ho hN hq hq4 ha4 ha1 hqm hform hl hI
  obtain ⟨_, hd17, _, _, _, _, _, _⟩ :=
    exceptional_euler_pell_fundamental_profile hN ho hq hq4 ha4 ha1 hqm hform hl hI
  have ha33 : 33 ≤ a := by omega
  have h36 : cardFactors (componentIndex N q) + 36 ≤ cardFactors N := by omega
  refine ⟨h36, ?_⟩
  intro hN3
  rcases exceptional_euler_three_dvd_dichotomy hN ho hq hq4 ha4 ha1 hqm hform hl hI with
    ⟨h3, _⟩ | ⟨_, _, _, _, ha145⟩
  · exact absurd h3 hN3
  · omega

end OddPerfect
