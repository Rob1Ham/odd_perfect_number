module

public import OddPerfect.ExceptionalBlockCoprimeFactorizationAndTargetRouting
public import OddPerfect.ExceptionalValuationProfile
public import OddPerfect.ExceptionalBranchClosure
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exceptional Euler 42/86/150/486 Factor-Drop Profile (`OddPerfect.ExceptionalEuler42And486FactorDrop`)

Strengthens `exceptional_euler_thirty_six_and_148_factor_drop` on the exceptional
prime-times-square Euler-index branch `sigma 1 (m ^ 2) / q ^ a = l * t ^ 2`
(`a > 1`, `l.Prime`, `d := (a + 1) / 2`) using the coprime triple factorization
`sigma 1 (q ^ a) = 2 * d ^ 2 * l * (w * z * v) ^ 2` and `15 ∣ w` at `d = 17`:
1. `exceptional_euler_exact_sigma_q_cardFactors`: exact formula
   `cardFactors (sigma 1 (q ^ a)) = 4 + 2 * (cardFactors w + cardFactors z + cardFactors v)`,
   unconditional `6 ≤ cardFactors (sigma 1 (q ^ a))`, and at `d = 17` both
   `2 ≤ cardFactors w` and `10 ≤ cardFactors (sigma 1 (q ^ a))`.
2. `exceptional_euler_42_86_150_486_factor_drop`: unconditional `42`-factor drop,
   `86`-factor drop when `d ≠ 17`, `150`-factor drop when `¬ 3 ∣ N`, and
   `486`-factor drop when `¬ 3 ∣ N` and `¬ 5 ∣ N`.
-/

public section

namespace OddPerfect

open ArithmeticFunction Finset

private lemma not_prime_of_mul_eq {a b n : ℕ} (ha : 1 < a) (hb : 1 < b) (h : a * b = n) :
    ¬ Nat.Prime n := by
  intro hp
  have hdvd : a ∣ n := ⟨b, h.symm⟩
  rcases hp.eq_one_or_self_of_dvd a hdvd with h1 | han <;> nlinarith

private lemma d_ge_41_of_ne_17 {d : ℕ} (hd : d.Prime) (hd17 : 17 ≤ d) (hd8 : d % 8 = 1)
    (hne : d ≠ 17) : 41 ≤ d := by
  by_contra hd_lt
  have hd_cases : d = 17 ∨ d = 25 ∨ d = 33 := by omega
  rcases hd_cases with rfl | rfl | rfl
  · exact hne rfl
  · exact not_prime_of_mul_eq (by decide : 1 < 5) (by decide : 1 < 5) (by norm_num) hd
  · exact not_prime_of_mul_eq (by decide : 1 < 3) (by decide : 1 < 11) (by norm_num) hd

/-- Exact prime-factor multiplicity formula for `sigma 1 (q ^ a)` on the exceptional
Euler-index branch `sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`),
giving `6 ≤ cardFactors (sigma 1 (q ^ a))` unconditionally and
`2 ≤ cardFactors w ∧ 10 ≤ cardFactors (sigma 1 (q ^ a))` at `d = 17`. -/
theorem exceptional_euler_exact_sigma_q_cardFactors {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    let d := (a + 1) / 2
    ∃ w z v : ℕ,
      0 < w ∧ 3 ≤ z ∧ 0 < v ∧
      q + 1 = 2 * d * w ^ 2 ∧
      (q ^ d + 1) / (q + 1) = d * z ^ 2 ∧
      geometricBlock q d = l * v ^ 2 ∧
      sigma 1 (q ^ a) = 2 * d ^ 2 * l * (w * z * v) ^ 2 ∧
      cardFactors (sigma 1 (q ^ a)) =
        4 + 2 * (cardFactors w + cardFactors z + cardFactors v) ∧
      6 ≤ cardFactors (sigma 1 (q ^ a)) ∧
      (d = 17 → 2 ≤ cardFactors w ∧ 10 ≤ cardFactors (sigma 1 (q ^ a))) := by
  intro d
  obtain ⟨hd_prime, hd17, _, _, _, _, _, _, _, _⟩ :=
    exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
  change d.Prime at hd_prime
  change 17 ≤ d at hd17
  obtain ⟨_, _, hq193, _, _, _⟩ :=
    exceptional_index_parameter_floors hN ho hq hq4 ha4 ha hqm hform hl hi
  change 193 ≤ q at hq193
  obtain ⟨w, z, v, hw_pos, hz_ge3, _, _, _, hv_odd, _, hq1, hdiv, hgeom, _⟩ :=
    exceptional_euler_coprime_triple_factorization_and_l_routing
      hN ho hq hq4 ha4 ha hqm hform hl hi
  change q + 1 = 2 * d * w ^ 2 at hq1
  change (q ^ d + 1) / (q + 1) = d * z ^ 2 at hdiv
  change geometricBlock q d = l * v ^ 2 at hgeom
  have hv_pos : 0 < v := hv_odd.pos
  have ha_eq : a + 1 = d * 2 := by dsimp [d]; omega
  have hd_odd : Odd d := hd_prime.odd_of_ne_two (by omega)
  have hq1_dvd : q + 1 ∣ q ^ d + 1 := by
    simpa only [one_pow] using hd_odd.nat_add_dvd_pow_add_pow q 1
  have hqd1_eq : q ^ d + 1 = (q + 1) * ((q ^ d + 1) / (q + 1)) :=
    (Nat.mul_div_cancel' hq1_dvd).symm
  have hsig_eq : sigma 1 (q ^ a) = 2 * d ^ 2 * l * (w * z * v) ^ 2 := by
    rw [sigma_one_apply_prime_pow hq]
    change geometricBlock q (a + 1) = 2 * d ^ 2 * l * (w * z * v) ^ 2
    rw [ha_eq, geometricBlock_mul q d 2]
    have hg2 : geometricBlock (q ^ d) 2 = q ^ d + 1 := by
      rw [geometricBlock, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
      ring
    rw [hg2, hqd1_eq, hdiv, hq1, hgeom]
    ring
  have hw_ne0 : w ≠ 0 := hw_pos.ne'
  have hz_ne0 : z ≠ 0 := by omega
  have hv_ne0 : v ≠ 0 := hv_pos.ne'
  have hcf_sig :
      cardFactors (sigma 1 (q ^ a)) =
        4 + 2 * (cardFactors w + cardFactors z + cardFactors v) := by
    rw [hsig_eq,
      cardFactors_mul
        (mul_ne_zero (mul_ne_zero (by decide) (pow_ne_zero 2 hd_prime.ne_zero)) hl.ne_zero)
        (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero hw_ne0 hz_ne0) hv_ne0)),
      cardFactors_mul (mul_ne_zero (by decide) (pow_ne_zero 2 hd_prime.ne_zero)) hl.ne_zero,
      cardFactors_mul (by decide) (pow_ne_zero 2 hd_prime.ne_zero),
      cardFactors_apply_prime Nat.prime_two,
      cardFactors_pow, cardFactors_apply_prime hd_prime,
      cardFactors_apply_prime hl,
      cardFactors_pow,
      cardFactors_mul (mul_ne_zero hw_ne0 hz_ne0) hv_ne0,
      cardFactors_mul hw_ne0 hz_ne0]
  have hz_cf : 1 ≤ cardFactors z := cardFactors_pos_iff_one_lt.mpr (by omega)
  have hcf_ge6 : 6 ≤ cardFactors (sigma 1 (q ^ a)) := by omega
  have hd17_imp : d = 17 → 2 ≤ cardFactors w ∧ 10 ≤ cardFactors (sigma 1 (q ^ a)) := by
    intro hd_eq
    have hq1_34 : q + 1 = 34 * w ^ 2 := by
      rw [hq1, hd_eq]
    have hq17 : q ^ 17 + 1 = (q + 1) * 17 * z ^ 2 := by
      calc
        q ^ 17 + 1 = q ^ d + 1 := by rw [hd_eq]
        _ = (q + 1) * ((q ^ d + 1) / (q + 1)) := hqd1_eq
        _ = (q + 1) * (d * z ^ 2) := by rw [hdiv]
        _ = (q + 1) * 17 * z ^ 2 := by rw [hd_eq]; ring
    obtain ⟨k, hk⟩ := exceptional_d17_fifteen_dvd_w hq hq193 hq1_34 hq17
    have hk_ne0 : k ≠ 0 := by
      intro hk0
      subst hk0
      simp at hk
      omega
    have hcf15 : cardFactors 15 = 2 := by
      rw [show (15 : ℕ) = 3 * 5 by decide,
        cardFactors_mul (by decide) (by decide),
        cardFactors_apply_prime (by decide : Nat.Prime 3),
        cardFactors_apply_prime (by decide : Nat.Prime 5)]
    have hw_cf : 2 ≤ cardFactors w := by
      rw [hk, cardFactors_mul (by decide) hk_ne0, hcf15]
      omega
    exact ⟨hw_cf, by omega⟩
  exact ⟨w, z, v, hw_pos, hz_ge3, hv_pos, hq1, hdiv, hgeom, hsig_eq, hcf_sig, hcf_ge6, hd17_imp⟩

/-- Unconditional `42`-factor drop, `86`-factor drop when `d ≠ 17`, `150`-factor drop
when `¬ 3 ∣ N`, and `486`-factor drop when `¬ 3 ∣ N` and `¬ 5 ∣ N` on the exceptional
Euler-index branch `sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`). -/
theorem exceptional_euler_42_86_150_486_factor_drop {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    let d := (a + 1) / 2
    cardFactors (componentIndex N q) + 42 ≤ cardFactors N ∧
    (d ≠ 17 → cardFactors (componentIndex N q) + 86 ≤ cardFactors N) ∧
    (¬ 3 ∣ N → cardFactors (componentIndex N q) + 150 ≤ cardFactors N) ∧
    (¬ 3 ∣ N → ¬ 5 ∣ N → cardFactors (componentIndex N q) + 486 ≤ cardFactors N) := by
  intro d
  obtain ⟨hqN, hval, _, _, _, _, _, _, _⟩ :=
    exceptional_euler_componentIndex_eq ho hN hq hq4 ha4 ha hqm hform hl hi
  have hbalance := cardFactors_componentIndex_add_eq hN hqN
  rw [hval] at hbalance
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hcf_ge6, hd17_imp⟩ :=
    exceptional_euler_exact_sigma_q_cardFactors hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨hd_prime, hd17, hd8, _, _, _, _, _, _, _⟩ :=
    exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
  change d.Prime at hd_prime
  change 17 ≤ d at hd17
  change d % 8 = 1 at hd8
  have h86 : d ≠ 17 → cardFactors (componentIndex N q) + 86 ≤ cardFactors N := by
    intro hne17
    have hd41 : 41 ≤ d := d_ge_41_of_ne_17 hd_prime hd17 hd8 hne17
    have ha81 : 81 ≤ a := by dsimp [d] at hd41; omega
    omega
  have h42 : cardFactors (componentIndex N q) + 42 ≤ cardFactors N := by
    by_cases hdeq17 : d = 17
    · have ha33 : a = 33 := by dsimp [d] at hdeq17; omega
      have hcf10 : 10 ≤ cardFactors (sigma 1 (q ^ a)) := (hd17_imp hdeq17).2
      omega
    · exact le_trans (by omega) (h86 hdeq17)
  have h150 : ¬ 3 ∣ N → cardFactors (componentIndex N q) + 150 ≤ cardFactors N := by
    intro hN3
    obtain ⟨_, _, _, ha145⟩ :=
      exceptional_euler_of_not_three_dvd hN ho hq hq4 ha4 ha hqm hform hl hi hN3
    omega
  have h486 : ¬ 3 ∣ N → ¬ 5 ∣ N → cardFactors (componentIndex N q) + 486 ≤ cardFactors N := by
    intro hN3 hN5
    obtain ⟨_, _, _, _, ha481⟩ :=
      exceptional_euler_of_not_three_or_five_dvd hN ho hq hq4 ha4 ha hqm hform hl hi hN3 hN5
    omega
  exact ⟨h42, h86, h150, h486⟩

end OddPerfect
