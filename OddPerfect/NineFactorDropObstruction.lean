module

public import OddPerfect.GlobalWave10Obstruction
import Mathlib.Tactic.Ring

/-!
# Nine-Factor Component-Index Drop Obstruction (`OddPerfect.NineFactorDropObstruction`)

Establishes the structural obstruction profile when no prime component `p ∈ N.primeFactors`
drops the prime-factor multiplicity of its component index by at least `9`
(`∀ p ∈ N.primeFactors, cardFactors N < cardFactors (componentIndex N p) + 9`), together with
unconditional sufficient conditions forcing a nine-factor component-index drop:
1. `five_le_cardFactors_sigma_fifth_pow`: for any prime `q ≡ 1 [MOD 4]`,
   `5 ≤ cardFactors (sigma 1 (q ^ 5))`.
2. `two_le_cardFactors_sigma_eighth_pow`: for any prime `r`,
   `2 ≤ cardFactors (sigma 1 (r ^ 8))`.
3. `no_nine_factor_drop_profile`: absence of a nine-factor drop forces:
   - `N.factorization p + cardFactors (sigma 1 (ordProj[p] N)) ≤ 9` for all `p ∈ N.primeFactors`,
   - `N.factorization q = 1` for the Euler prime `q`,
   - eighth-power-freeness (`∀ p, p.Prime → ¬ p ^ 8 ∣ N`),
   - bounded sextic divisor sums (`cardFactors (sigma 1 (r ^ 6)) ≤ 3` and
     `r % 7 ≠ 1 → sigma 1 (r ^ 6) % 7 = 1` whenever `N.factorization r = 6`),
   - global support density `2 * cardFactors N + 1 ≤ 9 * N.primeFactors.card`.
4. Unconditional sufficient theorems for
   `∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 9 ≤ cardFactors N`
   under `1 < N.factorization q`, an eighth power `p ^ 8 ∣ N`, or `largeSources N q = ∅`
   (which explicitly forces `3 ∈ N.primeFactors ∧ cardFactors (componentIndex N 3) + 9 ≤ cardFactors N`).
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- For any prime `q ≡ 1 [MOD 4]`, `σ(q^5)` has at least `5` prime factors with multiplicity. -/
theorem five_le_cardFactors_sigma_fifth_pow {q : ℕ} (hq : q.Prime) (hq4 : q % 4 = 1) :
    5 ≤ cardFactors (sigma 1 (q ^ 5)) := by
  have h5 : 5 ≤ q := by
    have := hq.two_le
    omega
  have hndvd3 : ¬ 3 ∣ q := by
    intro h3
    rcases (Nat.dvd_prime hq).mp h3 with h1 | hq3
    · omega
    · omega
  rw [sigma_one_apply_prime_pow hq]
  obtain ⟨m, rfl⟩ : ∃ m, q = 4 * m + 5 := ⟨(q - 5) / 4, by omega⟩
  have hm3 : m % 3 = 0 ∨ m % 3 = 2 := by
    by_contra! hne
    have hm1 : m % 3 = 1 := by omega
    apply hndvd3
    exact ⟨4 * (m / 3) + 3, by omega⟩
  have hfac :
      (∑ i ∈ range (5 + 1), (4 * m + 5) ^ i) =
        2 * (2 * m + 3) * (16 * m ^ 2 + 36 * m + 21) * (16 * m ^ 2 + 44 * m + 31) := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
    ring
  rw [hfac]
  have h1 : 1 < 2 := by omega
  have h2 : 1 < 2 * m + 3 := by omega
  have h3 : 1 < 16 * m ^ 2 + 36 * m + 21 := by omega
  have h4 : 1 < 16 * m ^ 2 + 44 * m + 31 := by omega
  rw [cardFactors_mul (by positivity) (by positivity),
    cardFactors_mul (by positivity) (by positivity),
    cardFactors_mul (by positivity) (by positivity)]
  have hc1 : 0 < cardFactors 2 := cardFactors_pos_iff_one_lt.mpr h1
  have hc2 : 0 < cardFactors (2 * m + 3) := cardFactors_pos_iff_one_lt.mpr h2
  rcases hm3 with hm0 | hm2
  · obtain ⟨k, rfl⟩ : ∃ k, m = 3 * k := ⟨m / 3, by omega⟩
    have hsplit : 16 * (3 * k) ^ 2 + 36 * (3 * k) + 21 = 3 * (48 * k ^ 2 + 36 * k + 7) := by
      ring
    rw [hsplit, cardFactors_mul (by positivity) (by positivity)]
    have h3a : 0 < cardFactors 3 := cardFactors_pos_iff_one_lt.mpr (by omega)
    have h3b : 0 < cardFactors (48 * k ^ 2 + 36 * k + 7) :=
      cardFactors_pos_iff_one_lt.mpr (by omega)
    have hc4 : 0 < cardFactors (16 * (3 * k) ^ 2 + 44 * (3 * k) + 31) :=
      cardFactors_pos_iff_one_lt.mpr h4
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, m = 3 * k + 2 := ⟨m / 3, by omega⟩
    have hsplit :
        16 * (3 * k + 2) ^ 2 + 44 * (3 * k + 2) + 31 = 3 * (48 * k ^ 2 + 108 * k + 61) := by
      ring
    rw [hsplit, cardFactors_mul (by positivity) (by positivity)]
    have hc3 : 0 < cardFactors (16 * (3 * k + 2) ^ 2 + 36 * (3 * k + 2) + 21) :=
      cardFactors_pos_iff_one_lt.mpr h3
    have h4a : 0 < cardFactors 3 := cardFactors_pos_iff_one_lt.mpr (by omega)
    have h4b : 0 < cardFactors (48 * k ^ 2 + 108 * k + 61) :=
      cardFactors_pos_iff_one_lt.mpr (by omega)
    omega

/-- For any prime `r`, `σ(r^8)` has at least `2` prime factors with multiplicity. -/
theorem two_le_cardFactors_sigma_eighth_pow {r : ℕ} (hr : r.Prime) :
    2 ≤ cardFactors (sigma 1 (r ^ 8)) := by
  rw [sigma_one_apply_prime_pow hr]
  change 2 ≤ cardFactors (geometricBlock r (3 * 3))
  rw [geometricBlock_mul r 3 3]
  have h1 : geometricBlock r 3 = 1 + r + r ^ 2 := by
    simp only [geometricBlock, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      zero_add, pow_zero, pow_one]
  have h2 : geometricBlock (r ^ 3) 3 = 1 + r ^ 3 + r ^ 6 := by
    simp only [geometricBlock, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      zero_add, pow_zero, pow_one]
    ring
  have hr2 : 2 ≤ r := hr.two_le
  have hr2_pos : 1 ≤ r ^ 2 := Nat.one_le_pow 2 r hr.pos
  have hr3_pos : 1 ≤ r ^ 3 := Nat.one_le_pow 3 r hr.pos
  have hr6_pos : 1 ≤ r ^ 6 := Nat.one_le_pow 6 r hr.pos
  have hg1 : 1 < geometricBlock r 3 := by rw [h1]; omega
  have hg2 : 1 < geometricBlock (r ^ 3) 3 := by rw [h2]; omega
  rw [cardFactors_mul (by omega) (by omega)]
  have hc1 : 0 < cardFactors (geometricBlock r 3) := cardFactors_pos_iff_one_lt.mpr hg1
  have hc2 : 0 < cardFactors (geometricBlock (r ^ 3) 3) := cardFactors_pos_iff_one_lt.mpr hg2
  omega

/-- Structural profile of an odd perfect number lacking a nine-factor component-index drop. -/
theorem no_nine_factor_drop_profile {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (_hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hno : ∀ p ∈ N.primeFactors, cardFactors N < cardFactors (componentIndex N p) + 9) :
    (∀ p ∈ N.primeFactors, N.factorization p + cardFactors (sigma 1 (ordProj[p] N)) ≤ 9) ∧
    N.factorization q = 1 ∧
    (∀ p : ℕ, p.Prime → ¬ p ^ 8 ∣ N) ∧
    (∀ r ∈ N.primeFactors, N.factorization r = 6 →
      cardFactors (sigma 1 (r ^ 6)) ≤ 3 ∧ (r % 7 ≠ 1 → sigma 1 (r ^ 6) % 7 = 1)) ∧
    2 * cardFactors N + 1 ≤ 9 * N.primeFactors.card := by
  have hcap : ∀ p ∈ N.primeFactors,
      N.factorization p + cardFactors (sigma 1 (ordProj[p] N)) ≤ 9 := by
    intro p hp
    have hbal := cardFactors_componentIndex_add_eq hN hp
    have hlt := hno p hp
    omega
  have hsig_pos_of : ∀ p : ℕ, p.Prime → N.factorization p ≠ 0 →
      0 < cardFactors (sigma 1 (ordProj[p] N)) := by
    intro p hp hp_ne0
    have hpow_gt1 : 1 < ordProj[p] N := one_lt_pow₀ hp.one_lt hp_ne0
    have hsig_gt1 : 1 < sigma 1 (ordProj[p] N) :=
      hpow_gt1.trans (self_lt_sigma_of_one_lt hpow_gt1)
    exact cardFactors_pos_iff_one_lt.mpr hsig_gt1
  have hq_one : N.factorization q = 1 := by
    have hq_cap := hcap q hq
    have hq_prime := Nat.prime_of_mem_primeFactors hq
    have hsig_pos := hsig_pos_of q hq_prime (by omega)
    have hq_le8 : N.factorization q ≤ 8 := by omega
    rcases (show N.factorization q = 1 ∨ N.factorization q = 5 by omega) with h1 | h5
    · exact h1
    · exfalso
      have h5cf := five_le_cardFactors_sigma_fifth_pow hq_prime hq4
      have hord : ordProj[q] N = q ^ 5 := by rw [h5]
      rw [hord] at hq_cap
      omega
  have height_free : ∀ p : ℕ, p.Prime → ¬ p ^ 8 ∣ N := by
    intro p hp hd
    have hm : p ∈ N.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, (dvd_pow_self p (by decide : 8 ≠ 0)).trans hd, hN.2.ne'⟩
    have h8 : 8 ≤ N.factorization p := (hp.pow_dvd_iff_le_factorization hN.2.ne').1 hd
    have hp_cap := hcap p hm
    rcases (show N.factorization p = 8 ∨ 9 ≤ N.factorization p by omega) with hp8 | hp9
    · have h2cf := two_le_cardFactors_sigma_eighth_pow hp
      have hord : ordProj[p] N = p ^ 8 := by rw [hp8]
      rw [hord] at hp_cap
      omega
    · have hsig_pos := hsig_pos_of p hp (by omega)
      omega
  have hsextic : ∀ r ∈ N.primeFactors, N.factorization r = 6 →
      cardFactors (sigma 1 (r ^ 6)) ≤ 3 ∧ (r % 7 ≠ 1 → sigma 1 (r ^ 6) % 7 = 1) := by
    intro r hr hr6
    have hr_prime := Nat.prime_of_mem_primeFactors hr
    have hr_cap := hcap r hr
    have hord : ordProj[r] N = r ^ 6 := by rw [hr6]
    rw [hord, hr6] at hr_cap
    refine ⟨by omega, ?_⟩
    intro hr7
    by_cases hr_eq7 : r = 7
    · subst hr_eq7
      exact sigma_prime_pow_mod_self hr_prime 6
    · have hndvd7 : ¬ 7 ∣ r := by
        intro hdvd
        rcases (Nat.dvd_prime hr_prime).mp hdvd with h1 | h7
        · norm_num at h1
        · exact hr_eq7 h7.symm
      have hr0 : r % 7 ≠ 0 := fun h0 => hndvd7 (Nat.dvd_of_mod_eq_zero h0)
      have hmod_cases : r % 7 = 2 ∨ r % 7 = 3 ∨ r % 7 = 4 ∨ r % 7 = 5 ∨ r % 7 = 6 := by omega
      rw [sigma_one_apply_prime_pow hr_prime]
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
        pow_zero, pow_one]
      have hrm : r ≡ r % 7 [MOD 7] := (Nat.mod_modEq r 7).symm
      have hsum :
          (1 + r + r ^ 2 + r ^ 3 + r ^ 4 + r ^ 5 + r ^ 6) ≡
            (1 + (r % 7) + (r % 7) ^ 2 + (r % 7) ^ 3 + (r % 7) ^ 4 + (r % 7) ^ 5 + (r % 7) ^ 6)
              [MOD 7] :=
        ((((((Nat.ModEq.refl 1).add hrm).add (hrm.pow 2)).add (hrm.pow 3)).add
          (hrm.pow 4)).add (hrm.pow 5)).add (hrm.pow 6)
      change (1 + r + r ^ 2 + r ^ 3 + r ^ 4 + r ^ 5 + r ^ 6) % 7 =
        (1 + (r % 7) + (r % 7) ^ 2 + (r % 7) ^ 3 + (r % 7) ^ 4 + (r % 7) ^ 5 +
          (r % 7) ^ 6) % 7 at hsum
      rw [hsum]
      rcases hmod_cases with hm | hm | hm | hm | hm <;> rw [hm] <;> decide
  have hdensity : 2 * cardFactors N + 1 ≤ 9 * N.primeFactors.card := by
    calc
      2 * cardFactors N + 1
          = 1 + 2 * cardFactors N := by omega
      _ = ∑ p ∈ N.primeFactors, (N.factorization p + cardFactors (sigma 1 (ordProj[p] N))) :=
            (sum_component_factor_capture ho hN).symm
      _ ≤ ∑ _p ∈ N.primeFactors, 9 := Finset.sum_le_sum hcap
      _ = 9 * N.primeFactors.card := by simp [Nat.mul_comm]
  exact ⟨hcap, hq_one, height_free, hsextic, hdensity⟩

/-- An Euler prime exponent strictly greater than `1` forces a nine-factor component-index drop. -/
theorem exists_componentIndex_cardFactors_add_nine_le_of_euler_exp_gt_one {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) (hgt : 1 < N.factorization q) :
    ∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 9 ≤ cardFactors N := by
  by_contra! hno
  obtain ⟨_, hq1, _, _, _⟩ := no_nine_factor_drop_profile ho hN hq hq4 he hev hno
  omega

/-- Any prime eighth power dividing `N` forces a nine-factor component-index drop. -/
theorem exists_componentIndex_cardFactors_add_nine_le_of_eighth_power {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) (h8 : ∃ p : ℕ, p.Prime ∧ p ^ 8 ∣ N) :
    ∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 9 ≤ cardFactors N := by
  by_contra! hno
  obtain ⟨q, hq, hq4, he, hev⟩ := euler_exponents ho hN
  obtain ⟨_, _, hfree8, _, _⟩ := no_nine_factor_drop_profile ho hN hq hq4 he hev hno
  obtain ⟨p, hp, hd⟩ := h8
  exact hfree8 p hp hd

/-- If `largeSources N q = ∅`, then `3 ∈ N.primeFactors` and the component index at `3` yields
at least a `9`-factor drop: `cardFactors (componentIndex N 3) + 9 ≤ cardFactors N`. -/
theorem exists_nine_drop_at_three_of_largeSources_empty {N q : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) (hempty : largeSources N q = ∅) :
    3 ∈ N.primeFactors ∧ cardFactors (componentIndex N 3) + 9 ≤ cardFactors N := by
  have h3_8 := eight_le_three_exponent_of_largeSources_empty ho hN hq hq4 he hev hempty
  have h3_mem : 3 ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨by decide, Nat.dvd_of_factorization_pos (by omega), hN.2.ne'⟩
  have hbal := cardFactors_componentIndex_add_eq hN h3_mem
  refine ⟨h3_mem, ?_⟩
  rcases (show N.factorization 3 = 8 ∨ 9 ≤ N.factorization 3 by omega) with h8 | h9
  · have h2 := two_le_cardFactors_sigma_eighth_pow (by decide : Nat.Prime 3)
    have hord : ordProj[3] N = 3 ^ 8 := by rw [h8]
    rw [hord] at hbal
    omega
  · have hpow_gt1 : 1 < ordProj[3] N := one_lt_pow₀ (by decide) (by omega)
    have hsig_gt1 : 1 < sigma 1 (ordProj[3] N) :=
      hpow_gt1.trans (self_lt_sigma_of_one_lt hpow_gt1)
    have hsig_pos : 0 < cardFactors (sigma 1 (ordProj[3] N)) :=
      cardFactors_pos_iff_one_lt.mpr hsig_gt1
    omega

end OddPerfect
