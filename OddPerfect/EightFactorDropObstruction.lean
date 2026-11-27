module

public import OddPerfect.GlobalWave8Obstruction

/-!
# Eight-Factor Component-Index Drop Obstruction (`OddPerfect.EightFactorDropObstruction`)

Establishes the structural obstruction profile when no prime component `p ∈ N.primeFactors`
drops the prime-factor multiplicity of its component index by at least `8`
(`∀ p ∈ N.primeFactors, cardFactors N < cardFactors (componentIndex N p) + 8`), together with
unconditional sufficient conditions forcing an eight-factor component-index drop:
1. `no_eight_factor_drop_profile`: absence of an eight-factor drop forces:
   - `N.factorization p + cardFactors (sigma 1 (ordProj[p] N)) ≤ 8` for all `p ∈ N.primeFactors`,
   - `N.factorization q = 1` for the Euler prime `q`,
   - eighth-power-freeness (`∀ p, p.Prime → ¬ p ^ 8 ∣ N`),
   - bounded sextic divisor sums (`cardFactors (sigma 1 (r ^ 6)) ≤ 2` and
     `r % 7 ≠ 1 → sigma 1 (r ^ 6) % 7 = 1` whenever `N.factorization r = 6`),
   - global support density `2 * cardFactors N + 1 ≤ 8 * N.primeFactors.card`.
2. Unconditional sufficient theorems for
   `∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 8 ≤ cardFactors N`
   under `1 < N.factorization q`, an eighth power `p ^ 8 ∣ N`, or factor density
   `4 * N.primeFactors.card ≤ cardFactors N`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- Structural profile of an odd perfect number lacking an eight-factor component-index drop. -/
theorem no_eight_factor_drop_profile {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (_hev : ∀ r, r ≠ q → Even (N.factorization r))
    (hno : ∀ p ∈ N.primeFactors, cardFactors N < cardFactors (componentIndex N p) + 8) :
    (∀ p ∈ N.primeFactors, N.factorization p + cardFactors (sigma 1 (ordProj[p] N)) ≤ 8) ∧
    N.factorization q = 1 ∧
    (∀ p : ℕ, p.Prime → ¬ p ^ 8 ∣ N) ∧
    (∀ r ∈ N.primeFactors, N.factorization r = 6 →
      cardFactors (sigma 1 (r ^ 6)) ≤ 2 ∧ (r % 7 ≠ 1 → sigma 1 (r ^ 6) % 7 = 1)) ∧
    2 * cardFactors N + 1 ≤ 8 * N.primeFactors.card := by
  have hcap : ∀ p ∈ N.primeFactors,
      N.factorization p + cardFactors (sigma 1 (ordProj[p] N)) ≤ 8 := by
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
    have hq_le7 : N.factorization q ≤ 7 := by omega
    rcases (show N.factorization q = 1 ∨ N.factorization q = 5 by omega) with h1 | h5
    · exact h1
    · exfalso
      have h4 := four_le_cardFactors_sigma_fifth_pow hq_prime hq4
      have hord : ordProj[q] N = q ^ 5 := by rw [h5]
      rw [hord] at hq_cap
      omega
  have height_free : ∀ p : ℕ, p.Prime → ¬ p ^ 8 ∣ N := by
    intro p hp hd
    have hm : p ∈ N.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, (dvd_pow_self p (by decide : 8 ≠ 0)).trans hd, hN.2.ne'⟩
    have h8 : 8 ≤ N.factorization p := (hp.pow_dvd_iff_le_factorization hN.2.ne').1 hd
    have hsig_pos := hsig_pos_of p hp (by omega)
    have hp_cap := hcap p hm
    omega
  have hsextic : ∀ r ∈ N.primeFactors, N.factorization r = 6 →
      cardFactors (sigma 1 (r ^ 6)) ≤ 2 ∧ (r % 7 ≠ 1 → sigma 1 (r ^ 6) % 7 = 1) := by
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
  have hdensity : 2 * cardFactors N + 1 ≤ 8 * N.primeFactors.card := by
    calc
      2 * cardFactors N + 1
          = 1 + 2 * cardFactors N := by omega
      _ = ∑ p ∈ N.primeFactors, (N.factorization p + cardFactors (sigma 1 (ordProj[p] N))) :=
            (sum_component_factor_capture ho hN).symm
      _ ≤ ∑ _p ∈ N.primeFactors, 8 := Finset.sum_le_sum hcap
      _ = 8 * N.primeFactors.card := by simp [Nat.mul_comm]
  exact ⟨hcap, hq_one, height_free, hsextic, hdensity⟩

/-- An Euler prime exponent strictly greater than `1` forces an eight-factor component-index drop. -/
theorem exists_componentIndex_cardFactors_add_eight_le_of_euler_exp_gt_one {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r, r ≠ q → Even (N.factorization r)) (hgt : 1 < N.factorization q) :
    ∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 8 ≤ cardFactors N := by
  by_contra! hno
  obtain ⟨_, hq1, _, _, _⟩ := no_eight_factor_drop_profile ho hN hq hq4 he hev hno
  omega

/-- Any prime eighth power dividing `N` forces an eight-factor component-index drop. -/
theorem exists_componentIndex_cardFactors_add_eight_le_of_eighth_power {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) (h8 : ∃ p : ℕ, p.Prime ∧ p ^ 8 ∣ N) :
    ∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 8 ≤ cardFactors N := by
  by_contra! hno
  obtain ⟨q, hq, hq4, he, hev⟩ := euler_exponents ho hN
  obtain ⟨_, _, hfree8, _, _⟩ := no_eight_factor_drop_profile ho hN hq hq4 he hev hno
  obtain ⟨p, hp, hd⟩ := h8
  exact hfree8 p hp hd

/-- Factor density `4 * ω(N) ≤ Ω(N)` forces an eight-factor component-index drop. -/
theorem exists_componentIndex_cardFactors_add_eight_le_of_factor_density {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hdens : 4 * N.primeFactors.card ≤ cardFactors N) :
    ∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 8 ≤ cardFactors N := by
  by_contra! hno
  obtain ⟨q, hq, hq4, he, hev⟩ := euler_exponents ho hN
  obtain ⟨_, _, _, _, hbd⟩ := no_eight_factor_drop_profile ho hN hq hq4 he hev hno
  omega

end OddPerfect
