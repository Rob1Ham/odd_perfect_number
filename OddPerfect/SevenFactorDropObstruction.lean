module

public import OddPerfect.GlobalWave6Obstruction
import Mathlib.Tactic.Ring

/-!
# Seven-Factor Component-Index Drop Obstruction (`OddPerfect.SevenFactorDropObstruction`)

Establishes the structural obstruction profile when no prime component `p ∈ N.primeFactors`
drops the prime-factor multiplicity of its component index by at least `7`
(`∀ p ∈ N.primeFactors, cardFactors N < cardFactors (componentIndex N p) + 7`), together with
unconditional sufficient conditions forcing a seven-factor component-index drop:
1. `four_le_cardFactors_sigma_fifth_pow`: for any prime `q ≡ 1 [MOD 4]`,
   `4 ≤ cardFactors (sigma 1 (q ^ 5))`.
2. `no_seven_factor_drop_profile`: absence of a seven-factor drop forces:
   - `N.factorization p + cardFactors (sigma 1 (ordProj[p] N)) ≤ 7` for all `p ∈ N.primeFactors`,
   - `N.factorization q = 1` for the Euler prime `q`,
   - eighth-power-freeness (`∀ p, p.Prime → ¬ p ^ 8 ∣ N`),
   - prime sextic divisor sums (`(sigma 1 (r ^ 6)).Prime ∧ r % 7 ≠ 1` whenever
     `N.factorization r = 6`),
   - global support density `2 * cardFactors N + 1 ≤ 7 * N.primeFactors.card`.
3. Unconditional sufficient theorems for `∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 7 ≤ cardFactors N`
   under `1 < N.factorization q`, an eighth power `p ^ 8 ∣ N`, factor density
   `7 * N.primeFactors.card ≤ 2 * cardFactors N`, or a composite/7-divisible sextic divisor sum.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- For any prime `q ≡ 1 [MOD 4]`, `σ(q^5)` has at least `4` prime factors with multiplicity. -/
theorem four_le_cardFactors_sigma_fifth_pow {q : ℕ} (hq : q.Prime) (hq4 : q % 4 = 1) :
    4 ≤ cardFactors (sigma 1 (q ^ 5)) := by
  have h5 : 5 ≤ q := by
    have := hq.two_le
    omega
  rw [sigma_one_apply_prime_pow hq]
  obtain ⟨m, rfl⟩ : ∃ m, q = 4 * m + 5 := ⟨(q - 5) / 4, by omega⟩
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
  have hc3 : 0 < cardFactors (16 * m ^ 2 + 36 * m + 21) := cardFactors_pos_iff_one_lt.mpr h3
  have hc4 : 0 < cardFactors (16 * m ^ 2 + 44 * m + 31) := cardFactors_pos_iff_one_lt.mpr h4
  omega

/-- Structural profile of an odd perfect number lacking a seven-factor component-index drop. -/
theorem no_seven_factor_drop_profile {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (_hev : ∀ r, r ≠ q → Even (N.factorization r))
    (hno : ∀ p ∈ N.primeFactors, cardFactors N < cardFactors (componentIndex N p) + 7) :
    (∀ p ∈ N.primeFactors, N.factorization p + cardFactors (sigma 1 (ordProj[p] N)) ≤ 7) ∧
    N.factorization q = 1 ∧
    (∀ p : ℕ, p.Prime → ¬ p ^ 8 ∣ N) ∧
    (∀ r ∈ N.primeFactors, N.factorization r = 6 → (sigma 1 (r ^ 6)).Prime ∧ r % 7 ≠ 1) ∧
    2 * cardFactors N + 1 ≤ 7 * N.primeFactors.card := by
  have hcap : ∀ p ∈ N.primeFactors,
      N.factorization p + cardFactors (sigma 1 (ordProj[p] N)) ≤ 7 := by
    intro p hp
    have hbal := cardFactors_componentIndex_add_eq hN hp
    have hlt := hno p hp
    omega
  have hq_one : N.factorization q = 1 := by
    have hq_cap := hcap q hq
    have hq_prime := Nat.prime_of_mem_primeFactors hq
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
    have hp_cap := hcap p hm
    omega
  have hsextic : ∀ r ∈ N.primeFactors, N.factorization r = 6 →
      (sigma 1 (r ^ 6)).Prime ∧ r % 7 ≠ 1 := by
    intro r hr hr6
    have hr_prime := Nat.prime_of_mem_primeFactors hr
    have hr_cap := hcap r hr
    have hord : ordProj[r] N = r ^ 6 := by rw [hr6]
    rw [hord, hr6] at hr_cap
    have hpow_gt1 : 1 < r ^ 6 := one_lt_pow₀ hr_prime.one_lt (by decide : 6 ≠ 0)
    have hsig_gt1 : 1 < sigma 1 (r ^ 6) := hpow_gt1.trans (self_lt_sigma_of_one_lt hpow_gt1)
    have hsig_pos : 0 < cardFactors (sigma 1 (r ^ 6)) :=
      cardFactors_pos_iff_one_lt.mpr hsig_gt1
    have hsig_one : cardFactors (sigma 1 (r ^ 6)) = 1 := by omega
    have hsig_prime : (sigma 1 (r ^ 6)).Prime := cardFactors_eq_one_iff_prime.mp hsig_one
    refine ⟨hsig_prime, ?_⟩
    intro hr7
    have hmod : sigma 1 (r ^ 6) ≡ 6 + 1 [MOD 7] :=
      sigma_modEq_of_one hr_prime (show r ≡ 1 [MOD 7] from hr7) 6
    have h7_dvd : 7 ∣ sigma 1 (r ^ 6) :=
      Nat.dvd_of_mod_eq_zero (by change sigma 1 (r ^ 6) % 7 = (6 + 1) % 7 at hmod; omega)
    have hsig_eq7 : sigma 1 (r ^ 6) = 7 :=
      (((Nat.dvd_prime hsig_prime).mp h7_dvd).resolve_left (by decide)).symm
    have hr2 : 2 ≤ r := hr_prime.two_le
    have h64 : 64 ≤ r ^ 6 := by
      calc
        64 = 2 ^ 6 := by decide
        _ ≤ r ^ 6 := Nat.pow_le_pow_left hr2 6
    have hlt : r ^ 6 < sigma 1 (r ^ 6) := self_lt_sigma_of_one_lt hpow_gt1
    omega
  have hdensity : 2 * cardFactors N + 1 ≤ 7 * N.primeFactors.card := by
    calc
      2 * cardFactors N + 1
          = 1 + 2 * cardFactors N := by omega
      _ = ∑ p ∈ N.primeFactors, (N.factorization p + cardFactors (sigma 1 (ordProj[p] N))) :=
            (sum_component_factor_capture ho hN).symm
      _ ≤ ∑ _p ∈ N.primeFactors, 7 := Finset.sum_le_sum hcap
      _ = 7 * N.primeFactors.card := by simp [Nat.mul_comm]
  exact ⟨hcap, hq_one, height_free, hsextic, hdensity⟩

/-- An Euler prime exponent strictly greater than `1` forces a seven-factor component-index drop. -/
theorem exists_componentIndex_cardFactors_add_seven_le_of_euler_exp_gt_one {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r, r ≠ q → Even (N.factorization r)) (hgt : 1 < N.factorization q) :
    ∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 7 ≤ cardFactors N := by
  by_contra! hno
  obtain ⟨_, hq1, _, _, _⟩ := no_seven_factor_drop_profile ho hN hq hq4 he hev hno
  omega

/-- Any prime eighth power dividing `N` forces a seven-factor component-index drop. -/
theorem exists_componentIndex_cardFactors_add_seven_le_of_eighth_power {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) (h8 : ∃ p : ℕ, p.Prime ∧ p ^ 8 ∣ N) :
    ∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 7 ≤ cardFactors N := by
  by_contra! hno
  obtain ⟨q, hq, hq4, he, hev⟩ := euler_exponents ho hN
  obtain ⟨_, _, hfree8, _, _⟩ := no_seven_factor_drop_profile ho hN hq hq4 he hev hno
  obtain ⟨p, hp, hd⟩ := h8
  exact hfree8 p hp hd

/-- Factor density `7 * ω(N) ≤ 2 * Ω(N)` forces a seven-factor component-index drop. -/
theorem exists_componentIndex_cardFactors_add_seven_le_of_factor_density {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hdens : 7 * N.primeFactors.card ≤ 2 * cardFactors N) :
    ∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 7 ≤ cardFactors N := by
  by_contra! hno
  obtain ⟨q, hq, hq4, he, hev⟩ := euler_exponents ho hN
  obtain ⟨_, _, _, _, hbd⟩ := no_seven_factor_drop_profile ho hN hq hq4 he hev hno
  omega

/-- A sextic prime power whose divisor sum is composite or `r ≡ 1 [MOD 7]` forces a seven-factor
component-index drop. -/
theorem exists_componentIndex_cardFactors_add_seven_le_of_sextic_composite {N : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hsex : ∃ r ∈ N.primeFactors, N.factorization r = 6 ∧ (¬ (sigma 1 (r ^ 6)).Prime ∨ r % 7 = 1)) :
    ∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 7 ≤ cardFactors N := by
  by_contra! hno
  obtain ⟨q, hq, hq4, he, hev⟩ := euler_exponents ho hN
  obtain ⟨_, _, _, hsextic, _⟩ := no_seven_factor_drop_profile ho hN hq hq4 he hev hno
  obtain ⟨r, hr, hr6, hbad⟩ := hsex
  obtain ⟨hprime, hmod7⟩ := hsextic r hr hr6
  rcases hbad with hnotp | hr7
  · exact hnotp hprime
  · exact hmod7 hr7

end OddPerfect
