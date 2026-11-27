module

public import OddPerfect.GlobalWave4Obstruction
public import OddPerfect.Thirteen
import Mathlib.Algebra.BigOperators.ModEq

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- A complete block of six terms forces 3 from any prime component. For the
base 3 itself, membership in the support already gives the conclusion. -/
theorem three_dvd_of_six_dvd_component_length {N p : ℕ} (hN : N.Perfect)
    (hp : p ∈ N.primeFactors) (hlen : 6 ∣ N.factorization p + 1) : 3 ∣ N := by
  have hpd := Nat.dvd_of_mem_primeFactors hp
  by_cases h3p : 3 ∣ p
  · exact h3p.trans hpd
  have hres : p % 3 = 1 ∨ p % 3 = 2 := by omega
  have block : 3 ∣ ∑ i ∈ range 6, p ^ i := by
    have hsum (a : ℕ) (ha : p ≡ a [MOD 3]) :
        (∑ i ∈ range 6, p ^ i) ≡ ∑ i ∈ range 6, a ^ i [MOD 3] :=
      Nat.ModEq.sum fun i _ => ha.pow i
    apply Nat.dvd_of_mod_eq_zero
    rcases hres with h | h
    · exact (hsum 1 h).trans (by decide : (∑ i ∈ range 6, 1 ^ i) ≡ 0 [MOD 3])
    · exact (hsum 2 h).trans (by decide : (∑ i ∈ range 6, 2 ^ i) ≡ 0 [MOD 3])
  have hprime := Nat.prime_of_mem_primeFactors hp
  apply dvd_perfect_of_exact_prime_pow hN hprime (Nat.ordProj_dvd N p)
    ((hprime.pow_dvd_iff_le_factorization hN.2.ne').not.mpr (by omega))
    (by decide : Nat.Prime 3) (by decide : Odd 3)
  rw [← sigma_one_apply, sigma_one_apply_prime_pow hprime,
    dvd_geom_sum_iff_remainder block, Nat.mod_eq_zero_of_dvd hlen]
  simp

/-- The small-factor sieve excludes 3 from a sixth-power-free odd perfect candidate. -/
theorem sixth_power_free_three_not_dvd {N : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) : ¬ 3 ∣ N := by
  intro hd
  obtain ⟨p, hp, hpow⟩ :=
    prime_sixth_power_dvd_of_small_factor ho hN (by decide : 2 ≤ 3) hd (by decide)
  exact hfree p hp hpow

/-- In the sixth-power-free case the Euler exponent is one. The sieve excludes
3, while exponent five would force a component of length six. -/
theorem sixth_power_free_euler_exponent_one {N q : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (he : N.factorization q % 4 = 1)
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) : N.factorization q = 1 := by
  have hprime := Nat.prime_of_mem_primeFactors hq
  have hsmall : N.factorization q < 6 := by
    by_contra! hge
    exact hfree q hprime ((hprime.pow_dvd_iff_le_factorization hN.2.ne').2 hge)
  have h3 := sixth_power_free_three_not_dvd ho hN hfree
  rcases (show N.factorization q = 1 ∨ N.factorization q = 5 by omega) with h1 | h5
  · exact h1
  · exact (h3 (three_dvd_of_six_dvd_component_length hN hq (h5 ▸ by decide))).elim

/-- A sixth-power-free candidate must have at least 92 exact-square source
primes congruent to one modulo five, strictly more than a sixth of its entire
prime support. This rules out both the zero-exception and one-sixth-exception
slope hypotheses on this branch. -/
theorem sixth_power_free_square_sources_one_mod_five {N : ℕ} (ho : Odd N)
    (hN : N.Perfect) (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    92 ≤ ((squareSources N).filter (· % 5 = 1)).card ∧
      N.primeFactors.card < 6 * ((squareSources N).filter (· % 5 = 1)).card ∧
      5 * N.primeFactors.card ≤ 24 * ((squareSources N).filter (· % 5 = 1)).card + 28 := by
  obtain ⟨q, hq, hq4, he, hev⟩ := euler_exponents ho hN
  have h3 := sixth_power_free_three_not_dvd ho hN hfree
  have h5 := sixth_power_free_five_not_dvd ho hN hfree
  have h1 := sixth_power_free_euler_exponent_one ho hN hq he hfree
  obtain ⟨hfour, h147, _⟩ :=
    three_free_sixthPowerFree_forces_147_largeSources ho hN hq hq4 he hev h3 hfree
  obtain ⟨hquartic, hsquare, hcard⟩ :=
    three_five_free_quartic_source_bounds ho hN hq hq4 he hev h3 h5 hfour
  omega

end OddPerfect
