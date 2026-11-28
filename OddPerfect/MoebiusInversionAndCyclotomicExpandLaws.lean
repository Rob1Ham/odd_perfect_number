module

public import OddPerfect.CyclotomicIrreducibleAndZetaDivisorLaws
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.NormNum

/-!
# Möbius Inversion and Cyclotomic Expand Laws (`OddPerfect.MoebiusInversionAndCyclotomicExpandLaws`)

Formalizes:
1. `odd_perfect_moebius_and_squarefree_divisor_laws`: Non-squarefreeness of an odd perfect
   number `N`, vanishing `μ N = 0`, zero Möbius divisor sum `∑ d ∣ N, μ d = 0`, exact
   squarefree-divisor count `#{d ∣ N : Squarefree d} = 2 ^ ω(N)` and `∑ d ∣ N, (μ d)^2 = 2 ^ ω(N)`,
   and Möbius inversion of `σ 1` giving `∑ d ∣ N, μ d * σ 1 (N / d) = N`.
2. `cyclotomic_expand_eval_and_char_p_laws`: Integer evaluation identities for
   `Φ_{np}(x)` vs. `Φ_n(x^p)` and characteristic-`p` `ZMod p` polynomial identities
   for `Φ_{np}` in both `p ∣ n` and `p ∤ n` regimes.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta ArithmeticFunction.sigma

/-- **1. Odd Perfect Möbius and Squarefree Divisor Laws**:
For an odd perfect number `N`, `N` is not squarefree, `μ N = 0`, `∑ d ∈ N.divisors, μ d = 0`,
`∑ d ∈ N.divisors, (μ d) ^ 2 = (2 : ℤ) ^ N.primeFactors.card`,
`(N.divisors.filter Squarefree).card = 2 ^ N.primeFactors.card`, and
`∑ d ∈ N.divisors, μ d * (σ 1 (N / d) : ℤ) = (N : ℤ)`. -/
theorem odd_perfect_moebius_and_squarefree_divisor_laws {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) :
    ¬ Squarefree N ∧
    ArithmeticFunction.moebius N = 0 ∧
    (∑ d ∈ N.divisors, ArithmeticFunction.moebius d) = 0 ∧
    (∑ d ∈ N.divisors, (ArithmeticFunction.moebius d) ^ 2) =
      (2 : ℤ) ^ N.primeFactors.card ∧
    (N.divisors.filter Squarefree).card = 2 ^ N.primeFactors.card ∧
    (∑ d ∈ N.divisors, ArithmeticFunction.moebius d * (sigma 1 (N / d) : ℤ)) = (N : ℤ) := by
  have hN0 : N ≠ 0 := hN.2.ne'
  have hN1 : N ≠ 1 := by
    rintro rfl
    simp [Nat.Perfect] at hN
  have hnot_sq : ¬ Squarefree N := by
    intro hsq
    obtain ⟨q, a, m, hq, _, ha4, _, hform⟩ := euler_form ho hN
    by_cases hm1 : m = 1
    · have hNqa : N = q ^ a := by simpa [hm1] using hform
      have ha0 : a ≠ 0 := by omega
      have hcard : N.primeFactors.card = 1 := by
        rw [hNqa, Nat.primeFactors_prime_pow ha0 hq, Finset.card_singleton]
      have h6 : 6 ≤ N.primeFactors.card := six_le_distinct_prime_factor_count ho hN
      omega
    · have hm0 : m ≠ 0 := by
        intro hm0
        rw [hm0, zero_pow two_ne_zero, mul_zero] at hform
        exact hN0 hform
      set p := m.minFac
      have hp : p.Prime := Nat.minFac_prime hm1
      have hpm : p ∣ m := Nat.minFac_dvd m
      have hpp_m2 : p * p ∣ m ^ 2 := by
        rw [pow_two]
        exact mul_dvd_mul hpm hpm
      have hpp_N : p * p ∣ N := by
        rw [hform]
        exact dvd_mul_of_dvd_right hpp_m2 (q ^ a)
      exact hp.ne_one (Nat.isUnit_iff.mp (hsq p hpp_N))
  have hmu_N : μ N = 0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnot_sq
  have hsum_mu : (∑ d ∈ N.divisors, μ d) = 0 := by
    rw [← ArithmeticFunction.coe_mul_zeta_apply (R := ℤ) (f := μ) (x := N),
      ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply, ite_eq_right hN1]
  have hsq_card : (N.divisors.filter Squarefree).card = 2 ^ N.primeFactors.card := by
    have hsum1 : (N.divisors.filter Squarefree).card =
        ∑ d ∈ N.divisors with Squarefree d, (1 : ℕ) := by
      simp
    rw [hsum1, Nat.sum_divisors_filter_squarefree hN0, Nat.factors_eq]
    simp [List.toFinset_coe, Nat.toFinset_factors]
  have hsum_mu_sq : (∑ d ∈ N.divisors, (μ d) ^ 2) = (2 : ℤ) ^ N.primeFactors.card := by
    simp_rw [ArithmeticFunction.moebius_sq]
    rw [← Finset.sum_filter]
    simp [hsq_card]
  have hinv : (∑ d ∈ N.divisors, μ d * (sigma 1 (N / d) : ℤ)) = (N : ℤ) := by
    have hsigma_eq : (sigma 1 : ArithmeticFunction ℤ) =
        (ζ : ArithmeticFunction ℤ) * (ArithmeticFunction.id : ArithmeticFunction ℤ) := by
      rw [← ArithmeticFunction.zeta_mul_pow_eq_sigma, ArithmeticFunction.pow_one_eq_id,
        ArithmeticFunction.natCoe_mul]
    have hconv : μ * (sigma 1 : ArithmeticFunction ℤ) =
        (ArithmeticFunction.id : ArithmeticFunction ℤ) := by
      rw [hsigma_eq, ← mul_assoc, ArithmeticFunction.moebius_mul_coe_zeta, one_mul]
    have hN_eval := congrArg (fun f : ArithmeticFunction ℤ => f N) hconv
    rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (f := fun x y => μ x * ((sigma 1 : ArithmeticFunction ℤ) y))]
      at hN_eval
    simpa [ArithmeticFunction.natCoe_apply] using hN_eval
  exact ⟨hnot_sq, hmu_N, hsum_mu, hsum_mu_sq, hsq_card, hinv⟩

/-- **2. Cyclotomic Expand Evaluation and Characteristic-`p` Laws**:
Bundles the integer evaluation identities relating `Φ_{np}(x)` and `Φ_n(x^p)` together with
the characteristic-`p` identities over `ZMod p` in both `p ∣ n` and `¬ p ∣ n` cases. -/
theorem cyclotomic_expand_eval_and_char_p_laws :
    (∀ (p n : ℕ) (x : ℤ), p.Prime → p ∣ n →
      (Polynomial.cyclotomic (n * p) ℤ).eval x =
        (Polynomial.cyclotomic n ℤ).eval (x ^ p)) ∧
    (∀ (p n : ℕ) (x : ℤ), p.Prime → ¬ p ∣ n →
      (Polynomial.cyclotomic (n * p) ℤ).eval x * (Polynomial.cyclotomic n ℤ).eval x =
        (Polynomial.cyclotomic n ℤ).eval (x ^ p)) ∧
    (∀ (p n : ℕ), [Fact p.Prime] → p ∣ n →
      Polynomial.cyclotomic (n * p) (ZMod p) = (Polynomial.cyclotomic n (ZMod p)) ^ p) ∧
    (∀ (p n : ℕ), [Fact p.Prime] → ¬ p ∣ n →
      Polynomial.cyclotomic (n * p) (ZMod p) = (Polynomial.cyclotomic n (ZMod p)) ^ (p - 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p n x hp hdiv
    rw [← Polynomial.cyclotomic_expand_eq_cyclotomic hp hdiv ℤ, Polynomial.expand_eval]
  · intro p n x hp hndiv
    rw [← Polynomial.eval_mul, ← Polynomial.cyclotomic_expand_eq_cyclotomic_mul hp hndiv ℤ,
      Polynomial.expand_eval]
  · intro p n _ hdiv
    exact Polynomial.cyclotomic_mul_prime_dvd_eq_pow (ZMod p) hdiv
  · intro p n _ hndiv
    exact Polynomial.cyclotomic_mul_prime_eq_pow_of_not_dvd (ZMod p) hndiv

end OddPerfect
