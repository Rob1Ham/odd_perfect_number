module

public import OddPerfect.FormalParity
public import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Euler's form for an odd perfect number

The argument follows the prime-power divisor-sum analysis of `euler_opn_form` in
`umpolungfish/odd-perfect-numbers` (Unlicense). See `research/EULER.md` for the
pinned source. We isolate the single even factor by divisibility by 4 and use
mathlib's square criterion on the remaining cofactor.
-/

public section

namespace OddPerfect

open ArithmeticFunction

/-- For a prime congruent to one, its divisor sum is congruent to the number of terms. -/
theorem sigma_modEq_of_one {p d : ℕ} (hp : p.Prime) (hd : p ≡ 1 [MOD d]) (a : ℕ) :
    sigma 1 (p ^ a) ≡ a + 1 [MOD d] := by
  rw [sigma_one_apply_prime_pow hp]
  exact geom_modEq_of_one hd _

/-- For odd exponent, the full sum of divisors contains the factor `p + 1`. -/
theorem succ_dvd_sigma_prime_pow {p a : ℕ} (hp : p.Prime) (ha : Odd a) :
    p + 1 ∣ sigma 1 (p ^ a) := by
  obtain ⟨k, hk⟩ := ha
  rw [sigma_one_apply_prime_pow hp, show a + 1 = 2 * (k + 1) by omega]
  exact succ_dvd_sum_even _ _

/-- Euler's special prime and the parity of every other prime's exponent. -/
theorem euler_exponents {n : ℕ} (hn : Odd n) (hperf : Nat.Perfect n) :
    ∃ p ∈ n.primeFactors, p % 4 = 1 ∧ n.factorization p % 4 = 1 ∧
      ∀ q : ℕ, q ≠ p → Even (n.factorization q) := by
  have hbal : formalSigma n.primeFactors id n.factorization =
      2 * ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
    rw [← Nat.prod_primeFactors_pow_factorization hn.pos.ne']
    have hσ : sigma 1 n = 2 * n := (sigma_one_apply n).trans
      ((Nat.perfect_iff_sum_divisors_eq_two_mul hn.pos).mp hperf)
    rw [← hσ, isMultiplicative_sigma.multiplicative_factorization _ hn.pos.ne']
    exact Finset.prod_congr rfl (fun p hp =>
      (sigma_one_apply_prime_pow (Nat.prime_of_mem_primeFactors hp)).symm)
  obtain ⟨p, hp, hp4, he4, hrest⟩ := formal_euler_exponents n.primeFactors id n.factorization
    (fun _ hq => hn.of_dvd_nat (Nat.dvd_of_mem_primeFactors hq)) hbal
  refine ⟨p, hp, hp4, he4, fun q hqp => ?_⟩
  by_cases hq : q ∈ n.primeFactors
  · exact hrest q hq hqp
  · have hz : n.factorization q = 0 := Finsupp.notMem_support_iff.mp hq
    simp [hz]

/-- Euler's form, including the coprimality condition on its square factor. -/
theorem euler_form {n : ℕ} (hn : Odd n) (hperf : Nat.Perfect n) :
    ∃ q a m : ℕ, q.Prime ∧ q % 4 = 1 ∧ a % 4 = 1 ∧ ¬ q ∣ m ∧ n = q ^ a * m ^ 2 := by
  obtain ⟨q, hq, hq4, ha4, hEven⟩ := euler_exponents hn hperf
  have hprime := Nat.prime_of_mem_primeFactors hq
  have hsq : IsSquare (ordCompl[q] n) := by
    apply Nat.isSquare_iff_even_factorization.mpr
    intro r _
    rw [Nat.factorization_ordCompl]
    rcases eq_or_ne r q with rfl | h
    · simp
    · rw [Finsupp.erase_ne h]
      exact hEven r h
  obtain ⟨m, hm⟩ := hsq
  refine ⟨q, n.factorization q, m, hprime, hq4, ha4, ?_, ?_⟩
  · intro hd
    apply Nat.not_dvd_ordCompl hprime hn.pos.ne'
    rw [hm]
    exact hd.mul_right m
  · rw [pow_two, ← hm]
    exact (Nat.ordProj_mul_ordCompl_eq_self n q).symm

end OddPerfect
