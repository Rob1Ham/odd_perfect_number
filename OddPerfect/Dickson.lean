module

public import OddPerfect.SpoofFiniteness
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- Apply the formal factor bound to the true prime factorization by
multiplicativity of the divisor sum. -/
theorem component_le_of_bounded_prime_count {N k : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hk : N.primeFactors.card ≤ k) :
    ∀ p ∈ N.primeFactors, p ^ (N.factorization p + 1) ≤ productLabelBound (2*k) (2*k) 1 := by
  apply formal_component_le_of_bounded_factor_count N.primeFactors id N.factorization hk
    (fun p hp => ⟨(Nat.prime_of_mem_primeFactors hp).one_lt, ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)⟩)
    (fun p hp => Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp))
  have heq : formalSigma N.primeFactors id N.factorization = sigma 1 N := by
    trans ∏ p ∈ N.primeFactors, sigma 1 (p ^ N.factorization p)
    · exact prod_congr rfl (fun p hp => (sigma_one_apply_prime_pow (Nat.prime_of_mem_primeFactors hp)).symm)
    · exact (isMultiplicative_sigma.multiplicative_factorization _ hN.2.ne').symm
  simp only [heq, sigma_one_apply, id_eq, ← Nat.prod_primeFactors_pow_factorization hN.2.ne']
  exact (Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN

/-- An explicit uniform upper bound for fixed support cardinality. -/
theorem le_of_bounded_prime_count {N k : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hk : N.primeFactors.card ≤ k) :
    N ≤ (max 1 (productLabelBound (2*k) (2*k) 1)) ^ k := by
  let B := max 1 (productLabelBound (2*k) (2*k) 1)
  have hcap (p : ℕ) (hp : p ∈ N.primeFactors) : p ^ N.factorization p ≤ B :=
    (Nat.pow_le_pow_right (Nat.prime_of_mem_primeFactors hp).pos (Nat.le_succ _)).trans
      ((component_le_of_bounded_prime_count ho hN hk p hp).trans (le_max_right _ _))
  rw [Nat.prod_primeFactors_pow_factorization hN.2.ne']
  have h := Finset.prod_le_prod₀ (fun p (_ : p ∈ N.primeFactors) => Nat.zero_le (p ^ N.factorization p)) hcap
  rw [prod_const] at h
  exact h.trans (Nat.pow_le_pow_right (le_max_left 1 _) hk)

/-- Dickson's 1913 finiteness theorem for odd perfect numbers. -/
theorem dickson_finite (k : ℕ) :
    Set.Finite {N : ℕ | Odd N ∧ N.Perfect ∧ N.primeFactors.card ≤ k} := by
  apply (Set.finite_le_nat ((max 1 (productLabelBound (2*k) (2*k) 1)) ^ k)).subset
  rintro N ⟨ho, hN, hk⟩
  exact le_of_bounded_prime_count ho hN hk

end OddPerfect
