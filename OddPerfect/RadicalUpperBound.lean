module

public import OddPerfect.SpoofFiniteness
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Ring

public section

namespace OddPerfect
open Finset ArithmeticFunction

/-- An explicit upper bound on N times the square of its radical. The
right hand side only uses the number of distinct prime factors. -/
theorem radical_squared_size_upper {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    let k := N.primeFactors.card
    (4*k)*(N.primeFactors.prod id)^2*N ≤ (4*k)^(4^k) := by
  have hf : formalSigma N.primeFactors id N.factorization = sigma 1 N := by
    trans ∏ p ∈ N.primeFactors, sigma 1 (p^N.factorization p)
    · exact prod_congr rfl (fun p hp => (sigma_one_apply_prime_pow (Nat.prime_of_mem_primeFactors hp)).symm)
    · exact (isMultiplicative_sigma.multiplicative_factorization _ hN.2.ne').symm
  have hbalance : formalSigma N.primeFactors id N.factorization =
       2*∏ p ∈ N.primeFactors, id p^N.factorization p := by
    rw [hf,sigma_one_apply]
    simpa only [id_eq,← Nat.prod_primeFactors_pow_factorization hN.2.ne'] using
      (Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN
  have h := formal_product_bound_of_bounded_factor_count N.primeFactors id N.factorization
    (k:=N.primeFactors.card) le_rfl
    (fun p hp => ⟨(Nat.prime_of_mem_primeFactors hp).one_lt,ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)⟩)
    (fun p hp => Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)) hbalance
  simp only [id_eq,pow_add,prod_mul_distrib,Finset.prod_pow,
    ← Nat.prod_primeFactors_pow_factorization hN.2.ne'] at h
  simpa only [mul_assoc,mul_left_comm,mul_comm,id_eq] using h

end OddPerfect
