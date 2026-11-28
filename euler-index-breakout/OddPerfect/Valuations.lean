module

public import OddPerfect.Forcing

public section

namespace OddPerfect

open ArithmeticFunction

/-- In a perfect number the exponent of each odd prime equals the total
exponent it receives from the divisor sums of the exact prime powers. -/
theorem factorization_eq_sum_sigma_factorizations {N r : ℕ} (hN : N.Perfect) (hr : Odd r)
    (hprime : r.Prime) :
    N.factorization r = ∑ p ∈ N.primeFactors, (sigma 1 (p ^ N.factorization p)).factorization r := by
  have hprod : (∏ p ∈ N.primeFactors, sigma 1 (p ^ N.factorization p)) = 2 * N := by
    trans sigma 1 N
    · exact (isMultiplicative_sigma.multiplicative_factorization _ hN.2.ne').symm
    rw [sigma_one_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN
  have h := Nat.factorization_prod_apply (p := r) (S := N.primeFactors)
    (g := fun p => sigma 1 (p ^ N.factorization p))
    (fun p hp => (sigma_pos _ _ (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)).ne')
  have htwo : ¬ r ∣ 2 := by
    intro h
    have heq := ((Nat.dvd_prime Nat.prime_two).mp h).resolve_left hprime.ne_one
    exact hr.not_two_dvd_nat (heq ▸ dvd_rfl)
  simpa only [hprod, Nat.factorization_mul (by decide : 2 ≠ 0) hN.2.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd htwo, zero_add] using h

/-- Distinct components contributing an odd prime consume at least one copy
of that prime each. This bound holds for any chosen subset of components. -/
theorem card_le_factorization_of_sigma_sources {N r : ℕ} (hN : N.Perfect) (hr : Odd r)
    (hprime : r.Prime) (sources : Finset ℕ) (hsub : sources ⊆ N.primeFactors)
    (hsrc : ∀ p ∈ sources, r ∣ sigma 1 (p ^ N.factorization p)) :
    sources.card ≤ N.factorization r := by
  rw [factorization_eq_sum_sigma_factorizations hN hr hprime]
  calc
    _ = ∑ _p ∈ sources, (1 : ℕ) := by simp
    _ ≤ ∑ p ∈ sources, (sigma 1 (p ^ N.factorization p)).factorization r := by
      apply Finset.sum_le_sum
      intro p hp
      exact (hprime.dvd_iff_one_le_factorization
        (sigma_pos _ _ (pow_ne_zero _ (Nat.prime_of_mem_primeFactors (hsub hp)).ne_zero)).ne').mp
        (hsrc p hp)
    _ ≤ _ := Finset.sum_le_sum_of_subset hsub

end OddPerfect
