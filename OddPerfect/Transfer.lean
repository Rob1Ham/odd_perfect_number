module

public import OddPerfect.Valuations

public section

namespace OddPerfect

open ArithmeticFunction

/-- Count odd primes transferred by divisors of the component sums. Each
source contributes with multiplicity, and all of its prime factors must be
included in the specified set of targets. -/
theorem sum_cardFactors_le_target_exponents {N : ℕ} (hN : N.Perfect)
    (sources targets : Finset ℕ) (f : ℕ → ℕ) (hs : sources ⊆ N.primeFactors)
    (hdiv : ∀ u ∈ sources, f u ∣ sigma 1 (u ^ N.factorization u))
    (hcover : ∀ u ∈ sources, (f u).primeFactors ⊆ targets)
    (ht : ∀ r ∈ targets, r.Prime ∧ Odd r) :
    ∑ u ∈ sources, cardFactors (f u) ≤ ∑ r ∈ targets, N.factorization r := by
  have line (u : ℕ) (hu : u ∈ sources) :
      cardFactors (f u) = ∑ r ∈ targets, (f u).factorization r := by
    rw [cardFactors_eq_sum_factorization]
    exact Finset.sum_subset (hcover u hu) (fun r _ hr => Finsupp.notMem_support_iff.mp hr)
  calc
    _ = ∑ u ∈ sources, ∑ r ∈ targets, (f u).factorization r := Finset.sum_congr rfl line
    _ = ∑ r ∈ targets, ∑ u ∈ sources, (f u).factorization r := Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro r hr
      rw [factorization_eq_sum_sigma_factorizations hN (ht r hr).2 (ht r hr).1]
      refine (Finset.sum_le_sum ?_).trans (Finset.sum_le_sum_of_subset hs)
      intro u hu
      have hpos := sigma_pos 1 (u ^ N.factorization u)
        (pow_ne_zero _ (Nat.prime_of_mem_primeFactors (hs hu)).ne_zero)
      have hne : f u ≠ 0 := by
        rintro h
        have hd := hdiv u hu
        rw [h, zero_dvd_iff] at hd
        exact hpos.ne' hd
      exact (Nat.factorization_le_iff_dvd hne hpos.ne').mpr (hdiv u hu) r

end OddPerfect
