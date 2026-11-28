module

public import OddPerfect.FactorBudget

public section

namespace OddPerfect

/-- The fourteen smallest eligible primes already have limiting abundancy
strictly below two when both 3 and 5 are absent. -/
theorem fifteen_distinct_of_three_five_free {N : ℕ} (ho : Odd N) (hN : N.Perfect)
    (h3 : ¬ 3 ∣ N) (h5 : ¬ 5 ∣ N) : 15 ≤ N.primeFactors.card := by
  by_contra! hcard
  have hlen : ((Finset.Icc 7 59).filter Nat.Prime).card = 14 := by decide +kernel
  have hsmall := prod_primeAbundancyLimit_le_interval (by decide : 1 < 59) N.primeFactors
    (a := 7) (by
      intro p hp
      have hp' := Nat.prime_of_mem_primeFactors hp
      have hd := Nat.dvd_of_mem_primeFactors hp
      have hodd := (ho.of_dvd_nat hd).not_two_dvd_nat
      have hclass : ∀ x : Fin 7, x.val.Prime → ¬ 2 ∣ x.val → x.val = 3 ∨ x.val = 5 := by decide
      refine ⟨hp', ?_⟩
      by_contra! h
      rcases hclass ⟨p, h⟩ hp' hodd with h | h
      · exact h3 (h ▸ hd)
      · exact h5 (h ▸ hd)) (by omega)
  have hnum : (∏ p ∈ (Finset.Icc 7 59).filter Nat.Prime, primeAbundancyLimit p) < 2 := by
    decide +kernel
  exact (two_lt_prod_primeAbundancyLimit hN).not_ge (hsmall.trans hnum.le)

/-- These two seeds exhaust every odd perfect candidate with at most 30
prime factors counted with multiplicity. -/
theorem three_or_five_dvd_of_total_count_le_thirty {N : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hc : N.primeFactorsList.length ≤ 30) : 3 ∣ N ∨ 5 ∣ N := by
  by_contra! h
  have := fifteen_distinct_of_three_five_free ho hN h.1 h.2
  have := steuerwald_prime_factor_count ho hN
  omega

end OddPerfect
