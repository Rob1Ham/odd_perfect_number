module

public import OddPerfect.CountChain35
public import OddPerfect.HigherCountSeeds

public section

namespace OddPerfect

/-- A checked factor-chain proof of Iannucci and Sorli's 37-prime-factor bound. -/
theorem thirty_seven_le_total_prime_factor_count {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    37 ≤ N.primeFactorsList.length := by
  by_contra! hsmall
  have := Nat.odd_iff.mp (odd_total_prime_factor_count ho hN)
  have hb : N.primeFactorsList.length ≤ 35 := by omega
  by_cases h3 : 3 ∣ N
  · exact FactorBudget.exclude_3_budget_35 ⟨ho, hN, hb, five_le_distinct_prime_factor_count ho hN⟩ h3
  · by_cases h5 : 5 ∣ N
    · exact FactorBudget.exclude_5_budget_35
        ⟨ho, hN, hb, eight_le_distinct_prime_factor_count_of_three_free ho hN h3⟩ h3 h5
    · exact hsmall.not_ge (total_count_of_three_five_free ho hN h3 h5)

end OddPerfect
