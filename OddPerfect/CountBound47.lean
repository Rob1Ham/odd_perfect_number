module

public import OddPerfect.CountChain45
public import OddPerfect.HigherCountSeeds

public section

namespace OddPerfect

/-- A factor-chain proof of Hare's bound on the number of prime factors with multiplicity. -/
theorem forty_seven_le_total_prime_factor_count {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    47 ≤ N.primeFactorsList.length := by
  by_contra! hsmall
  have := Nat.odd_iff.mp (odd_total_prime_factor_count ho hN)
  have hb : N.primeFactorsList.length ≤ 45 := by omega
  by_cases h3 : 3 ∣ N
  · exact FactorBudget.exclude_3_budget_45 ⟨ho, hN, hb, five_le_distinct_prime_factor_count ho hN⟩ h3
  by_cases h5 : 5 ∣ N
  · exact FactorBudget.exclude_5_budget_45
      ⟨ho, hN, hb, eight_le_distinct_prime_factor_count_of_three_free ho hN h3⟩ h3 h5
  by_cases h7 : 7 ∣ N
  · exact FactorBudget.exclude_7_budget_45
      ⟨ho, hN, hb, fifteen_distinct_of_three_five_free ho hN h3 h5⟩ h3 h5 h7
  have := (counts_of_three_five_seven_free ho hN h3 h5 h7).2
  omega

end OddPerfect
