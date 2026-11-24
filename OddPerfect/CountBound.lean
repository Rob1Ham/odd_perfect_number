module

public import OddPerfect.CountChain19
public import OddPerfect.CountSeeds

public section

namespace OddPerfect

/-- Every odd perfect number has at least 21 prime factors counted with
multiplicity. Both small-prime seeds are discharged by exact-exponent chains. -/
theorem twenty_one_le_total_prime_factor_count {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    21 ≤ N.primeFactorsList.length := by
  by_contra! hc
  have hodd := Nat.odd_iff.mp (odd_total_prime_factor_count ho hN)
  have hb : N.primeFactorsList.length ≤ 19 := by omega
  by_cases h3 : 3 ∣ N
  · exact FactorBudget.exclude_3_budget_19
      ⟨ho, hN, hb, five_le_distinct_prime_factor_count ho hN⟩ h3
  · have h5 := (three_or_five_dvd_of_total_count_le_thirty ho hN (by omega)).resolve_left h3
    exact FactorBudget.exclude_5_budget_19
      ⟨ho, hN, hb, eight_le_distinct_prime_factor_count_of_three_free ho hN h3⟩ h5

end OddPerfect
