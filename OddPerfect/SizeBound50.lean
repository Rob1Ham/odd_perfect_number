module

public import OddPerfect.CountBound37
public import OddPerfect.SizeChain50
public import OddPerfect.SizeSeeds

public section

namespace OddPerfect

/-- The least-prime cases 3, 5 and 7 have finite size certificates. Outside
those three cases every prime is at least 11 and there are at least 69 factors. -/
theorem ten_pow_fifty_lt_of_odd_perfect {N : ℕ} (ho : Odd N) (hN : N.Perfect) : 10^50 < N := by
  by_contra! hx
  have hlow := thirty_seven_le_total_prime_factor_count ho hN
  by_cases h3 : 3 ∣ N
  · exact FactorBudget.exclude_3_size_50 ho hN (five_le_distinct_prime_factor_count ho hN) hx hlow h3
  by_cases h5 : 5 ∣ N
  · exact FactorBudget.exclude_5_size_50 ho hN (eight_le_distinct_prime_factor_count_of_three_free ho hN h3)
      hx hlow h3 h5
  by_cases h7 : 7 ∣ N
  · exact FactorBudget.exclude_7_size_50 ho hN (fifteen_distinct_of_three_five_free ho hN h3 h5)
      hx hlow h3 h5 h7
  exact (by decide : ¬ (10:ℕ)^106 < 10^50) ((size_of_three_five_seven_free ho hN h3 h5 h7).trans_le hx)

end OddPerfect
