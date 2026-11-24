module

public import OddPerfect.CountChain27
public import OddPerfect.CountBound25

public section

namespace OddPerfect

/-- A checked factor-chain proof of Sayers's 29-prime-factor lower bound. -/
theorem twenty_nine_le_total_prime_factor_count {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    29 ≤ N.primeFactorsList.length :=
  total_count_of_two_seed_exclusions (B := 27) (by decide) (by decide)
    FactorBudget.exclude_3_budget_27 FactorBudget.exclude_5_budget_27 ho hN

end OddPerfect
