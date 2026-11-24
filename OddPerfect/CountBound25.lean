module

public import OddPerfect.CountChain23
public import OddPerfect.CountSeeds

public section

namespace OddPerfect

/-- Glue the two seed certificates whenever the seed-free support bound
already exceeds the hypothesized budget. -/
theorem total_count_of_two_seed_exclusions {B : ℕ} (hB : B ≤ 30) (hoddB : Odd B)
    (hthree : ∀ {N : ℕ}, FactorBudget.Conditions N B 5 → 3 ∣ N → False)
    (hfive : ∀ {N : ℕ}, FactorBudget.Conditions N B 8 → ¬ 3 ∣ N → 5 ∣ N → False)
    {N : ℕ} (ho : Odd N) (hN : N.Perfect) : B+2 ≤ N.primeFactorsList.length := by
  by_contra! hc
  have := Nat.odd_iff.mp (odd_total_prime_factor_count ho hN)
  have := Nat.odd_iff.mp hoddB
  have hb : N.primeFactorsList.length ≤ B := by omega
  by_cases h3 : 3 ∣ N
  · exact hthree ⟨ho, hN, hb, five_le_distinct_prime_factor_count ho hN⟩ h3
  · have h5 := (three_or_five_dvd_of_total_count_le_thirty ho hN (by omega)).resolve_left h3
    exact hfive ⟨ho, hN, hb, eight_le_distinct_prime_factor_count_of_three_free ho hN h3⟩ h3 h5

/-- The budget-23 certificates raise the unconditional bound to 25. -/
theorem twenty_five_le_total_prime_factor_count {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    25 ≤ N.primeFactorsList.length :=
  total_count_of_two_seed_exclusions (B := 23) (by decide) (by decide)
    FactorBudget.exclude_3_budget_23 (fun H _ => FactorBudget.exclude_5_budget_23 H) ho hN

end OddPerfect
