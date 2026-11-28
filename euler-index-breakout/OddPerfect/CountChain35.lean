module

public import OddPerfect.CountChain35.Part19

public section

namespace OddPerfect.FactorBudget

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem exclude_3_budget_35 {N : ℕ} (H : Conditions N 35 5)
    (hs : 3 ∣ N) : False := by
  apply Count35.rejectS3_82 H hs (Nat.coprime_one_left N) ?_ (root_realizes N)
  have := ochem_rao_prime_factor_count H.odd H.perfect
  have hu : N.primeFactorsList.length ≤ 35 := H.count
  omega

theorem exclude_5_budget_35 {N : ℕ} (H : Conditions N 35 8) (h3 : ¬ 3 ∣ N)
    (hs : 5 ∣ N) : False := by
  apply Count35.rejectS5_19 H hs ((by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr h3) ?_ (root_realizes N)
  have := (ochem_rao_count_cases H.odd H.perfect).2 h3
  have hu : N.primeFactorsList.length ≤ 35 := H.count
  omega

end OddPerfect.FactorBudget
