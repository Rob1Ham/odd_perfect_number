module

public import OddPerfect.CountChain45.Part159

public section

namespace OddPerfect.FactorBudget

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem exclude_3_budget_45 {N : ℕ} (H : Conditions N 45 5)
    (hs : 3 ∣ N) : False := by
  apply Count45.rejectS3_641 H hs (Nat.coprime_one_left N) ?_ (root_realizes N)
  have := ochem_rao_prime_factor_count H.odd H.perfect
  have hu : N.primeFactorsList.length ≤ 45 := H.count
  omega

theorem exclude_5_budget_45 {N : ℕ} (H : Conditions N 45 8) (h3 : ¬ 3 ∣ N)
    (hs : 5 ∣ N) : False := by
  apply Count45.rejectS5_148 H hs ((by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr h3) ?_ (root_realizes N)
  have := (ochem_rao_count_cases H.odd H.perfect).2 h3
  have hu : N.primeFactorsList.length ≤ 45 := H.count
  omega

theorem exclude_7_budget_45 {N : ℕ} (H : Conditions N 45 15) (h3 : ¬ 3 ∣ N) (h5 : ¬ 5 ∣ N)
    (hs : 7 ∣ N) : False := by
  apply Count45.rejectS7_9 H hs (((by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr h3).mul_left ((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr h5)) ?_ (root_realizes N)
  have := (ochem_rao_count_cases H.odd H.perfect).2 h3
  have hu : N.primeFactorsList.length ≤ 45 := H.count
  omega

end OddPerfect.FactorBudget
