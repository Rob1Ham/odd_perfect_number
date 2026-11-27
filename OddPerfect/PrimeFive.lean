module

public import OddPerfect.PrimeRank5_1.Part067
public import OddPerfect.PrimeRank5_2.Part051
public import OddPerfect.PrimeRank5_3.Part028
public import OddPerfect.PrimeRank5_4.Part046
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect
open SpoofBox

/-- A five-slot prime factorization would place the Euler prime in one
of five positions. The first position already forces incompatible base
bounds, while the four other positions each have a checked cover. -/
theorem six_le_distinct_prime_factor_count {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    6 ≤ N.primeFactors.card := by
  have small := five_le_distinct_prime_factor_count ho hN
  have neq : N.primeFactors.card ≠ 5 := by
    apply exclude_prime_count_of_covers (by decide) ?_ hN ho
    intro j
    fin_cases j
    · exact primeCovered_reject _ (by decide +kernel)
    · exact closed_prime_5_1
    · exact closed_prime_5_2
    · exact closed_prime_5_3
    · exact closed_prime_5_4
  omega

end OddPerfect
