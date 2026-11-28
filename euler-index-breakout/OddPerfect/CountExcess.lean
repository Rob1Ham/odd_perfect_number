module

public import OddPerfect.CountBound37

/-! Additive forms of the verified total and distinct prime-factor bounds. -/

public section

namespace OddPerfect

/-- The verified absolute count and the Ochem–Rao linear count give a
uniform excess of at least five above twice the distinct prime count. -/
theorem five_le_prime_factor_count_excess {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    2 * N.primeFactors.card + 5 ≤ N.primeFactorsList.length := by
  have := thirty_seven_le_total_prime_factor_count ho hN
  have := ochem_rao_prime_factor_count ho hN
  omega

/-- If three is absent, the stronger constant in the linear count gives
an excess of at least seven. -/
theorem seven_le_prime_factor_count_excess_of_three_free {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) (h3 : ¬3∣N) :
    2 * N.primeFactors.card + 7 ≤ N.primeFactorsList.length := by
  have := thirty_seven_le_total_prime_factor_count ho hN
  have := (ochem_rao_count_cases ho hN).2 h3
  omega

end OddPerfect
