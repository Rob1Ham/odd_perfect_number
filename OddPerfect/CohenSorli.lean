module

public import OddPerfect.DivisorCount2.Part01
public import OddPerfect.DivisorCount3.Part02
public import OddPerfect.DivisorCount4.Part06
public import OddPerfect.HarmonicSize
import Mathlib.Tactic.IntervalCases

public section

namespace OddPerfect

open DivisorCountSearch

/-- Cohen and Sorli (2010), Theorem 1. The two odd exceptions are
3 and 15. The theorem is stated using only natural-number powers. -/
theorem odd_divisor_count_squared {n : ℕ} (ho : Odd n) (h3 : n ≠ 3) (h15 : n ≠ 15) :
    n.divisors.card^2 ≤ n := by
  by_cases h : 16≤n
  · exact divisor_bound_of_closed node2_1 ho h
  · interval_cases n <;> first | decide | contradiction

/-- The sharp cutoff in the proof of Cohen–Sorli's Theorem 2. -/
theorem odd_divisor_count_cubed {n : ℕ} (ho : Odd n) (h : 883575 < n) :
    n.divisors.card^3 ≤ n := divisor_bound_of_closed node3_23 ho h

/-- The sharp cutoff accompanying Cohen–Sorli's Theorem 3. -/
theorem odd_divisor_count_fourth {n : ℕ} (ho : Odd n) (h : 883086389887727025 < n) :
    n.divisors.card^4 ≤ n := divisor_bound_of_closed node4_106 ho h

/-- The last exceptions at degrees three and four genuinely violate the
respective bounds. Computing the prime-power exponents suffices. -/
theorem last_cubic_and_quartic_divisor_exceptions :
    883575 < (883575:ℕ).divisors.card^3 ∧
    883086389887727025 < (883086389887727025:ℕ).divisors.card^4 := by
  rw [Nat.card_divisors (by decide : 883575 ≠ 0),Nat.card_divisors (by decide : 883086389887727025≠0)]
  decide +kernel

end OddPerfect
