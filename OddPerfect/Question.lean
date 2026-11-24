module

public import Mathlib.NumberTheory.Divisors

public section

namespace OddPerfect

/-- The existence question pursued in this repository. -/
def existsOddPerfect : Prop := ∃ n : ℕ, Odd n ∧ Nat.Perfect n

end OddPerfect
