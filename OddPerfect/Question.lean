module

public import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Ring.Parity

public section

namespace OddPerfect

-- Upstream: formal-conjectures FormalConjectures/Wikipedia/PerfectNumbers.lean:83 (declaration PerfectNumbers.odd_perfect_number_conjecture)
/-- The existence question pursued in this repository. -/
def existsOddPerfect : Prop := ∃ n : ℕ, Odd n ∧ Nat.Perfect n

/-- Constructive equivalence between negating `existsOddPerfect` and the universal
statement `∀ n : ℕ, Nat.Perfect n → Even n` (`PerfectNumbers.odd_perfect_number_conjecture`
in `FormalConjectures/Wikipedia/PerfectNumbers.lean`). -/
theorem not_existsOddPerfect_iff_forall_perfect_even :
    ¬ existsOddPerfect ↔ ∀ n : ℕ, Nat.Perfect n → Even n := by
  unfold existsOddPerfect
  constructor
  · intro h n hn
    exact Nat.not_odd_iff_even.mp fun ho => h ⟨n, ho, hn⟩
  · rintro h ⟨n, ho, hn⟩
    exact Nat.not_odd_iff_even.mpr (h n hn) ho

end OddPerfect
