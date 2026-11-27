module

public import Archive.Wiedijk100Theorems.PerfectNumbers
public import Mathlib.Data.Set.Finite.Basic
public import OddPerfect.Question

public section

namespace OddPerfect

/-- Five concrete witnesses on the even side of the existence question.
Euclid's construction checks them using their Mersenne primes. -/
theorem even_perfect_examples (n : ℕ) (hn : n ∈ ({6, 28, 496, 8128, 33550336} : Finset ℕ)) :
    Even n ∧ Nat.Perfect n := by
  apply Theorems100.Nat.even_and_perfect_iff.mpr
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with h | h | h | h | h <;> subst n
  · exact ⟨1, by decide, rfl⟩
  · exact ⟨2, by decide, rfl⟩
  · exact ⟨4, by decide, rfl⟩
  · exact ⟨6, by decide, rfl⟩
  · exact ⟨12, by norm_num [mersenne], rfl⟩

/-- Under `¬ existsOddPerfect` (`PerfectNumbers.odd_perfect_number_conjecture` in
`FormalConjectures/Wikipedia/PerfectNumbers.lean`), Euclid–Euler's theorem characterizes
all perfect numbers without an evenness hypothesis. -/
theorem perfect_iff_mersenne_of_not_existsOddPerfect (h : ¬ existsOddPerfect) (n : ℕ) :
    Nat.Perfect n ↔ ∃ k : ℕ, (mersenne (k + 1)).Prime ∧ n = 2 ^ k * mersenne (k + 1) := by
  have heven : Nat.Perfect n → Even n :=
    not_existsOddPerfect_iff_forall_perfect_even.mp h n
  refine ⟨fun hp => Theorems100.Nat.even_and_perfect_iff.mp ⟨heven hp, hp⟩, fun hM => ?_⟩
  exact (Theorems100.Nat.even_and_perfect_iff.mpr hM).2

/-- Under `¬ existsOddPerfect`, the set of all perfect numbers equals the set of even
perfect numbers. -/
theorem perfect_set_eq_even_perfect_set_of_not_existsOddPerfect (h : ¬ existsOddPerfect) :
    {n : ℕ | Nat.Perfect n} = {n : ℕ | Nat.Perfect n ∧ Even n} := by
  ext n
  exact ⟨fun hp => ⟨hp, not_existsOddPerfect_iff_forall_perfect_even.mp h n hp⟩, fun hp => hp.1⟩

/-- Under `¬ existsOddPerfect`, `PerfectNumbers.infinitely_many_perfect` and
`PerfectNumbers.infinitely_many_even_perfect` in `FormalConjectures/Wikipedia/PerfectNumbers.lean`
are equivalent. -/
theorem infinite_perfect_iff_infinite_even_perfect_of_not_existsOddPerfect
    (h : ¬ existsOddPerfect) :
    {n : ℕ | Nat.Perfect n}.Infinite ↔ {n : ℕ | Nat.Perfect n ∧ Even n}.Infinite := by
  rw [perfect_set_eq_even_perfect_set_of_not_existsOddPerfect h]

end OddPerfect
