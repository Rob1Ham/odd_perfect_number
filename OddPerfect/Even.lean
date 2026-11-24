module

public import Archive.Wiedijk100Theorems.PerfectNumbers

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

end OddPerfect
