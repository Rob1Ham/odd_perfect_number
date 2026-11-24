module

public import Mathlib.Data.Nat.Prime.Basic

public section

namespace OddPerfect

/-- A bounded-size leaf list and numeric cutoffs give logarithmic lookup in
large collections of separately certified split and multiplicity witnesses. -/
inductive PrimeBank where
  | leaf (primes : List ℕ)
  | branch (pivot : ℕ) (left right : PrimeBank)

@[expose] def PrimeBank.contains : PrimeBank → ℕ → Bool
  | .leaf ps, p => ps.contains p
  | .branch k l r, p => if p < k then l.contains p else r.contains p

@[expose] def PrimeBank.Certified : PrimeBank → Prop
  | .leaf ps => ∀ p ∈ ps, p.Prime
  | .branch _ l r => l.Certified ∧ r.Certified

theorem PrimeBank.prime_of_contains (bank : PrimeBank) (hc : bank.Certified) {p : ℕ}
    (h : bank.contains p = true) : p.Prime := by
  induction bank with
  | leaf ps => exact hc p (List.contains_iff_mem.mp h)
  | branch k l r il ir =>
    by_cases hlt : p < k
    · exact il hc.1 (by simpa [PrimeBank.contains, hlt] using h)
    · exact ir hc.2 (by simpa [PrimeBank.contains, hlt] using h)

end OddPerfect
