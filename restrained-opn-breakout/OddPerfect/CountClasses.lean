module

public import OddPerfect.Euler

public section

namespace OddPerfect

/-- Non-3 primes of exact exponent two (Ochem and Rao's class counted by p₂). -/
@[expose] def squareSources (N : ℕ) : Finset ℕ :=
  N.primeFactors.filter fun q => q ≠ 3 ∧ N.factorization q = 2

/-- The square components introducing a factor 3 into the divisor sum. -/
@[expose] def squareSourcesOne (N : ℕ) : Finset ℕ :=
  (squareSources N).filter fun q => q % 3 = 1

/-- Non-3, non-special primes with an exponent of at least four. -/
@[expose] def largeSources (N p : ℕ) : Finset ℕ :=
  N.primeFactors.filter fun q => q ≠ 3 ∧ q ≠ p ∧ 4 ≤ N.factorization q

end OddPerfect
