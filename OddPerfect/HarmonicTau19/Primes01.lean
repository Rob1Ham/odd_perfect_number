module

public import OddPerfect.HarmonicRoots
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htauPrime19_36389 : Nat.Prime 36389 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 827] }])

theorem htauPrime19_363889 : Nat.Prime 363889 :=
  by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 19] }])

end OddPerfect.HarmonicChain
