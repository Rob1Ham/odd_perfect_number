module

public import OddPerfect.HarmonicRoots
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htauPrime17_34511 : Nat.Prime 34511 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 17, 29] }])

theorem htauPrime17_466344409 : Nat.Prime 466344409 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 17, 31, 36871] }, .lucas { root := 15, primeFactors := [2, 3, 5, 1229] }, .lucas { root := 2, primeFactors := [2, 307] }])

end OddPerfect.HarmonicChain
