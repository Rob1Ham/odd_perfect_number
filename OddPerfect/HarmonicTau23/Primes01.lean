module

public import OddPerfect.HarmonicRoots
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htauPrime23_1001523179 : Nat.Prime 1001523179 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 23, 29, 37, 103, 197] }])

end OddPerfect.HarmonicChain
