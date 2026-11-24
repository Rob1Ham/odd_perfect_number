module

public import OddPerfect.SixthPowerChain
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem sixPrime23_292561 : Nat.Prime 292561 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 23, 53] }])

end OddPerfect.SixthPowerChain
