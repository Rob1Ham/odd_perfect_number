module

public import OddPerfect.SixthPowerChain
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem sixPrime13_433 : Nat.Prime 433 :=
  by norm_num

theorem sixPrime13_30941 : Nat.Prime 30941 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 13, 17] }])

end OddPerfect.SixthPowerChain
