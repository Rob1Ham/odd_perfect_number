module

public import OddPerfect.SixthPowerChain
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem sixPrime41_41 : Nat.Prime 41 :=
  by norm_num

theorem sixPrime41_1723 : Nat.Prime 1723 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 41] }])

theorem sixPrime41_6101 : Nat.Prime 6101 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 61] }])

end OddPerfect.SixthPowerChain
