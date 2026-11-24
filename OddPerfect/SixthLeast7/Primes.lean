module

public import OddPerfect.SixthPowerChain
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem sixPrime7_43 : Nat.Prime 43 :=
  by norm_num

theorem sixPrime7_2801 : Nat.Prime 2801 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7] }])

theorem sixPrime7_28411 : Nat.Prime 28411 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 947] }])

theorem sixPrime7_3500201 : Nat.Prime 3500201 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 11, 37, 43] }])

end OddPerfect.SixthPowerChain
