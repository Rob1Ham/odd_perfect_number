module

public import OddPerfect.SixthPowerChain
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem sixPrime17_307 : Nat.Prime 307 :=
  by norm_num

theorem sixPrime17_1051 : Nat.Prime 1051 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7] }])

theorem sixPrime17_44371 : Nat.Prime 44371 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17, 29] }])

theorem sixPrime17_88741 : Nat.Prime 88741 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17, 29] }])

end OddPerfect.SixthPowerChain
