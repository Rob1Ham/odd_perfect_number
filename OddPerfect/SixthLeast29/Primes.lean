module

public import OddPerfect.SixthPowerChain
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem sixPrime29_7793 : Nat.Prime 7793 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 487] }])

theorem sixPrime29_732541 : Nat.Prime 732541 :=
  by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 29, 421] }])

end OddPerfect.SixthPowerChain
