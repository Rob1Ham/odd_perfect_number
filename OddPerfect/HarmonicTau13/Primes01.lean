module

public import OddPerfect.HarmonicRoots
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htauPrime13_617 : Nat.Prime 617 :=
  by norm_num

theorem htauPrime13_398581 : Nat.Prime 398581 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 73] }])

theorem htauPrime13_797161 : Nat.Prime 797161 :=
  by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 7, 13, 73] }])

theorem htauPrime13_305175781 : Nat.Prime 305175781 :=
  by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 13, 31, 601] }])

theorem htauPrime13_16148168401 : Nat.Prime 16148168401 :=
  by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 5, 7, 13, 19, 43, 181] }])

end OddPerfect.HarmonicChain
