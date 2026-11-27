module

public import OddPerfect.HarmonicRoots
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htauPrime11_859 : Nat.Prime 859 :=
  by norm_num

theorem htauPrime11_1123 : Nat.Prime 1123 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 17] }])

theorem htauPrime11_3851 : Nat.Prime 3851 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 11] }])

theorem htauPrime11_293459 : Nat.Prime 293459 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 13339] }, .lucas { root := 2, primeFactors := [2, 3, 13, 19] }])

theorem htauPrime11_1141081 : Nat.Prime 1141081 :=
  by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 37, 257] }])

theorem htauPrime11_1806113 : Nat.Prime 1806113 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 11, 733] }])

theorem htauPrime11_12207031 : Nat.Prime 12207031 :=
  by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11, 71, 521] }])

end OddPerfect.HarmonicChain
