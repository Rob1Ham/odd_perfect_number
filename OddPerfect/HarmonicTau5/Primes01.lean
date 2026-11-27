module

public import OddPerfect.HarmonicRoots
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htauPrime5_43 : Nat.Prime 43 :=
  by norm_num

theorem htauPrime5_47 : Nat.Prime 47 :=
  by norm_num

theorem htauPrime5_59 : Nat.Prime 59 :=
  by norm_num

theorem htauPrime5_67 : Nat.Prime 67 :=
  by norm_num

theorem htauPrime5_71 : Nat.Prime 71 :=
  by norm_num

theorem htauPrime5_127 : Nat.Prime 127 :=
  by norm_num

theorem htauPrime5_131 : Nat.Prime 131 :=
  by norm_num

theorem htauPrime5_151 : Nat.Prime 151 :=
  by norm_num

theorem htauPrime5_163 : Nat.Prime 163 :=
  by norm_num

theorem htauPrime5_179 : Nat.Prime 179 :=
  by norm_num

theorem htauPrime5_191 : Nat.Prime 191 :=
  by norm_num

theorem htauPrime5_211 : Nat.Prime 211 :=
  by norm_num

theorem htauPrime5_251 : Nat.Prime 251 :=
  by norm_num

theorem htauPrime5_271 : Nat.Prime 271 :=
  by norm_num

theorem htauPrime5_331 : Nat.Prime 331 :=
  by norm_num

theorem htauPrime5_367 : Nat.Prime 367 :=
  by norm_num

theorem htauPrime5_467 : Nat.Prime 467 :=
  by norm_num

theorem htauPrime5_491 : Nat.Prime 491 :=
  by norm_num

theorem htauPrime5_547 : Nat.Prime 547 :=
  by norm_num

theorem htauPrime5_571 : Nat.Prime 571 :=
  by norm_num

theorem htauPrime5_631 : Nat.Prime 631 :=
  by norm_num

theorem htauPrime5_691 : Nat.Prime 691 :=
  by norm_num

theorem htauPrime5_911 : Nat.Prime 911 :=
  by norm_num

theorem htauPrime5_991 : Nat.Prime 991 :=
  by norm_num

theorem htauPrime5_1031 : Nat.Prime 1031 :=
  by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 5, 103] }])

theorem htauPrime5_1051 : Nat.Prime 1051 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7] }])

theorem htauPrime5_1093 : Nat.Prime 1093 :=
  by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13] }])

theorem htauPrime5_1231 : Nat.Prime 1231 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 41] }])

theorem htauPrime5_1279 : Nat.Prime 1279 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 71] }])

theorem htauPrime5_1301 : Nat.Prime 1301 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 13] }])

theorem htauPrime5_1451 : Nat.Prime 1451 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 29] }])

theorem htauPrime5_1471 : Nat.Prime 1471 :=
  by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7] }])

end OddPerfect.HarmonicChain
