module

public import OddPerfect.HarmonicTau7.Primes01
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htauPrime7_127159831 : Nat.Prime 127159831 :=
  by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 17, 31, 383] }])

theorem htauPrime7_256128979 : Nat.Prime 256128979 :=
  by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 233, 3739] }, .lucas { root := 7, primeFactors := [2, 3, 7, 89] }])

theorem htauPrime7_778986167 : Nat.Prime 778986167 :=
  by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 31, 607, 2957] }, .lucas { root := 2, primeFactors := [2, 739] }])

theorem htauPrime7_917087137 : Nat.Prime 917087137 :=
  by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 19, 31, 331] }])

theorem htauPrime7_11411291417 : Nat.Prime 11411291417 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 203773061] }, .lucas { root := 10, primeFactors := [2, 5, 37, 509, 541] }])

theorem htauPrime7_52379047267 : Nat.Prime 52379047267 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 13, 31, 61, 97, 523] }])

theorem htauPrime7_153436090543 : Nat.Prime 153436090543 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 37, 73, 751, 1801] }, .lucas { root := 11, primeFactors := [2, 3, 5] }])

theorem htauPrime7_502628805631 : Nat.Prime 502628805631 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 89, 373, 8011] }, .lucas { root := 14, primeFactors := [2, 3, 5, 89] }])

end OddPerfect.HarmonicChain
