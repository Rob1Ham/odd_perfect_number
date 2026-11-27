module

public import OddPerfect.HarmonicTau5.Primes03
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htauPrime5_222991 : Nat.Prime 222991 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7433] }, .lucas { root := 3, primeFactors := [2, 929] }])

theorem htauPrime5_230611 : Nat.Prime 230611 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7687] }, .lucas { root := 6, primeFactors := [2, 3, 7, 61] }])

theorem htauPrime5_251491 : Nat.Prime 251491 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 83, 101] }])

theorem htauPrime5_257351 : Nat.Prime 257351 :=
  by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 5, 5147] }, .lucas { root := 2, primeFactors := [2, 31, 83] }])

theorem htauPrime5_262321 : Nat.Prime 262321 :=
  by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 1093] }, .lucas { root := 5, primeFactors := [2, 3, 7, 13] }])

theorem htauPrime5_282281 : Nat.Prime 282281 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7057] }, .lucas { root := 5, primeFactors := [2, 3, 7] }])

theorem htauPrime5_292561 : Nat.Prime 292561 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 23, 53] }])

theorem htauPrime5_292661 : Nat.Prime 292661 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 14633] }, .lucas { root := 3, primeFactors := [2, 31, 59] }])

theorem htauPrime5_305411 : Nat.Prime 305411 :=
  by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 7, 4363] }, .lucas { root := 2, primeFactors := [2, 3, 727] }])

theorem htauPrime5_316991 : Nat.Prime 316991 :=
  by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 31699] }, .lucas { root := 2, primeFactors := [2, 3, 587] }])

theorem htauPrime5_319411 : Nat.Prime 319411 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13] }])

theorem htauPrime5_391151 : Nat.Prime 391151 :=
  by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 5, 7823] }, .lucas { root := 5, primeFactors := [2, 3911] }, .lucas { root := 13, primeFactors := [2, 5, 17, 23] }])

theorem htauPrime5_398311 : Nat.Prime 398311 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 11, 17, 71] }])

theorem htauPrime5_412891 : Nat.Prime 412891 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13763] }, .lucas { root := 2, primeFactors := [2, 7, 983] }])

theorem htauPrime5_510031 : Nat.Prime 510031 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 1889] }, .lucas { root := 3, primeFactors := [2, 59] }])

theorem htauPrime5_579281 : Nat.Prime 579281 :=
  by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 13, 557] }])

theorem htauPrime5_583367 : Nat.Prime 583367 :=
  by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 41669] }, .lucas { root := 2, primeFactors := [2, 11, 947] }])

theorem htauPrime5_603791 : Nat.Prime 603791 :=
  by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 11, 499] }])

theorem htauPrime5_620351 : Nat.Prime 620351 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 19, 653] }])

theorem htauPrime5_627091 : Nat.Prime 627091 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 20903] }, .lucas { root := 5, primeFactors := [2, 7, 1493] }, .lucas { root := 2, primeFactors := [2, 373] }])

theorem htauPrime5_672901 : Nat.Prime 672901 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 2243] }, .lucas { root := 2, primeFactors := [2, 19, 59] }])

theorem htauPrime5_732541 : Nat.Prime 732541 :=
  by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 29, 421] }])

theorem htauPrime5_823241 : Nat.Prime 823241 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 11, 1871] }, .lucas { root := 14, primeFactors := [2, 5, 11, 17] }])

theorem htauPrime5_830833 : Nat.Prime 830833 :=
  by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 19, 911] }])

theorem htauPrime5_973001 : Nat.Prime 973001 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 139] }])

theorem htauPrime5_1772893 : Nat.Prime 1772893 :=
  by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 11, 37] }])

theorem htauPrime5_1789091 : Nat.Prime 1789091 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 178909] }, .lucas { root := 7, primeFactors := [2, 3, 17, 877] }])

theorem htauPrime5_1793161 : Nat.Prime 1793161 :=
  by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 17, 293] }])

theorem htauPrime5_1806113 : Nat.Prime 1806113 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 11, 733] }])

theorem htauPrime5_2573621 : Nat.Prime 2573621 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 31, 593] }])

theorem htauPrime5_2961121 : Nat.Prime 2961121 :=
  by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 31, 199] }])

theorem htauPrime5_3409261 : Nat.Prime 3409261 :=
  by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 56821] }, .lucas { root := 6, primeFactors := [2, 3, 5, 947] }])

end OddPerfect.HarmonicChain
