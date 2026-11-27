module

public import OddPerfect.HarmonicTau5.Primes04
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htauPrime5_3500201 : Nat.Prime 3500201 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 11, 37, 43] }])

theorem htauPrime5_3706621 : Nat.Prime 3706621 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 163, 379] }])

theorem htauPrime5_4313591 : Nat.Prime 4313591 :=
  by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 5, 97, 4447] }, .lucas { root := 3, primeFactors := [2, 3, 13, 19] }])

theorem htauPrime5_4524851 : Nat.Prime 4524851 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 19, 433] }])

theorem htauPrime5_4772771 : Nat.Prime 4772771 :=
  by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 477277] }, .lucas { root := 2, primeFactors := [2, 3, 31, 1283] }, .lucas { root := 2, primeFactors := [2, 641] }])

theorem htauPrime5_5064511 : Nat.Prime 5064511 :=
  by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 11, 103, 149] }])

theorem htauPrime5_5278271 : Nat.Prime 5278271 :=
  by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 5, 23, 53, 433] }])

theorem htauPrime5_5514451 : Nat.Prime 5514451 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 97, 379] }])

theorem htauPrime5_5885051 : Nat.Prime 5885051 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 117701] }, .lucas { root := 2, primeFactors := [2, 5, 11, 107] }])

theorem htauPrime5_6586781 : Nat.Prime 6586781 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 61, 5399] }, .lucas { root := 7, primeFactors := [2, 2699] }, .lucas { root := 2, primeFactors := [2, 19, 71] }])

theorem htauPrime5_8715961 : Nat.Prime 8715961 :=
  by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 11, 31, 71] }])

theorem htauPrime5_9170881 : Nat.Prime 9170881 :=
  by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 41, 233] }])

theorem htauPrime5_10332211 : Nat.Prime 10332211 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 49201] }, .lucas { root := 7, primeFactors := [2, 3, 5, 41] }])

theorem htauPrime5_10378063 : Nat.Prime 10378063 :=
  by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 179, 3221] }, .lucas { root := 10, primeFactors := [2, 5, 7, 23] }])

theorem htauPrime5_11105551 : Nat.Prime 11105551 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 23, 29, 37] }])

theorem htauPrime5_11106421 : Nat.Prime 11106421 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 29, 491] }])

theorem htauPrime5_11631811 : Nat.Prime 11631811 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 387727] }, .lucas { root := 3, primeFactors := [2, 3, 64621] }, .lucas { root := 6, primeFactors := [2, 3, 5, 359] }])

theorem htauPrime5_12774841 : Nat.Prime 12774841 :=
  by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 13, 19, 431] }])

theorem htauPrime5_14275091 : Nat.Prime 14275091 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 1427509] }, .lucas { root := 2, primeFactors := [2, 3, 19, 2087] }, .lucas { root := 5, primeFactors := [2, 7, 149] }])

theorem htauPrime5_17884211 : Nat.Prime 17884211 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 31, 1861] }, .lucas { root := 2, primeFactors := [2, 3, 5, 31] }])

theorem htauPrime5_19587401 : Nat.Prime 19587401 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 17, 823] }])

theorem htauPrime5_19622651 : Nat.Prime 19622651 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 601, 653] }])

theorem htauPrime5_21472771 : Nat.Prime 21472771 :=
  by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 11, 31, 2099] }, .lucas { root := 2, primeFactors := [2, 1049] }, .lucas { root := 3, primeFactors := [2, 131] }])

theorem htauPrime5_22199431 : Nat.Prime 22199431 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 11, 67271] }, .lucas { root := 14, primeFactors := [2, 5, 7, 31] }])

theorem htauPrime5_28792661 : Nat.Prime 28792661 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 13, 37, 41, 73] }])

theorem htauPrime5_39449441 : Nat.Prime 39449441 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 79, 3121] }, .lucas { root := 7, primeFactors := [2, 3, 5, 13] }])

theorem htauPrime5_43435141 : Nat.Prime 43435141 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 19, 5443] }, .lucas { root := 2, primeFactors := [2, 3, 907] }])

theorem htauPrime5_45869891 : Nat.Prime 45869891 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 167, 227] }])

theorem htauPrime5_46753151 : Nat.Prime 46753151 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 935063] }, .lucas { root := 5, primeFactors := [2, 467531] }, .lucas { root := 6, primeFactors := [2, 5, 7, 6679] }, .lucas { root := 7, primeFactors := [2, 3, 7, 53] }])

theorem htauPrime5_48037081 : Nat.Prime 48037081 :=
  by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 7, 13, 53, 83] }])

theorem htauPrime5_51245141 : Nat.Prime 51245141 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 17, 150721] }, .lucas { root := 31, primeFactors := [2, 3, 5, 157] }])

theorem htauPrime5_52274161 : Nat.Prime 52274161 :=
  by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 2689] }, .lucas { root := 19, primeFactors := [2, 3, 7] }])

end OddPerfect.HarmonicChain
