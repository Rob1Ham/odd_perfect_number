module

public import OddPerfect.HarmonicTau5.Primes01
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htauPrime5_1499 : Nat.Prime 1499 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 107] }])

theorem htauPrime5_1511 : Nat.Prime 1511 :=
  by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 151] }])

theorem htauPrime5_1601 : Nat.Prime 1601 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5] }])

theorem htauPrime5_1811 : Nat.Prime 1811 :=
  by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 181] }])

theorem htauPrime5_1871 : Nat.Prime 1871 :=
  by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 5, 11, 17] }])

theorem htauPrime5_2221 : Nat.Prime 2221 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 37] }])

theorem htauPrime5_2281 : Nat.Prime 2281 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 19] }])

theorem htauPrime5_2311 : Nat.Prime 2311 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 11] }])

theorem htauPrime5_2411 : Nat.Prime 2411 :=
  by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 241] }])

theorem htauPrime5_2437 : Nat.Prime 2437 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 29] }])

theorem htauPrime5_2467 : Nat.Prime 2467 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 137] }])

theorem htauPrime5_2557 : Nat.Prime 2557 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 71] }])

theorem htauPrime5_2801 : Nat.Prime 2801 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7] }])

theorem htauPrime5_3221 : Nat.Prime 3221 :=
  by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 5, 7, 23] }])

theorem htauPrime5_3299 : Nat.Prime 3299 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 97] }])

theorem htauPrime5_3691 : Nat.Prime 3691 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 41] }])

theorem htauPrime5_4091 : Nat.Prime 4091 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 409] }])

theorem htauPrime5_4231 : Nat.Prime 4231 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 47] }])

theorem htauPrime5_4271 : Nat.Prime 4271 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 61] }])

theorem htauPrime5_4561 : Nat.Prime 4561 :=
  by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 19] }])

theorem htauPrime5_4603 : Nat.Prime 4603 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 59] }])

theorem htauPrime5_4933 : Nat.Prime 4933 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 137] }])

theorem htauPrime5_5113 : Nat.Prime 5113 :=
  by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 71] }])

theorem htauPrime5_5231 : Nat.Prime 5231 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 523] }])

theorem htauPrime5_5419 : Nat.Prime 5419 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 43] }])

theorem htauPrime5_5821 : Nat.Prime 5821 :=
  by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 97] }])

theorem htauPrime5_6011 : Nat.Prime 6011 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 601] }])

theorem htauPrime5_6131 : Nat.Prime 6131 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 613] }])

theorem htauPrime5_7699 : Nat.Prime 7699 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1283] }, .lucas { root := 2, primeFactors := [2, 641] }])

theorem htauPrime5_7793 : Nat.Prime 7793 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 487] }])

theorem htauPrime5_8971 : Nat.Prime 8971 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 23] }])

theorem htauPrime5_9431 : Nat.Prime 9431 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 23, 41] }])

end OddPerfect.HarmonicChain
