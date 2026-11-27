module

public import OddPerfect.HarmonicTau5.Primes06
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htauPrime5_4802611441 : Nat.Prime 4802611441 :=
  by primality (cert := .witnesses [.lucas { root := 29, primeFactors := [2, 3, 5, 11, 263, 6917] }, .lucas { root := 2, primeFactors := [2, 7, 13, 19] }])

theorem htauPrime5_5908670381 : Nat.Prime 5908670381 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 139, 277, 7673] }, .lucas { root := 3, primeFactors := [2, 7, 137] }])

theorem htauPrime5_6114099671 : Nat.Prime 6114099671 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 73, 157, 7621] }, .lucas { root := 2, primeFactors := [2, 3, 5, 127] }])

theorem htauPrime5_7296664931 : Nat.Prime 7296664931 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 47, 15524819] }, .lucas { root := 2, primeFactors := [2, 83, 93523] }, .lucas { root := 2, primeFactors := [2, 3, 11, 13, 109] }])

theorem htauPrime5_7677461821 : Nat.Prime 7677461821 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 83, 113, 1949] }, .lucas { root := 2, primeFactors := [2, 487] }])

theorem htauPrime5_12936304421 : Nat.Prime 12936304421 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 13, 41, 277, 337] }])

theorem htauPrime5_15954977651 : Nat.Prime 15954977651 :=
  by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 59, 5408467] }, .lucas { root := 2, primeFactors := [2, 3, 7, 131, 983] }])

theorem htauPrime5_16656709681 : Nat.Prime 16656709681 :=
  by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 13, 359, 4957] }, .lucas { root := 2, primeFactors := [2, 3, 7, 59] }])

theorem htauPrime5_17097943091 : Nat.Prime 17097943091 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 23, 37, 233, 8623] }, .lucas { root := 3, primeFactors := [2, 3, 479] }])

theorem htauPrime5_19408913261 : Nat.Prime 19408913261 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 17, 373, 13913] }, .lucas { root := 3, primeFactors := [2, 37, 47] }])

theorem htauPrime5_24903325661 : Nat.Prime 24903325661 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 199, 397, 15761] }, .lucas { root := 3, primeFactors := [2, 5, 197] }])

theorem htauPrime5_26136721201 : Nat.Prime 26136721201 :=
  by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 1193, 18257] }, .lucas { root := 3, primeFactors := [2, 149] }, .lucas { root := 5, primeFactors := [2, 7, 163] }])

theorem htauPrime5_34216526831 : Nat.Prime 34216526831 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 31, 110375893] }, .lucas { root := 2, primeFactors := [2, 3, 11, 53, 1753] }, .lucas { root := 7, primeFactors := [2, 3, 73] }])

theorem htauPrime5_37226181521 : Nat.Prime 37226181521 :=
  by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 5, 11, 173, 439, 557] }])

theorem htauPrime5_43713558101 : Nat.Prime 43713558101 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 229, 457, 4177] }, .lucas { root := 5, primeFactors := [2, 3, 29] }])

theorem htauPrime5_52753304641 : Nat.Prime 52753304641 :=
  by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 89, 479, 1289] }, .lucas { root := 6, primeFactors := [2, 7, 23] }])

theorem htauPrime5_64141071121 : Nat.Prime 64141071121 :=
  by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 7, 503, 25301] }, .lucas { root := 3, primeFactors := [2, 5, 11, 23] }])

theorem htauPrime5_67164484721 : Nat.Prime 67164484721 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 19, 673, 65657] }, .lucas { root := 3, primeFactors := [2, 29, 283] }])

theorem htauPrime5_84969569171 : Nat.Prime 84969569171 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 113, 197, 381697] }, .lucas { root := 15, primeFactors := [2, 3, 7, 71] }])

theorem htauPrime5_96427561501 : Nat.Prime 96427561501 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17, 31, 73, 557] }])

theorem htauPrime5_100648118041 : Nat.Prime 100648118041 :=
  by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 29, 47, 563, 1093] }, .lucas { root := 5, primeFactors := [2, 3, 7, 13] }])

theorem htauPrime5_145159381141 : Nat.Prime 145159381141 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 103, 617, 38069] }, .lucas { root := 2, primeFactors := [2, 31, 307] }])

theorem htauPrime5_156982145081 : Nat.Prime 156982145081 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 43, 47, 907, 2141] }, .lucas { root := 2, primeFactors := [2, 5, 107] }])

theorem htauPrime5_193091463181 : Nat.Prime 193091463181 :=
  by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7, 11, 13931563] }, .lucas { root := 2, primeFactors := [2, 3, 151, 15377] }, .lucas { root := 3, primeFactors := [2, 31] }])

theorem htauPrime5_416450882401 : Nat.Prime 416450882401 :=
  by primality (cert := .witnesses [.lucas { root := 41, primeFactors := [2, 3, 5, 7, 3541249] }, .lucas { root := 7, primeFactors := [2, 3, 29, 53] }])

theorem htauPrime5_714060279761 : Nat.Prime 714060279761 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 23, 37, 101, 113, 919] }])

theorem htauPrime5_875296605041 : Nat.Prime 875296605041 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 11, 13, 967, 7193] }, .lucas { root := 3, primeFactors := [2, 29, 31] }])

end OddPerfect.HarmonicChain
