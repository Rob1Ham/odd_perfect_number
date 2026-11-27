module

public import OddPerfect.HarmonicTau5.Primes02
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htauPrime5_9511 : Nat.Prime 9511 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 317] }])

theorem htauPrime5_10037 : Nat.Prime 10037 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 193] }])

theorem htauPrime5_11503 : Nat.Prime 11503 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 71] }])

theorem htauPrime5_13441 : Nat.Prime 13441 :=
  by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7] }])

theorem htauPrime5_14083 : Nat.Prime 14083 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 2347] }, .lucas { root := 3, primeFactors := [2, 3, 17, 23] }])

theorem htauPrime5_14621 : Nat.Prime 14621 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 17, 43] }])

theorem htauPrime5_15971 : Nat.Prime 15971 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 1597] }, .lucas { root := 11, primeFactors := [2, 3, 7, 19] }])

theorem htauPrime5_17293 : Nat.Prime 17293 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 131] }])

theorem htauPrime5_17351 : Nat.Prime 17351 :=
  by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 347] }])

theorem htauPrime5_21491 : Nat.Prime 21491 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 307] }])

theorem htauPrime5_21787 : Nat.Prime 21787 :=
  by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 3631] }, .lucas { root := 15, primeFactors := [2, 3, 5, 11] }])

theorem htauPrime5_23971 : Nat.Prime 23971 :=
  by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 17, 47] }])

theorem htauPrime5_24061 : Nat.Prime 24061 :=
  by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 401] }])

theorem htauPrime5_26881 : Nat.Prime 26881 :=
  by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7] }])

theorem htauPrime5_30431 : Nat.Prime 30431 :=
  by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 17, 179] }])

theorem htauPrime5_30941 : Nat.Prime 30941 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 13, 17] }])

theorem htauPrime5_44371 : Nat.Prime 44371 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17, 29] }])

theorem htauPrime5_45319 : Nat.Prime 45319 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 13, 83] }])

theorem htauPrime5_53551 : Nat.Prime 53551 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 17] }])

theorem htauPrime5_63601 : Nat.Prime 63601 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 53] }])

theorem htauPrime5_70841 : Nat.Prime 70841 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 11, 23] }])

theorem htauPrime5_75571 : Nat.Prime 75571 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 229] }])

theorem htauPrime5_88741 : Nat.Prime 88741 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17, 29] }])

theorem htauPrime5_95531 : Nat.Prime 95531 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 41, 233] }])

theorem htauPrime5_103231 : Nat.Prime 103231 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 31, 37] }])

theorem htauPrime5_125731 : Nat.Prime 125731 :=
  by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 11, 127] }])

theorem htauPrime5_126631 : Nat.Prime 126631 :=
  by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 67] }])

theorem htauPrime5_148961 : Nat.Prime 148961 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 19] }])

theorem htauPrime5_159871 : Nat.Prime 159871 :=
  by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 73] }])

theorem htauPrime5_184511 : Nat.Prime 184511 :=
  by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 5, 18451] }, .lucas { root := 3, primeFactors := [2, 3, 5, 41] }])

theorem htauPrime5_192811 : Nat.Prime 192811 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 6427] }, .lucas { root := 3, primeFactors := [2, 3, 7, 17] }])

theorem htauPrime5_193811 : Nat.Prime 193811 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 19381] }, .lucas { root := 7, primeFactors := [2, 3, 5, 17, 19] }])

end OddPerfect.HarmonicChain
