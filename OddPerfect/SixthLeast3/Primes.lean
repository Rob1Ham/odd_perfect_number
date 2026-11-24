module

public import OddPerfect.SixthPowerChain
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem sixPrime3_37 : Nat.Prime 37 :=
  by norm_num

theorem sixPrime3_43 : Nat.Prime 43 :=
  by norm_num

theorem sixPrime3_61 : Nat.Prime 61 :=
  by norm_num

theorem sixPrime3_67 : Nat.Prime 67 :=
  by norm_num

theorem sixPrime3_71 : Nat.Prime 71 :=
  by norm_num

theorem sixPrime3_79 : Nat.Prime 79 :=
  by norm_num

theorem sixPrime3_97 : Nat.Prime 97 :=
  by norm_num

theorem sixPrime3_127 : Nat.Prime 127 :=
  by norm_num

theorem sixPrime3_131 : Nat.Prime 131 :=
  by norm_num

theorem sixPrime3_151 : Nat.Prime 151 :=
  by norm_num

theorem sixPrime3_157 : Nat.Prime 157 :=
  by norm_num

theorem sixPrime3_181 : Nat.Prime 181 :=
  by norm_num

theorem sixPrime3_211 : Nat.Prime 211 :=
  by norm_num

theorem sixPrime3_331 : Nat.Prime 331 :=
  by norm_num

theorem sixPrime3_421 : Nat.Prime 421 :=
  by norm_num

theorem sixPrime3_433 : Nat.Prime 433 :=
  by norm_num

theorem sixPrime3_523 : Nat.Prime 523 :=
  by norm_num

theorem sixPrime3_541 : Nat.Prime 541 :=
  by norm_num

theorem sixPrime3_631 : Nat.Prime 631 :=
  by norm_num

theorem sixPrime3_769 : Nat.Prime 769 :=
  by norm_num

theorem sixPrime3_1093 : Nat.Prime 1093 :=
  by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13] }])

theorem sixPrime3_1511 : Nat.Prime 1511 :=
  by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 151] }])

theorem sixPrime3_2801 : Nat.Prime 2801 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7] }])

theorem sixPrime3_3221 : Nat.Prime 3221 :=
  by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 5, 7, 23] }])

theorem sixPrime3_4591 : Nat.Prime 4591 :=
  by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 17] }])

theorem sixPrime3_4933 : Nat.Prime 4933 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 137] }])

theorem sixPrime3_14083 : Nat.Prime 14083 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 2347] }, .lucas { root := 3, primeFactors := [2, 3, 17, 23] }])

theorem sixPrime3_14401 : Nat.Prime 14401 :=
  by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5] }])

theorem sixPrime3_17351 : Nat.Prime 17351 :=
  by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 347] }])

theorem sixPrime3_21491 : Nat.Prime 21491 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 307] }])

theorem sixPrime3_30941 : Nat.Prime 30941 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 13, 17] }])

theorem sixPrime3_33151 : Nat.Prime 33151 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13, 17] }])

theorem sixPrime3_37861 : Nat.Prime 37861 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 631] }])

theorem sixPrime3_46411 : Nat.Prime 46411 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 13, 17] }])

theorem sixPrime3_55333 : Nat.Prime 55333 :=
  by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 29, 53] }])

theorem sixPrime3_63601 : Nat.Prime 63601 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 53] }])

theorem sixPrime3_1963111 : Nat.Prime 1963111 :=
  by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 65437] }, .lucas { root := 6, primeFactors := [2, 3, 7, 19, 41] }])

theorem sixPrime3_3500201 : Nat.Prime 3500201 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 11, 37, 43] }])

theorem sixPrime3_6294091 : Nat.Prime 6294091 :=
  by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 11, 19073] }, .lucas { root := 3, primeFactors := [2, 149] }])

theorem sixPrime3_10378063 : Nat.Prime 10378063 :=
  by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 179, 3221] }, .lucas { root := 10, primeFactors := [2, 5, 7, 23] }])

theorem sixPrime3_68409301 : Nat.Prime 68409301 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 37, 6163] }, .lucas { root := 3, primeFactors := [2, 3, 13, 79] }])

theorem sixPrime3_69617111 : Nat.Prime 69617111 :=
  by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 29, 240059] }, .lucas { root := 2, primeFactors := [2, 7, 13, 1319] }, .lucas { root := 13, primeFactors := [2, 659] }])

theorem sixPrime3_262209281 : Nat.Prime 262209281 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 127, 1613] }, .lucas { root := 3, primeFactors := [2, 13, 31] }])

theorem sixPrime3_366340651 : Nat.Prime 366340651 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 17, 43, 257] }])

theorem sixPrime3_647251721 : Nat.Prime 647251721 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 19, 851647] }, .lucas { root := 3, primeFactors := [2, 3, 141941] }, .lucas { root := 2, primeFactors := [2, 5, 47, 151] }])

theorem sixPrime3_50368674550301 : Nat.Prime 50368674550301 :=
  by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 5, 7039, 71556577] }, .lucas { root := 3, primeFactors := [2, 3, 17, 23] }, .lucas { root := 17, primeFactors := [2, 3, 7, 13, 8191] }, .lucas { root := 17, primeFactors := [2, 3, 5, 7, 13] }])

theorem sixPrime3_31810898376456201755581 : Nat.Prime 31810898376456201755581 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 37, 14329233502908198989] }, .lucas { root := 2, primeFactors := [2, 5463181, 655718413087] }, .lucas { root := 2, primeFactors := [2, 3, 5, 67, 151] }, .lucas { root := 3, primeFactors := [2, 3, 11, 17, 11437, 17033] }, .lucas { root := 2, primeFactors := [2, 3, 953] }, .lucas { root := 3, primeFactors := [2, 2129] }, .lucas { root := 3, primeFactors := [2, 7, 19] }])

end OddPerfect.SixthPowerChain
