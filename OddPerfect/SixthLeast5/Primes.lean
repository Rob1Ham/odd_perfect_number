module

public import OddPerfect.SixthPowerChain
import Mathlib.Tactic.Primality
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect.SixthPowerChain

set_option maxRecDepth 16000

theorem sixPrime5_37 : Nat.Prime 37 :=
  by norm_num

theorem sixPrime5_41 : Nat.Prime 41 :=
  by norm_num

theorem sixPrime5_43 : Nat.Prime 43 :=
  by norm_num

theorem sixPrime5_61 : Nat.Prime 61 :=
  by norm_num

theorem sixPrime5_71 : Nat.Prime 71 :=
  by norm_num

theorem sixPrime5_79 : Nat.Prime 79 :=
  by norm_num

theorem sixPrime5_151 : Nat.Prime 151 :=
  by norm_num

theorem sixPrime5_193 : Nat.Prime 193 :=
  by norm_num

theorem sixPrime5_199 : Nat.Prime 199 :=
  by norm_num

theorem sixPrime5_211 : Nat.Prime 211 :=
  by norm_num

theorem sixPrime5_251 : Nat.Prime 251 :=
  by norm_num

theorem sixPrime5_271 : Nat.Prime 271 :=
  by norm_num

theorem sixPrime5_331 : Nat.Prime 331 :=
  by norm_num

theorem sixPrime5_521 : Nat.Prime 521 :=
  by norm_num

theorem sixPrime5_911 : Nat.Prime 911 :=
  by norm_num

theorem sixPrime5_1063 : Nat.Prime 1063 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 59] }])

theorem sixPrime5_1291 : Nat.Prime 1291 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 43] }])

theorem sixPrime5_1361 : Nat.Prime 1361 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 17] }])

theorem sixPrime5_1471 : Nat.Prime 1471 :=
  by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7] }])

theorem sixPrime5_1723 : Nat.Prime 1723 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 41] }])

theorem sixPrime5_2221 : Nat.Prime 2221 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 37] }])

theorem sixPrime5_2467 : Nat.Prime 2467 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 137] }])

theorem sixPrime5_2557 : Nat.Prime 2557 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 71] }])

theorem sixPrime5_2801 : Nat.Prime 2801 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7] }])

theorem sixPrime5_3221 : Nat.Prime 3221 :=
  by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 5, 7, 23] }])

theorem sixPrime5_4271 : Nat.Prime 4271 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 61] }])

theorem sixPrime5_4751 : Nat.Prime 4751 :=
  by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 5, 19] }])

theorem sixPrime5_4933 : Nat.Prime 4933 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 137] }])

theorem sixPrime5_5113 : Nat.Prime 5113 :=
  by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 71] }])

theorem sixPrime5_6101 : Nat.Prime 6101 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 61] }])

theorem sixPrime5_17351 : Nat.Prime 17351 :=
  by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 347] }])

theorem sixPrime5_33151 : Nat.Prime 33151 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13, 17] }])

theorem sixPrime5_142591 : Nat.Prime 142591 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 97] }])

theorem sixPrime5_171559 : Nat.Prime 171559 :=
  by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 353] }])

theorem sixPrime5_579281 : Nat.Prime 579281 :=
  by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 13, 557] }])

theorem sixPrime5_1963111 : Nat.Prime 1963111 :=
  by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 65437] }, .lucas { root := 6, primeFactors := [2, 3, 7, 19, 41] }])

theorem sixPrime5_6294091 : Nat.Prime 6294091 :=
  by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 11, 19073] }, .lucas { root := 3, primeFactors := [2, 149] }])

theorem sixPrime5_10378063 : Nat.Prime 10378063 :=
  by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 179, 3221] }, .lucas { root := 10, primeFactors := [2, 5, 7, 23] }])

theorem sixPrime5_22576753 : Nat.Prime 22576753 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 4751] }, .lucas { root := 19, primeFactors := [2, 5, 19] }])

theorem sixPrime5_58044391 : Nat.Prime 58044391 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 83, 23311] }, .lucas { root := 3, primeFactors := [2, 3, 5, 7, 37] }])

theorem sixPrime5_104670301 : Nat.Prime 104670301 :=
  by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 49843] }, .lucas { root := 2, primeFactors := [2, 3, 13, 71] }])

theorem sixPrime5_1445413861 : Nat.Prime 1445413861 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 59, 12373] }, .lucas { root := 2, primeFactors := [2, 3, 1031] }, .lucas { root := 14, primeFactors := [2, 5, 103] }])

theorem sixPrime5_1957650063931 : Nat.Prime 1957650063931 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 107, 1129, 16369] }, .lucas { root := 11, primeFactors := [2, 3, 47] }, .lucas { root := 7, primeFactors := [2, 3, 11, 31] }])

theorem sixPrime5_59376284620771 : Nat.Prime 59376284620771 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 37, 43, 163, 379, 1549] }, .lucas { root := 2, primeFactors := [2, 3, 43] }])

theorem sixPrime5_241562563680036301 : Nat.Prime 241562563680036301 :=
  by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 13, 17, 3643477581901] }, .lucas { root := 2, primeFactors := [2, 3, 5, 13, 17, 31, 1772723] }, .lucas { root := 2, primeFactors := [2, 7, 18089] }, .lucas { root := 3, primeFactors := [2, 7, 17, 19] }])

theorem sixPrime5_31810898376456201755581 : Nat.Prime 31810898376456201755581 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 37, 14329233502908198989] }, .lucas { root := 2, primeFactors := [2, 5463181, 655718413087] }, .lucas { root := 2, primeFactors := [2, 3, 5, 67, 151] }, .lucas { root := 3, primeFactors := [2, 3, 11, 17, 11437, 17033] }, .lucas { root := 2, primeFactors := [2, 3, 953] }, .lucas { root := 3, primeFactors := [2, 2129] }, .lucas { root := 3, primeFactors := [2, 7, 19] }])

theorem sixPrime5_1531042113494635691575231 : Nat.Prime 1531042113494635691575231 :=
  by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11, 1546507185348116860177] }, .lucas { root := 23, primeFactors := [2, 3, 7, 11, 47, 91670197, 97116709] }, .lucas { root := 2, primeFactors := [2, 3, 179, 42677] }, .lucas { root := 2, primeFactors := [2, 47, 227] }, .lucas { root := 2, primeFactors := [2, 3, 13, 29, 21467] }, .lucas { root := 2, primeFactors := [2, 10733] }, .lucas { root := 2, primeFactors := [2, 2683] }, .lucas { root := 2, primeFactors := [2, 3, 149] }])

end OddPerfect.SixthPowerChain
