module

public import OddPerfect.HarmonicRoots
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htauPrime7_67 : Nat.Prime 67 :=
  by norm_num

theorem htauPrime7_103 : Nat.Prime 103 :=
  by norm_num

theorem htauPrime7_109 : Nat.Prime 109 :=
  by norm_num

theorem htauPrime7_163 : Nat.Prime 163 :=
  by norm_num

theorem htauPrime7_263 : Nat.Prime 263 :=
  by norm_num

theorem htauPrime7_547 : Nat.Prime 547 :=
  by norm_num

theorem htauPrime7_571 : Nat.Prime 571 :=
  by norm_num

theorem htauPrime7_617 : Nat.Prime 617 :=
  by norm_num

theorem htauPrime7_883 : Nat.Prime 883 :=
  by norm_num

theorem htauPrime7_1093 : Nat.Prime 1093 :=
  by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13] }])

theorem htauPrime7_2017 : Nat.Prime 2017 :=
  by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7] }])

theorem htauPrime7_4691 : Nat.Prime 4691 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 67] }])

theorem htauPrime7_4733 : Nat.Prime 4733 :=
  by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 13] }])

theorem htauPrime7_5839 : Nat.Prime 5839 :=
  by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 139] }])

theorem htauPrime7_11807 : Nat.Prime 11807 :=
  by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 5903] }, .lucas { root := 5, primeFactors := [2, 13, 227] }])

theorem htauPrime7_19531 : Nat.Prime 19531 :=
  by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 31] }])

theorem htauPrime7_36809 : Nat.Prime 36809 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 43, 107] }])

theorem htauPrime7_45319 : Nat.Prime 45319 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 13, 83] }])

theorem htauPrime7_70841 : Nat.Prime 70841 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 11, 23] }])

theorem htauPrime7_368089 : Nat.Prime 368089 :=
  by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 313] }])

theorem htauPrime7_398581 : Nat.Prime 398581 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 73] }])

theorem htauPrime7_522061 : Nat.Prime 522061 :=
  by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 11, 113] }])

theorem htauPrime7_889453 : Nat.Prime 889453 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 31, 797] }])

theorem htauPrime7_5229043 : Nat.Prime 5229043 :=
  by primality (cert := .witnesses [.lucas { root := 26, primeFactors := [2, 3, 7, 13, 61, 157] }])

theorem htauPrime7_5336717 : Nat.Prime 5336717 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 11, 17327] }, .lucas { root := 5, primeFactors := [2, 8663] }, .lucas { root := 5, primeFactors := [2, 61, 71] }])

theorem htauPrime7_6670903 : Nat.Prime 6670903 :=
  by primality (cert := .witnesses [.lucas { root := 26, primeFactors := [2, 3, 7, 17, 9343] }, .lucas { root := 5, primeFactors := [2, 3, 173] }])

theorem htauPrime7_20241187 : Nat.Prime 20241187 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 17, 28349] }, .lucas { root := 2, primeFactors := [2, 19, 373] }])

theorem htauPrime7_22406023 : Nat.Prime 22406023 :=
  by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 263, 4733] }, .lucas { root := 5, primeFactors := [2, 7, 13] }])

theorem htauPrime7_25646167 : Nat.Prime 25646167 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 13, 17, 307] }])

theorem htauPrime7_37140797 : Nat.Prime 37140797 :=
  by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 11, 120587] }, .lucas { root := 2, primeFactors := [2, 60293] }, .lucas { root := 2, primeFactors := [2, 15073] }, .lucas { root := 5, primeFactors := [2, 3, 157] }])

theorem htauPrime7_88009573 : Nat.Prime 88009573 :=
  by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 7, 337, 3109] }, .lucas { root := 6, primeFactors := [2, 3, 7, 37] }])

theorem htauPrime7_113229229 : Nat.Prime 113229229 :=
  by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 1347967] }, .lucas { root := 6, primeFactors := [2, 3, 74887] }, .lucas { root := 3, primeFactors := [2, 3, 7, 1783] }, .lucas { root := 10, primeFactors := [2, 3, 11] }])

end OddPerfect.HarmonicChain
