module

public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.SpoofBox

theorem rank5_1_prime1093 : Nat.Prime 1093 :=
  by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13] }])

theorem rank5_1_prime1723 : Nat.Prime 1723 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 41] }])

theorem rank5_1_prime1801 : Nat.Prime 1801 :=
  by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5] }])

theorem rank5_1_prime1871 : Nat.Prime 1871 :=
  by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 5, 11, 17] }])

theorem rank5_1_prime3169 : Nat.Prime 3169 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11] }])

theorem rank5_1_prime3221 : Nat.Prime 3221 :=
  by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 5, 7, 23] }])

theorem rank5_1_prime3541 : Nat.Prime 3541 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 59] }])

theorem rank5_1_prime3571 : Nat.Prime 3571 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 17] }])

theorem rank5_1_prime3851 : Nat.Prime 3851 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 11] }])

theorem rank5_1_prime8011 : Nat.Prime 8011 :=
  by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 89] }])

theorem rank5_1_prime10303 : Nat.Prime 10303 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 101] }])

theorem rank5_1_prime30941 : Nat.Prime 30941 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 13, 17] }])

theorem rank5_1_prime88741 : Nat.Prime 88741 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17, 29] }])

theorem rank5_1_prime292561 : Nat.Prime 292561 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 23, 53] }])

theorem rank5_1_prime797161 : Nat.Prime 797161 :=
  by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 7, 13, 73] }])

end OddPerfect.SpoofBox
