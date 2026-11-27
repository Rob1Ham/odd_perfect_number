module

public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.SpoofBox

theorem rank5_4_prime1093 : Nat.Prime 1093 :=
  by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13] }])

theorem rank5_4_prime1597 : Nat.Prime 1597 :=
  by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 19] }])

theorem rank5_4_prime1871 : Nat.Prime 1871 :=
  by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 5, 11, 17] }])

theorem rank5_4_prime2801 : Nat.Prime 2801 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7] }])

theorem rank5_4_prime3169 : Nat.Prime 3169 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11] }])

theorem rank5_4_prime4591 : Nat.Prime 4591 :=
  by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 17] }])

theorem rank5_4_prime10303 : Nat.Prime 10303 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 101] }])

theorem rank5_4_prime19531 : Nat.Prime 19531 :=
  by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 31] }])

theorem rank5_4_prime30941 : Nat.Prime 30941 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 13, 17] }])

theorem rank5_4_prime32749 : Nat.Prime 32749 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 2729] }, .lucas { root := 3, primeFactors := [2, 11, 31] }])

theorem rank5_4_prime88741 : Nat.Prime 88741 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17, 29] }])

theorem rank5_4_prime797161 : Nat.Prime 797161 :=
  by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 7, 13, 73] }])

theorem rank5_4_prime12207031 : Nat.Prime 12207031 :=
  by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11, 71, 521] }])

theorem rank5_4_prime25646167 : Nat.Prime 25646167 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 13, 17, 307] }])

end OddPerfect.SpoofBox
