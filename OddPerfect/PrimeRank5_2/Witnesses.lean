module

public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.SpoofBox

theorem rank5_2_prime1093 : Nat.Prime 1093 :=
  by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13] }])

theorem rank5_2_prime1871 : Nat.Prime 1871 :=
  by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 5, 11, 17] }])

theorem rank5_2_prime8269 : Nat.Prime 8269 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 53] }])

theorem rank5_2_prime19531 : Nat.Prime 19531 :=
  by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 31] }])

theorem rank5_2_prime797161 : Nat.Prime 797161 :=
  by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 7, 13, 73] }])

theorem rank5_2_prime12207031 : Nat.Prime 12207031 :=
  by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11, 71, 521] }])

end OddPerfect.SpoofBox
