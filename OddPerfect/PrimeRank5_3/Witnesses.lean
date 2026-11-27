module

public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.SpoofBox

theorem rank5_3_prime12207031 : Nat.Prime 12207031 :=
  by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11, 71, 521] }])

end OddPerfect.SpoofBox
