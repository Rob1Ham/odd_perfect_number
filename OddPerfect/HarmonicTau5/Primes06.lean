module

public import OddPerfect.HarmonicTau5.Primes05
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain

open FactorBudget

set_option maxRecDepth 16000

theorem htauPrime5_55918991 : Nat.Prime 55918991 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 5591899] }, .lucas { root := 2, primeFactors := [2, 3, 13, 23, 1039] }, .lucas { root := 3, primeFactors := [2, 3, 173] }])

theorem htauPrime5_60671251 : Nat.Prime 60671251 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 5393] }, .lucas { root := 3, primeFactors := [2, 337] }])

theorem htauPrime5_68053211 : Nat.Prime 68053211 :=
  by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 17, 400313] }, .lucas { root := 3, primeFactors := [2, 11, 4549] }, .lucas { root := 6, primeFactors := [2, 3, 379] }])

theorem htauPrime5_91525691 : Nat.Prime 91525691 :=
  by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 9152569] }, .lucas { root := 11, primeFactors := [2, 3, 42373] }, .lucas { root := 5, primeFactors := [2, 3, 11, 107] }])

theorem htauPrime5_93249971 : Nat.Prime 93249971 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 847727] }, .lucas { root := 5, primeFactors := [2, 11, 31, 113] }])

theorem htauPrime5_93853931 : Nat.Prime 93853931 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 181, 51853] }, .lucas { root := 11, primeFactors := [2, 3, 29, 149] }])

theorem htauPrime5_95483851 : Nat.Prime 95483851 :=
  by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 7, 11, 1181] }, .lucas { root := 7, primeFactors := [2, 5, 59] }])

theorem htauPrime5_104670301 : Nat.Prime 104670301 :=
  by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 49843] }, .lucas { root := 2, primeFactors := [2, 3, 13, 71] }])

theorem htauPrime5_160479461 : Nat.Prime 160479461 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 89, 1013] }])

theorem htauPrime5_169942181 : Nat.Prime 169942181 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 883, 9623] }, .lucas { root := 5, primeFactors := [2, 17, 283] }])

theorem htauPrime5_170638711 : Nat.Prime 170638711 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 11, 517087] }, .lucas { root := 3, primeFactors := [2, 3, 23, 1249] }, .lucas { root := 7, primeFactors := [2, 3, 13] }])

theorem htauPrime5_183201841 : Nat.Prime 183201841 :=
  by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 5, 254447] }, .lucas { root := 5, primeFactors := [2, 29, 41, 107] }])

theorem htauPrime5_189340631 : Nat.Prime 189340631 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 109, 173707] }, .lucas { root := 2, primeFactors := [2, 3, 13, 17, 131] }])

theorem htauPrime5_203447171 : Nat.Prime 203447171 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 3083, 6599] }, .lucas { root := 2, primeFactors := [2, 23, 67] }, .lucas { root := 13, primeFactors := [2, 3299] }, .lucas { root := 2, primeFactors := [2, 17, 97] }])

theorem htauPrime5_208097431 : Nat.Prime 208097431 :=
  by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 131, 52951] }, .lucas { root := 3, primeFactors := [2, 3, 5, 353] }])

theorem htauPrime5_251101831 : Nat.Prime 251101831 :=
  by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 1195723] }, .lucas { root := 2, primeFactors := [2, 3, 11, 61] }])

theorem htauPrime5_262209281 : Nat.Prime 262209281 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 127, 1613] }, .lucas { root := 3, primeFactors := [2, 13, 31] }])

theorem htauPrime5_398137391 : Nat.Prime 398137391 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 37, 347, 443] }])

theorem htauPrime5_461955121 : Nat.Prime 461955121 :=
  by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 11, 233, 751] }])

theorem htauPrime5_478851301 : Nat.Prime 478851301 :=
  by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 19, 41, 683] }])

theorem htauPrime5_647251721 : Nat.Prime 647251721 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 19, 851647] }, .lucas { root := 3, primeFactors := [2, 3, 141941] }, .lucas { root := 2, primeFactors := [2, 5, 47, 151] }])

theorem htauPrime5_827607071 : Nat.Prime 827607071 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 3251, 25457] }, .lucas { root := 6, primeFactors := [2, 5, 13] }, .lucas { root := 3, primeFactors := [2, 37, 43] }])

theorem htauPrime5_875335231 : Nat.Prime 875335231 :=
  by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 11, 126311] }, .lucas { root := 23, primeFactors := [2, 5, 17, 743] }])

theorem htauPrime5_895781311 : Nat.Prime 895781311 :=
  by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 5, 29859377] }, .lucas { root := 3, primeFactors := [2, 1866211] }, .lucas { root := 2, primeFactors := [2, 3, 5, 62207] }, .lucas { root := 5, primeFactors := [2, 19, 1637] }, .lucas { root := 2, primeFactors := [2, 409] }])

theorem htauPrime5_996625831 : Nat.Prime 996625831 :=
  by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 139, 199, 1201] }, .lucas { root := 11, primeFactors := [2, 3, 5] }])

theorem htauPrime5_1394714501 : Nat.Prime 1394714501 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 97, 149, 193] }])

theorem htauPrime5_2229158741 : Nat.Prime 2229158741 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 111457937] }, .lucas { root := 3, primeFactors := [2, 577, 12073] }, .lucas { root := 7, primeFactors := [2, 3, 503] }])

theorem htauPrime5_2666986681 : Nat.Prime 2666986681 :=
  by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 19, 227, 5153] }, .lucas { root := 5, primeFactors := [2, 7, 23] }])

theorem htauPrime5_3021473501 : Nat.Prime 3021473501 :=
  by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 79, 76493] }, .lucas { root := 2, primeFactors := [2, 13, 1471] }, .lucas { root := 6, primeFactors := [2, 3, 5, 7] }])

theorem htauPrime5_3276517921 : Nat.Prime 3276517921 :=
  by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 13, 239] }])

theorem htauPrime5_3703062191 : Nat.Prime 3703062191 :=
  by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 5, 19, 41, 127, 197] }])

theorem htauPrime5_4448157781 : Nat.Prime 4448157781 :=
  by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 17, 396449] }, .lucas { root := 3, primeFactors := [2, 13, 953] }])

end OddPerfect.HarmonicChain
