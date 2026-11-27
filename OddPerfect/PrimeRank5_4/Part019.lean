module

public import OddPerfect.PrimeRank5_4.Part018
import OddPerfect.PrimeRank5_4.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_432 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨true,1093,1449,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1433 1449 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨true,1093,1433,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1237 rank5_4_430 rank5_4_431

theorem rank5_4_433 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨true,1453,2161,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_434 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨true,1093,2161,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1449 rank5_4_432 rank5_4_433

theorem rank5_4_435 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨true,1093,2185,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2161 2185 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨true,1093,2161,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_4_425 rank5_4_434

theorem rank5_4_436 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨true,2189,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2213 2189 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨true,2213,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_437 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨true,1085,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1093 1085 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨true,1093,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 2185 rank5_4_435 rank5_4_436

theorem rank5_4_438 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,2⟩, ⟨false,167,331,2,0⟩, ⟨true,541,0,1,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 2 3 307 (by norm_num) (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨true,541,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1081 rank5_4_424 rank5_4_437

theorem rank5_4_439 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,167,221,2,0⟩, ⟨true,541,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 211 221 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,167,211,2,0⟩, ⟨true,541,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_440 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,223,265,2,0⟩, ⟨true,541,1069,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 263 265 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,223,263,2,0⟩, ⟨true,541,1069,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_441 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,331,2,0⟩, ⟨true,541,717,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 709 717 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,331,2,0⟩, ⟨true,541,709,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_442 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,331,2,0⟩, ⟨true,733,1069,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_443 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,331,2,0⟩, ⟨true,733,1069,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_444 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,331,2,0⟩, ⟨true,721,1069,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 733 721 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,331,2,0⟩, ⟨true,733,1069,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_4_442 rank5_4_443

theorem rank5_4_445 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,267,331,2,0⟩, ⟨true,541,1069,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 269 267 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,331,2,0⟩, ⟨true,541,1069,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 717 rank5_4_441 rank5_4_444

theorem rank5_4_446 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,223,331,2,0⟩, ⟨true,541,1081,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1069 1081 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,223,331,2,0⟩, ⟨true,541,1069,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 265 rank5_4_440 rank5_4_445

theorem rank5_4_447 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,223,263,2,0⟩, ⟨true,1093,2185,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2161 2185 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,223,263,2,0⟩, ⟨true,1093,2161,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_448 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,223,263,2,0⟩, ⟨true,2213,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_449 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,223,241,2,0⟩, ⟨true,2213,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_450 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,251,263,2,0⟩, ⟨true,2213,4425,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 4421 4425 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,251,263,2,0⟩, ⟨true,2213,4421,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_451 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨false,251,263,2,0⟩, ⟨true,4441,8861,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_4_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_452 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,251,263,2,0⟩, ⟨true,4441,8861,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_453 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,251,263,2,0⟩, ⟨true,4441,8881,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 8861 8881 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,251,263,2,0⟩, ⟨true,4441,8861,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_4_451 rank5_4_452

theorem rank5_4_454 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨false,251,263,2,0⟩, ⟨true,8893,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_4_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_455 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,251,255,2,0⟩, ⟨true,8893,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 251 255 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,251,251,2,0⟩, ⟨true,8893,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
