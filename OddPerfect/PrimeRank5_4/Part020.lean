module

public import OddPerfect.PrimeRank5_4.Part019
import OddPerfect.PrimeRank5_4.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_456 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,263,2,0⟩, ⟨true,8893,17761,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_457 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,259,2,0⟩, ⟨true,8893,17761,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 257 259 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨true,8893,17761,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_458 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,4⟩, ⟨false,263,263,2,0⟩, ⟨true,8893,9473,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 88741 rank5_4_prime88741 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_459 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨true,8893,9473,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_4_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_460 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨true,8893,9473,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_461 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨true,8893,9473,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_4_459 rank5_4_460

theorem rank5_4_462 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,263,2,0⟩, ⟨true,8893,9473,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 4 rank5_4_458 rank5_4_461

theorem rank5_4_463 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,4⟩, ⟨false,263,263,2,0⟩, ⟨true,9497,10141,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 88741 rank5_4_prime88741 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_464 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨true,9497,10141,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_4_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_465 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,8⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨true,9497,10141,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_466 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨true,9497,9561,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 9533 9561 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨true,9497,9533,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_467 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨true,9565,9629,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 9601 9565 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨true,9601,9629,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_468 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨true,9497,9633,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 9629 9633 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨true,9497,9629,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 9561 rank5_4_466 rank5_4_467

theorem rank5_4_469 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨true,9637,9781,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 9649 9637 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨true,9649,9781,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_470 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨true,9497,9805,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 9781 9805 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨true,9497,9781,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 9633 rank5_4_468 rank5_4_469

theorem rank5_4_471 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨true,9809,10141,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 9817 9809 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨true,9817,10141,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_472 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨true,9497,10141,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 9805 rank5_4_470 rank5_4_471

theorem rank5_4_473 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨true,9497,10141,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 8 rank5_4_465 rank5_4_472

theorem rank5_4_474 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨true,9497,10141,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_4_464 rank5_4_473

theorem rank5_4_475 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,263,2,0⟩, ⟨true,9477,10141,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 9497 9477 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,263,2,0⟩, ⟨true,9497,10141,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_4_463 rank5_4_474

theorem rank5_4_476 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,263,2,0⟩, ⟨true,8893,10153,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 10141 10153 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,263,2,0⟩, ⟨true,8893,10141,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 9473 rank5_4_462 rank5_4_475

theorem rank5_4_477 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,263,2,0⟩, ⟨true,10157,11833,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 10169 10157 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,263,2,0⟩, ⟨true,10169,11833,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_478 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,263,2,0⟩, ⟨true,8893,11849,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 11833 11849 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,263,2,0⟩, ⟨true,8893,11833,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 10153 rank5_4_476 rank5_4_477

theorem rank5_4_479 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,263,2,0⟩, ⟨true,11853,17761,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 11897 11853 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,263,2,0⟩, ⟨true,11897,17761,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
