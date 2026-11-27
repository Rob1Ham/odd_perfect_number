module

public import OddPerfect.PrimeRank5_4.Part021
import OddPerfect.PrimeRank5_4.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_504 : PrimeCovered (#v[⟨false,3,3,20,0⟩, ⟨false,5,5,12,12⟩, ⟨false,17,17,8,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65517,65537,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 65521 65517 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,20,0⟩, ⟨false,5,5,12,12⟩, ⟨false,17,17,8,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65521,65537,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 65525 rank5_4_502 rank5_4_503

theorem rank5_4_505 : PrimeCovered (#v[⟨false,3,3,20,0⟩, ⟨false,5,5,12,12⟩, ⟨false,17,17,8,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65497,65537,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 65513 rank5_4_501 rank5_4_504

theorem rank5_4_506 : PrimeCovered (#v[⟨false,3,3,20,0⟩, ⟨false,5,5,14,0⟩, ⟨false,17,17,8,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65497,65513,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 65497 65513 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,20,0⟩, ⟨false,5,5,14,0⟩, ⟨false,17,17,8,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65497,65497,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 32749 rank5_4_prime32749 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_507 : PrimeCovered (#v[⟨false,3,3,20,0⟩, ⟨false,5,5,14,0⟩, ⟨false,17,17,8,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65521,65525,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 65521 65525 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,20,0⟩, ⟨false,5,5,14,0⟩, ⟨false,17,17,8,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65521,65521,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 181 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_508 : PrimeCovered (#v[⟨false,3,3,20,0⟩, ⟨false,5,5,14,0⟩, ⟨false,17,17,8,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65529,65537,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 65537 65529 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,20,0⟩, ⟨false,5,5,14,0⟩, ⟨false,17,17,8,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65537,65537,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_509 : PrimeCovered (#v[⟨false,3,3,20,0⟩, ⟨false,5,5,14,0⟩, ⟨false,17,17,8,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65517,65537,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 65521 65517 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,20,0⟩, ⟨false,5,5,14,0⟩, ⟨false,17,17,8,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65521,65537,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 65525 rank5_4_507 rank5_4_508

theorem rank5_4_510 : PrimeCovered (#v[⟨false,3,3,20,0⟩, ⟨false,5,5,14,0⟩, ⟨false,17,17,8,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65497,65537,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 65513 rank5_4_506 rank5_4_509

theorem rank5_4_511 : PrimeCovered (#v[⟨false,3,3,20,0⟩, ⟨false,5,5,12,0⟩, ⟨false,17,17,8,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65497,65537,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 12 rank5_4_505 rank5_4_510

theorem rank5_4_512 : PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨false,5,5,12,0⟩, ⟨false,17,17,8,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65493,65537,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 65497 65493 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨false,5,5,12,0⟩, ⟨false,17,17,8,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65497,65537,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 18 rank5_4_500 rank5_4_511

theorem rank5_4_513 : PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨false,5,5,12,0⟩, ⟨false,17,17,8,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65449,65537,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 65489 rank5_4_499 rank5_4_512

theorem rank5_4_514 : PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨false,5,5,12,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65445,65537,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 65449 65445 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨false,5,5,12,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65449,65537,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 6 rank5_4_498 rank5_4_513

theorem rank5_4_515 : PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨false,5,5,12,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65321,65537,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 65353 65321 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨false,5,5,12,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65353,65537,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 65441 rank5_4_497 rank5_4_514

theorem rank5_4_516 : PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨false,5,5,12,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65101,65537,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 65317 rank5_4_496 rank5_4_515

theorem rank5_4_517 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65101,65541,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 65537 65541 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65101,65537,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 16 rank5_4_495 rank5_4_516

theorem rank5_4_518 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65545,65993,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 65557 65545 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65557,65993,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_519 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65101,65993,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 65541 rank5_4_517 rank5_4_518

theorem rank5_4_520 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65101,66025,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 65993 66025 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65101,65993,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 10 rank5_4_494 rank5_4_519

theorem rank5_4_521 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨true,66029,66977,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_522 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65097,66977,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 65101 65097 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65101,66977,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 66025 rank5_4_520 rank5_4_521

theorem rank5_4_523 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨true,63313,66977,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 65093 rank5_4_493 rank5_4_522

theorem rank5_4_524 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨true,63313,66977,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .exponent 2 rank5_4_492 rank5_4_523

theorem rank5_4_525 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨true,63313,67005,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 66977 67005 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨true,63313,66977,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 14 rank5_4_491 rank5_4_524

theorem rank5_4_526 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨true,67009,71161,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 67021 67009 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨true,67021,71161,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_527 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨true,63293,71161,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 63313 63293 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨true,63313,71161,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 67005 rank5_4_525 rank5_4_526

end OddPerfect.SpoofBox
