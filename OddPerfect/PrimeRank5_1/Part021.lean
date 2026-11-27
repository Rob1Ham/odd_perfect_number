module

public import OddPerfect.PrimeRank5_1.Part020
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_480 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,137,139,2,0⟩, ⟨false,353,367,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 359 rank5_1_472 rank5_1_479

theorem rank5_1_481 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,137,139,2,0⟩, ⟨false,369,383,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 373 369 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,137,139,2,0⟩, ⟨false,373,383,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_482 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,137,139,2,0⟩, ⟨false,353,383,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 367 rank5_1_480 rank5_1_481

theorem rank5_1_483 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,137,139,2,0⟩, ⟨false,385,421,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 389 385 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,137,139,2,0⟩, ⟨false,389,421,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_484 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,133,139,2,0⟩, ⟨false,353,421,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 137 133 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,137,139,2,0⟩, ⟨false,353,421,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 383 rank5_1_482 rank5_1_483

theorem rank5_1_485 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,127,139,2,0⟩, ⟨false,353,421,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 131 rank5_1_463 rank5_1_484

theorem rank5_1_486 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,127,139,2,0⟩, ⟨false,353,421,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 8 rank5_1_448 rank5_1_485

theorem rank5_1_487 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,127,139,2,0⟩, ⟨false,431,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_488 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,127,127,2,0⟩, ⟨false,431,447,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 443 447 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,127,127,2,0⟩, ⟨false,431,443,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_489 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,4⟩, ⟨false,127,127,2,0⟩, ⟨false,449,467,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 3221 rank5_1_prime3221 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_490 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,127,127,2,0⟩, ⟨false,449,467,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_491 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,127,127,2,0⟩, ⟨false,449,457,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_492 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,127,127,2,0⟩, ⟨false,461,463,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_493 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,127,127,2,0⟩, ⟨false,465,467,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 467 465 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,127,127,2,0⟩, ⟨false,467,467,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_494 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,127,127,2,0⟩, ⟨false,459,467,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 461 459 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,127,127,2,0⟩, ⟨false,461,467,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 463 rank5_1_492 rank5_1_493

theorem rank5_1_495 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,127,127,2,0⟩, ⟨false,449,467,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 457 rank5_1_491 rank5_1_494

theorem rank5_1_496 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,127,127,2,0⟩, ⟨false,449,467,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_1_490 rank5_1_495

theorem rank5_1_497 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,127,127,2,0⟩, ⟨false,449,467,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 4 rank5_1_489 rank5_1_496

theorem rank5_1_498 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,127,127,2,0⟩, ⟨false,431,467,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 447 rank5_1_488 rank5_1_497

theorem rank5_1_499 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,129,131,2,0⟩, ⟨false,431,467,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 131 129 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,131,131,2,0⟩, ⟨false,431,467,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_500 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,127,131,2,0⟩, ⟨false,431,471,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 467 471 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,127,131,2,0⟩, ⟨false,431,467,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 127 rank5_1_498 rank5_1_499

theorem rank5_1_501 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,127,131,2,0⟩, ⟨false,473,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 479 473 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,127,131,2,0⟩, ⟨false,479,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_502 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,127,131,2,0⟩, ⟨false,431,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 471 rank5_1_500 rank5_1_501

theorem rank5_1_503 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,133,139,2,0⟩, ⟨false,431,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 137 133 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,137,139,2,0⟩, ⟨false,431,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
