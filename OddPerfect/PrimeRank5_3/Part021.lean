module

public import OddPerfect.PrimeRank5_3.Part020
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_3_480 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,401,1,0⟩, ⟨false,673,683,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 67 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_481 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,405,409,1,0⟩, ⟨false,673,683,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 409 405 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,409,409,1,0⟩, ⟨false,673,683,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 3 41 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_482 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,409,1,0⟩, ⟨false,673,683,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 401 rank5_3_480 rank5_3_481

theorem rank5_3_483 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,409,1,0⟩, ⟨false,663,683,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 673 663 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,409,1,0⟩, ⟨false,673,683,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_3_479 rank5_3_482

theorem rank5_3_484 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,413,1,0⟩, ⟨false,641,683,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 409 413 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,409,1,0⟩, ⟨false,641,683,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 661 rank5_3_478 rank5_3_483

theorem rank5_3_485 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,421,433,1,0⟩, ⟨false,641,661,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_486 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,421,425,1,0⟩, ⟨false,641,661,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 421 425 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,421,421,1,0⟩, ⟨false,641,661,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 3 211 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_487 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,429,433,1,0⟩, ⟨false,641,661,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 433 429 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,433,433,1,0⟩, ⟨false,641,661,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 3 7 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_488 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,421,433,1,0⟩, ⟨false,641,661,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 425 rank5_3_486 rank5_3_487

theorem rank5_3_489 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,421,433,1,0⟩, ⟨false,641,661,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_3_485 rank5_3_488

theorem rank5_3_490 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,421,433,1,0⟩, ⟨false,663,683,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 673 663 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,421,433,1,0⟩, ⟨false,673,683,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_491 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,417,433,1,0⟩, ⟨false,641,683,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 421 417 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,421,433,1,0⟩, ⟨false,641,683,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 661 rank5_3_489 rank5_3_490

theorem rank5_3_492 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,433,1,0⟩, ⟨false,641,683,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 413 rank5_3_484 rank5_3_491

theorem rank5_3_493 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,433,1,0⟩, ⟨false,641,687,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 683 687 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,433,1,0⟩, ⟨false,641,683,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_3_477 rank5_3_492

theorem rank5_3_494 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨true,401,433,1,0⟩, ⟨false,691,743,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_495 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,409,1,0⟩, ⟨false,691,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_496 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,401,1,0⟩, ⟨false,691,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 67 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_497 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,405,409,1,0⟩, ⟨false,691,709,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 409 405 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,409,409,1,0⟩, ⟨false,691,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 3 41 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_498 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,409,1,0⟩, ⟨false,691,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 401 rank5_3_496 rank5_3_497

theorem rank5_3_499 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,409,1,0⟩, ⟨false,691,715,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 709 715 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,409,1,0⟩, ⟨false,691,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_3_495 rank5_3_498

theorem rank5_3_500 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,409,1,0⟩, ⟨false,717,743,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 719 717 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,409,1,0⟩, ⟨false,719,743,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_501 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,413,1,0⟩, ⟨false,691,743,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 409 413 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,409,1,0⟩, ⟨false,691,743,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 715 rank5_3_499 rank5_3_500

theorem rank5_3_502 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,417,433,1,0⟩, ⟨false,691,743,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 421 417 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,421,433,1,0⟩, ⟨false,691,743,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_503 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,433,1,0⟩, ⟨false,691,743,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 413 rank5_3_501 rank5_3_502

end OddPerfect.SpoofBox
