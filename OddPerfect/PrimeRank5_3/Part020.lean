module

public import OddPerfect.PrimeRank5_3.Part019
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_3_456 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,429,433,1,0⟩, ⟨false,617,631,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 433 429 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,433,433,1,0⟩, ⟨false,617,631,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 3 7 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_457 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,421,433,1,0⟩, ⟨false,615,631,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 617 615 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,421,433,1,0⟩, ⟨false,617,631,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 425 rank5_3_455 rank5_3_456

theorem rank5_3_458 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,421,433,1,0⟩, ⟨false,599,631,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 613 rank5_3_454 rank5_3_457

theorem rank5_3_459 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,417,433,1,0⟩, ⟨false,599,631,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 421 417 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,421,433,1,0⟩, ⟨false,599,631,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_3_453 rank5_3_458

theorem rank5_3_460 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,433,1,0⟩, ⟨false,597,631,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 599 597 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,433,1,0⟩, ⟨false,599,631,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 413 rank5_3_452 rank5_3_459

theorem rank5_3_461 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,433,1,0⟩, ⟨false,563,631,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 595 rank5_3_451 rank5_3_460

theorem rank5_3_462 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,433,1,0⟩, ⟨false,563,631,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 6 rank5_3_450 rank5_3_461

theorem rank5_3_463 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,433,1,0⟩, ⟨false,563,639,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 631 639 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,433,1,0⟩, ⟨false,563,631,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 397 rank5_3_449 rank5_3_462

theorem rank5_3_464 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,397,1,0⟩, ⟨false,641,687,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 683 687 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,397,1,0⟩, ⟨false,641,683,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_465 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨true,373,397,1,0⟩, ⟨false,691,743,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_466 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,381,1,0⟩, ⟨false,691,743,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 373 381 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,373,1,0⟩, ⟨false,691,743,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 3 11 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_467 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,389,397,1,0⟩, ⟨false,691,715,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 709 715 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,389,397,1,0⟩, ⟨false,691,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_468 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,389,397,1,0⟩, ⟨false,719,743,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_469 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,389,389,1,0⟩, ⟨false,719,743,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 13 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_470 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,393,397,1,0⟩, ⟨false,719,743,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 397 393 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,397,397,1,0⟩, ⟨false,719,743,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 3 199 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_471 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,389,397,1,0⟩, ⟨false,719,743,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 389 rank5_3_469 rank5_3_470

theorem rank5_3_472 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,389,397,1,0⟩, ⟨false,717,743,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 719 717 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,389,397,1,0⟩, ⟨false,719,743,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_3_468 rank5_3_471

theorem rank5_3_473 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,385,397,1,0⟩, ⟨false,691,743,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 389 385 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,389,397,1,0⟩, ⟨false,691,743,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 715 rank5_3_467 rank5_3_472

theorem rank5_3_474 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,397,1,0⟩, ⟨false,691,743,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 381 rank5_3_466 rank5_3_473

theorem rank5_3_475 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,397,1,0⟩, ⟨false,689,743,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 691 689 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,397,1,0⟩, ⟨false,691,743,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_3_465 rank5_3_474

theorem rank5_3_476 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,397,1,0⟩, ⟨false,641,743,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 687 rank5_3_464 rank5_3_475

theorem rank5_3_477 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨true,401,433,1,0⟩, ⟨false,641,683,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_478 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,409,1,0⟩, ⟨false,641,661,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_479 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,409,1,0⟩, ⟨false,673,683,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

end OddPerfect.SpoofBox
