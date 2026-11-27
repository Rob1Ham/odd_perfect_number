module

public import OddPerfect.PrimeRank5_3.Part022
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_3_528 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,461,1,0⟩, ⟨false,597,631,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 599 597 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,461,1,0⟩, ⟨false,599,631,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_529 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,461,1,0⟩, ⟨false,563,631,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 595 rank5_3_527 rank5_3_528

theorem rank5_3_530 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,489,1,0⟩, ⟨false,563,631,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 461 489 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,461,1,0⟩, ⟨false,563,631,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_3_510 rank5_3_529

theorem rank5_3_531 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,493,541,1,0⟩, ⟨false,563,631,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 509 493 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,509,541,1,0⟩, ⟨false,563,631,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_532 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,541,1,0⟩, ⟨false,563,639,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 631 639 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,541,1,0⟩, ⟨false,563,631,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 489 rank5_3_530 rank5_3_531

theorem rank5_3_533 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,541,1,0⟩, ⟨false,641,743,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_534 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,541,1,0⟩, ⟨false,563,743,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 639 rank5_3_532 rank5_3_533

theorem rank5_3_535 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,445,541,1,0⟩, ⟨false,563,743,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 449 445 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,541,1,0⟩, ⟨false,563,743,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_3_509 rank5_3_534

theorem rank5_3_536 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,541,1,0⟩, ⟨false,563,749,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 743 749 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,541,1,0⟩, ⟨false,563,743,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 441 rank5_3_508 rank5_3_535

theorem rank5_3_537 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,433,1,0⟩, ⟨false,751,1123,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_538 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨true,373,397,1,0⟩, ⟨false,751,887,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_539 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,381,1,0⟩, ⟨false,751,811,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 373 381 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,373,1,0⟩, ⟨false,751,811,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 3 11 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_540 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,385,397,1,0⟩, ⟨false,751,811,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 389 385 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,389,397,1,0⟩, ⟨false,751,811,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_541 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,397,1,0⟩, ⟨false,751,813,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 811 813 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,397,1,0⟩, ⟨false,751,811,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 381 rank5_3_539 rank5_3_540

theorem rank5_3_542 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,397,1,0⟩, ⟨false,815,887,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 821 815 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,397,1,0⟩, ⟨false,821,887,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_543 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,397,1,0⟩, ⟨false,751,887,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 813 rank5_3_541 rank5_3_542

theorem rank5_3_544 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,397,1,0⟩, ⟨false,751,887,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 6 rank5_3_538 rank5_3_543

theorem rank5_3_545 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,433,1,0⟩, ⟨false,751,887,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_546 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,433,1,0⟩, ⟨false,751,899,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 887 899 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,433,1,0⟩, ⟨false,751,887,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 397 rank5_3_544 rank5_3_545

theorem rank5_3_547 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,433,1,0⟩, ⟨false,901,1123,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 907 901 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,433,1,0⟩, ⟨false,907,1123,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_548 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,433,1,0⟩, ⟨false,751,1123,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 899 rank5_3_546 rank5_3_547

theorem rank5_3_549 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,441,1,0⟩, ⟨false,751,1123,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 433 441 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,433,1,0⟩, ⟨false,751,1123,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_3_537 rank5_3_548

theorem rank5_3_550 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,445,541,1,0⟩, ⟨false,751,1123,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 449 445 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,541,1,0⟩, ⟨false,751,1123,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_551 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,541,1,0⟩, ⟨false,751,1123,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 441 rank5_3_549 rank5_3_550

end OddPerfect.SpoofBox
