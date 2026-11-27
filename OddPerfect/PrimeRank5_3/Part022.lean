module

public import OddPerfect.PrimeRank5_3.Part021
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_3_504 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,433,1,0⟩, ⟨false,689,743,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 691 689 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,433,1,0⟩, ⟨false,691,743,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_3_494 rank5_3_503

theorem rank5_3_505 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,401,433,1,0⟩, ⟨false,641,743,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 687 rank5_3_493 rank5_3_504

theorem rank5_3_506 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,433,1,0⟩, ⟨false,641,743,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 397 rank5_3_476 rank5_3_505

theorem rank5_3_507 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,433,1,0⟩, ⟨false,563,743,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 639 rank5_3_463 rank5_3_506

theorem rank5_3_508 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,441,1,0⟩, ⟨false,563,743,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 433 441 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,433,1,0⟩, ⟨false,563,743,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_3_448 rank5_3_507

theorem rank5_3_509 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,541,1,0⟩, ⟨false,563,743,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_510 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨true,449,461,1,0⟩, ⟨false,563,631,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_511 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,461,1,0⟩, ⟨false,563,593,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_512 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,453,1,0⟩, ⟨false,563,577,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 449 453 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,449,1,0⟩, ⟨false,563,577,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_513 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,457,461,1,0⟩, ⟨false,563,569,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_514 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,457,457,1,0⟩, ⟨false,571,577,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 229 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_515 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,461,461,1,0⟩, ⟨false,571,577,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 7 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_516 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,457,461,1,0⟩, ⟨false,571,577,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 457 rank5_3_514 rank5_3_515

theorem rank5_3_517 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,457,461,1,0⟩, ⟨false,563,577,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 569 rank5_3_513 rank5_3_516

theorem rank5_3_518 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,461,1,0⟩, ⟨false,563,577,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 453 rank5_3_512 rank5_3_517

theorem rank5_3_519 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,449,1,1⟩, ⟨false,587,589,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 587 589 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,449,1,1⟩, ⟨false,587,587,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_520 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,449,1,1⟩, ⟨false,591,593,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 593 591 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,449,1,1⟩, ⟨false,593,593,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_521 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,449,1,1⟩, ⟨false,587,593,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 589 rank5_3_519 rank5_3_520

theorem rank5_3_522 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,449,5,0⟩, ⟨false,587,593,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_523 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,453,1,0⟩, ⟨false,587,593,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 449 453 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,449,1,0⟩, ⟨false,587,593,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .exponent 1 rank5_3_521 rank5_3_522

theorem rank5_3_524 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,457,461,1,0⟩, ⟨false,587,593,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_525 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,461,1,0⟩, ⟨false,579,593,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 587 579 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,461,1,0⟩, ⟨false,587,593,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 453 rank5_3_523 rank5_3_524

theorem rank5_3_526 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,461,1,0⟩, ⟨false,563,593,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 577 rank5_3_518 rank5_3_525

theorem rank5_3_527 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,461,1,0⟩, ⟨false,563,595,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 593 595 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,461,1,0⟩, ⟨false,563,593,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_3_511 rank5_3_526

end OddPerfect.SpoofBox
