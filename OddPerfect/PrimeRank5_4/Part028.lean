module

public import OddPerfect.PrimeRank5_4.Part027
import OddPerfect.PrimeRank5_4.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_648 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,277,2,0⟩, ⟨true,2953,3533,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 3217 rank5_4_636 rank5_4_647

theorem rank5_4_649 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,273,277,2,0⟩, ⟨true,2953,3533,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 277 273 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,277,2,0⟩, ⟨true,2953,3533,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_4_635 rank5_4_648

theorem rank5_4_650 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,277,2,0⟩, ⟨true,2953,3537,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 3533 3537 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,277,2,0⟩, ⟨true,2953,3533,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 271 rank5_4_634 rank5_4_649

theorem rank5_4_651 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,271,2,0⟩, ⟨true,3541,4421,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_652 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,273,277,2,0⟩, ⟨true,3541,4421,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 277 273 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,277,2,0⟩, ⟨true,3541,4421,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_653 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,277,2,0⟩, ⟨true,3541,4421,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 271 rank5_4_651 rank5_4_652

theorem rank5_4_654 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,277,2,0⟩, ⟨true,2953,4421,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 3537 rank5_4_650 rank5_4_653

theorem rank5_4_655 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,277,2,0⟩, ⟨true,2953,4421,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 6 rank5_4_633 rank5_4_654

theorem rank5_4_656 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,279,2,0⟩, ⟨true,2213,4421,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 277 279 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,277,2,0⟩, ⟨true,2213,4421,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 2949 rank5_4_632 rank5_4_655

theorem rank5_4_657 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨false,281,293,2,0⟩, ⟨true,2213,2917,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_4_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_658 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,283,2,0⟩, ⟨true,2213,2513,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2477 2513 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,283,2,0⟩, ⟨true,2213,2477,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_659 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,283,2,0⟩, ⟨true,2521,2917,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_660 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,283,2,0⟩, ⟨true,2521,2601,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2593 2601 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,283,2,0⟩, ⟨true,2521,2593,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_661 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,281,2,0⟩, ⟨true,2609,2693,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_662 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,283,283,2,0⟩, ⟨true,2609,2649,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2633 2649 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,283,283,2,0⟩, ⟨true,2609,2633,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_663 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,4⟩, ⟨false,283,283,2,0⟩, ⟨true,2657,2693,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 88741 rank5_4_prime88741 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_664 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,283,283,2,0⟩, ⟨true,2657,2693,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_4_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_665 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,8⟩, ⟨false,17,17,6,0⟩, ⟨false,283,283,2,0⟩, ⟨true,2657,2693,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_666 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,283,283,2,0⟩, ⟨true,2657,2673,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2657 2673 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,283,283,2,0⟩, ⟨true,2657,2657,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 443 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_667 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,283,283,2,0⟩, ⟨true,2677,2693,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_668 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,283,283,2,0⟩, ⟨true,2657,2693,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2673 rank5_4_666 rank5_4_667

theorem rank5_4_669 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,283,283,2,0⟩, ⟨true,2657,2693,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 8 rank5_4_665 rank5_4_668

theorem rank5_4_670 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,283,283,2,0⟩, ⟨true,2657,2693,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_4_664 rank5_4_669

theorem rank5_4_671 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,283,283,2,0⟩, ⟨true,2653,2693,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2657 2653 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,283,283,2,0⟩, ⟨true,2657,2693,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_4_663 rank5_4_670

end OddPerfect.SpoofBox
