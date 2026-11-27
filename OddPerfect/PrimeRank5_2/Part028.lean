module

public import OddPerfect.PrimeRank5_2.Part027
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_648 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3313,3389,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_2_638 rank5_2_647

theorem rank5_2_649 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3391,3469,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_650 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3313,3469,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 3389 rank5_2_648 rank5_2_649

theorem rank5_2_651 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3165,3469,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 3167 3165 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3167,3469,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 3311 rank5_2_637 rank5_2_650

theorem rank5_2_652 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,279,2,0⟩, ⟨false,2909,3469,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 277 279 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,277,2,0⟩, ⟨false,2909,3469,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 3163 rank5_2_636 rank5_2_651

theorem rank5_2_653 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,281,283,2,0⟩, ⟨false,2909,3469,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_654 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,283,2,0⟩, ⟨false,2909,3469,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 279 rank5_2_652 rank5_2_653

theorem rank5_2_655 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,283,2,0⟩, ⟨false,2909,3487,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 3469 3487 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,283,2,0⟩, ⟨false,2909,3469,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_2_635 rank5_2_654

theorem rank5_2_656 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,283,2,0⟩, ⟨false,3489,4357,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 3491 3489 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,283,2,0⟩, ⟨false,3491,4357,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_657 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,283,2,0⟩, ⟨false,2909,4357,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 3487 rank5_2_655 rank5_2_656

theorem rank5_2_658 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,283,2,0⟩, ⟨false,2907,4357,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2909 2907 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,283,2,0⟩, ⟨false,2909,4357,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_2_634 rank5_2_657

theorem rank5_2_659 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,273,283,2,0⟩, ⟨false,2179,4357,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 277 273 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,283,2,0⟩, ⟨false,2179,4357,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 2905 rank5_2_633 rank5_2_658

theorem rank5_2_660 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,283,2,0⟩, ⟨false,2179,4357,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 271 rank5_2_590 rank5_2_659

theorem rank5_2_661 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨true,17,17,5,0⟩, ⟨false,263,271,2,0⟩, ⟨false,4363,8719,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_2_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_662 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,265,2,0⟩, ⟨false,4363,5813,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 263 265 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,2,0⟩, ⟨false,4363,5813,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_663 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,271,2,0⟩, ⟨false,4363,5813,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_664 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,269,2,0⟩, ⟨false,4363,4643,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_665 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4363,4497,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 4493 4497 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4363,4493,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_666 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4507,4643,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_2_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_667 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,8⟩, ⟨true,17,17,5,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4507,4643,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_668 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4507,4573,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 4567 4573 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4507,4567,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_669 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4583,4611,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 4603 4611 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4583,4603,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_670 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4613,4643,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 4621 4613 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4621,4643,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_671 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4575,4643,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 4583 4575 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4583,4643,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 4611 rank5_2_669 rank5_2_670

end OddPerfect.SpoofBox
