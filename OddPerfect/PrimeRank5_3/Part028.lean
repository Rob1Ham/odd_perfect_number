module

public import OddPerfect.PrimeRank5_3.Part027
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_3_648 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨true,61,73,1,0⟩, ⟨false,263,525,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 523 525 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨true,61,73,1,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 65 rank5_3_646 rank5_3_647

theorem rank5_3_649 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨true,61,73,1,0⟩, ⟨false,527,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 541 527 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨true,61,73,1,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_650 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨true,61,73,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 525 rank5_3_648 rank5_3_649

theorem rank5_3_651 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,23,2,0⟩, ⟨true,61,73,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 4 rank5_3_645 rank5_3_650

theorem rank5_3_652 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,23,2,0⟩, ⟨true,61,77,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 73 77 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,23,2,0⟩, ⟨true,61,73,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 6 rank5_3_644 rank5_3_651

theorem rank5_3_653 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,23,2,0⟩, ⟨true,81,113,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 89 81 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,23,2,0⟩, ⟨true,89,113,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_654 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,25,2,0⟩, ⟨true,61,113,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 2 23 25 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,23,2,0⟩, ⟨true,61,113,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 77 rank5_3_652 rank5_3_653

theorem rank5_3_655 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,27,31,2,0⟩, ⟨true,61,113,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 2 29 27 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,29,31,2,0⟩, ⟨true,61,113,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_656 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,31,2,0⟩, ⟨true,61,121,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 113 121 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,31,2,0⟩, ⟨true,61,113,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .base 25 rank5_3_654 rank5_3_655

theorem rank5_3_657 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,31,2,0⟩, ⟨true,125,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 137 125 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,31,2,0⟩, ⟨true,137,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_658 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,31,2,0⟩, ⟨true,61,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 121 rank5_3_656 rank5_3_657

theorem rank5_3_659 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,31,2,0⟩, ⟨true,61,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .base 21 rank5_3_643 rank5_3_658

theorem rank5_3_660 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,33,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 2 31 33 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,31,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 57 rank5_3_160 rank5_3_659

theorem rank5_3_661 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,35,0,2,0⟩, ⟨true,37,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 2 37 35 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,37,0,2,0⟩, ⟨true,37,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 3 41 38 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,37,0,2,0⟩, ⟨true,41,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_662 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,0,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .base 33 rank5_3_660 rank5_3_661

theorem rank5_3_663 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,0,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 4 rank5_3_107 rank5_3_662

theorem rank5_3_664 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,17,0,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 2 rank5_3_106 rank5_3_663

theorem rank5_3_665 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,17,0,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_666 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,7,2,0⟩, ⟨false,15,0,2,0⟩, ⟨true,17,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 2 17 15 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,7,2,0⟩, ⟨false,17,0,2,0⟩, ⟨true,17,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 3 29 18 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,7,2,0⟩, ⟨false,17,0,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .base 5 rank5_3_664 rank5_3_665

theorem rank5_3_667 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,9,2,0⟩, ⟨false,7,0,2,0⟩, ⟨true,13,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 1 7 9 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,7,2,0⟩, ⟨false,7,0,2,0⟩, ⟨true,13,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .base 13 rank5_3_105 rank5_3_666

theorem rank5_3_668 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,11,0,2,0⟩, ⟨false,11,0,2,0⟩, ⟨true,13,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 2 13 12 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,11,0,2,0⟩, ⟨false,13,0,2,0⟩, ⟨true,13,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 3 17 14 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,11,0,2,0⟩, ⟨false,13,0,2,0⟩, ⟨true,17,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_669 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,0,2,0⟩, ⟨false,7,0,2,0⟩, ⟨true,13,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .base 9 rank5_3_667 rank5_3_668

theorem rank5_3_670 : PrimeCovered (#v[⟨false,3,3,2,0⟩, ⟨false,3,0,2,0⟩, ⟨false,3,0,2,0⟩, ⟨true,5,0,1,0⟩, ⟨false,258,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 1 5 4 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,0⟩, ⟨false,5,0,2,0⟩, ⟨false,3,0,2,0⟩, ⟨true,5,0,1,0⟩, ⟨false,258,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 2 7 6 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,0⟩, ⟨false,5,0,2,0⟩, ⟨false,7,0,2,0⟩, ⟨true,5,0,1,0⟩, ⟨false,258,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 3 13 8 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,0⟩, ⟨false,5,0,2,0⟩, ⟨false,7,0,2,0⟩, ⟨true,13,0,1,0⟩, ⟨false,258,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 4 263 258 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,0⟩, ⟨false,5,0,2,0⟩, ⟨false,7,0,2,0⟩, ⟨true,13,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 2 rank5_3_74 rank5_3_669

theorem closed_prime_5_3 : PrimeCovered (primeInitial (3 : Fin 5)) := rank5_3_670

end OddPerfect.SpoofBox
