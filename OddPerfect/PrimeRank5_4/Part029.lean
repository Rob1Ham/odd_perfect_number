module

public import OddPerfect.PrimeRank5_4.Part028
import OddPerfect.PrimeRank5_4.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_672 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,283,283,2,0⟩, ⟨true,2609,2693,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2649 rank5_4_662 rank5_4_671

theorem rank5_4_673 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,283,2,0⟩, ⟨true,2605,2693,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2609 2605 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,283,2,0⟩, ⟨true,2609,2693,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 281 rank5_4_661 rank5_4_672

theorem rank5_4_674 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,283,2,0⟩, ⟨true,2521,2701,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2693 2701 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,283,2,0⟩, ⟨true,2521,2693,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 2601 rank5_4_660 rank5_4_673

theorem rank5_4_675 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,281,2,0⟩, ⟨true,2713,2801,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_676 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,283,283,2,0⟩, ⟨true,2713,2801,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_677 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,283,2,0⟩, ⟨true,2713,2809,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2801 2809 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,283,2,0⟩, ⟨true,2713,2801,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 281 rank5_4_675 rank5_4_676

theorem rank5_4_678 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,4⟩, ⟨false,281,281,2,0⟩, ⟨true,2833,2917,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 88741 rank5_4_prime88741 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_679 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,281,281,2,0⟩, ⟨true,2833,2861,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_4_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_680 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,281,281,2,0⟩, ⟨true,2833,2861,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_681 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,281,281,2,0⟩, ⟨true,2833,2873,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2861 2873 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,281,281,2,0⟩, ⟨true,2833,2861,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 12 rank5_4_679 rank5_4_680

theorem rank5_4_682 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,281,281,2,0⟩, ⟨true,2877,2917,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2897 2877 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,281,281,2,0⟩, ⟨true,2897,2917,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_683 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,281,281,2,0⟩, ⟨true,2833,2917,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2873 rank5_4_681 rank5_4_682

theorem rank5_4_684 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,281,2,0⟩, ⟨true,2833,2917,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 4 rank5_4_678 rank5_4_683

theorem rank5_4_685 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,283,283,2,0⟩, ⟨true,2833,2917,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_686 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,283,2,0⟩, ⟨true,2813,2917,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2833 2813 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,283,2,0⟩, ⟨true,2833,2917,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 281 rank5_4_684 rank5_4_685

theorem rank5_4_687 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,283,2,0⟩, ⟨true,2705,2917,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2713 2705 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,283,2,0⟩, ⟨true,2713,2917,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 2809 rank5_4_677 rank5_4_686

theorem rank5_4_688 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,283,2,0⟩, ⟨true,2521,2917,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2701 rank5_4_674 rank5_4_687

theorem rank5_4_689 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,283,2,0⟩, ⟨true,2517,2917,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2521 2517 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,283,2,0⟩, ⟨true,2521,2917,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_4_659 rank5_4_688

theorem rank5_4_690 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,285,2,0⟩, ⟨true,2213,2917,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 283 285 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,283,2,0⟩, ⟨true,2213,2917,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 2513 rank5_4_658 rank5_4_689

theorem rank5_4_691 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,287,293,2,0⟩, ⟨true,2213,2917,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 293 287 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨true,2213,2917,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_692 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,293,2,0⟩, ⟨true,2213,2917,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 285 rank5_4_690 rank5_4_691

theorem rank5_4_693 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,293,2,0⟩, ⟨true,2213,2949,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2917 2949 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,293,2,0⟩, ⟨true,2213,2917,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_4_657 rank5_4_692

theorem rank5_4_694 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,293,2,0⟩, ⟨true,2953,4421,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_695 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,293,2,0⟩, ⟨true,2213,4421,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2949 rank5_4_693 rank5_4_694

end OddPerfect.SpoofBox
