module

public import OddPerfect.PrimeRank5_2.Part028
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_672 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4507,4643,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 4573 rank5_2_668 rank5_2_671

theorem rank5_2_673 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4507,4643,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 8 rank5_2_667 rank5_2_672

theorem rank5_2_674 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4499,4643,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 4507 4499 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4507,4643,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 12 rank5_2_666 rank5_2_673

theorem rank5_2_675 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4363,4643,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 4497 rank5_2_665 rank5_2_674

theorem rank5_2_676 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,271,2,0⟩, ⟨false,4363,4647,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 4643 4647 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,271,2,0⟩, ⟨false,4363,4643,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 269 rank5_2_664 rank5_2_675

theorem rank5_2_677 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,269,2,0⟩, ⟨false,4649,4973,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_678 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4649,4973,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_679 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,271,2,0⟩, ⟨false,4649,4973,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 269 rank5_2_677 rank5_2_678

theorem rank5_2_680 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,271,2,0⟩, ⟨false,4363,4983,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 4973 4983 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,271,2,0⟩, ⟨false,4363,4973,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 4647 rank5_2_676 rank5_2_679

theorem rank5_2_681 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,269,2,0⟩, ⟨false,4987,5161,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5153 5161 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,269,2,0⟩, ⟨false,4987,5153,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_682 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5167,5351,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_2_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_683 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,8⟩, ⟨true,17,17,5,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5167,5351,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_684 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5167,5257,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5237 5257 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5167,5237,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_685 : PrimeCovered (#v[⟨false,3,3,14,14⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5261,5281,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_686 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,269,2,2⟩, ⟨false,5261,5281,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_687 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,269,4,0⟩, ⟨false,5261,5269,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5261 5269 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,269,4,0⟩, ⟨false,5261,5261,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_688 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,5⟩, ⟨false,269,269,4,0⟩, ⟨false,5273,5281,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_689 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,10⟩, ⟨true,17,17,9,0⟩, ⟨false,269,269,4,0⟩, ⟨false,5273,5281,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 12207031 rank5_2_prime12207031 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_690 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,9,0⟩, ⟨false,269,269,4,0⟩, ⟨false,5273,5275,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5273 5275 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,9,0⟩, ⟨false,269,269,4,0⟩, ⟨false,5273,5273,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_691 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,9,0⟩, ⟨false,269,269,4,0⟩, ⟨false,5277,5281,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5279 5277 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,9,0⟩, ⟨false,269,269,4,0⟩, ⟨false,5279,5281,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_692 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,9,0⟩, ⟨false,269,269,4,0⟩, ⟨false,5273,5281,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 5275 rank5_2_690 rank5_2_691

theorem rank5_2_693 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,9,0⟩, ⟨false,269,269,4,0⟩, ⟨false,5273,5281,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 10 rank5_2_689 rank5_2_692

theorem rank5_2_694 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,269,4,0⟩, ⟨false,5271,5281,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5273 5271 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,269,4,0⟩, ⟨false,5273,5281,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 5 rank5_2_688 rank5_2_693

theorem rank5_2_695 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,269,4,0⟩, ⟨false,5261,5281,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 5269 rank5_2_687 rank5_2_694

end OddPerfect.SpoofBox
