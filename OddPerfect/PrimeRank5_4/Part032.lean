module

public import OddPerfect.PrimeRank5_4.Part031
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_744 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,271,2,0⟩, ⟨true,4441,5897,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_4_698 rank5_4_743

theorem rank5_4_745 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,273,277,2,0⟩, ⟨true,4441,5897,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 277 273 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,277,2,0⟩, ⟨true,4441,5897,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_746 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,277,2,0⟩, ⟨true,4441,5913,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5897 5913 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,277,2,0⟩, ⟨true,4441,5897,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 271 rank5_4_744 rank5_4_745

theorem rank5_4_747 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,277,2,0⟩, ⟨true,5917,8861,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5953 5917 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,277,2,0⟩, ⟨true,5953,8861,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_748 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,277,2,0⟩, ⟨true,4441,8861,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 5913 rank5_4_746 rank5_4_747

theorem rank5_4_749 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,277,2,0⟩, ⟨true,4441,8881,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 8861 8881 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,277,2,0⟩, ⟨true,4441,8861,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_4_697 rank5_4_748

theorem rank5_4_750 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,277,2,0⟩, ⟨true,8885,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 8893 8885 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,277,2,0⟩, ⟨true,8893,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_751 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,279,2,0⟩, ⟨true,4441,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 277 279 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,277,2,0⟩, ⟨true,4441,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 8881 rank5_4_749 rank5_4_750

theorem rank5_4_752 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,293,2,0⟩, ⟨true,4441,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_753 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,293,2,0⟩, ⟨true,4429,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 4441 4429 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,293,2,0⟩, ⟨true,4441,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 279 rank5_4_751 rank5_4_752

theorem rank5_4_754 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,295,2,0⟩, ⟨true,2213,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 293 295 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,293,2,0⟩, ⟨true,2213,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 4425 rank5_4_696 rank5_4_753

theorem rank5_4_755 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,297,331,2,0⟩, ⟨true,2213,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 307 297 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,331,2,0⟩, ⟨true,2213,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_756 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,331,2,0⟩, ⟨true,2213,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 295 rank5_4_754 rank5_4_755

theorem rank5_4_757 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,331,2,0⟩, ⟨true,2189,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2213 2189 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,331,2,0⟩, ⟨true,2213,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_4_631 rank5_4_756

theorem rank5_4_758 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,267,331,2,0⟩, ⟨true,1093,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 269 267 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,331,2,0⟩, ⟨true,1093,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 2185 rank5_4_630 rank5_4_757

theorem rank5_4_759 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,223,331,2,0⟩, ⟨true,1085,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1093 1085 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,223,331,2,0⟩, ⟨true,1093,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 265 rank5_4_547 rank5_4_758

theorem rank5_4_760 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,223,331,2,0⟩, ⟨true,541,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1081 rank5_4_446 rank5_4_759

theorem rank5_4_761 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,167,331,2,0⟩, ⟨true,541,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 221 rank5_4_439 rank5_4_760

theorem rank5_4_762 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨false,167,331,2,0⟩, ⟨true,541,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 2 rank5_4_438 rank5_4_761

theorem rank5_4_763 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨false,167,331,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 537 rank5_4_423 rank5_4_762

theorem rank5_4_764 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,167,333,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 331 333 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,167,331,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 4 rank5_4_422 rank5_4_763

theorem rank5_4_765 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,4⟩, ⟨false,17,17,2,0⟩, ⟨false,337,0,2,0⟩, ⟨true,349,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_766 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,2⟩, ⟨false,337,0,2,0⟩, ⟨true,349,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 307 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_767 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,449,2,0⟩, ⟨true,349,457,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
