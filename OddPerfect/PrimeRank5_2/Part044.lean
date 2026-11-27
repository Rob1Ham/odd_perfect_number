module

public import OddPerfect.PrimeRank5_2.Part043
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_1032 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,389,2,0⟩, ⟨false,741,761,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 743 741 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,389,2,0⟩, ⟨false,743,761,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 383 rank5_2_1026 rank5_2_1031

theorem rank5_2_1033 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,389,2,0⟩, ⟨false,719,761,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 739 rank5_2_1025 rank5_2_1032

theorem rank5_2_1034 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,389,2,0⟩, ⟨false,719,761,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_2_1024 rank5_2_1033

theorem rank5_2_1035 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,391,401,2,0⟩, ⟨false,719,761,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 397 391 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,397,401,2,0⟩, ⟨false,719,761,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1036 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,401,2,0⟩, ⟨false,717,761,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 719 717 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,401,2,0⟩, ⟨false,719,761,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 389 rank5_2_1034 rank5_2_1035

theorem rank5_2_1037 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,401,2,0⟩, ⟨false,677,761,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 715 rank5_2_1023 rank5_2_1036

theorem rank5_2_1038 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,401,2,0⟩, ⟨false,677,767,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 761 767 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,401,2,0⟩, ⟨false,677,761,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_2_1012 rank5_2_1037

theorem rank5_2_1039 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨true,17,17,5,0⟩, ⟨false,379,401,2,0⟩, ⟨false,769,887,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_2_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_1040 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,389,2,0⟩, ⟨false,769,823,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_1041 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,379,2,0⟩, ⟨false,769,773,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1042 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,383,383,2,0⟩, ⟨false,769,773,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_2_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_1043 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,8⟩, ⟨true,17,17,5,0⟩, ⟨false,383,383,2,0⟩, ⟨false,769,773,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_1044 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,383,383,2,0⟩, ⟨false,769,769,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1045 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,383,383,2,0⟩, ⟨false,771,773,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 773 771 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,383,383,2,0⟩, ⟨false,773,773,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1046 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,383,383,2,0⟩, ⟨false,769,773,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 769 rank5_2_1044 rank5_2_1045

theorem rank5_2_1047 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,383,383,2,0⟩, ⟨false,769,773,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 8 rank5_2_1043 rank5_2_1046

theorem rank5_2_1048 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,381,383,2,0⟩, ⟨false,769,773,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 383 381 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,383,383,2,0⟩, ⟨false,769,773,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 12 rank5_2_1042 rank5_2_1047

theorem rank5_2_1049 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,383,2,0⟩, ⟨false,769,777,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 773 777 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,383,2,0⟩, ⟨false,769,773,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 379 rank5_2_1041 rank5_2_1048

theorem rank5_2_1050 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,383,2,0⟩, ⟨false,779,787,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 787 779 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,383,2,0⟩, ⟨false,787,787,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1051 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,383,2,0⟩, ⟨false,769,787,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 777 rank5_2_1049 rank5_2_1050

theorem rank5_2_1052 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,385,389,2,0⟩, ⟨false,769,787,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 389 385 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,389,389,2,0⟩, ⟨false,769,787,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1053 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,389,2,0⟩, ⟨false,769,795,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 787 795 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,389,2,0⟩, ⟨false,769,787,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 383 rank5_2_1051 rank5_2_1052

theorem rank5_2_1054 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,389,2,0⟩, ⟨false,797,823,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1055 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,389,2,0⟩, ⟨false,769,823,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 795 rank5_2_1053 rank5_2_1054

end OddPerfect.SpoofBox
