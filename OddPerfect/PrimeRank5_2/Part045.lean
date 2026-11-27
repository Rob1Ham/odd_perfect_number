module

public import OddPerfect.PrimeRank5_2.Part044
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_1056 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,389,2,0⟩, ⟨false,769,823,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_2_1040 rank5_2_1055

theorem rank5_2_1057 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,391,401,2,0⟩, ⟨false,769,823,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 397 391 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,397,401,2,0⟩, ⟨false,769,823,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1058 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,401,2,0⟩, ⟨false,769,823,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 389 rank5_2_1056 rank5_2_1057

theorem rank5_2_1059 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,401,2,0⟩, ⟨false,825,887,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 827 825 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,401,2,0⟩, ⟨false,827,887,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1060 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,401,2,0⟩, ⟨false,769,887,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 823 rank5_2_1058 rank5_2_1059

theorem rank5_2_1061 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,401,2,0⟩, ⟨false,769,887,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 6 rank5_2_1039 rank5_2_1060

theorem rank5_2_1062 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,405,2,0⟩, ⟨false,677,887,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 401 405 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,401,2,0⟩, ⟨false,677,887,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 767 rank5_2_1038 rank5_2_1061

theorem rank5_2_1063 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨true,17,17,5,0⟩, ⟨false,409,439,2,0⟩, ⟨false,677,761,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_2_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_1064 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,421,2,0⟩, ⟨false,677,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_1065 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,409,2,0⟩, ⟨false,677,679,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 677 679 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,409,2,0⟩, ⟨false,677,677,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1066 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,409,2,0⟩, ⟨false,681,683,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 683 681 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,409,2,0⟩, ⟨false,683,683,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1067 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,409,2,0⟩, ⟨false,677,683,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 679 rank5_2_1065 rank5_2_1066

theorem rank5_2_1068 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,409,2,0⟩, ⟨false,685,691,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 691 685 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,409,2,0⟩, ⟨false,691,691,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1069 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,409,2,0⟩, ⟨false,677,691,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 683 rank5_2_1067 rank5_2_1068

theorem rank5_2_1070 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,409,2,0⟩, ⟨false,693,709,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 701 693 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,409,2,0⟩, ⟨false,701,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1071 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,413,2,0⟩, ⟨false,677,709,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 409 413 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,409,2,0⟩, ⟨false,677,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 691 rank5_2_1069 rank5_2_1070

theorem rank5_2_1072 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,415,421,2,0⟩, ⟨false,677,709,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 419 415 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,419,421,2,0⟩, ⟨false,677,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1073 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,421,2,0⟩, ⟨false,677,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 413 rank5_2_1071 rank5_2_1072

theorem rank5_2_1074 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,421,2,0⟩, ⟨false,677,715,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 709 715 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,421,2,0⟩, ⟨false,677,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_2_1064 rank5_2_1073

theorem rank5_2_1075 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,421,2,0⟩, ⟨false,717,761,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 719 717 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,421,2,0⟩, ⟨false,719,761,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1076 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,423,2,0⟩, ⟨false,677,761,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 421 423 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,421,2,0⟩, ⟨false,677,761,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 715 rank5_2_1074 rank5_2_1075

theorem rank5_2_1077 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,425,439,2,0⟩, ⟨false,677,761,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 431 425 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,431,439,2,0⟩, ⟨false,677,761,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1078 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,439,2,0⟩, ⟨false,677,761,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 423 rank5_2_1076 rank5_2_1077

theorem rank5_2_1079 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,439,2,0⟩, ⟨false,677,767,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 761 767 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,439,2,0⟩, ⟨false,677,761,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_2_1063 rank5_2_1078

end OddPerfect.SpoofBox
