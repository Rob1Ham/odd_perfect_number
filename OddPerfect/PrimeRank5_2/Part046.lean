module

public import OddPerfect.PrimeRank5_2.Part045
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_1080 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,439,2,0⟩, ⟨false,769,887,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1081 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,407,439,2,0⟩, ⟨false,677,887,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 409 407 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,439,2,0⟩, ⟨false,677,887,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 767 rank5_2_1079 rank5_2_1080

theorem rank5_2_1082 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,439,2,0⟩, ⟨false,677,895,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 887 895 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,439,2,0⟩, ⟨false,677,887,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 405 rank5_2_1062 rank5_2_1081

theorem rank5_2_1083 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,439,2,0⟩, ⟨false,897,1327,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 907 897 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,439,2,0⟩, ⟨false,907,1327,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1084 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,439,2,0⟩, ⟨false,677,1327,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 895 rank5_2_1082 rank5_2_1083

theorem rank5_2_1085 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,439,2,0⟩, ⟨false,677,1327,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 377 rank5_2_1011 rank5_2_1084

theorem rank5_2_1086 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,439,2,0⟩, ⟨false,677,1353,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1327 1353 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,439,2,0⟩, ⟨false,677,1327,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_2_898 rank5_2_1085

theorem rank5_2_1087 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,439,2,0⟩, ⟨false,1355,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1361 1355 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,439,2,0⟩, ⟨false,1361,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1088 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,441,2,0⟩, ⟨false,677,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 439 441 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,439,2,0⟩, ⟨false,677,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1353 rank5_2_1086 rank5_2_1087

theorem rank5_2_1089 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,661,2,0⟩, ⟨false,677,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1090 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,661,2,0⟩, ⟨false,675,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 677 675 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,661,2,0⟩, ⟨false,677,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 441 rank5_2_1088 rank5_2_1089

theorem rank5_2_1091 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,661,2,0⟩, ⟨false,337,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 673 rank5_2_897 rank5_2_1090

theorem rank5_2_1092 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,663,0,2,0⟩, ⟨false,663,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 673 663 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,673,0,2,0⟩, ⟨false,663,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 4 677 674 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,673,0,2,0⟩, ⟨false,677,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1093 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,0,2,0⟩, ⟨false,337,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 661 rank5_2_1091 rank5_2_1092

theorem rank5_2_1094 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,5,0⟩, ⟨false,327,0,2,0⟩, ⟨false,327,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 331 327 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,0,2,0⟩, ⟨false,327,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 4 337 332 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,0,2,0⟩, ⟨false,337,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 4 rank5_2_766 rank5_2_1093

theorem rank5_2_1095 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,5,0⟩, ⟨false,163,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 325 rank5_2_765 rank5_2_1094

theorem rank5_2_1096 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,5,0⟩, ⟨false,159,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 163 159 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,5,0⟩, ⟨false,163,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 6 rank5_2_434 rank5_2_1095

theorem rank5_2_1097 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,5,0⟩, ⟨false,79,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 157 rank5_2_419 rank5_2_1096

theorem rank5_2_1098 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,0⟩, ⟨false,79,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 1 rank5_2_418 rank5_2_1097

theorem rank5_2_1099 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,13,17,1,0⟩, ⟨false,75,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 79 75 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,13,17,1,0⟩, ⟨false,79,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .base 13 rank5_2_7 rank5_2_1098

theorem rank5_2_1100 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,13,17,1,0⟩, ⟨false,35,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 37 35 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,13,17,1,0⟩, ⟨false,37,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 73 rank5_2_6 rank5_2_1099

theorem rank5_2_1101 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,13,17,1,0⟩, ⟨false,17,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 33 rank5_2_5 rank5_2_1100

theorem rank5_2_1102 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨true,13,17,1,0⟩, ⟨false,17,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 4 rank5_2_4 rank5_2_1101

theorem rank5_2_1103 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,17,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 2 rank5_2_3 rank5_2_1102

end OddPerfect.SpoofBox
