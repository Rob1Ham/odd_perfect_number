module

public import OddPerfect.PrimeRank5_2.Part046
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_1104 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨false,7,7,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,17,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_1105 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,2,2⟩, ⟨true,13,13,1,1⟩, ⟨false,19,19,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1106 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,7,7,2,2⟩, ⟨true,13,13,5,0⟩, ⟨false,19,19,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 0 4 1093 rank5_2_prime1093 (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,7,7,2,2⟩, ⟨true,13,13,5,0⟩, ⟨false,19,19,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1107 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,2,2⟩, ⟨true,13,13,5,0⟩, ⟨false,19,19,2,2⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 127 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_1108 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,2,2⟩, ⟨true,13,13,5,0⟩, ⟨false,19,19,4,0⟩, ⟨false,263,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1109 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,7,7,2,2⟩, ⟨true,13,13,5,0⟩, ⟨false,19,19,4,0⟩, ⟨false,353,421,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 757 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_1110 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,7,7,2,2⟩, ⟨true,13,13,5,0⟩, ⟨false,19,19,4,0⟩, ⟨false,353,421,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1111 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,2,2⟩, ⟨true,13,13,5,0⟩, ⟨false,19,19,4,0⟩, ⟨false,353,421,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 8 rank5_2_1109 rank5_2_1110

theorem rank5_2_1112 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,2,2⟩, ⟨true,13,13,5,0⟩, ⟨false,19,19,4,0⟩, ⟨false,423,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 431 423 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,2,2⟩, ⟨true,13,13,5,0⟩, ⟨false,19,19,4,0⟩, ⟨false,431,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1113 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,2,2⟩, ⟨true,13,13,5,0⟩, ⟨false,19,19,4,0⟩, ⟨false,351,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 353 351 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,2,2⟩, ⟨true,13,13,5,0⟩, ⟨false,19,19,4,0⟩, ⟨false,353,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 421 rank5_2_1111 rank5_2_1112

theorem rank5_2_1114 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,2,2⟩, ⟨true,13,13,5,0⟩, ⟨false,19,19,4,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 349 rank5_2_1108 rank5_2_1113

theorem rank5_2_1115 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,2,2⟩, ⟨true,13,13,5,0⟩, ⟨false,19,19,2,0⟩, ⟨false,263,525,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 523 525 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,2,2⟩, ⟨true,13,13,5,0⟩, ⟨false,19,19,2,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .exponent 2 rank5_2_1107 rank5_2_1114

theorem rank5_2_1116 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,2,2⟩, ⟨true,13,13,5,0⟩, ⟨false,19,19,2,0⟩, ⟨false,527,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 541 527 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,2,2⟩, ⟨true,13,13,5,0⟩, ⟨false,19,19,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1117 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,2,2⟩, ⟨true,13,13,5,0⟩, ⟨false,19,19,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 525 rank5_2_1115 rank5_2_1116

theorem rank5_2_1118 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,2,2⟩, ⟨true,13,13,5,0⟩, ⟨false,19,19,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 6 rank5_2_1106 rank5_2_1117

theorem rank5_2_1119 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,2,2⟩, ⟨true,13,13,1,0⟩, ⟨false,19,19,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 1 rank5_2_1105 rank5_2_1118

theorem rank5_2_1120 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,2,2⟩, ⟨true,17,17,1,0⟩, ⟨false,19,19,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1121 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,2,2⟩, ⟨true,13,17,1,0⟩, ⟨false,17,31,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 1 3 19 (by norm_num) (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,2,2⟩, ⟨true,13,17,1,0⟩, ⟨false,19,19,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .base 13 rank5_2_1119 rank5_2_1120

theorem rank5_2_1122 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,7,7,4,0⟩, ⟨true,13,13,1,1⟩, ⟨false,17,17,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1123 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,7,7,4,0⟩, ⟨true,13,13,1,1⟩, ⟨false,19,19,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1124 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,7,7,4,0⟩, ⟨true,13,13,1,1⟩, ⟨false,17,19,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 0 4 1093 rank5_2_prime1093 (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,7,7,4,0⟩, ⟨true,13,13,1,1⟩, ⟨false,17,19,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 17 rank5_2_1122 rank5_2_1123

theorem rank5_2_1125 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,4,0⟩, ⟨true,13,13,1,1⟩, ⟨false,17,17,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1126 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,4,0⟩, ⟨true,13,13,1,1⟩, ⟨false,19,19,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1127 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,4,0⟩, ⟨true,13,13,1,1⟩, ⟨false,17,19,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 17 rank5_2_1125 rank5_2_1126

end OddPerfect.SpoofBox
