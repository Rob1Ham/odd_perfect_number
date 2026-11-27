module

public import OddPerfect.PrimeRank5_1.Part046
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_1104 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9551,9629,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .exponent 2 rank5_1_1098 rank5_1_1103

theorem rank5_1_1105 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9551,9629,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 14 rank5_1_1097 rank5_1_1104

theorem rank5_1_1106 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9551,9629,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 9 rank5_1_1096 rank5_1_1105

theorem rank5_1_1107 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9469,9629,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 9473 9469 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9473,9629,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 9549 rank5_1_1095 rank5_1_1106

theorem rank5_1_1108 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9311,9629,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 9467 rank5_1_1094 rank5_1_1107

theorem rank5_1_1109 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9631,9973,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1110 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9311,9973,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 9629 rank5_1_1108 rank5_1_1109

theorem rank5_1_1111 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9311,9973,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_1_1093 rank5_1_1110

theorem rank5_1_1112 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9311,9973,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 4 rank5_1_1092 rank5_1_1111

theorem rank5_1_1113 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,263,2,0⟩, ⟨false,8731,9975,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 9973 9975 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,263,2,0⟩, ⟨false,8731,9973,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 9309 rank5_1_1091 rank5_1_1112

theorem rank5_1_1114 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9977,11633,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 10007 9977 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,263,2,0⟩, ⟨false,10007,11633,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1115 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,263,2,0⟩, ⟨false,8731,11637,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 11633 11637 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,263,2,0⟩, ⟨false,8731,11633,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 9975 rank5_1_1113 rank5_1_1114

theorem rank5_1_1116 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,263,2,0⟩, ⟨false,11639,17449,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 11657 11639 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,263,2,0⟩, ⟨false,11657,17449,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1117 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,265,2,0⟩, ⟨false,8731,17449,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 263 265 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,263,2,0⟩, ⟨false,8731,17449,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 11637 rank5_1_1115 rank5_1_1116

theorem rank5_1_1118 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,267,269,2,0⟩, ⟨false,8731,17449,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 269 267 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,269,2,0⟩, ⟨false,8731,17449,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1119 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,269,2,0⟩, ⟨false,8731,17449,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 265 rank5_1_1117 rank5_1_1118

theorem rank5_1_1120 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,269,2,0⟩, ⟨false,8731,17461,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 17449 17461 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,269,2,0⟩, ⟨false,8731,17449,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_1_1090 rank5_1_1119

theorem rank5_1_1121 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,269,2,0⟩, ⟨false,17463,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 17467 17463 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,269,2,0⟩, ⟨false,17467,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1122 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,269,2,0⟩, ⟨false,8731,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 17461 rank5_1_1120 rank5_1_1121

theorem rank5_1_1123 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,269,2,0⟩, ⟨false,8727,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 8731 8727 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,269,2,0⟩, ⟨false,8731,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 261 rank5_1_1089 rank5_1_1122

theorem rank5_1_1124 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,269,2,0⟩, ⟨false,4363,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 8725 rank5_1_1052 rank5_1_1123

theorem rank5_1_1125 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4363,5813,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1126 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4363,4497,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 4493 4497 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4363,4493,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1127 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,4⟩, ⟨false,271,271,2,0⟩, ⟨false,4507,4643,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 88741 rank5_1_prime88741 (by decide +kernel) (by decide +kernel) (by decide +kernel)

end OddPerfect.SpoofBox
