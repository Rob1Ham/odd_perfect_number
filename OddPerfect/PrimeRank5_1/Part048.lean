module

public import OddPerfect.PrimeRank5_1.Part047
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_1128 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4507,4643,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_1_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1129 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4507,4573,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 4567 4573 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4507,4567,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1130 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4583,4611,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 4603 4611 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4583,4603,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1131 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4613,4643,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 4621 4613 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4621,4643,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1132 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4575,4643,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 4583 4575 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4583,4643,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 4611 rank5_1_1130 rank5_1_1131

theorem rank5_1_1133 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4507,4643,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 4573 rank5_1_1129 rank5_1_1132

theorem rank5_1_1134 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4507,4643,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_1_1128 rank5_1_1133

theorem rank5_1_1135 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4499,4643,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 4507 4499 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4507,4643,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_1_1127 rank5_1_1134

theorem rank5_1_1136 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4363,4647,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 4643 4647 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4363,4643,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 4497 rank5_1_1126 rank5_1_1135

theorem rank5_1_1137 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4649,4973,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1138 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4363,4983,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 4973 4983 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4363,4973,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 4647 rank5_1_1136 rank5_1_1137

theorem rank5_1_1139 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4985,5813,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 4987 4985 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4987,5813,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1140 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4363,5813,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 4983 rank5_1_1138 rank5_1_1139

theorem rank5_1_1141 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4363,5815,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5813 5815 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4363,5813,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_1_1125 rank5_1_1140

theorem rank5_1_1142 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,271,2,0⟩, ⟨false,5817,8719,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5821 5817 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,271,2,0⟩, ⟨false,5821,8719,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1143 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,275,2,0⟩, ⟨false,4363,8719,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 271 275 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4363,8719,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 5815 rank5_1_1141 rank5_1_1142

theorem rank5_1_1144 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,283,2,0⟩, ⟨false,4363,8719,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1145 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,283,2,0⟩, ⟨false,4363,8725,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 8719 8725 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,283,2,0⟩, ⟨false,4363,8719,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 275 rank5_1_1143 rank5_1_1144

theorem rank5_1_1146 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,283,2,0⟩, ⟨false,8727,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 8731 8727 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,283,2,0⟩, ⟨false,8731,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1147 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,283,2,0⟩, ⟨false,4363,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 8725 rank5_1_1145 rank5_1_1146

theorem rank5_1_1148 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,283,2,0⟩, ⟨false,4359,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 4363 4359 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,283,2,0⟩, ⟨false,4363,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 269 rank5_1_1124 rank5_1_1147

theorem rank5_1_1149 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,283,2,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 4357 rank5_1_1013 rank5_1_1148

theorem rank5_1_1150 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,283,2,0⟩, ⟨false,2175,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2179 2175 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,283,2,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_1_938 rank5_1_1149

theorem rank5_1_1151 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,291,2,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 283 291 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,283,2,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 2173 rank5_1_937 rank5_1_1150

end OddPerfect.SpoofBox
