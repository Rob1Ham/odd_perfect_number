module

public import OddPerfect.PrimeRank5_1.Part049
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_1176 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,317,325,2,0⟩, ⟨false,1087,1237,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 317 325 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,317,317,2,0⟩, ⟨false,1087,1237,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1177 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,337,2,0⟩, ⟨false,1087,1153,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1178 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1087,1119,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1117 1119 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1087,1117,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1179 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,4⟩, ⟨false,331,331,2,0⟩, ⟨false,1123,1129,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 88741 rank5_1_prime88741 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1180 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1123,1129,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_1_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1181 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1123,1125,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1123 1125 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1123,1123,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1182 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1127,1129,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1129 1127 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1129,1129,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1183 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1123,1129,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1125 rank5_1_1181 rank5_1_1182

theorem rank5_1_1184 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1123,1129,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_1_1180 rank5_1_1183

theorem rank5_1_1185 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1123,1137,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1129 1137 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1123,1129,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_1_1179 rank5_1_1184

theorem rank5_1_1186 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1139,1153,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1151 1139 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1151,1153,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1187 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1121,1153,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1123 1121 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1123,1153,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1137 rank5_1_1185 rank5_1_1186

theorem rank5_1_1188 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,333,2,0⟩, ⟨false,1087,1153,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 331 333 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1087,1153,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1119 rank5_1_1178 rank5_1_1187

theorem rank5_1_1189 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,335,337,2,0⟩, ⟨false,1087,1153,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 337 335 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1087,1153,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1190 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,337,2,0⟩, ⟨false,1087,1153,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 333 rank5_1_1188 rank5_1_1189

theorem rank5_1_1191 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,337,2,0⟩, ⟨false,1087,1157,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1153 1157 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,337,2,0⟩, ⟨false,1087,1153,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_1_1177 rank5_1_1190

theorem rank5_1_1192 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,337,2,0⟩, ⟨false,1159,1237,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1163 1159 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,337,2,0⟩, ⟨false,1163,1237,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1193 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,327,337,2,0⟩, ⟨false,1087,1237,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 331 327 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,337,2,0⟩, ⟨false,1087,1237,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1157 rank5_1_1191 rank5_1_1192

theorem rank5_1_1194 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,317,337,2,0⟩, ⟨false,1087,1237,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 325 rank5_1_1176 rank5_1_1193

theorem rank5_1_1195 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,317,317,2,0⟩, ⟨false,1249,1327,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1196 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,317,317,2,0⟩, ⟨false,1249,1285,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1283 1285 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,317,317,2,0⟩, ⟨false,1249,1283,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1197 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,317,317,2,0⟩, ⟨false,1289,1307,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1198 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,4⟩, ⟨false,317,317,2,0⟩, ⟨false,1319,1327,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 88741 rank5_1_prime88741 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1199 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,317,317,2,0⟩, ⟨false,1319,1327,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_1_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

end OddPerfect.SpoofBox
