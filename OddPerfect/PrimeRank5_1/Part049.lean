module

public import OddPerfect.PrimeRank5_1.Part048
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_1152 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,337,2,0⟩, ⟨false,1087,2161,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1153 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,313,2,0⟩, ⟨false,1087,1237,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1154 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,301,2,0⟩, ⟨false,1249,1439,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 293 301 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1249,1439,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1155 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,313,2,0⟩, ⟨false,1249,1337,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1327 1337 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,313,2,0⟩, ⟨false,1249,1327,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1156 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,313,2,0⟩, ⟨false,1361,1439,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1157 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,309,2,0⟩, ⟨false,1361,1439,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 307 309 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,307,2,0⟩, ⟨false,1361,1439,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1158 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,311,313,2,0⟩, ⟨false,1361,1397,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1381 1397 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,311,313,2,0⟩, ⟨false,1361,1381,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1159 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,311,311,2,0⟩, ⟨false,1399,1439,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1160 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,4⟩, ⟨false,313,313,2,0⟩, ⟨false,1399,1409,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 88741 rank5_1_prime88741 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1161 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,313,313,2,0⟩, ⟨false,1399,1409,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_1_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1162 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,313,313,2,0⟩, ⟨false,1399,1403,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1399 1403 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,313,313,2,0⟩, ⟨false,1399,1399,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1163 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,313,313,2,0⟩, ⟨false,1405,1409,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1409 1405 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,313,313,2,0⟩, ⟨false,1409,1409,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1164 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,313,313,2,0⟩, ⟨false,1399,1409,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1403 rank5_1_1162 rank5_1_1163

theorem rank5_1_1165 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,313,313,2,0⟩, ⟨false,1399,1409,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_1_1161 rank5_1_1164

theorem rank5_1_1166 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,313,313,2,0⟩, ⟨false,1399,1417,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1409 1417 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,313,313,2,0⟩, ⟨false,1399,1409,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_1_1160 rank5_1_1165

theorem rank5_1_1167 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,313,313,2,0⟩, ⟨false,1419,1439,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1423 1419 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,313,313,2,0⟩, ⟨false,1423,1439,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1168 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,313,313,2,0⟩, ⟨false,1399,1439,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1417 rank5_1_1166 rank5_1_1167

theorem rank5_1_1169 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,311,313,2,0⟩, ⟨false,1399,1439,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 311 rank5_1_1159 rank5_1_1168

theorem rank5_1_1170 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,311,313,2,0⟩, ⟨false,1361,1439,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1397 rank5_1_1158 rank5_1_1169

theorem rank5_1_1171 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,313,2,0⟩, ⟨false,1361,1439,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 309 rank5_1_1157 rank5_1_1170

theorem rank5_1_1172 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,313,2,0⟩, ⟨false,1339,1439,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1361 1339 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,313,2,0⟩, ⟨false,1361,1439,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_1_1156 rank5_1_1171

theorem rank5_1_1173 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,303,313,2,0⟩, ⟨false,1249,1439,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 307 303 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,313,2,0⟩, ⟨false,1249,1439,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1337 rank5_1_1155 rank5_1_1172

theorem rank5_1_1174 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,313,2,0⟩, ⟨false,1239,1439,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1249 1239 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,313,2,0⟩, ⟨false,1249,1439,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 301 rank5_1_1154 rank5_1_1173

theorem rank5_1_1175 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,313,2,0⟩, ⟨false,1087,1439,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1237 rank5_1_1153 rank5_1_1174

end OddPerfect.SpoofBox
