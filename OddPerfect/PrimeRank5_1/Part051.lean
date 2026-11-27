module

public import OddPerfect.PrimeRank5_1.Part050
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_1200 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,317,317,2,0⟩, ⟨false,1319,1321,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1201 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,317,317,2,0⟩, ⟨false,1323,1327,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1327 1323 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,317,317,2,0⟩, ⟨false,1327,1327,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1202 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,317,317,2,0⟩, ⟨false,1319,1327,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1321 rank5_1_1200 rank5_1_1201

theorem rank5_1_1203 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,317,317,2,0⟩, ⟨false,1319,1327,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_1_1199 rank5_1_1202

theorem rank5_1_1204 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,317,317,2,0⟩, ⟨false,1309,1327,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1319 1309 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,317,317,2,0⟩, ⟨false,1319,1327,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_1_1198 rank5_1_1203

theorem rank5_1_1205 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,317,317,2,0⟩, ⟨false,1287,1327,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1289 1287 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,317,317,2,0⟩, ⟨false,1289,1327,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1307 rank5_1_1197 rank5_1_1204

theorem rank5_1_1206 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,317,317,2,0⟩, ⟨false,1249,1327,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1285 rank5_1_1196 rank5_1_1205

theorem rank5_1_1207 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,317,317,2,0⟩, ⟨false,1249,1337,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1327 1337 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,317,317,2,0⟩, ⟨false,1249,1327,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_1_1195 rank5_1_1206

theorem rank5_1_1208 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,317,317,2,0⟩, ⟨false,1339,1439,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1361 1339 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,317,317,2,0⟩, ⟨false,1361,1439,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1209 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,317,325,2,0⟩, ⟨false,1249,1439,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 317 325 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,317,317,2,0⟩, ⟨false,1249,1439,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1337 rank5_1_1207 rank5_1_1208

theorem rank5_1_1210 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,327,337,2,0⟩, ⟨false,1249,1439,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 331 327 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,337,2,0⟩, ⟨false,1249,1439,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1211 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,317,337,2,0⟩, ⟨false,1239,1439,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1249 1239 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,317,337,2,0⟩, ⟨false,1249,1439,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 325 rank5_1_1209 rank5_1_1210

theorem rank5_1_1212 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,315,337,2,0⟩, ⟨false,1087,1439,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 317 315 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,317,337,2,0⟩, ⟨false,1087,1439,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1237 rank5_1_1194 rank5_1_1211

theorem rank5_1_1213 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,337,2,0⟩, ⟨false,1087,1445,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1439 1445 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,337,2,0⟩, ⟨false,1087,1439,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 313 rank5_1_1175 rank5_1_1212

theorem rank5_1_1214 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,301,2,0⟩, ⟨false,1447,1733,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 293 301 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1447,1733,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1215 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,313,2,0⟩, ⟨false,1447,1571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1216 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,307,2,0⟩, ⟨false,1447,1505,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1499 1505 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,307,2,0⟩, ⟨false,1447,1499,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1217 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,307,2,0⟩, ⟨false,1511,1539,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1531 1539 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,307,2,0⟩, ⟨false,1511,1531,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1218 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,307,2,0⟩, ⟨false,1541,1571,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1543 1541 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,307,2,0⟩, ⟨false,1543,1571,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1219 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,307,2,0⟩, ⟨false,1507,1571,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1511 1507 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,307,2,0⟩, ⟨false,1511,1571,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1539 rank5_1_1217 rank5_1_1218

theorem rank5_1_1220 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,309,2,0⟩, ⟨false,1447,1571,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 307 309 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,307,2,0⟩, ⟨false,1447,1571,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1505 rank5_1_1216 rank5_1_1219

theorem rank5_1_1221 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,311,313,2,0⟩, ⟨false,1447,1571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1222 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,313,2,0⟩, ⟨false,1447,1571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 309 rank5_1_1220 rank5_1_1221

theorem rank5_1_1223 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,313,2,0⟩, ⟨false,1447,1577,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1571 1577 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,313,2,0⟩, ⟨false,1447,1571,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_1_1215 rank5_1_1222

end OddPerfect.SpoofBox
