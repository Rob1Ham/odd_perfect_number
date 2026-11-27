module

public import OddPerfect.PrimeRank5_2.Part049
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_1176 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,29,29,5,0⟩, ⟨false,37,37,2,2⟩, ⟨false,479,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_1177 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨true,29,29,5,0⟩, ⟨false,37,37,4,0⟩, ⟨false,479,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_2_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_1178 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,29,29,5,0⟩, ⟨false,37,37,4,0⟩, ⟨false,479,499,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_1179 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,29,29,5,0⟩, ⟨false,37,37,4,0⟩, ⟨false,479,487,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1180 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,29,29,5,0⟩, ⟨false,37,37,4,0⟩, ⟨false,489,499,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 491 489 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,29,29,5,0⟩, ⟨false,37,37,4,0⟩, ⟨false,491,499,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1181 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,29,29,5,0⟩, ⟨false,37,37,4,0⟩, ⟨false,479,499,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 487 rank5_2_1179 rank5_2_1180

theorem rank5_2_1182 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,29,29,5,0⟩, ⟨false,37,37,4,0⟩, ⟨false,479,499,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_2_1178 rank5_2_1181

theorem rank5_2_1183 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,29,29,5,0⟩, ⟨false,37,37,4,0⟩, ⟨false,501,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 503 501 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,29,29,5,0⟩, ⟨false,37,37,4,0⟩, ⟨false,503,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1184 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,29,29,5,0⟩, ⟨false,37,37,4,0⟩, ⟨false,479,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 499 rank5_2_1182 rank5_2_1183

theorem rank5_2_1185 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,29,29,5,0⟩, ⟨false,37,37,4,0⟩, ⟨false,479,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 6 rank5_2_1177 rank5_2_1184

theorem rank5_2_1186 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,29,29,5,0⟩, ⟨false,37,37,2,0⟩, ⟨false,473,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 479 473 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,29,29,5,0⟩, ⟨false,37,37,2,0⟩, ⟨false,479,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .exponent 2 rank5_2_1176 rank5_2_1185

theorem rank5_2_1187 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,29,29,5,0⟩, ⟨false,37,37,2,0⟩, ⟨false,431,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 471 rank5_2_1175 rank5_2_1186

theorem rank5_2_1188 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,29,29,5,0⟩, ⟨false,37,37,2,0⟩, ⟨false,423,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 431 423 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,29,29,5,0⟩, ⟨false,37,37,2,0⟩, ⟨false,431,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_2_1174 rank5_2_1187

theorem rank5_2_1189 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,29,29,5,0⟩, ⟨false,37,37,2,0⟩, ⟨false,351,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 353 351 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,29,29,5,0⟩, ⟨false,37,37,2,0⟩, ⟨false,353,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 421 rank5_2_1173 rank5_2_1188

theorem rank5_2_1190 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,29,29,5,0⟩, ⟨false,37,37,2,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 349 rank5_2_1172 rank5_2_1189

theorem rank5_2_1191 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,29,29,5,0⟩, ⟨false,39,41,2,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 41 39 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,29,29,5,0⟩, ⟨false,41,41,2,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1192 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,29,29,5,0⟩, ⟨false,37,41,2,0⟩, ⟨false,263,525,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 523 525 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,29,29,5,0⟩, ⟨false,37,41,2,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 37 rank5_2_1190 rank5_2_1191

theorem rank5_2_1193 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,29,29,5,0⟩, ⟨false,37,41,2,0⟩, ⟨false,527,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 541 527 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,29,29,5,0⟩, ⟨false,37,41,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1194 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,29,29,5,0⟩, ⟨false,37,41,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 525 rank5_2_1192 rank5_2_1193

theorem rank5_2_1195 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨true,29,29,5,0⟩, ⟨false,37,41,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 4 rank5_2_1171 rank5_2_1194

theorem rank5_2_1196 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨true,29,29,1,0⟩, ⟨false,37,41,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 1 rank5_2_1170 rank5_2_1195

theorem rank5_2_1197 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨true,33,37,1,0⟩, ⟨false,37,41,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 2 37 33 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨true,37,37,1,0⟩, ⟨false,37,41,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 3 41 38 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨true,37,37,1,0⟩, ⟨false,41,41,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 2 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_1198 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨true,29,37,1,0⟩, ⟨false,37,41,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .base 29 rank5_2_1196 rank5_2_1197

theorem rank5_2_1199 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,29,37,1,0⟩, ⟨false,37,41,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 6 rank5_2_1145 rank5_2_1198

end OddPerfect.SpoofBox
