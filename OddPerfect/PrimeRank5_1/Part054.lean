module

public import OddPerfect.PrimeRank5_1.Part053
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_1272 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,397,409,2,0⟩, ⟨false,661,683,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_1_1264 rank5_1_1271

theorem rank5_1_1273 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,397,409,2,0⟩, ⟨false,691,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1274 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,397,401,2,0⟩, ⟨false,691,699,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 691 699 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,397,401,2,0⟩, ⟨false,691,691,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1275 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,397,397,2,0⟩, ⟨false,701,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1276 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,401,401,2,0⟩, ⟨false,701,703,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 701 703 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,401,401,2,0⟩, ⟨false,701,701,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1277 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,401,401,2,0⟩, ⟨false,705,709,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 709 705 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,401,401,2,0⟩, ⟨false,709,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1278 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,399,401,2,0⟩, ⟨false,701,709,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 401 399 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,401,401,2,0⟩, ⟨false,701,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 703 rank5_1_1276 rank5_1_1277

theorem rank5_1_1279 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,397,401,2,0⟩, ⟨false,701,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 397 rank5_1_1275 rank5_1_1278

theorem rank5_1_1280 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,397,401,2,0⟩, ⟨false,691,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 699 rank5_1_1274 rank5_1_1279

theorem rank5_1_1281 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,403,409,2,0⟩, ⟨false,691,709,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 409 403 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,409,409,2,0⟩, ⟨false,691,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1282 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,397,409,2,0⟩, ⟨false,691,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 401 rank5_1_1280 rank5_1_1281

theorem rank5_1_1283 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,397,409,2,0⟩, ⟨false,685,709,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 691 685 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,397,409,2,0⟩, ⟨false,691,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_1_1273 rank5_1_1282

theorem rank5_1_1284 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,395,409,2,0⟩, ⟨false,661,709,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 397 395 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,397,409,2,0⟩, ⟨false,661,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 683 rank5_1_1272 rank5_1_1283

theorem rank5_1_1285 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,379,409,2,0⟩, ⟨false,661,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 393 rank5_1_1263 rank5_1_1284

theorem rank5_1_1286 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,377,409,2,0⟩, ⟨false,617,709,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 379 377 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,379,409,2,0⟩, ⟨false,617,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 659 rank5_1_1262 rank5_1_1285

theorem rank5_1_1287 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,409,2,0⟩, ⟨false,615,709,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 617 615 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,409,2,0⟩, ⟨false,617,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 375 rank5_1_1261 rank5_1_1286

theorem rank5_1_1288 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,409,2,0⟩, ⟨false,541,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 613 rank5_1_1260 rank5_1_1287

theorem rank5_1_1289 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,409,2,0⟩, ⟨false,541,717,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 709 717 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,409,2,0⟩, ⟨false,541,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_1_1259 rank5_1_1288

theorem rank5_1_1290 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,409,2,0⟩, ⟨false,719,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1291 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,373,2,0⟩, ⟨false,719,781,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 773 781 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,373,2,0⟩, ⟨false,719,773,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1292 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,359,2,0⟩, ⟨false,787,859,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1293 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,367,373,2,0⟩, ⟨false,787,821,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1294 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,367,373,2,0⟩, ⟨false,787,803,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 797 803 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,367,373,2,0⟩, ⟨false,787,797,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1295 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,367,369,2,0⟩, ⟨false,809,821,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 367 369 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,367,367,2,0⟩, ⟨false,809,821,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
