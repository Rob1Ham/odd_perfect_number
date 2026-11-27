module

public import OddPerfect.PrimeRank5_1.Part055
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_1320 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,383,383,2,0⟩, ⟨false,769,773,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 769 rank5_1_1318 rank5_1_1319

theorem rank5_1_1321 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,383,383,2,0⟩, ⟨false,769,773,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_1_1317 rank5_1_1320

theorem rank5_1_1322 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,381,383,2,0⟩, ⟨false,769,773,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 383 381 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,383,383,2,0⟩, ⟨false,769,773,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_1_1316 rank5_1_1321

theorem rank5_1_1323 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,379,383,2,0⟩, ⟨false,763,773,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 769 763 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,379,383,2,0⟩, ⟨false,769,773,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 379 rank5_1_1315 rank5_1_1322

theorem rank5_1_1324 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,379,383,2,0⟩, ⟨false,751,773,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 761 rank5_1_1314 rank5_1_1323

theorem rank5_1_1325 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,385,389,2,0⟩, ⟨false,751,773,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 389 385 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,389,389,2,0⟩, ⟨false,751,773,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1326 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,379,389,2,0⟩, ⟨false,751,773,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 383 rank5_1_1324 rank5_1_1325

theorem rank5_1_1327 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,379,389,2,0⟩, ⟨false,747,773,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 751 747 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,379,389,2,0⟩, ⟨false,751,773,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_1_1313 rank5_1_1326

theorem rank5_1_1328 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,379,393,2,0⟩, ⟨false,719,773,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 389 393 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,379,389,2,0⟩, ⟨false,719,773,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 745 rank5_1_1312 rank5_1_1327

theorem rank5_1_1329 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,395,409,2,0⟩, ⟨false,719,773,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 397 395 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,397,409,2,0⟩, ⟨false,719,773,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1330 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,379,409,2,0⟩, ⟨false,719,781,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 773 781 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,379,409,2,0⟩, ⟨false,719,773,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 393 rank5_1_1328 rank5_1_1329

theorem rank5_1_1331 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,379,409,2,0⟩, ⟨false,783,859,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 787 783 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,379,409,2,0⟩, ⟨false,787,859,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1332 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,377,409,2,0⟩, ⟨false,719,859,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 379 377 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,379,409,2,0⟩, ⟨false,719,859,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 781 rank5_1_1330 rank5_1_1331

theorem rank5_1_1333 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,409,2,0⟩, ⟨false,719,859,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 375 rank5_1_1311 rank5_1_1332

theorem rank5_1_1334 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,351,2,0⟩, ⟨false,863,887,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 349 351 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,349,2,0⟩, ⟨false,863,887,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1335 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,353,359,2,0⟩, ⟨false,863,887,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1336 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,353,359,2,0⟩, ⟨false,863,887,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1337 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,353,359,2,0⟩, ⟨false,863,887,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_1_1335 rank5_1_1336

theorem rank5_1_1338 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,359,2,0⟩, ⟨false,863,905,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 887 905 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,359,2,0⟩, ⟨false,863,887,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 351 rank5_1_1334 rank5_1_1337

theorem rank5_1_1339 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,349,2,0⟩, ⟨false,907,953,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1340 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,349,2,0⟩, ⟨false,907,953,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1341 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,351,2,0⟩, ⟨false,907,953,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 349 351 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,349,2,0⟩, ⟨false,907,953,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_1_1339 rank5_1_1340

theorem rank5_1_1342 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,353,359,2,0⟩, ⟨false,907,953,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1343 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,353,353,2,0⟩, ⟨false,907,917,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 911 917 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,353,353,2,0⟩, ⟨false,907,911,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
