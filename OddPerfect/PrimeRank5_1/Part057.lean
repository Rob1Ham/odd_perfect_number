module

public import OddPerfect.PrimeRank5_1.Part056
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_1344 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,353,353,2,0⟩, ⟨false,919,923,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 919 923 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,353,353,2,0⟩, ⟨false,919,919,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1345 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,353,353,2,0⟩, ⟨false,925,929,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 929 925 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,353,353,2,0⟩, ⟨false,929,929,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1346 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,353,353,2,0⟩, ⟨false,919,929,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 923 rank5_1_1344 rank5_1_1345

theorem rank5_1_1347 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,353,355,2,0⟩, ⟨false,907,929,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 353 355 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,353,353,2,0⟩, ⟨false,907,929,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 917 rank5_1_1343 rank5_1_1346

theorem rank5_1_1348 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,357,359,2,0⟩, ⟨false,907,929,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 359 357 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,359,359,2,0⟩, ⟨false,907,929,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1349 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,353,359,2,0⟩, ⟨false,907,929,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 355 rank5_1_1347 rank5_1_1348

theorem rank5_1_1350 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,353,359,2,0⟩, ⟨false,931,953,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 937 931 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,353,359,2,0⟩, ⟨false,937,953,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1351 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,353,359,2,0⟩, ⟨false,907,953,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 929 rank5_1_1349 rank5_1_1350

theorem rank5_1_1352 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,353,359,2,0⟩, ⟨false,907,953,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_1_1342 rank5_1_1351

theorem rank5_1_1353 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,359,2,0⟩, ⟨false,907,953,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 351 rank5_1_1341 rank5_1_1352

theorem rank5_1_1354 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,359,2,0⟩, ⟨false,863,953,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 905 rank5_1_1338 rank5_1_1353

theorem rank5_1_1355 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,361,373,2,0⟩, ⟨false,863,953,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 367 361 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,367,373,2,0⟩, ⟨false,863,953,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1356 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,373,2,0⟩, ⟨false,863,955,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 953 955 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,373,2,0⟩, ⟨false,863,953,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 359 rank5_1_1354 rank5_1_1355

theorem rank5_1_1357 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,349,2,0⟩, ⟨false,967,1013,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1358 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,347,2,0⟩, ⟨false,967,971,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1359 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,349,349,2,0⟩, ⟨false,967,971,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1360 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,349,2,0⟩, ⟨false,967,973,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 971 973 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,349,2,0⟩, ⟨false,967,971,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 347 rank5_1_1358 rank5_1_1359

theorem rank5_1_1361 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,349,2,0⟩, ⟨false,975,983,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 977 975 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,349,2,0⟩, ⟨false,977,983,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1362 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,349,2,0⟩, ⟨false,967,989,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 983 989 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,349,2,0⟩, ⟨false,967,983,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 973 rank5_1_1360 rank5_1_1361

theorem rank5_1_1363 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,349,2,0⟩, ⟨false,991,1013,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1364 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,349,2,0⟩, ⟨false,967,1013,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 989 rank5_1_1362 rank5_1_1363

theorem rank5_1_1365 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,351,2,0⟩, ⟨false,967,1013,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 349 351 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,349,2,0⟩, ⟨false,967,1013,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_1_1357 rank5_1_1364

theorem rank5_1_1366 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,353,359,2,0⟩, ⟨false,967,1013,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1367 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,359,2,0⟩, ⟨false,967,1015,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1013 1015 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,359,2,0⟩, ⟨false,967,1013,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 351 rank5_1_1365 rank5_1_1366

end OddPerfect.SpoofBox
