module

public import OddPerfect.PrimeRank5_1.Part057
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_1368 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,359,2,0⟩, ⟨false,1017,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1019 1017 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,359,2,0⟩, ⟨false,1019,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1369 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,359,2,0⟩, ⟨false,967,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1015 rank5_1_1367 rank5_1_1368

theorem rank5_1_1370 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,361,373,2,0⟩, ⟨false,967,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 367 361 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,367,373,2,0⟩, ⟨false,967,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1371 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,373,2,0⟩, ⟨false,957,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 967 957 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,373,2,0⟩, ⟨false,967,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 359 rank5_1_1369 rank5_1_1370

theorem rank5_1_1372 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,375,2,0⟩, ⟨false,863,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 373 375 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,373,2,0⟩, ⟨false,863,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 955 rank5_1_1356 rank5_1_1371

theorem rank5_1_1373 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,377,409,2,0⟩, ⟨false,863,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 379 377 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,379,409,2,0⟩, ⟨false,863,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1374 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,409,2,0⟩, ⟨false,861,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 863 861 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,409,2,0⟩, ⟨false,863,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 375 rank5_1_1372 rank5_1_1373

theorem rank5_1_1375 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,409,2,0⟩, ⟨false,719,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 859 rank5_1_1333 rank5_1_1374

theorem rank5_1_1376 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,409,2,0⟩, ⟨false,719,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 8 rank5_1_1290 rank5_1_1375

theorem rank5_1_1377 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,411,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 409 411 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,409,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 717 rank5_1_1289 rank5_1_1376

theorem rank5_1_1378 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,509,2,0⟩, ⟨false,541,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1379 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,457,2,0⟩, ⟨false,541,573,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 571 573 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,457,2,0⟩, ⟨false,541,571,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1380 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,437,2,0⟩, ⟨false,577,613,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 433 437 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,433,2,0⟩, ⟨false,577,613,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1381 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,439,457,2,0⟩, ⟨false,577,593,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1382 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,439,447,2,0⟩, ⟨false,577,593,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 443 447 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,439,443,2,0⟩, ⟨false,577,593,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1383 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,449,457,2,0⟩, ⟨false,577,583,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 577 583 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,449,457,2,0⟩, ⟨false,577,577,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1384 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,449,451,2,0⟩, ⟨false,587,593,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 449 451 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,449,449,2,0⟩, ⟨false,587,593,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1385 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,453,457,2,0⟩, ⟨false,587,593,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 457 453 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,457,2,0⟩, ⟨false,587,593,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1386 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,449,457,2,0⟩, ⟨false,585,593,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 587 585 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,449,457,2,0⟩, ⟨false,587,593,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 451 rank5_1_1384 rank5_1_1385

theorem rank5_1_1387 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,449,457,2,0⟩, ⟨false,577,593,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 583 rank5_1_1383 rank5_1_1386

theorem rank5_1_1388 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,439,457,2,0⟩, ⟨false,577,593,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 447 rank5_1_1382 rank5_1_1387

theorem rank5_1_1389 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,439,457,2,0⟩, ⟨false,577,593,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_1_1381 rank5_1_1388

theorem rank5_1_1390 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,439,457,2,0⟩, ⟨false,599,613,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1391 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,439,443,2,0⟩, ⟨false,599,605,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 601 605 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,439,443,2,0⟩, ⟨false,599,601,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
