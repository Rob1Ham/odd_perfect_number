module

public import OddPerfect.PrimeRank5_2.Part021
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_504 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,317,317,2,0⟩, ⟨false,1319,1327,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_2_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_505 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,8⟩, ⟨true,17,17,5,0⟩, ⟨false,317,317,2,0⟩, ⟨false,1319,1327,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_506 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,317,317,2,0⟩, ⟨false,1319,1321,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_507 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,317,317,2,0⟩, ⟨false,1323,1327,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1327 1323 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,317,317,2,0⟩, ⟨false,1327,1327,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_508 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,317,317,2,0⟩, ⟨false,1319,1327,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1321 rank5_2_506 rank5_2_507

theorem rank5_2_509 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,317,317,2,0⟩, ⟨false,1319,1327,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 8 rank5_2_505 rank5_2_508

theorem rank5_2_510 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,317,317,2,0⟩, ⟨false,1309,1327,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1319 1309 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,317,317,2,0⟩, ⟨false,1319,1327,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 12 rank5_2_504 rank5_2_509

theorem rank5_2_511 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,315,317,2,0⟩, ⟨false,1289,1327,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 317 315 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,317,317,2,0⟩, ⟨false,1289,1327,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1307 rank5_2_503 rank5_2_510

theorem rank5_2_512 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,313,317,2,0⟩, ⟨false,1287,1327,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1289 1287 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,313,317,2,0⟩, ⟨false,1289,1327,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 313 rank5_2_502 rank5_2_511

theorem rank5_2_513 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,313,317,2,0⟩, ⟨false,1249,1327,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1285 rank5_2_501 rank5_2_512

theorem rank5_2_514 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,313,317,2,0⟩, ⟨false,1249,1327,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_2_500 rank5_2_513

theorem rank5_2_515 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,307,317,2,0⟩, ⟨false,1249,1337,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1327 1337 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,307,317,2,0⟩, ⟨false,1249,1327,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 311 rank5_2_499 rank5_2_514

theorem rank5_2_516 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,307,311,2,0⟩, ⟨false,1361,1439,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_517 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,307,311,2,0⟩, ⟨false,1361,1439,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_518 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,307,311,2,0⟩, ⟨false,1361,1439,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_2_516 rank5_2_517

theorem rank5_2_519 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,313,317,2,0⟩, ⟨false,1361,1439,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_520 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,313,313,2,0⟩, ⟨false,1361,1397,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1381 1397 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,313,313,2,0⟩, ⟨false,1361,1381,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_521 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,313,313,2,0⟩, ⟨false,1399,1409,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_2_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_522 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,8⟩, ⟨true,17,17,5,0⟩, ⟨false,313,313,2,0⟩, ⟨false,1399,1409,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_523 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,313,313,2,0⟩, ⟨false,1399,1403,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1399 1403 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,313,313,2,0⟩, ⟨false,1399,1399,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_524 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,313,313,2,0⟩, ⟨false,1405,1409,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1409 1405 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,313,313,2,0⟩, ⟨false,1409,1409,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_525 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,313,313,2,0⟩, ⟨false,1399,1409,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1403 rank5_2_523 rank5_2_524

theorem rank5_2_526 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,313,313,2,0⟩, ⟨false,1399,1409,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 8 rank5_2_522 rank5_2_525

theorem rank5_2_527 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,313,313,2,0⟩, ⟨false,1399,1417,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1409 1417 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,313,313,2,0⟩, ⟨false,1399,1409,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 12 rank5_2_521 rank5_2_526

end OddPerfect.SpoofBox
