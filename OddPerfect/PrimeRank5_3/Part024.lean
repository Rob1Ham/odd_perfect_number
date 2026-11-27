module

public import OddPerfect.PrimeRank5_3.Part023
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_3_552 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,369,541,1,0⟩, ⟨false,563,1123,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 373 369 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,541,1,0⟩, ⟨false,563,1123,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 749 rank5_3_536 rank5_3_551

theorem rank5_3_553 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,541,1,0⟩, ⟨false,563,1125,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1123 1125 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,541,1,0⟩, ⟨false,563,1123,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 365 rank5_3_447 rank5_3_552

theorem rank5_3_554 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,353,1,0⟩, ⟨false,1129,2251,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_555 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,293,1,0⟩, ⟨false,1129,1503,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1499 1503 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,293,1,0⟩, ⟨false,1129,1499,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_556 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,293,1,0⟩, ⟨false,1511,1807,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1801 1807 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,293,1,0⟩, ⟨false,1511,1801,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_557 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨true,277,293,1,0⟩, ⟨false,1811,2251,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_558 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,281,1,0⟩, ⟨false,1811,2251,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_559 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,285,293,1,0⟩, ⟨false,1811,2251,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 293 285 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,293,293,1,0⟩, ⟨false,1811,2251,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 3 7 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_560 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,293,1,0⟩, ⟨false,1811,2251,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 281 rank5_3_558 rank5_3_559

theorem rank5_3_561 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,293,1,0⟩, ⟨false,1809,2251,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1811 1809 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,293,1,0⟩, ⟨false,1811,2251,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_3_557 rank5_3_560

theorem rank5_3_562 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,293,1,0⟩, ⟨false,1505,2251,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1511 1505 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,293,1,0⟩, ⟨false,1511,2251,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1807 rank5_3_556 rank5_3_561

theorem rank5_3_563 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,309,1,0⟩, ⟨false,1129,2251,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 293 309 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,293,1,0⟩, ⟨false,1129,2251,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1503 rank5_3_555 rank5_3_562

theorem rank5_3_564 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨true,313,317,1,0⟩, ⟨false,1129,1283,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_565 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,317,1,0⟩, ⟨false,1129,1283,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_566 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,317,1,0⟩, ⟨false,1129,1287,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1283 1287 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,317,1,0⟩, ⟨false,1129,1283,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_3_564 rank5_3_565

theorem rank5_3_567 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨true,313,317,1,0⟩, ⟨false,1289,1499,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_568 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,317,1,0⟩, ⟨false,1289,1381,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_569 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,313,1,0⟩, ⟨false,1289,1327,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 157 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_570 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,317,317,1,0⟩, ⟨false,1289,1327,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 53 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_571 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,317,1,0⟩, ⟨false,1289,1333,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1327 1333 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,317,1,0⟩, ⟨false,1289,1327,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 313 rank5_3_569 rank5_3_570

theorem rank5_3_572 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,313,1,0⟩, ⟨false,1361,1381,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 157 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_573 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,317,317,1,0⟩, ⟨false,1361,1381,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 53 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_574 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,317,1,0⟩, ⟨false,1335,1381,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1361 1335 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,317,1,0⟩, ⟨false,1361,1381,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 313 rank5_3_572 rank5_3_573

theorem rank5_3_575 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,317,1,0⟩, ⟨false,1289,1381,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1333 rank5_3_571 rank5_3_574

end OddPerfect.SpoofBox
