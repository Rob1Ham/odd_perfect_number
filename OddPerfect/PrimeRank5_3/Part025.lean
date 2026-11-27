module

public import OddPerfect.PrimeRank5_3.Part024
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_3_576 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,317,1,0⟩, ⟨false,1289,1385,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1381 1385 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,317,1,0⟩, ⟨false,1289,1381,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_3_568 rank5_3_575

theorem rank5_3_577 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,317,1,0⟩, ⟨false,1399,1499,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_578 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,313,1,0⟩, ⟨false,1399,1447,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 157 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_579 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,317,317,1,0⟩, ⟨false,1399,1447,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 53 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_580 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,317,1,0⟩, ⟨false,1399,1447,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 313 rank5_3_578 rank5_3_579

theorem rank5_3_581 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,317,1,0⟩, ⟨false,1449,1499,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1451 1449 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,317,1,0⟩, ⟨false,1451,1499,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_582 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,317,1,0⟩, ⟨false,1399,1499,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1447 rank5_3_580 rank5_3_581

theorem rank5_3_583 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,317,1,0⟩, ⟨false,1387,1499,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1399 1387 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,317,1,0⟩, ⟨false,1399,1499,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_3_577 rank5_3_582

theorem rank5_3_584 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,317,1,0⟩, ⟨false,1289,1499,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1385 rank5_3_576 rank5_3_583

theorem rank5_3_585 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,317,1,0⟩, ⟨false,1289,1499,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 6 rank5_3_567 rank5_3_584

theorem rank5_3_586 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,329,1,0⟩, ⟨false,1129,1499,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 317 329 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,317,1,0⟩, ⟨false,1129,1499,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1287 rank5_3_566 rank5_3_585

theorem rank5_3_587 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,333,353,1,0⟩, ⟨false,1129,1499,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 337 333 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,337,353,1,0⟩, ⟨false,1129,1499,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_588 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,353,1,0⟩, ⟨false,1129,1503,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1499 1503 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,353,1,0⟩, ⟨false,1129,1499,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 329 rank5_3_586 rank5_3_587

theorem rank5_3_589 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,353,1,0⟩, ⟨false,1505,2251,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1511 1505 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,353,1,0⟩, ⟨false,1511,2251,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_590 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,353,1,0⟩, ⟨false,1129,2251,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1503 rank5_3_588 rank5_3_589

theorem rank5_3_591 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,353,1,0⟩, ⟨false,1129,2251,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 309 rank5_3_563 rank5_3_590

theorem rank5_3_592 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,353,1,0⟩, ⟨false,1129,2257,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2251 2257 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,353,1,0⟩, ⟨false,1129,2251,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_3_554 rank5_3_591

theorem rank5_3_593 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,353,1,0⟩, ⟨false,2267,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_594 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨true,277,293,1,0⟩, ⟨false,2267,3019,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_595 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,281,1,0⟩, ⟨false,2267,2589,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2579 2589 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,281,1,0⟩, ⟨false,2267,2579,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_596 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,281,1,0⟩, ⟨false,2591,3019,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_597 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,277,1,0⟩, ⟨false,2591,2777,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 139 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_598 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,281,281,1,0⟩, ⟨false,2591,2777,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 47 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_599 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,281,1,0⟩, ⟨false,2591,2787,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2777 2787 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,281,1,0⟩, ⟨false,2591,2777,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 277 rank5_3_597 rank5_3_598

end OddPerfect.SpoofBox
