module

public import OddPerfect.PrimeRank5_1.Part062
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_1488 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,29,29,4,0⟩, ⟨false,37,37,4,0⟩, ⟨false,479,499,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_1_1484 rank5_1_1487

theorem rank5_1_1489 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,29,29,4,0⟩, ⟨false,37,37,4,0⟩, ⟨false,501,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 503 501 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,29,29,4,0⟩, ⟨false,37,37,4,0⟩, ⟨false,503,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1490 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,29,29,4,0⟩, ⟨false,37,37,4,0⟩, ⟨false,479,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 499 rank5_1_1488 rank5_1_1489

theorem rank5_1_1491 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,29,29,4,0⟩, ⟨false,37,37,2,0⟩, ⟨false,473,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 479 473 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,29,29,4,0⟩, ⟨false,37,37,2,0⟩, ⟨false,479,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .exponent 2 rank5_1_1483 rank5_1_1490

theorem rank5_1_1492 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,29,29,4,0⟩, ⟨false,37,37,2,0⟩, ⟨false,431,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 471 rank5_1_1482 rank5_1_1491

theorem rank5_1_1493 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,29,29,2,0⟩, ⟨false,37,37,2,0⟩, ⟨false,431,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 2 rank5_1_1481 rank5_1_1492

theorem rank5_1_1494 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,29,29,2,0⟩, ⟨false,37,37,2,0⟩, ⟨false,423,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 431 423 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,29,29,2,0⟩, ⟨false,37,37,2,0⟩, ⟨false,431,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_1_1480 rank5_1_1493

theorem rank5_1_1495 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,29,29,2,0⟩, ⟨false,37,37,2,0⟩, ⟨false,353,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 421 rank5_1_1479 rank5_1_1494

theorem rank5_1_1496 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,29,29,2,0⟩, ⟨false,37,37,2,0⟩, ⟨false,351,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 353 351 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,29,29,2,0⟩, ⟨false,37,37,2,0⟩, ⟨false,353,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 5 rank5_1_1478 rank5_1_1495

theorem rank5_1_1497 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,29,29,2,0⟩, ⟨false,37,37,2,0⟩, ⟨false,263,525,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 523 525 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,29,29,2,0⟩, ⟨false,37,37,2,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 349 rank5_1_1477 rank5_1_1496

theorem rank5_1_1498 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,29,29,2,0⟩, ⟨false,37,37,2,0⟩, ⟨false,527,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 541 527 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,29,29,2,0⟩, ⟨false,37,37,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1499 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,29,29,2,0⟩, ⟨false,35,37,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 37 35 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,29,29,2,0⟩, ⟨false,37,37,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 525 rank5_1_1497 rank5_1_1498

theorem rank5_1_1500 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,29,29,2,0⟩, ⟨false,31,37,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 33 rank5_1_1476 rank5_1_1499

theorem rank5_1_1501 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,27,29,2,0⟩, ⟨false,29,37,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 2 29 27 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,29,29,2,0⟩, ⟨false,29,37,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 3 31 30 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,29,29,2,0⟩, ⟨false,31,37,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 6 rank5_1_1475 rank5_1_1500

theorem rank5_1_1502 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,29,2,0⟩, ⟨false,29,37,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .base 25 rank5_1_1472 rank5_1_1501

theorem rank5_1_1503 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,41,45,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 43 45 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,41,43,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1504 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,47,49,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 47 49 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,47,47,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1505 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,51,53,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 53 51 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,53,53,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1506 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,47,53,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 49 rank5_1_1504 rank5_1_1505

theorem rank5_1_1507 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,41,53,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 0 4 1093 rank5_1_prime1093 (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,41,53,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 45 rank5_1_1503 rank5_1_1506

theorem rank5_1_1508 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,41,45,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 43 45 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,41,43,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1509 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,47,53,2,0⟩, ⟨false,263,525,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 523 525 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,47,53,2,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1510 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,47,49,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 47 49 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,47,47,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1511 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,2⟩, ⟨false,53,53,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end OddPerfect.SpoofBox
