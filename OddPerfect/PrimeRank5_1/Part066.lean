module

public import OddPerfect.PrimeRank5_1.Part065
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_1560 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,59,2,2⟩, ⟨false,331,337,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 3541 rank5_1_prime3541 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1561 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,59,4,0⟩, ⟨false,331,333,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 331 333 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,59,4,0⟩, ⟨false,331,331,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1562 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,59,4,0⟩, ⟨false,335,337,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 337 335 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,59,4,0⟩, ⟨false,337,337,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1563 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,59,4,0⟩, ⟨false,331,337,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 333 rank5_1_1561 rank5_1_1562

theorem rank5_1_1564 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,59,2,0⟩, ⟨false,331,337,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .exponent 2 rank5_1_1560 rank5_1_1563

theorem rank5_1_1565 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,59,2,0⟩, ⟨false,331,339,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 337 339 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,59,2,0⟩, ⟨false,331,337,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_1_1559 rank5_1_1564

theorem rank5_1_1566 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,59,2,0⟩, ⟨false,341,349,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 347 341 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,59,2,0⟩, ⟨false,347,349,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1567 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,59,2,0⟩, ⟨false,327,349,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 331 327 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,59,2,0⟩, ⟨false,331,349,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 339 rank5_1_1565 rank5_1_1566

theorem rank5_1_1568 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,59,2,0⟩, ⟨false,307,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 325 rank5_1_1558 rank5_1_1567

theorem rank5_1_1569 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,61,61,2,0⟩, ⟨false,307,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1570 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,61,2,0⟩, ⟨false,307,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 59 rank5_1_1568 rank5_1_1569

theorem rank5_1_1571 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,61,2,0⟩, ⟨false,301,349,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 307 301 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,61,2,0⟩, ⟨false,307,349,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_1_1557 rank5_1_1570

theorem rank5_1_1572 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,61,2,0⟩, ⟨false,263,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 299 rank5_1_1556 rank5_1_1571

theorem rank5_1_1573 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,61,2,0⟩, ⟨false,263,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 5 rank5_1_1541 rank5_1_1572

theorem rank5_1_1574 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,59,61,2,0⟩, ⟨false,263,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 2 rank5_1_1540 rank5_1_1573

theorem rank5_1_1575 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,59,61,2,0⟩, ⟨false,351,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 353 351 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,59,61,2,0⟩, ⟨false,353,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1576 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,59,65,2,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 61 65 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,59,61,2,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 349 rank5_1_1574 rank5_1_1575

theorem rank5_1_1577 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,67,73,2,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1578 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,59,73,2,0⟩, ⟨false,263,525,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 523 525 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,59,73,2,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 65 rank5_1_1576 rank5_1_1577

theorem rank5_1_1579 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,59,73,2,0⟩, ⟨false,527,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 541 527 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,59,73,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1580 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,59,73,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 525 rank5_1_1578 rank5_1_1579

theorem rank5_1_1581 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,59,77,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 73 77 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,59,73,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 6 rank5_1_1539 rank5_1_1580

theorem rank5_1_1582 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,79,113,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1583 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,25,2,0⟩, ⟨false,59,113,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 2 23 25 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,59,113,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 77 rank5_1_1581 rank5_1_1582

end OddPerfect.SpoofBox
