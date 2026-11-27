module

public import OddPerfect.PrimeRank5_2.Part023
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_552 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,293,2,0⟩, ⟨false,2017,2039,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 8 rank5_2_546 rank5_2_551

theorem rank5_2_553 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,293,2,0⟩, ⟨false,2013,2039,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2017 2013 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,293,2,0⟩, ⟨false,2017,2039,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 12 rank5_2_545 rank5_2_552

theorem rank5_2_554 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1985,2039,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1987 1985 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1987,2039,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 2011 rank5_2_544 rank5_2_553

theorem rank5_2_555 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1931,2039,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1983 rank5_2_543 rank5_2_554

theorem rank5_2_556 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,293,2,0⟩, ⟨false,2041,2161,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2053 2041 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,293,2,0⟩, ⟨false,2053,2161,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_557 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1931,2161,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2039 rank5_2_555 rank5_2_556

theorem rank5_2_558 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1929,2161,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1931 1929 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1931,2161,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_2_542 rank5_2_557

theorem rank5_2_559 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1741,2161,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1927 rank5_2_541 rank5_2_558

theorem rank5_2_560 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1735,2161,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1741 1735 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1741,2161,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_2_540 rank5_2_559

theorem rank5_2_561 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,303,2,0⟩, ⟨false,1447,2161,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 293 303 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1447,2161,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1733 rank5_2_539 rank5_2_560

theorem rank5_2_562 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨true,17,17,5,0⟩, ⟨false,307,317,2,0⟩, ⟨false,1447,1733,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_2_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_563 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,307,311,2,0⟩, ⟨false,1447,1571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_564 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,307,307,2,0⟩, ⟨false,1447,1499,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_565 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,309,311,2,0⟩, ⟨false,1447,1499,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 311 309 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,311,311,2,0⟩, ⟨false,1447,1499,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_566 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,307,311,2,0⟩, ⟨false,1447,1505,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1499 1505 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,307,311,2,0⟩, ⟨false,1447,1499,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 307 rank5_2_564 rank5_2_565

theorem rank5_2_567 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,307,307,2,0⟩, ⟨false,1511,1539,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1531 1539 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,307,307,2,0⟩, ⟨false,1511,1531,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_568 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,307,307,2,0⟩, ⟨false,1541,1571,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1543 1541 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,307,307,2,0⟩, ⟨false,1543,1571,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_569 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,307,307,2,0⟩, ⟨false,1511,1571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1539 rank5_2_567 rank5_2_568

theorem rank5_2_570 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,309,311,2,0⟩, ⟨false,1511,1571,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 311 309 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,311,311,2,0⟩, ⟨false,1511,1571,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_571 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,307,311,2,0⟩, ⟨false,1507,1571,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1511 1507 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,307,311,2,0⟩, ⟨false,1511,1571,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 307 rank5_2_569 rank5_2_570

theorem rank5_2_572 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,307,311,2,0⟩, ⟨false,1447,1571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1505 rank5_2_566 rank5_2_571

theorem rank5_2_573 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,307,311,2,0⟩, ⟨false,1447,1571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_2_563 rank5_2_572

theorem rank5_2_574 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,313,317,2,0⟩, ⟨false,1447,1571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_575 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,307,317,2,0⟩, ⟨false,1447,1577,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1571 1577 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,307,317,2,0⟩, ⟨false,1447,1571,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 311 rank5_2_573 rank5_2_574

end OddPerfect.SpoofBox
