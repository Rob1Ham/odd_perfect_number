module

public import OddPerfect.PrimeRank5_4.Part023
import OddPerfect.PrimeRank5_4.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_552 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨false,281,293,2,0⟩, ⟨true,1741,2161,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_4_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_553 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,285,2,0⟩, ⟨true,1741,2161,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 283 285 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,283,2,0⟩, ⟨true,1741,2161,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_554 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨true,1741,1925,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1913 1925 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨true,1741,1913,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_555 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨true,1933,2161,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_556 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨true,1933,1977,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1973 1977 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨true,1933,1973,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_557 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,4⟩, ⟨false,293,293,2,0⟩, ⟨true,1993,2029,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 88741 rank5_4_prime88741 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_558 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,293,293,2,0⟩, ⟨true,1993,2029,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_4_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_559 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,293,293,2,0⟩, ⟨true,1993,2009,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1997 2009 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,293,293,2,0⟩, ⟨true,1993,1997,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_560 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,8⟩, ⟨false,17,17,6,0⟩, ⟨false,293,293,2,0⟩, ⟨true,2017,2029,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_561 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,293,293,2,0⟩, ⟨true,2017,2021,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2017 2021 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,293,293,2,0⟩, ⟨true,2017,2017,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 1009 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_562 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,293,293,2,0⟩, ⟨true,2025,2029,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2029 2025 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,293,293,2,0⟩, ⟨true,2029,2029,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_563 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,293,293,2,0⟩, ⟨true,2017,2029,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2021 rank5_4_561 rank5_4_562

theorem rank5_4_564 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,293,293,2,0⟩, ⟨true,2013,2029,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2017 2013 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,293,293,2,0⟩, ⟨true,2017,2029,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 8 rank5_4_560 rank5_4_563

theorem rank5_4_565 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,293,293,2,0⟩, ⟨true,1993,2029,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2009 rank5_4_559 rank5_4_564

theorem rank5_4_566 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,293,293,2,0⟩, ⟨true,1993,2029,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_4_558 rank5_4_565

theorem rank5_4_567 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨true,1981,2029,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1993 1981 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨true,1993,2029,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_4_557 rank5_4_566

theorem rank5_4_568 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨true,1933,2037,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2029 2037 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨true,1933,2029,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1977 rank5_4_556 rank5_4_567

theorem rank5_4_569 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨true,2041,2161,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2053 2041 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨true,2053,2161,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_570 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨true,1933,2161,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2037 rank5_4_568 rank5_4_569

theorem rank5_4_571 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨true,1929,2161,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1933 1929 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨true,1933,2161,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_4_555 rank5_4_570

theorem rank5_4_572 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,287,293,2,0⟩, ⟨true,1741,2161,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 293 287 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,293,2,0⟩, ⟨true,1741,2161,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1925 rank5_4_554 rank5_4_571

theorem rank5_4_573 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,293,2,0⟩, ⟨true,1741,2161,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 285 rank5_4_553 rank5_4_572

theorem rank5_4_574 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,293,2,0⟩, ⟨true,1741,2161,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 6 rank5_4_552 rank5_4_573

theorem rank5_4_575 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,293,2,0⟩, ⟨true,1453,2161,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1737 rank5_4_551 rank5_4_574

end OddPerfect.SpoofBox
