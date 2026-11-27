module

public import OddPerfect.PrimeRank5_1.Part066
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_1584 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,27,29,2,0⟩, ⟨false,59,113,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 2 29 27 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,29,29,2,0⟩, ⟨false,59,113,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1585 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,29,2,0⟩, ⟨false,59,117,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 113 117 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,29,2,0⟩, ⟨false,59,113,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .base 25 rank5_1_1583 rank5_1_1584

theorem rank5_1_1586 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,29,2,0⟩, ⟨false,119,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 127 119 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,29,2,0⟩, ⟨false,127,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1587 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,29,2,0⟩, ⟨false,59,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 117 rank5_1_1585 rank5_1_1586

theorem rank5_1_1588 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,31,43,2,0⟩, ⟨false,59,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1589 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,43,2,0⟩, ⟨false,59,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .base 29 rank5_1_1587 rank5_1_1588

theorem rank5_1_1590 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,45,2,0⟩, ⟨false,29,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 2 43 45 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,43,2,0⟩, ⟨false,29,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 57 rank5_1_1538 rank5_1_1589

theorem rank5_1_1591 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,47,0,2,0⟩, ⟨false,47,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 53 48 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,47,0,2,0⟩, ⟨false,53,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1592 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,0,2,0⟩, ⟨false,29,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .base 45 rank5_1_1590 rank5_1_1591

theorem rank5_1_1593 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,0,2,0⟩, ⟨false,23,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 29 24 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,0,2,0⟩, ⟨false,29,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 4 rank5_1_1471 rank5_1_1592

theorem rank5_1_1594 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,11,0,2,0⟩, ⟨false,13,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .base 21 rank5_1_1470 rank5_1_1593

theorem rank5_1_1595 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨true,5,9,1,0⟩, ⟨false,7,0,2,0⟩, ⟨false,11,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 1 5 9 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨true,5,5,1,0⟩, ⟨false,7,0,2,0⟩, ⟨false,11,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 2 11 7 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨true,5,5,1,0⟩, ⟨false,11,0,2,0⟩, ⟨false,11,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 3 13 12 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨true,5,5,1,0⟩, ⟨false,11,0,2,0⟩, ⟨false,13,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 1 rank5_1_549 rank5_1_1594

theorem rank5_1_1596 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨true,13,0,1,0⟩, ⟨false,13,0,2,0⟩, ⟨false,13,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 2 17 14 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨true,13,0,1,0⟩, ⟨false,17,0,2,0⟩, ⟨false,13,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 3 19 18 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨true,13,0,1,0⟩, ⟨false,17,0,2,0⟩, ⟨false,19,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1597 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨true,5,0,1,0⟩, ⟨false,7,0,2,0⟩, ⟨false,11,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .base 9 rank5_1_1595 rank5_1_1596

theorem rank5_1_1598 : PrimeCovered (#v[⟨false,3,3,2,0⟩, ⟨true,5,0,1,0⟩, ⟨false,3,0,2,0⟩, ⟨false,3,0,2,0⟩, ⟨false,258,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 2 7 6 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,0⟩, ⟨true,5,0,1,0⟩, ⟨false,7,0,2,0⟩, ⟨false,3,0,2,0⟩, ⟨false,258,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 3 11 8 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,0⟩, ⟨true,5,0,1,0⟩, ⟨false,7,0,2,0⟩, ⟨false,11,0,2,0⟩, ⟨false,258,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 4 263 258 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,0⟩, ⟨true,5,0,1,0⟩, ⟨false,7,0,2,0⟩, ⟨false,11,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 2 rank5_1_88 rank5_1_1597

theorem closed_prime_5_1 : PrimeCovered (primeInitial (1 : Fin 5)) := rank5_1_1598

end OddPerfect.SpoofBox
