module

public import OddPerfect.PrimeRank5_1.Part064
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_1536 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,29,2,0⟩, ⟨false,29,53,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 37 rank5_1_1502 rank5_1_1535

theorem rank5_1_1537 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,31,43,2,0⟩, ⟨false,31,53,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 37 32 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,31,43,2,0⟩, ⟨false,37,53,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1538 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,43,2,0⟩, ⟨false,29,57,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 53 57 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,43,2,0⟩, ⟨false,29,53,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .base 29 rank5_1_1536 rank5_1_1537

theorem rank5_1_1539 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,59,73,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 0 4 1093 rank5_1_prime1093 (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,59,73,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1540 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,2⟩, ⟨false,59,61,2,0⟩, ⟨false,263,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1541 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,5⟩, ⟨false,23,23,4,0⟩, ⟨false,59,61,2,0⟩, ⟨false,263,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1542 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,61,2,0⟩, ⟨false,263,293,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1543 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,59,2,0⟩, ⟨false,263,293,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1544 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,61,61,2,0⟩, ⟨false,263,277,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1545 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,61,61,2,0⟩, ⟨false,281,283,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 3851 rank5_1_prime3851 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1546 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,61,61,2,2⟩, ⟨false,281,283,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1547 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,61,61,4,0⟩, ⟨false,281,281,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1548 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,61,61,4,0⟩, ⟨false,283,283,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1549 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,61,61,4,0⟩, ⟨false,281,283,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 281 rank5_1_1547 rank5_1_1548

theorem rank5_1_1550 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,61,61,2,0⟩, ⟨false,281,283,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .exponent 2 rank5_1_1546 rank5_1_1549

theorem rank5_1_1551 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,61,61,2,0⟩, ⟨false,281,285,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 283 285 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,61,61,2,0⟩, ⟨false,281,283,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_1_1545 rank5_1_1550

theorem rank5_1_1552 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,61,61,2,0⟩, ⟨false,287,293,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 293 287 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,61,61,2,0⟩, ⟨false,293,293,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1553 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,61,61,2,0⟩, ⟨false,279,293,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 281 279 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,61,61,2,0⟩, ⟨false,281,293,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 285 rank5_1_1551 rank5_1_1552

theorem rank5_1_1554 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,61,61,2,0⟩, ⟨false,263,293,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 277 rank5_1_1544 rank5_1_1553

theorem rank5_1_1555 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,61,2,0⟩, ⟨false,263,293,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 59 rank5_1_1543 rank5_1_1554

theorem rank5_1_1556 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,61,2,0⟩, ⟨false,263,299,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 293 299 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,61,2,0⟩, ⟨false,263,293,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_1_1542 rank5_1_1555

theorem rank5_1_1557 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,61,2,0⟩, ⟨false,307,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1558 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,59,2,0⟩, ⟨false,307,325,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 317 325 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,59,2,0⟩, ⟨false,307,317,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1559 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,59,2,0⟩, ⟨false,331,337,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 3851 rank5_1_prime3851 (by decide +kernel) (by decide +kernel) (by decide +kernel)

end OddPerfect.SpoofBox
