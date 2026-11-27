module

public import OddPerfect.PrimeRank5_4.Part025
import OddPerfect.PrimeRank5_4.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_600 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,331,2,0⟩, ⟨true,1093,1153,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_601 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,331,2,0⟩, ⟨true,1093,1121,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1117 1121 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,331,2,0⟩, ⟨true,1093,1117,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_602 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,331,2,0⟩, ⟨true,1125,1153,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1129 1125 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,331,2,0⟩, ⟨true,1129,1153,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_603 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,331,2,0⟩, ⟨true,1093,1153,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1121 rank5_4_601 rank5_4_602

theorem rank5_4_604 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,331,2,0⟩, ⟨true,1093,1157,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1153 1157 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,331,2,0⟩, ⟨true,1093,1153,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_4_600 rank5_4_603

theorem rank5_4_605 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,331,2,0⟩, ⟨true,1161,1237,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1181 1161 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,331,2,0⟩, ⟨true,1181,1237,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_606 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,331,2,0⟩, ⟨true,1093,1237,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1157 rank5_4_604 rank5_4_605

theorem rank5_4_607 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,331,2,0⟩, ⟨true,1093,1237,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 6 rank5_4_599 rank5_4_606

theorem rank5_4_608 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,331,2,0⟩, ⟨true,1241,1433,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1249 1241 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,331,2,0⟩, ⟨true,1249,1433,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_609 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,319,331,2,0⟩, ⟨true,1093,1433,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 331 319 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,331,2,0⟩, ⟨true,1093,1433,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1237 rank5_4_607 rank5_4_608

theorem rank5_4_610 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,331,2,0⟩, ⟨true,1093,1449,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1433 1449 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,331,2,0⟩, ⟨true,1093,1433,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 317 rank5_4_598 rank5_4_609

theorem rank5_4_611 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨false,307,317,2,0⟩, ⟨true,1453,1733,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_4_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_612 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,311,2,0⟩, ⟨true,1453,1553,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_613 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,307,2,0⟩, ⟨true,1453,1493,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_614 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,309,311,2,0⟩, ⟨true,1453,1493,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 311 309 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,311,311,2,0⟩, ⟨true,1453,1493,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_615 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,311,2,0⟩, ⟨true,1453,1501,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1493 1501 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,311,2,0⟩, ⟨true,1453,1493,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 307 rank5_4_613 rank5_4_614

theorem rank5_4_616 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,311,2,0⟩, ⟨true,1505,1553,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1549 1505 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,311,2,0⟩, ⟨true,1549,1553,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_617 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,311,2,0⟩, ⟨true,1453,1553,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1501 rank5_4_615 rank5_4_616

theorem rank5_4_618 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,311,2,0⟩, ⟨true,1453,1553,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_4_612 rank5_4_617

theorem rank5_4_619 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,313,317,2,0⟩, ⟨true,1453,1553,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_620 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,317,2,0⟩, ⟨true,1453,1577,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1553 1577 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,317,2,0⟩, ⟨true,1453,1553,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 311 rank5_4_618 rank5_4_619

theorem rank5_4_621 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,317,2,0⟩, ⟨true,1581,1733,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1597 1581 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,317,2,0⟩, ⟨true,1597,1733,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_622 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,317,2,0⟩, ⟨true,1453,1733,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1577 rank5_4_620 rank5_4_621

theorem rank5_4_623 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,317,2,0⟩, ⟨true,1453,1737,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1733 1737 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,317,2,0⟩, ⟨true,1453,1733,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_4_611 rank5_4_622

end OddPerfect.SpoofBox
