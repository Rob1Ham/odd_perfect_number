module

public import OddPerfect.PrimeRank5_1.Part063
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_1512 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,5⟩, ⟨false,23,23,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1513 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,541,717,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 709 717 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,541,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1514 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,719,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1515 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,719,859,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1516 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,863,905,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 887 905 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,863,887,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1517 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,53,53,2,2⟩, ⟨false,907,953,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1518 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,53,53,4,0⟩, ⟨false,907,953,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1519 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,907,953,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .exponent 2 rank5_1_1517 rank5_1_1518

theorem rank5_1_1520 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,863,955,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 953 955 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,863,953,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 905 rank5_1_1516 rank5_1_1519

theorem rank5_1_1521 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,957,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 967 957 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,967,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1522 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,861,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 863 861 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,863,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 955 rank5_1_1520 rank5_1_1521

theorem rank5_1_1523 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,719,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 859 rank5_1_1515 rank5_1_1522

theorem rank5_1_1524 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,719,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 8 rank5_1_1514 rank5_1_1523

theorem rank5_1_1525 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,23,23,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 717 rank5_1_1513 rank5_1_1524

theorem rank5_1_1526 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 5 rank5_1_1512 rank5_1_1525

theorem rank5_1_1527 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,53,53,2,0⟩, ⟨false,541,1081,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1069 1081 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,53,53,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 2 rank5_1_1511 rank5_1_1526

theorem rank5_1_1528 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,53,53,2,0⟩, ⟨false,1083,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1087 1083 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,53,53,2,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1529 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,51,53,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 53 51 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,53,53,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1081 rank5_1_1527 rank5_1_1528

theorem rank5_1_1530 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,47,53,2,0⟩, ⟨false,527,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 541 527 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,47,53,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 49 rank5_1_1510 rank5_1_1529

theorem rank5_1_1531 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,47,53,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 525 rank5_1_1509 rank5_1_1530

theorem rank5_1_1532 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,41,53,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 45 rank5_1_1508 rank5_1_1531

theorem rank5_1_1533 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,25,2,0⟩, ⟨false,41,53,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 2 23 25 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,23,2,0⟩, ⟨false,41,53,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 6 rank5_1_1507 rank5_1_1532

theorem rank5_1_1534 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,27,29,2,0⟩, ⟨false,41,53,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 2 29 27 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,29,29,2,0⟩, ⟨false,41,53,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1535 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,29,2,0⟩, ⟨false,39,53,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 41 39 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,23,29,2,0⟩, ⟨false,41,53,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .base 25 rank5_1_1533 rank5_1_1534

end OddPerfect.SpoofBox
