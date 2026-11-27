module

public import OddPerfect.PrimeRank5_1.Part027
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_648 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,101,2,0⟩, ⟨false,1823,1865,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1861 1865 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,101,2,0⟩, ⟨false,1823,1861,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_649 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,101,2,2⟩, ⟨false,1867,1913,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 10303 rank5_1_prime10303 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_650 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,101,4,0⟩, ⟨false,1867,1913,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_651 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,101,2,0⟩, ⟨false,1867,1913,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .exponent 2 rank5_1_649 rank5_1_650

theorem rank5_1_652 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,101,2,0⟩, ⟨false,1823,1913,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1865 rank5_1_648 rank5_1_651

theorem rank5_1_653 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,101,2,0⟩, ⟨false,1741,1913,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1821 rank5_1_647 rank5_1_652

theorem rank5_1_654 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,101,2,0⟩, ⟨false,1741,1927,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1913 1927 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,101,2,0⟩, ⟨false,1741,1913,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_1_646 rank5_1_653

theorem rank5_1_655 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,101,2,0⟩, ⟨false,1929,2161,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1931 1929 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,101,2,0⟩, ⟨false,1931,2161,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_656 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,101,2,0⟩, ⟨false,1741,2161,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1927 rank5_1_654 rank5_1_655

theorem rank5_1_657 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,103,103,2,0⟩, ⟨false,1741,2161,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_658 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,103,2,0⟩, ⟨false,1735,2161,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1741 1735 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,103,2,0⟩, ⟨false,1741,2161,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 101 rank5_1_656 rank5_1_657

theorem rank5_1_659 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,103,2,0⟩, ⟨false,1447,2161,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1733 rank5_1_645 rank5_1_658

theorem rank5_1_660 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,103,2,0⟩, ⟨false,1087,2161,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1445 rank5_1_642 rank5_1_659

theorem rank5_1_661 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,103,2,0⟩, ⟨false,1087,2161,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 99 rank5_1_631 rank5_1_660

theorem rank5_1_662 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,103,2,0⟩, ⟨false,1087,2173,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2161 2173 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,103,2,0⟩, ⟨false,1087,2161,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_1_630 rank5_1_661

theorem rank5_1_663 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,103,2,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_664 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨false,2179,4357,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_665 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨false,4363,5815,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5813 5815 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨false,4363,5813,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_666 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨false,5821,8719,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_667 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨false,5821,8719,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_668 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨false,5817,8719,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5821 5817 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨false,5821,8719,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_1_666 rank5_1_667

theorem rank5_1_669 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨false,4363,8725,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 8719 8725 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨false,4363,8719,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 5815 rank5_1_665 rank5_1_668

theorem rank5_1_670 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨false,8731,17449,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_671 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,2⟩, ⟨false,8731,9973,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 3169 rank5_1_prime3169 (by decide +kernel) (by decide +kernel) (by decide +kernel)

end OddPerfect.SpoofBox
