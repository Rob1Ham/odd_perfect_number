module

public import OddPerfect.PrimeRank5_1.Part029
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_696 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨false,9977,11633,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 10007 9977 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨false,10007,11633,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_697 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨false,8731,11637,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 11633 11637 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨false,8731,11633,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 9975 rank5_1_695 rank5_1_696

theorem rank5_1_698 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨false,11639,17449,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 11657 11639 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨false,11657,17449,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_699 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨false,8731,17449,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 11637 rank5_1_697 rank5_1_698

theorem rank5_1_700 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨false,8731,17461,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 17449 17461 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨false,8731,17449,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_1_670 rank5_1_699

theorem rank5_1_701 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨false,17463,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 17467 17463 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨false,17467,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_702 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨false,8727,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 8731 8727 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨false,8731,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 17461 rank5_1_700 rank5_1_701

theorem rank5_1_703 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨false,4359,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 4363 4359 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨false,4363,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 8725 rank5_1_669 rank5_1_702

theorem rank5_1_704 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,99,2,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 97 99 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 4357 rank5_1_664 rank5_1_703

theorem rank5_1_705 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,101,103,2,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_706 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,103,2,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 99 rank5_1_704 rank5_1_705

theorem rank5_1_707 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,103,2,0⟩, ⟨false,2175,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2179 2175 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,103,2,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_1_663 rank5_1_706

theorem rank5_1_708 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,103,2,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2173 rank5_1_662 rank5_1_707

theorem rank5_1_709 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,103,2,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 5 rank5_1_629 rank5_1_708

theorem rank5_1_710 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,4,0⟩, ⟨false,105,113,2,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 107 105 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,4,0⟩, ⟨false,107,113,2,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_711 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,113,2,0⟩, ⟨false,1083,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1087 1083 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,113,2,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 103 rank5_1_709 rank5_1_710

theorem rank5_1_712 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,113,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1081 rank5_1_628 rank5_1_711

theorem rank5_1_713 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,2,0⟩, ⟨false,97,113,2,0⟩, ⟨false,527,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 541 527 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,2,0⟩, ⟨false,97,113,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 2 rank5_1_571 rank5_1_712

theorem rank5_1_714 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,2,0⟩, ⟨false,93,113,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 97 93 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,2,0⟩, ⟨false,97,113,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 525 rank5_1_570 rank5_1_713

theorem rank5_1_715 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,2,0⟩, ⟨false,79,113,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 91 rank5_1_569 rank5_1_714

theorem rank5_1_716 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,19,2,0⟩, ⟨false,79,113,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .base 17 rank5_1_568 rank5_1_715

theorem rank5_1_717 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,19,2,0⟩, ⟨false,79,113,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 6 rank5_1_567 rank5_1_716

theorem rank5_1_718 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,19,2,0⟩, ⟨false,59,117,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 113 117 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,19,2,0⟩, ⟨false,59,113,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 77 rank5_1_554 rank5_1_717

theorem rank5_1_719 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,127,251,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
