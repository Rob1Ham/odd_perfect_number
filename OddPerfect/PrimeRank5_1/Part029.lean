module

public import OddPerfect.PrimeRank5_1.Part028
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_672 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,4,0⟩, ⟨false,8731,9293,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_1_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_673 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,4,0⟩, ⟨false,8731,9003,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 9001 9003 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,4,0⟩, ⟨false,8731,9001,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_674 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,4⟩, ⟨false,97,97,4,0⟩, ⟨false,9007,9293,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 151 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_675 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨false,9007,9147,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 9137 9147 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨false,9007,9137,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_676 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,9⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨false,9151,9221,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_677 : PrimeCovered (#v[⟨false,3,3,14,14⟩, ⟨true,5,5,13,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨false,9151,9221,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_678 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨false,9151,9185,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 9181 9185 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨false,9151,9181,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_679 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨false,9187,9203,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_680 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨false,9209,9213,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 9209 9213 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨false,9209,9209,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_681 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨false,9215,9221,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 9221 9215 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨false,9221,9221,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_682 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨false,9205,9221,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 9209 9205 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨false,9209,9221,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 9213 rank5_1_680 rank5_1_681

theorem rank5_1_683 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨false,9187,9221,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 9203 rank5_1_679 rank5_1_682

theorem rank5_1_684 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨false,9151,9221,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 9185 rank5_1_678 rank5_1_683

theorem rank5_1_685 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,13,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨false,9151,9221,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 14 rank5_1_677 rank5_1_684

theorem rank5_1_686 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨false,9151,9221,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 9 rank5_1_676 rank5_1_685

theorem rank5_1_687 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨false,9223,9293,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 9227 9223 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨false,9227,9293,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_688 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨false,9149,9293,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 9151 9149 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨false,9151,9293,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 9221 rank5_1_686 rank5_1_687

theorem rank5_1_689 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,6,0⟩, ⟨false,97,97,4,0⟩, ⟨false,9007,9293,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 9147 rank5_1_675 rank5_1_688

theorem rank5_1_690 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,4,0⟩, ⟨false,9005,9293,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 9007 9005 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,4,0⟩, ⟨false,9007,9293,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_1_674 rank5_1_689

theorem rank5_1_691 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,4,0⟩, ⟨false,8731,9293,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 9003 rank5_1_673 rank5_1_690

theorem rank5_1_692 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,4,0⟩, ⟨false,8731,9309,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 9293 9309 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,4,0⟩, ⟨false,8731,9293,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 12 rank5_1_672 rank5_1_691

theorem rank5_1_693 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,4,0⟩, ⟨false,9311,9973,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_694 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,4,0⟩, ⟨false,8731,9973,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 9309 rank5_1_692 rank5_1_693

theorem rank5_1_695 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨false,8731,9975,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 9973 9975 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,97,97,2,0⟩, ⟨false,8731,9973,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .exponent 2 rank5_1_671 rank5_1_694

end OddPerfect.SpoofBox
