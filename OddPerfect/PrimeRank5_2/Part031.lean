module

public import OddPerfect.PrimeRank5_2.Part030
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_720 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,2,0⟩, ⟨false,8731,9309,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 9293 9309 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,2,0⟩, ⟨false,8731,9293,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_721 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9311,9973,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_2_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_722 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,8⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9311,9973,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_723 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9311,9467,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_724 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9473,9549,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 9547 9549 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9473,9547,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_725 : PrimeCovered (#v[⟨false,3,3,14,14⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9551,9629,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_726 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,2,2⟩, ⟨false,9551,9629,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_727 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,5⟩, ⟨false,263,263,4,0⟩, ⟨false,9551,9587,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_728 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,9,0⟩, ⟨false,263,263,4,0⟩, ⟨false,9551,9567,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 9551 9567 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,9,0⟩, ⟨false,263,263,4,0⟩, ⟨false,9551,9551,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_729 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,9,0⟩, ⟨false,263,263,4,0⟩, ⟨false,9569,9587,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 9587 9569 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,9,0⟩, ⟨false,263,263,4,0⟩, ⟨false,9587,9587,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_730 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,9,0⟩, ⟨false,263,263,4,0⟩, ⟨false,9551,9587,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 9567 rank5_2_728 rank5_2_729

theorem rank5_2_731 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,4,0⟩, ⟨false,9551,9589,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 9587 9589 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,4,0⟩, ⟨false,9551,9587,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 5 rank5_2_727 rank5_2_730

theorem rank5_2_732 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,4,0⟩, ⟨false,9591,9629,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 9601 9591 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,4,0⟩, ⟨false,9601,9629,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_733 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,4,0⟩, ⟨false,9551,9629,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 9589 rank5_2_731 rank5_2_732

theorem rank5_2_734 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9551,9629,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .exponent 2 rank5_2_726 rank5_2_733

theorem rank5_2_735 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9551,9629,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 14 rank5_2_725 rank5_2_734

theorem rank5_2_736 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9469,9629,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 9473 9469 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9473,9629,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 9549 rank5_2_724 rank5_2_735

theorem rank5_2_737 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9311,9629,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 9467 rank5_2_723 rank5_2_736

theorem rank5_2_738 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9631,9973,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_739 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9311,9973,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 9629 rank5_2_737 rank5_2_738

theorem rank5_2_740 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9311,9973,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 8 rank5_2_722 rank5_2_739

theorem rank5_2_741 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9311,9973,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_2_721 rank5_2_740

theorem rank5_2_742 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,2,0⟩, ⟨false,8731,9975,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 9973 9975 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,2,0⟩, ⟨false,8731,9973,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 9309 rank5_2_720 rank5_2_741

theorem rank5_2_743 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9977,11633,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 10007 9977 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,2,0⟩, ⟨false,10007,11633,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
