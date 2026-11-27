module

public import OddPerfect.PrimeRank5_4.Part029
import OddPerfect.PrimeRank5_4.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_696 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,293,2,0⟩, ⟨true,2213,4425,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 4421 4425 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,293,2,0⟩, ⟨true,2213,4421,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 279 rank5_4_656 rank5_4_695

theorem rank5_4_697 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨false,269,277,2,0⟩, ⟨true,4441,8861,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_4_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_698 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,271,2,0⟩, ⟨true,4441,5897,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_699 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,269,2,0⟩, ⟨true,4441,5021,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_700 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,4⟩, ⟨false,271,271,2,0⟩, ⟨true,4441,4673,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 88741 rank5_4_prime88741 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_701 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,271,271,2,0⟩, ⟨true,4441,4553,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 4549 4553 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,271,271,2,0⟩, ⟨true,4441,4549,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_702 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,271,271,2,0⟩, ⟨true,4561,4673,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_4_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_703 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,8⟩, ⟨false,17,17,6,0⟩, ⟨false,271,271,2,0⟩, ⟨true,4561,4673,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_704 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,271,271,2,0⟩, ⟨true,4561,4613,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 4597 4613 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,271,271,2,0⟩, ⟨true,4561,4597,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_705 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,271,271,2,0⟩, ⟨true,4617,4673,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 4621 4617 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,271,271,2,0⟩, ⟨true,4621,4673,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_706 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,271,271,2,0⟩, ⟨true,4561,4673,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 4613 rank5_4_704 rank5_4_705

theorem rank5_4_707 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,271,271,2,0⟩, ⟨true,4561,4673,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 8 rank5_4_703 rank5_4_706

theorem rank5_4_708 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,271,271,2,0⟩, ⟨true,4557,4673,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 4561 4557 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,271,271,2,0⟩, ⟨true,4561,4673,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 12 rank5_4_702 rank5_4_707

theorem rank5_4_709 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,271,271,2,0⟩, ⟨true,4441,4673,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 4553 rank5_4_701 rank5_4_708

theorem rank5_4_710 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,271,2,0⟩, ⟨true,4441,4713,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 4673 4713 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,271,2,0⟩, ⟨true,4441,4673,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_4_700 rank5_4_709

theorem rank5_4_711 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,271,2,0⟩, ⟨true,4717,5021,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 4721 4717 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,271,2,0⟩, ⟨true,4721,5021,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_712 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,271,2,0⟩, ⟨true,4441,5021,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 4713 rank5_4_710 rank5_4_711

theorem rank5_4_713 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,271,2,0⟩, ⟨true,4441,5065,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5021 5065 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,271,2,0⟩, ⟨true,4441,5021,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 269 rank5_4_699 rank5_4_712

theorem rank5_4_714 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,4⟩, ⟨false,269,269,2,0⟩, ⟨true,5077,5237,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 88741 rank5_4_prime88741 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_715 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨true,5077,5237,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_716 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,269,2,0⟩, ⟨true,5077,5253,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5237 5253 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,269,2,0⟩, ⟨true,5077,5237,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_4_714 rank5_4_715

theorem rank5_4_717 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,4⟩, ⟨false,269,269,2,0⟩, ⟨true,5261,5449,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 88741 rank5_4_prime88741 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_718 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨true,5261,5449,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_4_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_719 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,8⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨true,5261,5449,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end OddPerfect.SpoofBox
