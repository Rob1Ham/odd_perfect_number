module

public import OddPerfect.PrimeRank5_4.Part030
import OddPerfect.PrimeRank5_4.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_720 : PrimeCovered (#v[⟨false,3,3,14,14⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨true,5261,5281,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_721 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,2⟩, ⟨true,5261,5281,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_722 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,4,0⟩, ⟨true,5261,5269,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5261 5269 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,4,0⟩, ⟨true,5261,5261,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 877 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_723 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,10⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,4,0⟩, ⟨true,5273,5281,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 12207031 rank5_4_prime12207031 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_724 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,4,0⟩, ⟨true,5273,5273,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 4 293 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_725 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,4,0⟩, ⟨true,5277,5281,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5281 5277 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,4,0⟩, ⟨true,5281,5281,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_726 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,4,0⟩, ⟨true,5273,5281,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 5273 rank5_4_724 rank5_4_725

theorem rank5_4_727 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,4,0⟩, ⟨true,5273,5281,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 10 rank5_4_723 rank5_4_726

theorem rank5_4_728 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,4,0⟩, ⟨true,5261,5281,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 5269 rank5_4_722 rank5_4_727

theorem rank5_4_729 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨true,5261,5281,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .exponent 2 rank5_4_721 rank5_4_728

theorem rank5_4_730 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨true,5261,5293,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5281 5293 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨true,5261,5281,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 14 rank5_4_720 rank5_4_729

theorem rank5_4_731 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨true,5297,5333,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_732 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨true,5261,5353,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5333 5353 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨true,5261,5333,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 5293 rank5_4_730 rank5_4_731

theorem rank5_4_733 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨true,5357,5449,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5381 5357 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨true,5381,5449,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_734 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨true,5261,5449,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 5353 rank5_4_732 rank5_4_733

theorem rank5_4_735 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨true,5261,5449,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 8 rank5_4_719 rank5_4_734

theorem rank5_4_736 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨true,5261,5449,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_4_718 rank5_4_735

theorem rank5_4_737 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,269,2,0⟩, ⟨true,5257,5449,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5261 5257 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,269,2,0⟩, ⟨true,5261,5449,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_4_717 rank5_4_736

theorem rank5_4_738 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,269,2,0⟩, ⟨true,5077,5453,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5449 5453 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,269,2,0⟩, ⟨true,5077,5449,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 5253 rank5_4_716 rank5_4_737

theorem rank5_4_739 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,269,2,0⟩, ⟨true,5457,5897,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5477 5457 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,269,2,0⟩, ⟨true,5477,5897,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_740 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,269,2,0⟩, ⟨true,5077,5897,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 5453 rank5_4_738 rank5_4_739

theorem rank5_4_741 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,271,2,0⟩, ⟨true,5077,5897,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_742 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,271,2,0⟩, ⟨true,5069,5897,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5077 5069 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,271,2,0⟩, ⟨true,5077,5897,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 269 rank5_4_740 rank5_4_741

theorem rank5_4_743 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,271,2,0⟩, ⟨true,4441,5897,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 5065 rank5_4_713 rank5_4_742

end OddPerfect.SpoofBox
