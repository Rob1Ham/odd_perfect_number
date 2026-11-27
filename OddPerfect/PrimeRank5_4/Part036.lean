module

public import OddPerfect.PrimeRank5_4.Part035
import OddPerfect.PrimeRank5_4.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_840 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨false,457,491,2,0⟩, ⟨true,557,601,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_4_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_841 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,467,2,0⟩, ⟨true,557,577,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_842 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,467,2,0⟩, ⟨true,557,565,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 557 565 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,467,2,0⟩, ⟨true,557,557,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 31 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_843 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,461,2,0⟩, ⟨true,569,569,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 4 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_844 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,457,2,0⟩, ⟨true,577,577,1,1⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_845 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,459,461,2,0⟩, ⟨true,577,577,1,1⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 461 459 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,461,461,2,0⟩, ⟨true,577,577,1,1⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_846 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,461,2,0⟩, ⟨true,577,577,1,1⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 457 rank5_4_844 rank5_4_845

theorem rank5_4_847 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,457,2,0⟩, ⟨true,577,577,5,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_848 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,459,461,2,0⟩, ⟨true,577,577,5,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 461 459 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,461,461,2,0⟩, ⟨true,577,577,5,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_849 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,461,2,0⟩, ⟨true,577,577,5,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 457 rank5_4_847 rank5_4_848

theorem rank5_4_850 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,461,2,0⟩, ⟨true,573,577,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 577 573 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,461,2,0⟩, ⟨true,577,577,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .exponent 1 rank5_4_846 rank5_4_849

theorem rank5_4_851 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,461,2,0⟩, ⟨true,569,577,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 569 rank5_4_843 rank5_4_850

theorem rank5_4_852 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,463,467,2,0⟩, ⟨true,569,569,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 4 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_853 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,463,467,2,0⟩, ⟨true,573,577,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 577 573 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,463,467,2,0⟩, ⟨true,577,577,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_854 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,463,467,2,0⟩, ⟨true,569,577,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 569 rank5_4_852 rank5_4_853

theorem rank5_4_855 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,467,2,0⟩, ⟨true,569,577,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 461 rank5_4_851 rank5_4_854

theorem rank5_4_856 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,467,2,0⟩, ⟨true,557,577,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 565 rank5_4_842 rank5_4_855

theorem rank5_4_857 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,467,2,0⟩, ⟨true,557,577,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_4_841 rank5_4_856

theorem rank5_4_858 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,467,2,0⟩, ⟨true,581,601,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 593 581 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,467,2,0⟩, ⟨true,593,601,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_859 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,473,2,0⟩, ⟨true,557,601,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 467 473 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,467,2,0⟩, ⟨true,557,601,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 577 rank5_4_857 rank5_4_858

theorem rank5_4_860 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,475,491,2,0⟩, ⟨true,557,601,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 479 475 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,479,491,2,0⟩, ⟨true,557,601,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_861 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,491,2,0⟩, ⟨true,557,601,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 473 rank5_4_859 rank5_4_860

theorem rank5_4_862 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,491,2,0⟩, ⟨true,557,609,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 601 609 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,491,2,0⟩, ⟨true,557,601,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_4_840 rank5_4_861

theorem rank5_4_863 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,491,2,0⟩, ⟨true,613,677,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
