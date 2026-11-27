module

public import OddPerfect.PrimeRank5_2.Part035
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_840 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,461,479,2,0⟩, ⟨false,541,563,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_2_834 rank5_2_839

theorem rank5_2_841 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,479,2,0⟩, ⟨false,541,567,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 563 567 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,479,2,0⟩, ⟨false,541,563,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 459 rank5_2_833 rank5_2_840

theorem rank5_2_842 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,457,2,0⟩, ⟨false,569,599,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_843 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,457,2,0⟩, ⟨false,569,583,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 577 583 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,457,2,0⟩, ⟨false,569,577,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_844 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,449,2,0⟩, ⟨false,587,591,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 587 591 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,449,2,0⟩, ⟨false,587,587,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_845 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,445,2,0⟩, ⟨false,593,599,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 443 445 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,443,2,0⟩, ⟨false,593,599,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_846 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,449,449,2,0⟩, ⟨false,593,595,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 593 595 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,449,449,2,0⟩, ⟨false,593,593,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_847 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,449,449,2,0⟩, ⟨false,597,599,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 599 597 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,449,449,2,0⟩, ⟨false,599,599,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_848 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,447,449,2,0⟩, ⟨false,593,599,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 449 447 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,449,449,2,0⟩, ⟨false,593,599,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 595 rank5_2_846 rank5_2_847

theorem rank5_2_849 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,449,2,0⟩, ⟨false,593,599,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 445 rank5_2_845 rank5_2_848

theorem rank5_2_850 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,449,2,0⟩, ⟨false,587,599,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 591 rank5_2_844 rank5_2_849

theorem rank5_2_851 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,451,457,2,0⟩, ⟨false,587,599,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 457 451 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,457,457,2,0⟩, ⟨false,587,599,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_852 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,457,2,0⟩, ⟨false,585,599,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 587 585 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,457,2,0⟩, ⟨false,587,599,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 449 rank5_2_850 rank5_2_851

theorem rank5_2_853 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,457,2,0⟩, ⟨false,569,599,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 583 rank5_2_843 rank5_2_852

theorem rank5_2_854 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,459,2,0⟩, ⟨false,569,599,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 457 459 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,457,2,0⟩, ⟨false,569,599,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_2_842 rank5_2_853

theorem rank5_2_855 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,461,479,2,0⟩, ⟨false,569,599,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_856 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,461,463,2,0⟩, ⟨false,569,571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_2_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_857 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,461,463,2,0⟩, ⟨false,569,571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_858 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,461,463,2,0⟩, ⟨false,569,571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_2_856 rank5_2_857

theorem rank5_2_859 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,461,463,2,0⟩, ⟨false,573,577,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 577 573 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,461,463,2,0⟩, ⟨false,577,577,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_860 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,461,463,2,0⟩, ⟨false,569,577,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 571 rank5_2_858 rank5_2_859

theorem rank5_2_861 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,465,467,2,0⟩, ⟨false,569,577,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 467 465 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,467,467,2,0⟩, ⟨false,569,577,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_862 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,461,469,2,0⟩, ⟨false,569,577,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 467 469 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,461,467,2,0⟩, ⟨false,569,577,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 463 rank5_2_860 rank5_2_861

theorem rank5_2_863 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,471,479,2,0⟩, ⟨false,569,577,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 479 471 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,479,479,2,0⟩, ⟨false,569,577,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
