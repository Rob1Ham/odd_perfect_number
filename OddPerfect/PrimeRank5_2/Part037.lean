module

public import OddPerfect.PrimeRank5_2.Part036
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_864 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,461,479,2,0⟩, ⟨false,569,583,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 577 583 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,461,479,2,0⟩, ⟨false,569,577,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 469 rank5_2_862 rank5_2_863

theorem rank5_2_865 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,461,479,2,0⟩, ⟨false,585,599,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 587 585 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,461,479,2,0⟩, ⟨false,587,599,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_866 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,461,479,2,0⟩, ⟨false,569,599,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 583 rank5_2_864 rank5_2_865

theorem rank5_2_867 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,461,479,2,0⟩, ⟨false,569,599,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_2_855 rank5_2_866

theorem rank5_2_868 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,479,2,0⟩, ⟨false,569,599,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 459 rank5_2_854 rank5_2_867

theorem rank5_2_869 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,479,2,0⟩, ⟨false,541,599,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 567 rank5_2_841 rank5_2_868

theorem rank5_2_870 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,479,2,0⟩, ⟨false,541,599,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 6 rank5_2_832 rank5_2_869

theorem rank5_2_871 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,481,523,2,0⟩, ⟨false,541,599,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 487 481 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,487,523,2,0⟩, ⟨false,541,599,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_872 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,523,2,0⟩, ⟨false,541,599,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 479 rank5_2_870 rank5_2_871

theorem rank5_2_873 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨true,17,17,5,0⟩, ⟨false,443,479,2,0⟩, ⟨false,601,673,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_2_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_874 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,457,2,0⟩, ⟨false,601,631,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_875 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,445,2,0⟩, ⟨false,601,601,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 443 445 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,443,2,0⟩, ⟨false,601,601,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_876 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,447,449,2,0⟩, ⟨false,601,601,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 449 447 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,449,449,2,0⟩, ⟨false,601,601,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_877 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,449,2,0⟩, ⟨false,601,605,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 601 605 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,449,2,0⟩, ⟨false,601,601,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 445 rank5_2_875 rank5_2_876

theorem rank5_2_878 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,449,2,0⟩, ⟨false,607,613,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_879 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,449,2,0⟩, ⟨false,601,613,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 605 rank5_2_877 rank5_2_878

theorem rank5_2_880 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,451,457,2,0⟩, ⟨false,601,613,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 457 451 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,457,457,2,0⟩, ⟨false,601,613,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_881 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,457,2,0⟩, ⟨false,601,615,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 613 615 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,457,2,0⟩, ⟨false,601,613,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 449 rank5_2_879 rank5_2_880

theorem rank5_2_882 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,457,2,0⟩, ⟨false,617,631,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_883 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,457,2,0⟩, ⟨false,601,631,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 615 rank5_2_881 rank5_2_882

theorem rank5_2_884 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,459,2,0⟩, ⟨false,601,631,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 457 459 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,457,2,0⟩, ⟨false,601,631,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_2_874 rank5_2_883

theorem rank5_2_885 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,461,479,2,0⟩, ⟨false,601,631,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_886 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,479,2,0⟩, ⟨false,601,633,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 631 633 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,479,2,0⟩, ⟨false,601,631,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 459 rank5_2_884 rank5_2_885

theorem rank5_2_887 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,479,2,0⟩, ⟨false,635,673,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 641 635 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,479,2,0⟩, ⟨false,641,673,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
