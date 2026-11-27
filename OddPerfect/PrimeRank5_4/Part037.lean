module

public import OddPerfect.PrimeRank5_4.Part036
import OddPerfect.PrimeRank5_4.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_864 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,495,2,0⟩, ⟨true,557,677,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 491 495 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,491,2,0⟩, ⟨true,557,677,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 609 rank5_4_862 rank5_4_863

theorem rank5_4_865 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,497,541,2,0⟩, ⟨true,557,677,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 499 497 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,499,541,2,0⟩, ⟨true,557,677,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_866 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,541,2,0⟩, ⟨true,549,677,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 557 549 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,541,2,0⟩, ⟨true,557,677,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 495 rank5_4_864 rank5_4_865

theorem rank5_4_867 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,543,2,0⟩, ⟨true,461,677,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 541 543 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,541,2,0⟩, ⟨true,461,677,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 545 rank5_4_839 rank5_4_866

theorem rank5_4_868 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,545,673,2,0⟩, ⟨true,545,677,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 547 545 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,547,673,2,0⟩, ⟨true,545,677,1,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 4 557 548 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,547,673,2,0⟩, ⟨true,557,677,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_869 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,673,2,0⟩, ⟨true,461,677,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 543 rank5_4_867 rank5_4_868

theorem rank5_4_870 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,451,673,2,0⟩, ⟨true,453,677,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 457 451 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,673,2,0⟩, ⟨true,453,677,1,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 4 461 458 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,673,2,0⟩, ⟨true,461,677,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_4_816 rank5_4_869

theorem rank5_4_871 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,673,2,0⟩, ⟨true,349,697,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 677 697 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,673,2,0⟩, ⟨true,349,677,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 449 rank5_4_815 rank5_4_870

theorem rank5_4_872 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,449,2,0⟩, ⟨true,701,1381,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_873 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,353,2,0⟩, ⟨true,701,797,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_874 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨false,337,353,2,0⟩, ⟨true,809,929,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_4_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_875 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,353,2,0⟩, ⟨true,809,861,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 857 861 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,353,2,0⟩, ⟨true,809,857,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_876 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,343,2,0⟩, ⟨true,877,929,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 337 343 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,337,2,0⟩, ⟨true,877,929,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_877 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,353,2,0⟩, ⟨true,877,929,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_878 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,353,2,0⟩, ⟨true,877,901,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 881 901 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,353,2,0⟩, ⟨true,877,881,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_879 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,353,2,0⟩, ⟨true,905,929,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 929 905 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,353,2,0⟩, ⟨true,929,929,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 31 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_880 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,353,2,0⟩, ⟨true,877,929,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 901 rank5_4_878 rank5_4_879

theorem rank5_4_881 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,345,353,2,0⟩, ⟨true,877,929,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 347 345 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,353,2,0⟩, ⟨true,877,929,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_4_877 rank5_4_880

theorem rank5_4_882 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,353,2,0⟩, ⟨true,865,929,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 877 865 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,353,2,0⟩, ⟨true,877,929,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 343 rank5_4_876 rank5_4_881

theorem rank5_4_883 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,353,2,0⟩, ⟨true,809,929,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 861 rank5_4_875 rank5_4_882

theorem rank5_4_884 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,353,2,0⟩, ⟨true,801,929,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 809 801 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,353,2,0⟩, ⟨true,809,929,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_4_874 rank5_4_883

theorem rank5_4_885 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,357,2,0⟩, ⟨true,701,929,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 353 357 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,353,2,0⟩, ⟨true,701,929,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 797 rank5_4_873 rank5_4_884

theorem rank5_4_886 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨false,359,383,2,0⟩, ⟨true,701,797,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_4_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_887 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,359,369,2,0⟩, ⟨true,701,797,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 367 369 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,359,367,2,0⟩, ⟨true,701,797,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
