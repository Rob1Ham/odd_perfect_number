module

public import OddPerfect.PrimeRank5_2.Part037
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_888 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,479,2,0⟩, ⟨false,601,673,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 633 rank5_2_886 rank5_2_887

theorem rank5_2_889 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,479,2,0⟩, ⟨false,601,673,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 6 rank5_2_873 rank5_2_888

theorem rank5_2_890 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,481,523,2,0⟩, ⟨false,601,673,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 487 481 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,487,523,2,0⟩, ⟨false,601,673,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_891 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,523,2,0⟩, ⟨false,601,673,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 479 rank5_2_889 rank5_2_890

theorem rank5_2_892 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,523,2,0⟩, ⟨false,539,673,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 541 539 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,523,2,0⟩, ⟨false,541,673,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 599 rank5_2_872 rank5_2_891

theorem rank5_2_893 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,529,2,0⟩, ⟨false,449,673,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 523 529 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,523,2,0⟩, ⟨false,449,673,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 537 rank5_2_831 rank5_2_892

theorem rank5_2_894 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,531,661,2,0⟩, ⟨false,531,673,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 541 531 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,541,661,2,0⟩, ⟨false,531,673,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 4 547 542 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,541,661,2,0⟩, ⟨false,547,673,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_895 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,661,2,0⟩, ⟨false,449,673,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 529 rank5_2_893 rank5_2_894

theorem rank5_2_896 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,661,2,0⟩, ⟨false,443,673,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 449 444 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,661,2,0⟩, ⟨false,449,673,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_2_814 rank5_2_895

theorem rank5_2_897 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,661,2,0⟩, ⟨false,337,673,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 441 rank5_2_813 rank5_2_896

theorem rank5_2_898 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,439,2,0⟩, ⟨false,677,1327,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_899 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,373,2,0⟩, ⟨false,677,767,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 761 767 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,373,2,0⟩, ⟨false,677,761,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_900 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,349,2,0⟩, ⟨false,769,887,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_901 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨true,17,17,5,0⟩, ⟨false,353,373,2,0⟩, ⟨false,769,887,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_2_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_902 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,353,361,2,0⟩, ⟨false,769,823,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 359 361 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,353,359,2,0⟩, ⟨false,769,823,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_903 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,367,373,2,0⟩, ⟨false,769,823,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_904 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,367,373,2,0⟩, ⟨false,769,795,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 787 795 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,367,373,2,0⟩, ⟨false,769,787,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_905 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,367,369,2,0⟩, ⟨false,797,823,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 367 369 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,367,367,2,0⟩, ⟨false,797,823,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_906 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,373,373,2,0⟩, ⟨false,797,809,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_907 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,373,373,2,0⟩, ⟨false,811,815,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 811 815 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,373,373,2,0⟩, ⟨false,811,811,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_908 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,373,373,2,0⟩, ⟨false,817,823,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 821 817 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,373,373,2,0⟩, ⟨false,821,823,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_909 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,373,373,2,0⟩, ⟨false,811,823,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 815 rank5_2_907 rank5_2_908

theorem rank5_2_910 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,371,373,2,0⟩, ⟨false,797,823,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 373 371 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,373,373,2,0⟩, ⟨false,797,823,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 809 rank5_2_906 rank5_2_909

theorem rank5_2_911 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,367,373,2,0⟩, ⟨false,797,823,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 369 rank5_2_905 rank5_2_910

end OddPerfect.SpoofBox
