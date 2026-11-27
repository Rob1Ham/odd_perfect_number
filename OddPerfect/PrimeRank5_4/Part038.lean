module

public import OddPerfect.PrimeRank5_4.Part037
import OddPerfect.PrimeRank5_4.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_888 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,373,383,2,0⟩, ⟨true,701,745,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 733 745 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,373,383,2,0⟩, ⟨true,701,733,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_889 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,373,383,2,0⟩, ⟨true,757,797,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_890 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,373,377,2,0⟩, ⟨true,757,797,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 373 377 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,373,373,2,0⟩, ⟨true,757,797,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_891 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,379,379,2,0⟩, ⟨true,757,773,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_892 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,383,383,2,0⟩, ⟨true,757,761,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_893 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,4⟩, ⟨false,383,383,2,0⟩, ⟨true,769,773,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 88741 rank5_4_prime88741 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_894 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,383,383,2,0⟩, ⟨true,769,773,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_4_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_895 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,8⟩, ⟨false,17,17,6,0⟩, ⟨false,383,383,2,0⟩, ⟨true,769,773,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_896 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,383,383,2,0⟩, ⟨true,769,769,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 4 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_897 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,383,383,2,0⟩, ⟨true,773,773,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 4 43 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_898 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,383,383,2,0⟩, ⟨true,769,773,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 769 rank5_4_896 rank5_4_897

theorem rank5_4_899 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,383,383,2,0⟩, ⟨true,769,773,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 8 rank5_4_895 rank5_4_898

theorem rank5_4_900 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,383,383,2,0⟩, ⟨true,769,773,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_4_894 rank5_4_899

theorem rank5_4_901 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,383,383,2,0⟩, ⟨true,765,773,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 769 765 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,383,383,2,0⟩, ⟨true,769,773,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_4_893 rank5_4_900

theorem rank5_4_902 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,381,383,2,0⟩, ⟨true,757,773,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 383 381 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,383,383,2,0⟩, ⟨true,757,773,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 761 rank5_4_892 rank5_4_901

theorem rank5_4_903 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,379,383,2,0⟩, ⟨true,757,773,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 379 rank5_4_891 rank5_4_902

theorem rank5_4_904 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,379,383,2,0⟩, ⟨true,777,797,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 797 777 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,379,383,2,0⟩, ⟨true,797,797,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_905 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,379,383,2,0⟩, ⟨true,757,797,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 773 rank5_4_903 rank5_4_904

theorem rank5_4_906 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,373,383,2,0⟩, ⟨true,757,797,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 377 rank5_4_890 rank5_4_905

theorem rank5_4_907 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,373,383,2,0⟩, ⟨true,749,797,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 757 749 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,373,383,2,0⟩, ⟨true,757,797,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_4_889 rank5_4_906

theorem rank5_4_908 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,371,383,2,0⟩, ⟨true,701,797,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 373 371 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,373,383,2,0⟩, ⟨true,701,797,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 745 rank5_4_888 rank5_4_907

theorem rank5_4_909 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,359,383,2,0⟩, ⟨true,701,797,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 369 rank5_4_887 rank5_4_908

theorem rank5_4_910 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,359,383,2,0⟩, ⟨true,701,797,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 6 rank5_4_886 rank5_4_909

theorem rank5_4_911 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨false,359,383,2,0⟩, ⟨true,809,929,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_4_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

end OddPerfect.SpoofBox
