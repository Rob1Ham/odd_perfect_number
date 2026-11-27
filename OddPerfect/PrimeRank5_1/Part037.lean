module

public import OddPerfect.PrimeRank5_1.Part036
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_864 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,461,509,2,0⟩, ⟨false,495,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 499 495 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,461,509,2,0⟩, ⟨false,499,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 483 rank5_1_852 rank5_1_863

theorem rank5_1_865 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,461,509,2,0⟩, ⟨false,467,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 493 rank5_1_851 rank5_1_864

theorem rank5_1_866 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,509,2,0⟩, ⟨false,467,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 459 rank5_1_850 rank5_1_865

theorem rank5_1_867 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,509,2,0⟩, ⟨false,421,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 465 rank5_1_849 rank5_1_866

theorem rank5_1_868 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,413,509,2,0⟩, ⟨false,419,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 419 413 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,509,2,0⟩, ⟨false,419,523,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 4 421 420 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,509,2,0⟩, ⟨false,421,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_1_848 rank5_1_867

theorem rank5_1_869 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,509,2,0⟩, ⟨false,419,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 411 rank5_1_847 rank5_1_868

theorem rank5_1_870 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,509,2,0⟩, ⟨false,349,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 417 rank5_1_846 rank5_1_869

theorem rank5_1_871 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,4,0⟩, ⟨false,343,509,2,0⟩, ⟨false,343,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 347 343 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,509,2,0⟩, ⟨false,343,523,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 4 349 348 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,509,2,0⟩, ⟨false,349,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 5 rank5_1_845 rank5_1_870

theorem rank5_1_872 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,509,2,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 341 rank5_1_844 rank5_1_871

theorem rank5_1_873 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,257,509,2,0⟩, ⟨false,263,525,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 523 525 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,257,509,2,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 2 rank5_1_843 rank5_1_872

theorem rank5_1_874 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,5⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_875 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_876 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,541,1081,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1069 1081 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 5 rank5_1_874 rank5_1_875

theorem rank5_1_877 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,5⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_878 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1087,2161,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_879 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1087,1157,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1153 1157 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1087,1153,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_880 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1163,1237,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_881 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1163,1171,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_1_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_882 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1163,1165,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1163 1165 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1163,1163,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_883 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1167,1171,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1171 1167 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1171,1171,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_884 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1163,1171,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1165 rank5_1_882 rank5_1_883

theorem rank5_1_885 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1163,1177,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1171 1177 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1163,1171,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 12 rank5_1_881 rank5_1_884

theorem rank5_1_886 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1179,1193,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1181 1179 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1181,1193,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_887 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1163,1197,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1193 1197 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1163,1193,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1177 rank5_1_885 rank5_1_886

end OddPerfect.SpoofBox
