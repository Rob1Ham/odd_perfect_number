module

public import OddPerfect.PrimeRank5_1.Part037
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_888 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1199,1237,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1201 1199 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1201,1237,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_889 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1163,1237,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1197 rank5_1_887 rank5_1_888

theorem rank5_1_890 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1159,1237,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1163 1159 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1163,1237,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_1_880 rank5_1_889

theorem rank5_1_891 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1087,1237,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1157 rank5_1_879 rank5_1_890

theorem rank5_1_892 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1239,1439,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1249 1239 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1249,1439,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_893 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1087,1445,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1439 1445 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1087,1439,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1237 rank5_1_891 rank5_1_892

theorem rank5_1_894 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1447,2161,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_895 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1087,2161,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1445 rank5_1_893 rank5_1_894

theorem rank5_1_896 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1087,2173,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2161 2173 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1087,2161,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_1_878 rank5_1_895

theorem rank5_1_897 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,2175,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2179 2175 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_898 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2173 rank5_1_896 rank5_1_897

theorem rank5_1_899 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1083,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1087 1083 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 5 rank5_1_877 rank5_1_898

theorem rank5_1_900 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,2⟩, ⟨false,257,509,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 2 3 307 (by norm_num) (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1081 rank5_1_876 rank5_1_899

theorem rank5_1_901 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,5⟩, ⟨false,17,17,4,0⟩, ⟨false,257,337,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_902 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,291,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 283 291 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,283,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_903 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,337,2,0⟩, ⟨false,541,717,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 709 717 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,337,2,0⟩, ⟨false,541,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_904 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,337,2,0⟩, ⟨false,719,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_905 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,337,2,0⟩, ⟨false,719,859,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_906 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,313,2,0⟩, ⟨false,863,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_907 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,317,337,2,0⟩, ⟨false,863,955,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 953 955 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,317,337,2,0⟩, ⟨false,863,953,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_908 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,317,325,2,0⟩, ⟨false,967,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 317 325 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,317,317,2,0⟩, ⟨false,967,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_909 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,337,2,0⟩, ⟨false,967,1015,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1013 1015 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,337,2,0⟩, ⟨false,967,1013,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_910 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,337,2,0⟩, ⟨false,1019,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_911 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,333,2,0⟩, ⟨false,1019,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 331 333 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1019,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
