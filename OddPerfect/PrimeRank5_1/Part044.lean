module

public import OddPerfect.PrimeRank5_1.Part043
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_1032 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5283,5303,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5297 5283 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5297,5303,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1033 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5261,5303,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 5281 rank5_1_1031 rank5_1_1032

theorem rank5_1_1034 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5261,5305,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5303 5305 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5261,5303,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 9 rank5_1_1022 rank5_1_1033

theorem rank5_1_1035 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5307,5351,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5309 5307 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5309,5351,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1036 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5259,5351,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5261 5259 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5261,5351,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 5305 rank5_1_1034 rank5_1_1035

theorem rank5_1_1037 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5167,5351,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 5257 rank5_1_1021 rank5_1_1036

theorem rank5_1_1038 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5167,5351,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_1_1020 rank5_1_1037

theorem rank5_1_1039 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5163,5351,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5167 5163 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5167,5351,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_1_1019 rank5_1_1038

theorem rank5_1_1040 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,269,2,0⟩, ⟨false,4987,5367,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5351 5367 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,269,2,0⟩, ⟨false,4987,5351,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 5161 rank5_1_1018 rank5_1_1039

theorem rank5_1_1041 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5369,5813,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5381 5369 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5381,5813,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1042 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,269,2,0⟩, ⟨false,4985,5813,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 4987 4985 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,269,2,0⟩, ⟨false,4987,5813,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 5367 rank5_1_1040 rank5_1_1041

theorem rank5_1_1043 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,267,269,2,0⟩, ⟨false,4363,5813,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 269 267 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,269,2,0⟩, ⟨false,4363,5813,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 4983 rank5_1_1017 rank5_1_1042

theorem rank5_1_1044 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,269,2,0⟩, ⟨false,4363,5813,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 265 rank5_1_1016 rank5_1_1043

theorem rank5_1_1045 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,269,2,0⟩, ⟨false,4363,5815,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5813 5815 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,269,2,0⟩, ⟨false,4363,5813,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_1_1015 rank5_1_1044

theorem rank5_1_1046 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,269,2,0⟩, ⟨false,5821,8719,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1047 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,265,2,0⟩, ⟨false,5821,8719,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 263 265 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,263,2,0⟩, ⟨false,5821,8719,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1048 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,267,269,2,0⟩, ⟨false,5821,8719,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 269 267 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5821,8719,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1049 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,269,2,0⟩, ⟨false,5821,8719,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 265 rank5_1_1047 rank5_1_1048

theorem rank5_1_1050 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,269,2,0⟩, ⟨false,5817,8719,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5821 5817 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,269,2,0⟩, ⟨false,5821,8719,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_1_1046 rank5_1_1049

theorem rank5_1_1051 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,269,2,0⟩, ⟨false,4363,8719,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 5815 rank5_1_1045 rank5_1_1050

theorem rank5_1_1052 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,269,2,0⟩, ⟨false,4363,8725,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 8719 8725 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,269,2,0⟩, ⟨false,4363,8719,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 261 rank5_1_1014 rank5_1_1051

theorem rank5_1_1053 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨false,8731,17461,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 17449 17461 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨false,8731,17449,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1054 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨false,17467,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1055 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨false,17467,34933,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 34919 34933 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨false,17467,34919,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
