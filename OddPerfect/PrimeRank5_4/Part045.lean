module

public import OddPerfect.PrimeRank5_4.Part044
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_1056 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,61,2,0⟩, ⟨true,269,305,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 293 305 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,61,2,0⟩, ⟨true,269,293,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_4_1046 rank5_4_1055

theorem rank5_4_1057 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,61,2,0⟩, ⟨true,313,353,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_1058 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,59,2,0⟩, ⟨true,313,329,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 317 329 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,59,2,0⟩, ⟨true,313,317,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_1059 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,59,2,0⟩, ⟨true,333,353,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 337 333 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,59,2,0⟩, ⟨true,337,353,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_1060 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,59,2,0⟩, ⟨true,313,353,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 329 rank5_4_1058 rank5_4_1059

theorem rank5_4_1061 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,4,0⟩, ⟨false,61,61,2,0⟩, ⟨true,313,353,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_1062 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,61,2,0⟩, ⟨true,313,353,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 59 rank5_4_1060 rank5_4_1061

theorem rank5_4_1063 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,61,2,0⟩, ⟨true,309,353,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 313 309 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,61,2,0⟩, ⟨true,313,353,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_4_1057 rank5_4_1062

theorem rank5_4_1064 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,4,0⟩, ⟨false,59,61,2,0⟩, ⟨true,269,353,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 305 rank5_4_1056 rank5_4_1063

theorem rank5_4_1065 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨false,59,61,2,0⟩, ⟨true,269,353,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 2 rank5_4_1045 rank5_4_1064

theorem rank5_4_1066 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨false,59,61,2,0⟩, ⟨true,357,521,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 373 357 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨false,59,61,2,0⟩, ⟨true,373,521,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_1067 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨false,59,61,2,0⟩, ⟨true,269,521,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 353 rank5_4_1065 rank5_4_1066

theorem rank5_4_1068 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨false,63,67,2,0⟩, ⟨true,269,521,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 67 63 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨false,67,67,2,0⟩, ⟨true,269,521,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_1069 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨false,59,67,2,0⟩, ⟨true,269,537,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 521 537 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨false,59,67,2,0⟩, ⟨true,269,521,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 61 rank5_4_1067 rank5_4_1068

theorem rank5_4_1070 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨false,59,67,2,0⟩, ⟨true,541,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_1071 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨false,59,67,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 537 rank5_4_1069 rank5_4_1070

theorem rank5_4_1072 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨false,69,79,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 71 69 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨false,71,79,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_1073 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨false,59,79,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 67 rank5_4_1071 rank5_4_1072

theorem rank5_4_1074 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,23,2,0⟩, ⟨false,59,79,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 4 rank5_4_1044 rank5_4_1073

theorem rank5_4_1075 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,25,2,0⟩, ⟨false,59,79,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 2 23 25 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,23,2,0⟩, ⟨false,59,79,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 6 rank5_4_1043 rank5_4_1074

theorem rank5_4_1076 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,27,31,2,0⟩, ⟨false,59,79,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 2 29 27 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,29,31,2,0⟩, ⟨false,59,79,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_1077 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,31,2,0⟩, ⟨false,55,79,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 59 55 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,31,2,0⟩, ⟨false,59,79,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .base 25 rank5_4_1075 rank5_4_1076

theorem rank5_4_1078 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,31,2,0⟩, ⟨false,41,81,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 79 81 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,31,2,0⟩, ⟨false,41,79,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 53 rank5_4_1042 rank5_4_1077

theorem rank5_4_1079 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,31,2,0⟩, ⟨false,83,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
