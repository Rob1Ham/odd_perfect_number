module

public import OddPerfect.PrimeRank5_4.Part045
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_1080 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,31,2,0⟩, ⟨false,41,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 81 rank5_4_1078 rank5_4_1079

theorem rank5_4_1081 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,31,2,0⟩, ⟨false,39,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 41 39 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,31,2,0⟩, ⟨false,41,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .base 21 rank5_4_1013 rank5_4_1080

theorem rank5_4_1082 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,33,2,0⟩, ⟨false,19,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 2 31 33 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,31,2,0⟩, ⟨false,19,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 37 rank5_4_196 rank5_4_1081

theorem rank5_4_1083 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,35,0,2,0⟩, ⟨false,35,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 2 37 35 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,37,0,2,0⟩, ⟨false,35,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 3 41 38 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,37,0,2,0⟩, ⟨false,41,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_1084 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,0,2,0⟩, ⟨false,19,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .base 33 rank5_4_1082 rank5_4_1083

theorem rank5_4_1085 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,0,2,0⟩, ⟨false,19,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 4 rank5_4_169 rank5_4_1084

theorem rank5_4_1086 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,17,0,2,0⟩, ⟨false,19,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 2 rank5_4_168 rank5_4_1085

theorem rank5_4_1087 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,17,0,2,0⟩, ⟨false,19,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_1088 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,7,2,0⟩, ⟨false,15,0,2,0⟩, ⟨false,15,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 2 17 15 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,7,2,0⟩, ⟨false,17,0,2,0⟩, ⟨false,15,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 3 19 18 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,7,2,0⟩, ⟨false,17,0,2,0⟩, ⟨false,19,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .base 5 rank5_4_1086 rank5_4_1087

theorem rank5_4_1089 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,9,2,0⟩, ⟨false,7,0,2,0⟩, ⟨false,11,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 1 7 9 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,7,2,0⟩, ⟨false,7,0,2,0⟩, ⟨false,11,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .base 13 rank5_4_157 rank5_4_1088

theorem rank5_4_1090 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,11,0,2,0⟩, ⟨false,11,0,2,0⟩, ⟨false,11,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 2 13 12 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,11,0,2,0⟩, ⟨false,13,0,2,0⟩, ⟨false,11,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 3 17 14 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,11,0,2,0⟩, ⟨false,13,0,2,0⟩, ⟨false,17,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_1091 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,0,2,0⟩, ⟨false,7,0,2,0⟩, ⟨false,11,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .base 9 rank5_4_1089 rank5_4_1090

theorem rank5_4_1092 : PrimeCovered (#v[⟨false,3,3,2,0⟩, ⟨false,3,0,2,0⟩, ⟨false,3,0,2,0⟩, ⟨false,3,0,2,0⟩, ⟨true,258,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 1 5 4 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,0⟩, ⟨false,5,0,2,0⟩, ⟨false,3,0,2,0⟩, ⟨false,3,0,2,0⟩, ⟨true,258,0,1,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 2 7 6 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,0⟩, ⟨false,5,0,2,0⟩, ⟨false,7,0,2,0⟩, ⟨false,3,0,2,0⟩, ⟨true,258,0,1,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 3 11 8 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,0⟩, ⟨false,5,0,2,0⟩, ⟨false,7,0,2,0⟩, ⟨false,11,0,2,0⟩, ⟨true,258,0,1,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 4 269 258 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,0⟩, ⟨false,5,0,2,0⟩, ⟨false,7,0,2,0⟩, ⟨false,11,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 2 rank5_4_70 rank5_4_1091

theorem closed_prime_5_4 : PrimeCovered (primeInitial (4 : Fin 5)) := rank5_4_1092

end OddPerfect.SpoofBox
