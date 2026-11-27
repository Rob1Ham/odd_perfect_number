module

public import OddPerfect.PrimeRank5_1.Part045
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_1080 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨false,55905,69877,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 55921 55905 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨false,55921,69877,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 62123 rank5_1_1060 rank5_1_1079

theorem rank5_1_1081 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨false,46589,69877,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 55903 rank5_1_1059 rank5_1_1080

theorem rank5_1_1082 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨false,46589,69877,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_1_1058 rank5_1_1081

theorem rank5_1_1083 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨false,46587,69877,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 46589 46587 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨false,46589,69877,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_1_1057 rank5_1_1082

theorem rank5_1_1084 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨false,34939,69877,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 46585 rank5_1_1056 rank5_1_1083

theorem rank5_1_1085 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨false,69879,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 69899 69879 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨false,69899,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1086 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨false,34935,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 34939 34935 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨false,34939,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 69877 rank5_1_1084 rank5_1_1085

theorem rank5_1_1087 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨false,17467,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 34933 rank5_1_1055 rank5_1_1086

theorem rank5_1_1088 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨false,17463,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 17467 17463 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨false,17467,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_1_1054 rank5_1_1087

theorem rank5_1_1089 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,261,2,0⟩, ⟨false,8731,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 257 261 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨false,8731,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 17461 rank5_1_1053 rank5_1_1088

theorem rank5_1_1090 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,269,2,0⟩, ⟨false,8731,17449,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1091 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,263,2,0⟩, ⟨false,8731,9309,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 9293 9309 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,263,2,0⟩, ⟨false,8731,9293,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1092 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,4⟩, ⟨false,263,263,2,0⟩, ⟨false,9311,9973,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 88741 rank5_1_prime88741 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1093 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9311,9973,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_1_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1094 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9311,9467,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1095 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9473,9549,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 9547 9549 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9473,9547,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1096 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,9⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9551,9629,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1097 : PrimeCovered (#v[⟨false,3,3,14,14⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,0⟩, ⟨false,9551,9629,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1098 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,2,2⟩, ⟨false,9551,9629,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1099 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,4,0⟩, ⟨false,9551,9567,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 9551 9567 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,4,0⟩, ⟨false,9551,9551,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1100 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,4,0⟩, ⟨false,9569,9587,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 9587 9569 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,4,0⟩, ⟨false,9587,9587,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1101 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,4,0⟩, ⟨false,9551,9589,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 9587 9589 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,4,0⟩, ⟨false,9551,9587,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 9567 rank5_1_1099 rank5_1_1100

theorem rank5_1_1102 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,4,0⟩, ⟨false,9591,9629,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 9601 9591 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,4,0⟩, ⟨false,9601,9629,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1103 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,263,263,4,0⟩, ⟨false,9551,9629,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 9589 rank5_1_1101 rank5_1_1102

end OddPerfect.SpoofBox
