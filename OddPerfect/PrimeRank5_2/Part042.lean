module

public import OddPerfect.PrimeRank5_2.Part041
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_984 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,373,2,0⟩, ⟨false,907,1077,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1069 1077 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,373,2,0⟩, ⟨false,907,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 349 rank5_2_968 rank5_2_983

theorem rank5_2_985 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨true,17,17,5,0⟩, ⟨false,331,349,2,0⟩, ⟨false,1087,1327,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_2_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_986 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,337,2,0⟩, ⟨false,1087,1193,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_987 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1087,1107,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1103 1107 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1087,1103,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_988 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1109,1117,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_989 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1123,1129,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_2_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_990 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,8⟩, ⟨true,17,17,5,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1123,1129,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_991 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1123,1125,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1123 1125 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1123,1123,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_992 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1127,1129,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1129 1127 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1129,1129,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_993 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1123,1129,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1125 rank5_2_991 rank5_2_992

theorem rank5_2_994 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1123,1129,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 8 rank5_2_990 rank5_2_993

theorem rank5_2_995 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1119,1129,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1123 1119 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1123,1129,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 12 rank5_2_989 rank5_2_994

theorem rank5_2_996 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1109,1129,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1117 rank5_2_988 rank5_2_995

theorem rank5_2_997 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,333,2,0⟩, ⟨false,1087,1129,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 331 333 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1087,1129,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1107 rank5_2_987 rank5_2_996

theorem rank5_2_998 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,335,337,2,0⟩, ⟨false,1087,1129,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 337 335 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1087,1129,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_999 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,337,2,0⟩, ⟨false,1087,1137,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1129 1137 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,337,2,0⟩, ⟨false,1087,1129,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 333 rank5_2_997 rank5_2_998

theorem rank5_2_1000 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,337,2,0⟩, ⟨false,1139,1193,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1151 1139 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,337,2,0⟩, ⟨false,1151,1193,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1001 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,337,2,0⟩, ⟨false,1087,1193,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1137 rank5_2_999 rank5_2_1000

theorem rank5_2_1002 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,339,2,0⟩, ⟨false,1087,1193,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 337 339 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,337,2,0⟩, ⟨false,1087,1193,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_2_986 rank5_2_1001

theorem rank5_2_1003 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,341,349,2,0⟩, ⟨false,1087,1193,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 347 341 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,347,349,2,0⟩, ⟨false,1087,1193,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1004 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,349,2,0⟩, ⟨false,1087,1195,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1193 1195 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,349,2,0⟩, ⟨false,1087,1193,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 339 rank5_2_1002 rank5_2_1003

theorem rank5_2_1005 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,349,2,0⟩, ⟨false,1197,1327,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1201 1197 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,349,2,0⟩, ⟨false,1201,1327,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_1006 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,349,2,0⟩, ⟨false,1087,1327,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1195 rank5_2_1004 rank5_2_1005

theorem rank5_2_1007 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,349,2,0⟩, ⟨false,1087,1327,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 6 rank5_2_985 rank5_2_1006

end OddPerfect.SpoofBox
