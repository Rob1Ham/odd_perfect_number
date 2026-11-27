module

public import OddPerfect.PrimeRank5_4.Part040
import OddPerfect.PrimeRank5_4.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_960 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,337,2,0⟩, ⟨true,1065,1109,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1069 1065 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,337,2,0⟩, ⟨true,1069,1109,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_961 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,337,2,0⟩, ⟨true,1021,1109,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1061 rank5_4_959 rank5_4_960

theorem rank5_4_962 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,343,2,0⟩, ⟨true,1021,1109,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 337 343 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,337,2,0⟩, ⟨true,1021,1109,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_4_952 rank5_4_961

theorem rank5_4_963 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,345,353,2,0⟩, ⟨true,1021,1109,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 347 345 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,353,2,0⟩, ⟨true,1021,1109,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_964 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,353,2,0⟩, ⟨true,1017,1109,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1021 1017 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,353,2,0⟩, ⟨true,1021,1109,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 343 rank5_4_962 rank5_4_963

theorem rank5_4_965 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,353,2,0⟩, ⟨true,937,1109,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1013 rank5_4_951 rank5_4_964

theorem rank5_4_966 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,353,2,0⟩, ⟨true,937,1113,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1109 1113 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,353,2,0⟩, ⟨true,937,1109,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_4_942 rank5_4_965

theorem rank5_4_967 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,353,2,0⟩, ⟨true,1117,1381,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_968 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,357,2,0⟩, ⟨true,937,1381,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 353 357 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,353,2,0⟩, ⟨true,937,1381,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1113 rank5_4_966 rank5_4_967

theorem rank5_4_969 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,359,383,2,0⟩, ⟨true,937,1381,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_970 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,383,2,0⟩, ⟨true,933,1381,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 937 933 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,383,2,0⟩, ⟨true,937,1381,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 357 rank5_4_968 rank5_4_969

theorem rank5_4_971 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,385,2,0⟩, ⟨true,701,1381,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 383 385 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,383,2,0⟩, ⟨true,701,1381,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 929 rank5_4_941 rank5_4_970

theorem rank5_4_972 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨false,389,409,2,0⟩, ⟨true,701,797,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_4_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_973 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,389,397,2,0⟩, ⟨true,701,733,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_974 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,389,397,2,0⟩, ⟨true,701,713,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 709 713 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,389,397,2,0⟩, ⟨true,701,709,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_975 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,389,397,2,0⟩, ⟨true,717,733,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 733 717 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,389,397,2,0⟩, ⟨true,733,733,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 367 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_976 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,389,397,2,0⟩, ⟨true,701,733,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 713 rank5_4_974 rank5_4_975

theorem rank5_4_977 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,389,397,2,0⟩, ⟨true,701,733,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_4_973 rank5_4_976

theorem rank5_4_978 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,401,409,2,0⟩, ⟨true,701,733,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_979 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,401,401,2,0⟩, ⟨true,701,701,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 4 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_980 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,401,401,2,0⟩, ⟨true,705,709,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 709 705 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,401,401,2,0⟩, ⟨true,709,709,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 71 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_981 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,401,403,2,0⟩, ⟨true,701,709,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 401 403 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,401,401,2,0⟩, ⟨true,701,709,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 701 rank5_4_979 rank5_4_980

theorem rank5_4_982 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,405,409,2,0⟩, ⟨true,701,709,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 409 405 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,409,409,2,0⟩, ⟨true,701,709,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_983 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,401,409,2,0⟩, ⟨true,701,713,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 709 713 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,401,409,2,0⟩, ⟨true,701,709,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 403 rank5_4_981 rank5_4_982

end OddPerfect.SpoofBox
