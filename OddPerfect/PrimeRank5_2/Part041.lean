module

public import OddPerfect.PrimeRank5_2.Part040
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_960 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1051,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1059 rank5_2_950 rank5_2_959

theorem rank5_2_961 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,335,337,2,0⟩, ⟨false,1031,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 337 335 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1031,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1049 rank5_2_949 rank5_2_960

theorem rank5_2_962 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,337,2,0⟩, ⟨false,1025,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1031 1025 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,337,2,0⟩, ⟨false,1031,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 333 rank5_2_948 rank5_2_961

theorem rank5_2_963 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,337,2,0⟩, ⟨false,983,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1023 rank5_2_947 rank5_2_962

theorem rank5_2_964 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,339,2,0⟩, ⟨false,983,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 337 339 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,337,2,0⟩, ⟨false,983,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_2_946 rank5_2_963

theorem rank5_2_965 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,341,349,2,0⟩, ⟨false,983,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 347 341 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,347,349,2,0⟩, ⟨false,983,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_966 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,349,2,0⟩, ⟨false,983,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 339 rank5_2_964 rank5_2_965

theorem rank5_2_967 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,349,2,0⟩, ⟨false,907,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 981 rank5_2_945 rank5_2_966

theorem rank5_2_968 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,349,2,0⟩, ⟨false,907,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 6 rank5_2_932 rank5_2_967

theorem rank5_2_969 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨true,17,17,5,0⟩, ⟨false,353,373,2,0⟩, ⟨false,907,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_2_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_970 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,353,359,2,0⟩, ⟨false,907,977,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_971 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,353,353,2,0⟩, ⟨false,907,921,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 919 921 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,353,353,2,0⟩, ⟨false,907,919,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_972 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,353,353,2,0⟩, ⟨false,923,937,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 929 923 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,353,353,2,0⟩, ⟨false,929,937,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_973 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,353,355,2,0⟩, ⟨false,907,937,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 353 355 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,353,353,2,0⟩, ⟨false,907,937,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 921 rank5_2_971 rank5_2_972

theorem rank5_2_974 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,357,359,2,0⟩, ⟨false,907,937,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 359 357 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,359,359,2,0⟩, ⟨false,907,937,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_975 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,353,359,2,0⟩, ⟨false,907,939,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 937 939 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,353,359,2,0⟩, ⟨false,907,937,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 355 rank5_2_973 rank5_2_974

theorem rank5_2_976 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,353,359,2,0⟩, ⟨false,941,977,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_977 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,353,359,2,0⟩, ⟨false,907,977,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 939 rank5_2_975 rank5_2_976

theorem rank5_2_978 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,353,361,2,0⟩, ⟨false,907,977,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 359 361 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,353,359,2,0⟩, ⟨false,907,977,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_2_970 rank5_2_977

theorem rank5_2_979 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,363,373,2,0⟩, ⟨false,907,977,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 367 363 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,367,373,2,0⟩, ⟨false,907,977,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_980 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,353,373,2,0⟩, ⟨false,907,981,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 977 981 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,353,373,2,0⟩, ⟨false,907,977,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 361 rank5_2_978 rank5_2_979

theorem rank5_2_981 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,353,373,2,0⟩, ⟨false,983,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_982 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,353,373,2,0⟩, ⟨false,907,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 981 rank5_2_980 rank5_2_981

theorem rank5_2_983 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,351,373,2,0⟩, ⟨false,907,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 353 351 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,353,373,2,0⟩, ⟨false,907,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_2_969 rank5_2_982

end OddPerfect.SpoofBox
