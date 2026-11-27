module

public import OddPerfect.PrimeRank5_2.Part039
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_936 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,347,349,2,0⟩, ⟨false,941,957,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 953 957 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,347,349,2,0⟩, ⟨false,941,953,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_937 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,347,347,2,0⟩, ⟨false,967,971,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_938 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,347,347,2,0⟩, ⟨false,973,977,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 977 973 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,347,347,2,0⟩, ⟨false,977,977,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_939 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,347,347,2,0⟩, ⟨false,967,977,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 971 rank5_2_937 rank5_2_938

theorem rank5_2_940 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,349,349,2,0⟩, ⟨false,967,977,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_941 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,347,349,2,0⟩, ⟨false,959,977,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 967 959 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,347,349,2,0⟩, ⟨false,967,977,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 347 rank5_2_939 rank5_2_940

theorem rank5_2_942 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,347,349,2,0⟩, ⟨false,941,977,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 957 rank5_2_936 rank5_2_941

theorem rank5_2_943 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,347,349,2,0⟩, ⟨false,907,977,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 939 rank5_2_935 rank5_2_942

theorem rank5_2_944 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,341,349,2,0⟩, ⟨false,907,977,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 347 341 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,347,349,2,0⟩, ⟨false,907,977,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_2_934 rank5_2_943

theorem rank5_2_945 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,349,2,0⟩, ⟨false,907,981,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 977 981 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,349,2,0⟩, ⟨false,907,977,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 339 rank5_2_933 rank5_2_944

theorem rank5_2_946 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,337,2,0⟩, ⟨false,983,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_947 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,337,2,0⟩, ⟨false,983,1023,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1021 1023 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,337,2,0⟩, ⟨false,983,1021,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_948 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,333,2,0⟩, ⟨false,1031,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 331 333 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,331,2,0⟩, ⟨false,1031,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_949 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1031,1049,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_950 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1051,1059,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1051 1059 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1051,1051,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_951 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1061,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_2_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_952 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,8⟩, ⟨true,17,17,5,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1061,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_953 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1061,1061,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_954 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1063,1063,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_955 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1061,1063,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1061 rank5_2_953 rank5_2_954

theorem rank5_2_956 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1065,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1069 1065 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1069,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_957 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1061,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1063 rank5_2_955 rank5_2_956

theorem rank5_2_958 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1061,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 8 rank5_2_952 rank5_2_957

theorem rank5_2_959 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1061,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_2_951 rank5_2_958

end OddPerfect.SpoofBox
