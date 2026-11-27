module

public import OddPerfect.PrimeRank5_4.Part039
import OddPerfect.PrimeRank5_4.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_936 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,373,383,2,0⟩, ⟨true,865,929,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 877 865 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,373,383,2,0⟩, ⟨true,877,929,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_937 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,371,383,2,0⟩, ⟨true,809,929,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 373 371 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,373,383,2,0⟩, ⟨true,809,929,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 861 rank5_4_935 rank5_4_936

theorem rank5_4_938 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,359,383,2,0⟩, ⟨true,809,929,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 369 rank5_4_926 rank5_4_937

theorem rank5_4_939 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,359,383,2,0⟩, ⟨true,801,929,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 809 801 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,359,383,2,0⟩, ⟨true,809,929,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_4_911 rank5_4_938

theorem rank5_4_940 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,359,383,2,0⟩, ⟨true,701,929,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 797 rank5_4_910 rank5_4_939

theorem rank5_4_941 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,383,2,0⟩, ⟨true,701,929,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 357 rank5_4_885 rank5_4_940

theorem rank5_4_942 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨false,337,353,2,0⟩, ⟨true,937,1109,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_4_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_943 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,343,2,0⟩, ⟨true,937,1013,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 337 343 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,337,2,0⟩, ⟨true,937,1013,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_944 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,353,2,0⟩, ⟨true,937,1013,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_945 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,349,2,0⟩, ⟨true,937,953,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_946 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,351,353,2,0⟩, ⟨true,937,953,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 353 351 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,353,353,2,0⟩, ⟨true,937,953,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_947 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,353,2,0⟩, ⟨true,937,973,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 953 973 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,353,2,0⟩, ⟨true,937,953,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 349 rank5_4_945 rank5_4_946

theorem rank5_4_948 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,353,2,0⟩, ⟨true,977,1013,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_949 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,353,2,0⟩, ⟨true,937,1013,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 973 rank5_4_947 rank5_4_948

theorem rank5_4_950 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,345,353,2,0⟩, ⟨true,937,1013,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 347 345 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,353,2,0⟩, ⟨true,937,1013,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_4_944 rank5_4_949

theorem rank5_4_951 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,353,2,0⟩, ⟨true,937,1013,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 343 rank5_4_943 rank5_4_950

theorem rank5_4_952 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,337,2,0⟩, ⟨true,1021,1109,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_953 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,337,2,0⟩, ⟨true,1021,1037,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1033 1037 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,337,2,0⟩, ⟨true,1021,1033,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_954 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,4⟩, ⟨false,337,337,2,0⟩, ⟨true,1049,1061,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 88741 rank5_4_prime88741 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_955 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,337,337,2,0⟩, ⟨true,1049,1053,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1049 1053 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,337,337,2,0⟩, ⟨true,1049,1049,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_956 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,337,337,2,0⟩, ⟨true,1057,1061,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1061 1057 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,337,337,2,0⟩, ⟨true,1061,1061,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 59 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_957 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,337,337,2,0⟩, ⟨true,1049,1061,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1053 rank5_4_955 rank5_4_956

theorem rank5_4_958 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,337,2,0⟩, ⟨true,1041,1061,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1049 1041 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,337,2,0⟩, ⟨true,1049,1061,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_4_954 rank5_4_957

theorem rank5_4_959 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,337,2,0⟩, ⟨true,1021,1061,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1037 rank5_4_953 rank5_4_958

end OddPerfect.SpoofBox
