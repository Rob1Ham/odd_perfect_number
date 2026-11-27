module

public import OddPerfect.PrimeRank5_4.Part038
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_912 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,359,367,2,0⟩, ⟨true,809,857,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_913 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,359,367,2,0⟩, ⟨true,809,829,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_914 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,359,361,2,0⟩, ⟨true,853,857,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 359 361 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,359,359,2,0⟩, ⟨true,853,857,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_915 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,363,367,2,0⟩, ⟨true,853,857,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 367 363 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,367,367,2,0⟩, ⟨true,853,857,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_916 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,359,367,2,0⟩, ⟨true,833,857,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 853 833 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,359,367,2,0⟩, ⟨true,853,857,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 361 rank5_4_914 rank5_4_915

theorem rank5_4_917 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,359,367,2,0⟩, ⟨true,809,857,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 829 rank5_4_913 rank5_4_916

theorem rank5_4_918 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,359,367,2,0⟩, ⟨true,809,861,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 857 861 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,359,367,2,0⟩, ⟨true,809,857,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_4_912 rank5_4_917

theorem rank5_4_919 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,359,367,2,0⟩, ⟨true,877,929,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_920 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,359,361,2,0⟩, ⟨true,877,881,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 359 361 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,359,359,2,0⟩, ⟨true,877,881,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_921 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,363,367,2,0⟩, ⟨true,877,881,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 367 363 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,367,367,2,0⟩, ⟨true,877,881,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_922 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,359,367,2,0⟩, ⟨true,877,901,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 881 901 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,359,367,2,0⟩, ⟨true,877,881,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 361 rank5_4_920 rank5_4_921

theorem rank5_4_923 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,359,367,2,0⟩, ⟨true,905,929,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 929 905 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,359,367,2,0⟩, ⟨true,929,929,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 31 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_924 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,359,367,2,0⟩, ⟨true,877,929,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 901 rank5_4_922 rank5_4_923

theorem rank5_4_925 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,359,367,2,0⟩, ⟨true,865,929,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 877 865 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,359,367,2,0⟩, ⟨true,877,929,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_4_919 rank5_4_924

theorem rank5_4_926 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,359,369,2,0⟩, ⟨true,809,929,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 367 369 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,359,367,2,0⟩, ⟨true,809,929,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 861 rank5_4_918 rank5_4_925

theorem rank5_4_927 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,373,383,2,0⟩, ⟨true,809,857,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_928 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,373,373,2,0⟩, ⟨true,809,817,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 809 817 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,373,373,2,0⟩, ⟨true,809,809,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_929 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,373,373,2,0⟩, ⟨true,821,829,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_930 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,373,373,2,0⟩, ⟨true,809,829,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 817 rank5_4_928 rank5_4_929

theorem rank5_4_931 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,373,373,2,0⟩, ⟨true,833,857,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 853 833 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,373,373,2,0⟩, ⟨true,853,857,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_932 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,373,377,2,0⟩, ⟨true,809,857,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 373 377 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,373,373,2,0⟩, ⟨true,809,857,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 829 rank5_4_930 rank5_4_931

theorem rank5_4_933 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,379,383,2,0⟩, ⟨true,809,857,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_934 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,373,383,2,0⟩, ⟨true,809,857,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 377 rank5_4_932 rank5_4_933

theorem rank5_4_935 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,373,383,2,0⟩, ⟨true,809,861,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 857 861 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,373,383,2,0⟩, ⟨true,809,857,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_4_927 rank5_4_934

end OddPerfect.SpoofBox
