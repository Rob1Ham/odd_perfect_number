module

public import OddPerfect.PrimeRank5_2.Part038
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_912 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,367,373,2,0⟩, ⟨false,769,823,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 795 rank5_2_904 rank5_2_911

theorem rank5_2_913 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,363,373,2,0⟩, ⟨false,769,823,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 367 363 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,367,373,2,0⟩, ⟨false,769,823,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_2_903 rank5_2_912

theorem rank5_2_914 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,353,373,2,0⟩, ⟨false,769,823,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 361 rank5_2_902 rank5_2_913

theorem rank5_2_915 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,353,359,2,0⟩, ⟨false,827,887,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_916 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,353,359,2,0⟩, ⟨false,827,887,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_917 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,353,361,2,0⟩, ⟨false,827,887,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 359 361 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,353,359,2,0⟩, ⟨false,827,887,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_2_915 rank5_2_916

theorem rank5_2_918 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,367,373,2,0⟩, ⟨false,827,887,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_919 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,367,367,2,0⟩, ⟨false,827,839,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_920 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,367,367,2,0⟩, ⟨false,841,853,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 853 841 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,367,367,2,0⟩, ⟨false,853,853,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_921 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,367,369,2,0⟩, ⟨false,827,853,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 367 369 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,367,367,2,0⟩, ⟨false,827,853,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 839 rank5_2_919 rank5_2_920

theorem rank5_2_922 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,371,373,2,0⟩, ⟨false,827,853,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 373 371 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,373,373,2,0⟩, ⟨false,827,853,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_923 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,367,373,2,0⟩, ⟨false,827,855,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 853 855 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,367,373,2,0⟩, ⟨false,827,853,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 369 rank5_2_921 rank5_2_922

theorem rank5_2_924 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,367,373,2,0⟩, ⟨false,857,887,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_925 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,367,373,2,0⟩, ⟨false,827,887,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 855 rank5_2_923 rank5_2_924

theorem rank5_2_926 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,363,373,2,0⟩, ⟨false,827,887,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 367 363 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,367,373,2,0⟩, ⟨false,827,887,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_2_918 rank5_2_925

theorem rank5_2_927 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,353,373,2,0⟩, ⟨false,825,887,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 827 825 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,353,373,2,0⟩, ⟨false,827,887,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 361 rank5_2_917 rank5_2_926

theorem rank5_2_928 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,353,373,2,0⟩, ⟨false,769,887,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 823 rank5_2_914 rank5_2_927

theorem rank5_2_929 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,351,373,2,0⟩, ⟨false,769,887,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 353 351 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,353,373,2,0⟩, ⟨false,769,887,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_2_901 rank5_2_928

theorem rank5_2_930 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,373,2,0⟩, ⟨false,769,887,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 349 rank5_2_900 rank5_2_929

theorem rank5_2_931 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,373,2,0⟩, ⟨false,677,895,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 887 895 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,373,2,0⟩, ⟨false,677,887,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 767 rank5_2_899 rank5_2_930

theorem rank5_2_932 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨true,17,17,5,0⟩, ⟨false,331,349,2,0⟩, ⟨false,907,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_2_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_933 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,339,2,0⟩, ⟨false,907,977,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 337 339 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,337,2,0⟩, ⟨false,907,977,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_934 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,347,349,2,0⟩, ⟨false,907,977,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_935 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,347,349,2,0⟩, ⟨false,907,939,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 937 939 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,347,349,2,0⟩, ⟨false,907,937,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
