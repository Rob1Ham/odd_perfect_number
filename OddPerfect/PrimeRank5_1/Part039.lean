module

public import OddPerfect.PrimeRank5_1.Part038
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_912 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1019,1043,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1039 1043 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1019,1039,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_913 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1049,1057,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1051 1057 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1049,1051,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_914 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,4⟩, ⟨false,337,337,2,0⟩, ⟨false,1061,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 88741 rank5_1_prime88741 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_915 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1061,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_1_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_916 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1061,1061,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_917 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1063,1063,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_918 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1061,1063,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1061 rank5_1_916 rank5_1_917

theorem rank5_1_919 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1065,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1069 1065 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1069,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_920 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1061,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1063 rank5_1_918 rank5_1_919

theorem rank5_1_921 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1061,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_1_915 rank5_1_920

theorem rank5_1_922 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1059,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1061 1059 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1061,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_1_914 rank5_1_921

theorem rank5_1_923 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1045,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1049 1045 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1049,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1057 rank5_1_913 rank5_1_922

theorem rank5_1_924 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,335,337,2,0⟩, ⟨false,1019,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 337 335 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,337,2,0⟩, ⟨false,1019,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1043 rank5_1_912 rank5_1_923

theorem rank5_1_925 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,337,2,0⟩, ⟨false,1019,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 333 rank5_1_911 rank5_1_924

theorem rank5_1_926 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,337,2,0⟩, ⟨false,1017,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1019 1017 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,337,2,0⟩, ⟨false,1019,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_1_910 rank5_1_925

theorem rank5_1_927 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,327,337,2,0⟩, ⟨false,967,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 331 327 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,337,2,0⟩, ⟨false,967,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1015 rank5_1_909 rank5_1_926

theorem rank5_1_928 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,317,337,2,0⟩, ⟨false,957,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 967 957 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,317,337,2,0⟩, ⟨false,967,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 325 rank5_1_908 rank5_1_927

theorem rank5_1_929 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,315,337,2,0⟩, ⟨false,863,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 317 315 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,317,337,2,0⟩, ⟨false,863,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 955 rank5_1_907 rank5_1_928

theorem rank5_1_930 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,337,2,0⟩, ⟨false,861,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 863 861 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,337,2,0⟩, ⟨false,863,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 313 rank5_1_906 rank5_1_929

theorem rank5_1_931 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,337,2,0⟩, ⟨false,719,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 859 rank5_1_905 rank5_1_930

theorem rank5_1_932 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,337,2,0⟩, ⟨false,719,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 8 rank5_1_904 rank5_1_931

theorem rank5_1_933 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,337,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 717 rank5_1_903 rank5_1_932

theorem rank5_1_934 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,337,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 291 rank5_1_902 rank5_1_933

theorem rank5_1_935 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,337,2,0⟩, ⟨false,541,1081,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1069 1081 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,337,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 5 rank5_1_901 rank5_1_934

end OddPerfect.SpoofBox
