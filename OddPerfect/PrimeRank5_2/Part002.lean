module

public import OddPerfect.PrimeRank5_2.Part001
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_24 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,157,2,0⟩, ⟨false,719,859,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_25 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,151,2,0⟩, ⟨false,863,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_26 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,157,157,2,0⟩, ⟨false,863,955,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 953 955 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,157,157,2,0⟩, ⟨false,863,953,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_27 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨true,17,17,1,1⟩, ⟨false,157,157,2,0⟩, ⟨false,967,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_2_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_28 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,157,157,2,0⟩, ⟨false,967,1013,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_29 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,157,157,2,0⟩, ⟨false,967,989,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 983 989 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,157,157,2,0⟩, ⟨false,967,983,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_30 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,157,157,2,0⟩, ⟨false,991,1001,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 997 1001 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,157,157,2,0⟩, ⟨false,991,997,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_31 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,157,157,2,0⟩, ⟨false,1009,1013,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_2_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_32 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,8⟩, ⟨true,17,17,1,1⟩, ⟨false,157,157,2,0⟩, ⟨false,1009,1013,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_33 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,157,157,2,2⟩, ⟨false,1009,1013,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 8269 rank5_2_prime8269 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_34 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,157,157,4,0⟩, ⟨false,1009,1009,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_35 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,157,157,4,0⟩, ⟨false,1011,1013,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1013 1011 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,157,157,4,0⟩, ⟨false,1013,1013,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_36 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,157,157,4,0⟩, ⟨false,1009,1013,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1009 rank5_2_34 rank5_2_35

theorem rank5_2_37 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,157,157,2,0⟩, ⟨false,1009,1013,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .exponent 2 rank5_2_33 rank5_2_36

theorem rank5_2_38 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,157,157,2,0⟩, ⟨false,1009,1013,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 8 rank5_2_32 rank5_2_37

theorem rank5_2_39 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,157,157,2,0⟩, ⟨false,1003,1013,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1009 1003 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,157,157,2,0⟩, ⟨false,1009,1013,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 12 rank5_2_31 rank5_2_38

theorem rank5_2_40 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,157,157,2,0⟩, ⟨false,991,1013,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1001 rank5_2_30 rank5_2_39

theorem rank5_2_41 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,157,157,2,0⟩, ⟨false,967,1013,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 989 rank5_2_29 rank5_2_40

theorem rank5_2_42 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,157,157,2,0⟩, ⟨false,967,1015,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1013 1015 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,157,157,2,0⟩, ⟨false,967,1013,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_2_28 rank5_2_41

theorem rank5_2_43 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,157,157,2,0⟩, ⟨false,1017,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1019 1017 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,157,157,2,0⟩, ⟨false,1019,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_44 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,157,157,2,0⟩, ⟨false,967,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1015 rank5_2_42 rank5_2_43

theorem rank5_2_45 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,157,157,2,0⟩, ⟨false,957,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 967 957 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,157,157,2,0⟩, ⟨false,967,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_2_27 rank5_2_44

theorem rank5_2_46 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,153,157,2,0⟩, ⟨false,863,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 157 153 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,157,157,2,0⟩, ⟨false,863,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 955 rank5_2_26 rank5_2_45

theorem rank5_2_47 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,157,2,0⟩, ⟨false,861,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 863 861 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,157,2,0⟩, ⟨false,863,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 151 rank5_2_25 rank5_2_46

end OddPerfect.SpoofBox
