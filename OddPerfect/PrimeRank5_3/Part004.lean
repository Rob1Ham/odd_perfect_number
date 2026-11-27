module

public import OddPerfect.PrimeRank5_3.Part003
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_3_72 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,9,2,0⟩, ⟨false,7,0,2,0⟩, ⟨true,13,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 1 7 9 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,7,2,0⟩, ⟨false,7,0,2,0⟩, ⟨true,13,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .base 13 rank5_3_70 rank5_3_71

theorem rank5_3_73 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,11,0,2,0⟩, ⟨false,11,0,2,0⟩, ⟨true,13,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 2 13 12 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,11,0,2,0⟩, ⟨false,13,0,2,0⟩, ⟨true,13,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 3 17 14 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,11,0,2,0⟩, ⟨false,13,0,2,0⟩, ⟨true,17,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_74 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,0,2,0⟩, ⟨false,7,0,2,0⟩, ⟨true,13,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .base 9 rank5_3_72 rank5_3_73

theorem rank5_3_75 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,7,2,0⟩, ⟨false,7,9,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 2 7 9 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,7,2,0⟩, ⟨false,7,7,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_upper _ 1 5 6 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,7,7,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact covered_impossible_prime_rows _ (by decide +kernel)

theorem rank5_3_76 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,11,13,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_77 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨false,7,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 0 2 11 (by norm_num) (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨false,7,7,2,0⟩, ⟨false,11,11,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_78 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,2,2⟩, ⟨false,11,13,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_79 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,13,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_80 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 2 rank5_3_78 rank5_3_79

theorem rank5_3_81 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 4 rank5_3_77 rank5_3_80

theorem rank5_3_82 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .base 5 rank5_3_76 rank5_3_81

theorem rank5_3_83 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,7,2,0⟩, ⟨false,7,13,2,0⟩, ⟨true,13,25,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 17 25 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,7,2,0⟩, ⟨false,7,13,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .base 9 rank5_3_75 rank5_3_82

theorem rank5_3_84 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,7,2,0⟩, ⟨false,7,9,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 2 7 9 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,7,2,0⟩, ⟨false,7,7,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_upper _ 1 5 6 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,7,7,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact covered_impossible_prime_rows _ (by decide +kernel)

theorem rank5_3_85 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,11,13,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_86 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨false,7,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 0 2 11 (by norm_num) (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨false,7,7,2,0⟩, ⟨false,11,11,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_87 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,2,2⟩, ⟨false,11,13,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_88 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,2,2⟩, ⟨true,29,37,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_89 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨true,29,37,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 0 4 1093 (by norm_num) (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨true,29,37,1,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_90 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨true,29,29,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 5 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_91 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨true,33,37,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 37 33 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨true,37,37,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 3 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_92 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨true,29,37,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 29 rank5_3_90 rank5_3_91

theorem rank5_3_93 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨true,29,37,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 6 rank5_3_89 rank5_3_92

theorem rank5_3_94 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,2,0⟩, ⟨true,29,37,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 2 rank5_3_88 rank5_3_93

theorem rank5_3_95 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,4,0⟩, ⟨false,13,13,2,0⟩, ⟨true,29,37,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
