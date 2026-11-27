module

public import OddPerfect.PrimeRank5_1.Part003
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_72 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2173 rank5_1_70 rank5_1_71

theorem rank5_1_73 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨false,1083,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1087 1083 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 5 rank5_1_55 rank5_1_72

theorem rank5_1_74 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,49,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 47 49 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1081 rank5_1_54 rank5_1_73

theorem rank5_1_75 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,13,13,4,0⟩, ⟨false,51,53,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 53 51 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_76 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,53,2,0⟩, ⟨false,527,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 541 527 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,53,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 49 rank5_1_74 rank5_1_75

theorem rank5_1_77 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,53,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 525 rank5_1_53 rank5_1_76

theorem rank5_1_78 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,13,13,4,0⟩, ⟨false,41,53,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 45 rank5_1_34 rank5_1_77

theorem rank5_1_79 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,13,13,2,0⟩, ⟨false,39,53,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 41 39 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,13,13,2,0⟩, ⟨false,41,53,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 2 rank5_1_33 rank5_1_78

theorem rank5_1_80 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,13,13,2,0⟩, ⟨false,29,57,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 53 57 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,13,13,2,0⟩, ⟨false,29,53,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 37 rank5_1_32 rank5_1_79

theorem rank5_1_81 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,13,13,2,0⟩, ⟨false,59,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_82 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,11,19,2,0⟩, ⟨false,27,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 29 27 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,11,19,2,0⟩, ⟨false,29,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  apply covered_force_base _ 0 2 13 (by norm_num) (Nat.odd_iff.mpr (by decide)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,13,13,2,0⟩, ⟨false,29,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 57 rank5_1_80 rank5_1_81

theorem rank5_1_83 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,11,21,2,0⟩, ⟨false,13,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 2 19 21 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,11,19,2,0⟩, ⟨false,13,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 25 rank5_1_31 rank5_1_82

theorem rank5_1_84 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,23,0,2,0⟩, ⟨false,23,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 29 24 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,23,0,2,0⟩, ⟨false,29,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_1_85 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,11,0,2,0⟩, ⟨false,13,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .base 21 rank5_1_83 rank5_1_84

theorem rank5_1_86 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,9,1,0⟩, ⟨false,7,0,2,0⟩, ⟨false,11,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 1 5 9 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,0⟩, ⟨false,7,0,2,0⟩, ⟨false,11,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 2 11 7 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,0⟩, ⟨false,11,0,2,0⟩, ⟨false,11,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 3 13 12 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,0⟩, ⟨false,11,0,2,0⟩, ⟨false,13,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 1 rank5_1_28 rank5_1_85

theorem rank5_1_87 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,13,0,1,0⟩, ⟨false,13,0,2,0⟩, ⟨false,13,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 2 17 14 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,13,0,1,0⟩, ⟨false,17,0,2,0⟩, ⟨false,13,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 3 19 18 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,13,0,1,0⟩, ⟨false,17,0,2,0⟩, ⟨false,19,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  apply covered_force_base _ 0 1 13 (by norm_num) (Nat.odd_iff.mpr (by decide)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,13,13,1,0⟩, ⟨false,17,0,2,0⟩, ⟨false,19,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 1 7 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_1_88 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,0,1,0⟩, ⟨false,7,0,2,0⟩, ⟨false,11,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .base 9 rank5_1_86 rank5_1_87

theorem rank5_1_89 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,19,2,0⟩, ⟨false,13,23,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 0 2 11 (by norm_num) (Nat.odd_iff.mpr (by decide)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,2,0⟩, ⟨false,13,23,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_90 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,13,2,0⟩, ⟨false,13,23,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_91 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,19,2,0⟩, ⟨false,19,19,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 2 17 18 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,2,0⟩, ⟨false,19,19,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_92 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,2,2⟩, ⟨false,23,23,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 307 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_1_93 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_94 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,2,0⟩, ⟨false,23,23,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 2 rank5_1_92 rank5_1_93

theorem rank5_1_95 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,1,1⟩, ⟨false,19,19,2,0⟩, ⟨false,23,23,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
