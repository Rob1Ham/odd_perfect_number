module

public import OddPerfect.PrimeRank5_4.Part004
import OddPerfect.PrimeRank5_4.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_96 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,2,2⟩, ⟨false,13,13,2,0⟩, ⟨false,19,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 2 rank5_4_76 rank5_4_95

theorem rank5_4_97 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,2,2⟩, ⟨false,13,13,2,0⟩, ⟨false,19,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 6 rank5_4_75 rank5_4_96

theorem rank5_4_98 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,2,2⟩, ⟨false,11,13,2,0⟩, ⟨false,13,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 1 3 19 (by norm_num) (Nat.odd_iff.mpr (by decide)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,2,2⟩, ⟨false,11,13,2,0⟩, ⟨false,19,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .base 11 rank5_4_74 rank5_4_97

theorem rank5_4_99 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,13,2,0⟩, ⟨false,13,15,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 13 15 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,13,2,0⟩, ⟨false,13,13,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  apply covered_prime_upper _ 2 11 12 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,2,0⟩, ⟨false,13,13,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_100 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,2,0⟩, ⟨false,17,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_101 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,7,7,4,0⟩, ⟨false,13,13,2,0⟩, ⟨false,17,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 0 4 1093 rank5_4_prime1093 (Nat.odd_iff.mpr (by decide)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,7,7,4,0⟩, ⟨false,13,13,2,0⟩, ⟨false,17,19,2,0⟩, ⟨true,1093,1093,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 547 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_4_102 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,4,0⟩, ⟨false,13,13,2,2⟩, ⟨false,17,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 61 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_4_103 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,4,0⟩, ⟨false,13,13,4,0⟩, ⟨false,17,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_104 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,4,0⟩, ⟨false,13,13,2,0⟩, ⟨false,17,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 2 rank5_4_102 rank5_4_103

theorem rank5_4_105 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,4,0⟩, ⟨false,13,13,2,0⟩, ⟨false,17,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 6 rank5_4_101 rank5_4_104

theorem rank5_4_106 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,13,2,0⟩, ⟨false,17,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .base 11 rank5_4_100 rank5_4_105

theorem rank5_4_107 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,13,2,0⟩, ⟨false,13,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 15 rank5_4_99 rank5_4_106

theorem rank5_4_108 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,13,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 2 rank5_4_98 rank5_4_107

theorem rank5_4_109 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,13,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 4 rank5_4_73 rank5_4_108

theorem rank5_4_110 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,11,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 13 12 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,13,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .base 5 rank5_4_72 rank5_4_109

theorem rank5_4_111 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,7,2,0⟩, ⟨false,7,13,2,0⟩, ⟨false,11,21,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 19 21 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,7,2,0⟩, ⟨false,7,13,2,0⟩, ⟨false,11,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .base 9 rank5_4_71 rank5_4_110

theorem rank5_4_112 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,7,2,0⟩, ⟨false,7,9,2,0⟩, ⟨false,23,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 2 7 9 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,7,2,0⟩, ⟨false,7,7,2,0⟩, ⟨false,23,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  apply covered_prime_upper _ 1 5 6 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,7,7,2,0⟩, ⟨false,23,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact covered_impossible_prime_rows _ (by decide +kernel)

theorem rank5_4_113 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,23,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_114 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨false,7,7,2,2⟩, ⟨false,11,11,2,0⟩, ⟨false,23,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_4_115 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,2,2⟩, ⟨false,23,29,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 19 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_4_116 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨false,23,25,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 23 25 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨false,23,23,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_117 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨false,27,29,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 29 27 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨false,29,29,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_118 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨false,23,29,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 25 rank5_4_116 rank5_4_117

theorem rank5_4_119 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,2,0⟩, ⟨false,23,29,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 2 rank5_4_115 rank5_4_118

end OddPerfect.SpoofBox
