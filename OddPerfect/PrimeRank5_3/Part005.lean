module

public import OddPerfect.PrimeRank5_3.Part004
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_3_96 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,13,2,0⟩, ⟨true,29,37,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .base 11 rank5_3_94 rank5_3_95

theorem rank5_3_97 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,13,2,0⟩, ⟨true,41,53,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_98 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,13,2,0⟩, ⟨true,29,57,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 53 57 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,13,2,0⟩, ⟨true,29,53,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 37 rank5_3_96 rank5_3_97

theorem rank5_3_99 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,13,2,0⟩, ⟨true,61,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_100 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,13,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 57 rank5_3_98 rank5_3_99

theorem rank5_3_101 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 2 rank5_3_87 rank5_3_100

theorem rank5_3_102 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 4 rank5_3_86 rank5_3_101

theorem rank5_3_103 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .base 5 rank5_3_85 rank5_3_102

theorem rank5_3_104 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,7,2,0⟩, ⟨false,7,13,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .base 9 rank5_3_84 rank5_3_103

theorem rank5_3_105 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,7,2,0⟩, ⟨false,7,13,2,0⟩, ⟨true,13,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 25 rank5_3_83 rank5_3_104

theorem rank5_3_106 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,2⟩, ⟨false,17,0,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 1 2 31 (by norm_num) (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,2⟩, ⟨false,31,31,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 3 37 32 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,2⟩, ⟨false,31,31,2,0⟩, ⟨true,37,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_107 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨false,5,5,4,0⟩, ⟨false,17,0,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_108 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,21,2,0⟩, ⟨true,29,53,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 2 19 21 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,19,2,0⟩, ⟨true,29,53,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_109 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,25,2,0⟩, ⟨true,29,37,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 2 23 25 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,23,2,0⟩, ⟨true,29,37,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_110 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,27,31,2,0⟩, ⟨true,29,37,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 2 29 27 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,29,31,2,0⟩, ⟨true,29,37,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 3 37 30 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,29,31,2,0⟩, ⟨true,37,37,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 3 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_111 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,31,2,0⟩, ⟨true,29,37,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .base 25 rank5_3_109 rank5_3_110

theorem rank5_3_112 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨false,23,23,2,0⟩, ⟨true,41,45,1,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 41 45 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨false,23,23,2,0⟩, ⟨true,41,41,1,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 3 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_113 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨false,23,23,2,0⟩, ⟨true,49,53,1,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 53 49 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨false,23,23,2,0⟩, ⟨true,53,53,1,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_114 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨false,23,23,2,0⟩, ⟨true,41,53,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 0 4 1093 (by norm_num) (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨false,23,23,2,0⟩, ⟨true,41,53,1,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 45 rank5_3_112 rank5_3_113

theorem rank5_3_115 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,23,2,0⟩, ⟨true,41,45,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 41 45 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,23,2,0⟩, ⟨true,41,41,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 3 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_116 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,4⟩, ⟨false,23,23,2,0⟩, ⟨true,53,53,1,1⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_117 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨true,53,53,1,1⟩, ⟨false,263,525,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 523 525 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨true,53,53,1,1⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_118 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,2⟩, ⟨true,53,53,1,1⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_119 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,541,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end OddPerfect.SpoofBox
