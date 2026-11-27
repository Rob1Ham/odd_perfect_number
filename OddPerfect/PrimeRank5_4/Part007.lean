module

public import OddPerfect.PrimeRank5_4.Part006
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_144 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨false,27,29,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 29 27 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨false,29,29,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 6 rank5_4_128 rank5_4_143

theorem rank5_4_145 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨false,23,29,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 25 rank5_4_127 rank5_4_144

theorem rank5_4_146 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,2,0⟩, ⟨false,23,29,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 2 rank5_4_126 rank5_4_145

theorem rank5_4_147 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,4,0⟩, ⟨false,13,13,2,0⟩, ⟨false,23,29,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_148 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,13,2,0⟩, ⟨false,23,29,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .base 11 rank5_4_146 rank5_4_147

theorem rank5_4_149 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,13,2,0⟩, ⟨false,31,43,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_150 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,13,2,0⟩, ⟨false,23,45,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 43 45 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,13,2,0⟩, ⟨false,23,43,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 29 rank5_4_148 rank5_4_149

theorem rank5_4_151 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,13,2,0⟩, ⟨false,47,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_152 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,13,2,0⟩, ⟨false,23,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 45 rank5_4_150 rank5_4_151

theorem rank5_4_153 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,23,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 2 rank5_4_125 rank5_4_152

theorem rank5_4_154 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,23,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 4 rank5_4_124 rank5_4_153

theorem rank5_4_155 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,23,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .base 5 rank5_4_113 rank5_4_154

theorem rank5_4_156 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,7,2,0⟩, ⟨false,7,13,2,0⟩, ⟨false,23,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .base 9 rank5_4_112 rank5_4_155

theorem rank5_4_157 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,7,2,0⟩, ⟨false,7,13,2,0⟩, ⟨false,11,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 21 rank5_4_111 rank5_4_156

theorem rank5_4_158 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨false,5,5,2,2⟩, ⟨false,17,0,2,0⟩, ⟨false,19,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 11 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_4_159 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,2,2⟩, ⟨false,17,21,2,0⟩, ⟨false,19,37,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 2 19 21 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,2,2⟩, ⟨false,17,19,2,0⟩, ⟨false,19,37,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  apply covered_force_base _ 1 3 31 (by norm_num) (Nat.odd_iff.mpr (by decide)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,2,2⟩, ⟨false,17,19,2,0⟩, ⟨false,31,31,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_160 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,2,2⟩, ⟨false,23,25,2,0⟩, ⟨false,29,37,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 2 23 25 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,2,2⟩, ⟨false,23,23,2,0⟩, ⟨false,29,37,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  apply covered_force_base _ 1 3 31 (by norm_num) (Nat.odd_iff.mpr (by decide)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,2,2⟩, ⟨false,23,23,2,0⟩, ⟨false,31,31,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_161 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,2,2⟩, ⟨false,27,31,2,0⟩, ⟨false,29,37,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 2 29 27 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,2,2⟩, ⟨false,29,31,2,0⟩, ⟨false,29,37,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 3 31 30 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,2,2⟩, ⟨false,29,31,2,0⟩, ⟨false,31,37,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_162 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,2,2⟩, ⟨false,23,31,2,0⟩, ⟨false,23,37,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 29 24 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,2,2⟩, ⟨false,23,31,2,0⟩, ⟨false,29,37,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .base 25 rank5_4_160 rank5_4_161

theorem rank5_4_163 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,2,2⟩, ⟨false,17,31,2,0⟩, ⟨false,19,37,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .base 21 rank5_4_159 rank5_4_162

theorem rank5_4_164 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,2,2⟩, ⟨false,17,31,2,0⟩, ⟨false,39,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 41 39 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,2,2⟩, ⟨false,17,31,2,0⟩, ⟨false,41,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  apply covered_force_base _ 1 2 31 (by norm_num) (Nat.odd_iff.mpr (by decide)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,2,2⟩, ⟨false,31,31,2,0⟩, ⟨false,41,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_165 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,2,2⟩, ⟨false,17,33,2,0⟩, ⟨false,19,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 2 31 33 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,2,2⟩, ⟨false,17,31,2,0⟩, ⟨false,19,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 37 rank5_4_163 rank5_4_164

theorem rank5_4_166 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,2,2⟩, ⟨false,35,0,2,0⟩, ⟨false,35,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 2 37 35 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,2,2⟩, ⟨false,37,0,2,0⟩, ⟨false,35,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 3 41 38 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,2,2⟩, ⟨false,37,0,2,0⟩, ⟨false,41,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 1 31 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_4_167 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,2,2⟩, ⟨false,17,0,2,0⟩, ⟨false,19,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .base 33 rank5_4_165 rank5_4_166

end OddPerfect.SpoofBox
