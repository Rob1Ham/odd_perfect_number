module

public import OddPerfect.PrimeRank5_4.Part005
import OddPerfect.PrimeRank5_4.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_120 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,2,0⟩, ⟨false,31,43,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_121 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,2,0⟩, ⟨false,23,45,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 43 45 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,2,0⟩, ⟨false,23,43,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 29 rank5_4_119 rank5_4_120

theorem rank5_4_122 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,2,0⟩, ⟨false,47,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_123 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,2,0⟩, ⟨false,23,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 45 rank5_4_121 rank5_4_122

theorem rank5_4_124 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨false,7,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,23,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 0 2 11 (by norm_num) (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨false,7,7,2,0⟩, ⟨false,11,11,2,0⟩, ⟨false,23,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 2 rank5_4_114 rank5_4_123

theorem rank5_4_125 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,2,2⟩, ⟨false,11,13,2,0⟩, ⟨false,23,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_126 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,2,2⟩, ⟨false,23,29,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_127 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨false,23,25,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 23 25 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨false,23,23,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_128 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨false,29,29,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 0 4 1093 rank5_4_prime1093 (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨false,29,29,2,0⟩, ⟨true,1093,1093,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 547 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_129 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,4,4⟩, ⟨false,11,11,4,0⟩, ⟨false,29,29,2,0⟩, ⟨true,269,353,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 2801 rank5_4_prime2801 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_130 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,6,0⟩, ⟨false,11,11,4,0⟩, ⟨false,29,29,2,0⟩, ⟨true,269,305,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 293 305 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,6,0⟩, ⟨false,11,11,4,0⟩, ⟨false,29,29,2,0⟩, ⟨true,269,293,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_131 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,7,7,6,0⟩, ⟨false,11,11,4,0⟩, ⟨false,29,29,2,0⟩, ⟨true,313,353,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_132 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,7,7,6,0⟩, ⟨false,11,11,4,0⟩, ⟨false,29,29,2,2⟩, ⟨true,313,353,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_133 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,7,7,6,0⟩, ⟨false,11,11,4,0⟩, ⟨false,29,29,4,0⟩, ⟨true,313,329,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 317 329 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,7,7,6,0⟩, ⟨false,11,11,4,0⟩, ⟨false,29,29,4,0⟩, ⟨true,313,317,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_134 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,7,7,6,0⟩, ⟨false,11,11,4,0⟩, ⟨false,29,29,4,0⟩, ⟨true,333,353,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 337 333 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,7,7,6,0⟩, ⟨false,11,11,4,0⟩, ⟨false,29,29,4,0⟩, ⟨true,337,353,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_135 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,7,7,6,0⟩, ⟨false,11,11,4,0⟩, ⟨false,29,29,4,0⟩, ⟨true,313,353,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 329 rank5_4_133 rank5_4_134

theorem rank5_4_136 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,7,7,6,0⟩, ⟨false,11,11,4,0⟩, ⟨false,29,29,2,0⟩, ⟨true,313,353,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .exponent 2 rank5_4_132 rank5_4_135

theorem rank5_4_137 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,6,0⟩, ⟨false,11,11,4,0⟩, ⟨false,29,29,2,0⟩, ⟨true,309,353,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 313 309 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,6,0⟩, ⟨false,11,11,4,0⟩, ⟨false,29,29,2,0⟩, ⟨true,313,353,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_4_131 rank5_4_136

theorem rank5_4_138 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,6,0⟩, ⟨false,11,11,4,0⟩, ⟨false,29,29,2,0⟩, ⟨true,269,353,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 305 rank5_4_130 rank5_4_137

theorem rank5_4_139 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨false,29,29,2,0⟩, ⟨true,269,353,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 4 rank5_4_129 rank5_4_138

theorem rank5_4_140 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨false,29,29,2,0⟩, ⟨true,357,521,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 373 357 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨false,29,29,2,0⟩, ⟨true,373,521,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_141 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨false,29,29,2,0⟩, ⟨true,269,537,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 521 537 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨false,29,29,2,0⟩, ⟨true,269,521,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 353 rank5_4_139 rank5_4_140

theorem rank5_4_142 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨false,29,29,2,0⟩, ⟨true,541,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_143 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨false,29,29,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 537 rank5_4_141 rank5_4_142

end OddPerfect.SpoofBox
