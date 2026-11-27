module

public import OddPerfect.PrimeRank5_4.Part007
import OddPerfect.PrimeRank5_4.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_168 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,2⟩, ⟨false,17,0,2,0⟩, ⟨false,19,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 4 rank5_4_158 rank5_4_167

theorem rank5_4_169 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨false,5,5,4,0⟩, ⟨false,17,0,2,0⟩, ⟨false,19,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 11 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_4_170 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,21,2,0⟩, ⟨false,19,37,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 2 19 21 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,19,2,0⟩, ⟨false,19,37,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_171 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,25,2,0⟩, ⟨false,29,37,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 2 23 25 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,23,2,0⟩, ⟨false,29,37,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_172 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨false,29,31,2,0⟩, ⟨false,31,37,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 0 4 1093 rank5_4_prime1093 (Nat.odd_iff.mpr (by decide)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨false,29,31,2,0⟩, ⟨false,31,37,2,0⟩, ⟨true,1093,1093,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 547 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_4_173 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,29,31,2,0⟩, ⟨false,31,33,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 31 33 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,29,31,2,0⟩, ⟨false,31,31,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  apply covered_prime_upper _ 2 29 30 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,29,29,2,0⟩, ⟨false,31,31,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_174 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,4⟩, ⟨false,29,31,2,0⟩, ⟨false,37,37,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 11 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_4_175 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,29,29,2,0⟩, ⟨false,37,37,2,0⟩, ⟨true,269,353,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_176 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨false,29,29,2,0⟩, ⟨false,37,37,2,0⟩, ⟨true,373,521,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_4_177 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,29,29,2,0⟩, ⟨false,37,37,2,0⟩, ⟨true,373,433,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_178 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,29,29,2,2⟩, ⟨false,37,37,2,0⟩, ⟨true,449,521,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 13 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_4_179 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,29,29,4,0⟩, ⟨false,37,37,2,2⟩, ⟨true,449,521,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 7 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_4_180 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,29,29,4,0⟩, ⟨false,37,37,4,0⟩, ⟨true,449,481,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 461 481 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,29,29,4,0⟩, ⟨false,37,37,4,0⟩, ⟨true,449,461,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_181 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,29,29,4,0⟩, ⟨false,37,37,4,0⟩, ⟨true,485,521,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 509 485 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,29,29,4,0⟩, ⟨false,37,37,4,0⟩, ⟨true,509,521,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_182 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,29,29,4,0⟩, ⟨false,37,37,4,0⟩, ⟨true,449,521,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 481 rank5_4_180 rank5_4_181

theorem rank5_4_183 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,29,29,4,0⟩, ⟨false,37,37,2,0⟩, ⟨true,449,521,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .exponent 2 rank5_4_179 rank5_4_182

theorem rank5_4_184 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,29,29,2,0⟩, ⟨false,37,37,2,0⟩, ⟨true,437,521,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 449 437 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,29,29,2,0⟩, ⟨false,37,37,2,0⟩, ⟨true,449,521,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 2 rank5_4_178 rank5_4_183

theorem rank5_4_185 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,29,29,2,0⟩, ⟨false,37,37,2,0⟩, ⟨true,373,521,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 433 rank5_4_177 rank5_4_184

theorem rank5_4_186 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,29,29,2,0⟩, ⟨false,37,37,2,0⟩, ⟨true,357,521,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 373 357 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,29,29,2,0⟩, ⟨false,37,37,2,0⟩, ⟨true,373,521,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_4_176 rank5_4_185

theorem rank5_4_187 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,29,29,2,0⟩, ⟨false,37,37,2,0⟩, ⟨true,269,521,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 353 rank5_4_175 rank5_4_186

theorem rank5_4_188 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,31,31,2,0⟩, ⟨false,37,37,2,0⟩, ⟨true,269,521,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_189 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,29,31,2,0⟩, ⟨false,37,37,2,0⟩, ⟨true,269,537,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 521 537 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,29,31,2,0⟩, ⟨false,37,37,2,0⟩, ⟨true,269,521,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .base 29 rank5_4_187 rank5_4_188

theorem rank5_4_190 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,29,31,2,0⟩, ⟨false,37,37,2,0⟩, ⟨true,541,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_191 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,29,31,2,0⟩, ⟨false,37,37,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 537 rank5_4_189 rank5_4_190

end OddPerfect.SpoofBox
