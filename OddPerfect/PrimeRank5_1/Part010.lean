module

public import OddPerfect.PrimeRank5_1.Part009
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_216 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,79,79,2,0⟩, ⟨false,691,699,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 691 699 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,79,79,2,0⟩, ⟨false,691,691,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_217 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,79,79,2,0⟩, ⟨false,701,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_218 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,79,79,2,0⟩, ⟨false,691,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 699 rank5_1_216 rank5_1_217

theorem rank5_1_219 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,79,2,0⟩, ⟨false,685,709,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 691 685 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,79,2,0⟩, ⟨false,691,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_1_215 rank5_1_218

theorem rank5_1_220 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,79,2,0⟩, ⟨false,661,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 683 rank5_1_214 rank5_1_219

theorem rank5_1_221 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,79,2,0⟩, ⟨false,615,709,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 617 615 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,79,2,0⟩, ⟨false,617,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 659 rank5_1_213 rank5_1_220

theorem rank5_1_222 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,79,2,0⟩, ⟨false,541,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 613 rank5_1_212 rank5_1_221

theorem rank5_1_223 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,81,83,2,0⟩, ⟨false,541,709,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 83 81 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,83,83,2,0⟩, ⟨false,541,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_224 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,83,2,0⟩, ⟨false,541,717,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 709 717 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,83,2,0⟩, ⟨false,541,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 79 rank5_1_222 rank5_1_223

theorem rank5_1_225 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,83,2,0⟩, ⟨false,719,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_226 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,83,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 717 rank5_1_224 rank5_1_225

theorem rank5_1_227 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,85,89,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 89 85 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,89,89,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_228 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,89,2,0⟩, ⟨false,541,1081,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1069 1081 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,89,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 83 rank5_1_226 rank5_1_227

theorem rank5_1_229 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,89,2,0⟩, ⟨false,1083,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1087 1083 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,89,2,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_230 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,89,2,0⟩, ⟨false,527,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 541 527 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,89,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1081 rank5_1_228 rank5_1_229

theorem rank5_1_231 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,91,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 89 91 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,89,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 525 rank5_1_211 rank5_1_230

theorem rank5_1_232 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,93,113,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 97 93 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,97,113,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_233 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,113,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 91 rank5_1_231 rank5_1_232

theorem rank5_1_234 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,59,113,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 77 rank5_1_180 rank5_1_233

theorem rank5_1_235 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,2,0⟩, ⟨false,59,117,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 113 117 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,2,0⟩, ⟨false,59,113,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 2 rank5_1_145 rank5_1_234

theorem rank5_1_236 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,2,0⟩, ⟨false,119,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 127 119 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,2,0⟩, ⟨false,127,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_237 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,2,0⟩, ⟨false,59,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 117 rank5_1_235 rank5_1_236

theorem rank5_1_238 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,19,2,0⟩, ⟨false,29,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 0 2 11 (by norm_num) (Nat.odd_iff.mpr (by decide)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,2,0⟩, ⟨false,29,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 57 rank5_1_144 rank5_1_237

theorem rank5_1_239 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,13,2,0⟩, ⟨false,29,37,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
