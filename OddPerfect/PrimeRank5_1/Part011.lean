module

public import OddPerfect.PrimeRank5_1.Part010
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_240 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,2,0⟩, ⟨false,41,53,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_241 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,2,0⟩, ⟨false,41,53,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 0 4 1093 rank5_1_prime1093 (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,2,0⟩, ⟨false,41,53,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_242 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,2,2⟩, ⟨false,41,53,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 61 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_243 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,43,2,0⟩, ⟨false,263,525,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 523 525 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,43,2,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_244 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,41,41,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_245 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,43,43,2,0⟩, ⟨false,541,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 757 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_246 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,43,43,2,2⟩, ⟨false,541,571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 631 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_247 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,43,43,4,0⟩, ⟨false,541,555,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 547 555 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,43,43,4,0⟩, ⟨false,541,547,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_248 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,43,43,4,0⟩, ⟨false,557,571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_249 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,4⟩, ⟨false,43,43,4,0⟩, ⟨false,557,563,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 30941 rank5_1_prime30941 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_250 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,6,0⟩, ⟨false,43,43,4,0⟩, ⟨false,557,559,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 557 559 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,6,0⟩, ⟨false,43,43,4,0⟩, ⟨false,557,557,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_251 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,6,0⟩, ⟨false,43,43,4,0⟩, ⟨false,561,563,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 563 561 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,6,0⟩, ⟨false,43,43,4,0⟩, ⟨false,563,563,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_252 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,6,0⟩, ⟨false,43,43,4,0⟩, ⟨false,557,563,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 559 rank5_1_250 rank5_1_251

theorem rank5_1_253 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,43,43,4,0⟩, ⟨false,557,563,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 4 rank5_1_249 rank5_1_252

theorem rank5_1_254 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,43,43,4,0⟩, ⟨false,565,571,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 569 565 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,43,43,4,0⟩, ⟨false,569,571,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_255 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,43,43,4,0⟩, ⟨false,557,571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 563 rank5_1_253 rank5_1_254

theorem rank5_1_256 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,43,43,4,0⟩, ⟨false,557,571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_1_248 rank5_1_255

theorem rank5_1_257 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,43,43,4,0⟩, ⟨false,541,571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 555 rank5_1_247 rank5_1_256

theorem rank5_1_258 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,43,43,2,0⟩, ⟨false,541,573,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 571 573 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,43,43,2,0⟩, ⟨false,541,571,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .exponent 2 rank5_1_246 rank5_1_257

theorem rank5_1_259 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,43,43,2,0⟩, ⟨false,575,613,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 577 575 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,43,43,2,0⟩, ⟨false,577,613,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_260 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,43,43,2,0⟩, ⟨false,541,613,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 573 rank5_1_258 rank5_1_259

theorem rank5_1_261 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,43,43,2,0⟩, ⟨false,615,709,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 617 615 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,43,43,2,0⟩, ⟨false,617,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_262 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,43,43,2,0⟩, ⟨false,541,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 613 rank5_1_260 rank5_1_261

theorem rank5_1_263 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,43,43,2,0⟩, ⟨false,541,717,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 709 717 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,43,43,2,0⟩, ⟨false,541,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_1_245 rank5_1_262

end OddPerfect.SpoofBox
