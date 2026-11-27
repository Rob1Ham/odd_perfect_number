module

public import OddPerfect.PrimeRank5_1.Part013
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_312 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,113,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 0 4 1093 rank5_1_prime1093 (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,113,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 91 rank5_1_308 rank5_1_311

theorem rank5_1_313 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,91,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 89 91 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,79,89,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_314 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,97,113,2,0⟩, ⟨false,263,525,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 523 525 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,97,113,2,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_315 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,97,103,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_316 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,107,113,2,0⟩, ⟨false,541,717,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 709 717 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,107,113,2,0⟩, ⟨false,541,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_317 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,107,113,2,0⟩, ⟨false,719,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_318 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,107,109,2,0⟩, ⟨false,719,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_319 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,113,113,2,0⟩, ⟨false,719,781,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 773 781 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,113,113,2,0⟩, ⟨false,719,773,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_320 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,113,113,2,0⟩, ⟨false,787,821,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_321 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,4⟩, ⟨false,113,113,2,0⟩, ⟨false,823,859,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 3221 rank5_1_prime3221 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_322 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,113,113,2,0⟩, ⟨false,823,859,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_323 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,113,113,2,0⟩, ⟨false,823,859,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_324 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,113,113,2,0⟩, ⟨false,823,859,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_1_322 rank5_1_323

theorem rank5_1_325 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,113,113,2,0⟩, ⟨false,823,859,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 4 rank5_1_321 rank5_1_324

theorem rank5_1_326 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,113,113,2,0⟩, ⟨false,783,859,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 787 783 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,113,113,2,0⟩, ⟨false,787,859,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 821 rank5_1_320 rank5_1_325

theorem rank5_1_327 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,113,113,2,0⟩, ⟨false,719,859,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 781 rank5_1_319 rank5_1_326

theorem rank5_1_328 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,113,113,2,0⟩, ⟨false,861,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 863 861 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,113,113,2,0⟩, ⟨false,863,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_329 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,111,113,2,0⟩, ⟨false,719,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 113 111 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,113,113,2,0⟩, ⟨false,719,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 859 rank5_1_327 rank5_1_328

theorem rank5_1_330 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,107,113,2,0⟩, ⟨false,719,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 109 rank5_1_318 rank5_1_329

theorem rank5_1_331 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,107,113,2,0⟩, ⟨false,719,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 8 rank5_1_317 rank5_1_330

theorem rank5_1_332 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,105,113,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 107 105 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,107,113,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 717 rank5_1_316 rank5_1_331

theorem rank5_1_333 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,97,113,2,0⟩, ⟨false,541,1081,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1069 1081 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,97,113,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 103 rank5_1_315 rank5_1_332

theorem rank5_1_334 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,97,103,2,0⟩, ⟨false,1087,2173,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2161 2173 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,97,103,2,0⟩, ⟨false,1087,2161,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_335 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,97,103,2,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end OddPerfect.SpoofBox
