module

public import OddPerfect.PrimeRank5_3.Part015
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_3_360 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,149,149,1,1⟩, ⟨false,263,277,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 6 rank5_3_352 rank5_3_359

theorem rank5_3_361 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,149,149,1,1⟩, ⟨false,279,293,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 281 279 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,149,149,1,1⟩, ⟨false,281,293,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_362 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,149,149,1,1⟩, ⟨false,263,293,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 277 rank5_3_360 rank5_3_361

theorem rank5_3_363 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,19,19,4,0⟩, ⟨true,149,149,5,0⟩, ⟨false,263,277,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_364 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨true,149,149,5,0⟩, ⟨false,263,269,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_365 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨true,149,149,5,0⟩, ⟨false,263,265,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 263 265 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨true,149,149,5,0⟩, ⟨false,263,263,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_366 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨true,149,149,5,0⟩, ⟨false,267,269,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 269 267 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨true,149,149,5,0⟩, ⟨false,269,269,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_367 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨true,149,149,5,0⟩, ⟨false,263,269,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 265 rank5_3_365 rank5_3_366

theorem rank5_3_368 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨true,149,149,5,0⟩, ⟨false,263,269,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_3_364 rank5_3_367

theorem rank5_3_369 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨true,149,149,5,0⟩, ⟨false,271,277,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_370 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨true,149,149,5,0⟩, ⟨false,263,277,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 269 rank5_3_368 rank5_3_369

theorem rank5_3_371 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,149,149,5,0⟩, ⟨false,263,277,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 6 rank5_3_363 rank5_3_370

theorem rank5_3_372 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,149,149,5,0⟩, ⟨false,279,293,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 281 279 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,149,149,5,0⟩, ⟨false,281,293,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_373 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,149,149,5,0⟩, ⟨false,263,293,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 277 rank5_3_371 rank5_3_372

theorem rank5_3_374 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,145,149,1,0⟩, ⟨false,263,293,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 149 145 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,149,149,1,0⟩, ⟨false,263,293,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .exponent 1 rank5_3_362 rank5_3_373

theorem rank5_3_375 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,137,149,1,0⟩, ⟨false,263,293,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 141 rank5_3_351 rank5_3_374

theorem rank5_3_376 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,137,149,1,0⟩, ⟨false,263,299,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 293 299 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,137,149,1,0⟩, ⟨false,263,293,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_3_350 rank5_3_375

theorem rank5_3_377 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,137,149,1,0⟩, ⟨false,307,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_378 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,137,141,1,0⟩, ⟨false,307,349,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 137 141 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,137,137,1,0⟩, ⟨false,307,349,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 3 23 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_379 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,145,149,1,0⟩, ⟨false,307,349,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 149 145 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,149,149,1,0⟩, ⟨false,307,349,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_380 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,137,149,1,0⟩, ⟨false,307,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 141 rank5_3_378 rank5_3_379

theorem rank5_3_381 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,137,149,1,0⟩, ⟨false,301,349,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 307 301 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,137,149,1,0⟩, ⟨false,307,349,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_3_377 rank5_3_380

theorem rank5_3_382 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,137,153,1,0⟩, ⟨false,263,349,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 149 153 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,137,149,1,0⟩, ⟨false,263,349,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 299 rank5_3_376 rank5_3_381

theorem rank5_3_383 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,157,181,1,0⟩, ⟨false,263,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
