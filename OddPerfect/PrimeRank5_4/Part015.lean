module

public import OddPerfect.PrimeRank5_4.Part014
import OddPerfect.PrimeRank5_4.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_336 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,131,2,0⟩, ⟨true,269,305,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 293 305 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,131,2,0⟩, ⟨true,269,293,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_337 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,131,2,0⟩, ⟨true,313,353,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_338 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,131,2,0⟩, ⟨true,313,353,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_339 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,131,2,0⟩, ⟨true,309,353,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 313 309 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,131,2,0⟩, ⟨true,313,353,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_4_337 rank5_4_338

theorem rank5_4_340 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,123,131,2,0⟩, ⟨true,269,353,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 127 123 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,131,2,0⟩, ⟨true,269,353,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 305 rank5_4_336 rank5_4_339

theorem rank5_4_341 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,113,131,2,0⟩, ⟨true,269,353,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 121 rank5_4_335 rank5_4_340

theorem rank5_4_342 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,113,121,2,0⟩, ⟨true,373,521,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 113 121 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,113,113,2,0⟩, ⟨true,373,521,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_343 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,131,2,0⟩, ⟨true,373,521,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_344 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,19,19,4,0⟩, ⟨false,127,127,2,0⟩, ⟨true,373,397,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_4_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_345 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,127,2,0⟩, ⟨true,373,381,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 373 381 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,127,2,0⟩, ⟨true,373,373,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_346 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,127,2,0⟩, ⟨true,389,397,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_347 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,127,2,0⟩, ⟨true,389,389,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 4 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_348 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,127,2,0⟩, ⟨true,393,397,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 397 393 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,127,2,0⟩, ⟨true,397,397,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 199 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_349 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,127,2,0⟩, ⟨true,389,397,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 389 rank5_4_347 rank5_4_348

theorem rank5_4_350 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,127,2,0⟩, ⟨true,385,397,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 389 385 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,127,2,0⟩, ⟨true,389,397,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_4_346 rank5_4_349

theorem rank5_4_351 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,127,2,0⟩, ⟨true,373,397,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 381 rank5_4_345 rank5_4_350

theorem rank5_4_352 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,127,2,0⟩, ⟨true,373,397,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 6 rank5_4_344 rank5_4_351

theorem rank5_4_353 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,129,131,2,0⟩, ⟨true,373,397,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 131 129 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,131,131,2,0⟩, ⟨true,373,397,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_354 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,131,2,0⟩, ⟨true,373,397,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 127 rank5_4_352 rank5_4_353

theorem rank5_4_355 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,131,2,0⟩, ⟨true,401,433,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_356 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,131,2,0⟩, ⟨true,373,433,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 397 rank5_4_354 rank5_4_355

theorem rank5_4_357 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,131,2,0⟩, ⟨true,437,521,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 449 437 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,131,2,0⟩, ⟨true,449,521,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_358 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,131,2,0⟩, ⟨true,373,521,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 433 rank5_4_356 rank5_4_357

theorem rank5_4_359 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,123,131,2,0⟩, ⟨true,373,521,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 127 123 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,131,2,0⟩, ⟨true,373,521,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_4_343 rank5_4_358

end OddPerfect.SpoofBox
