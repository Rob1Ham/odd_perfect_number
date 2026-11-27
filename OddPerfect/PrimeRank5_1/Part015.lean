module

public import OddPerfect.PrimeRank5_1.Part014
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_336 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,97,99,2,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 97 99 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,97,97,2,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_337 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,101,103,2,0⟩, ⟨false,2179,2905,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2903 2905 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,101,103,2,0⟩, ⟨false,2179,2903,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_338 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,101,101,2,0⟩, ⟨false,2909,4357,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_339 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,4⟩, ⟨false,103,103,2,0⟩, ⟨false,2909,3469,2,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 2 4 3221 rank5_1_prime3221 (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,4⟩, ⟨false,103,103,2,0⟩, ⟨false,3221,3221,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_340 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,103,103,2,0⟩, ⟨false,2909,3469,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_341 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,103,103,2,0⟩, ⟨false,2909,3163,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_342 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,103,103,2,0⟩, ⟨false,3167,3311,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 3307 3311 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,103,103,2,0⟩, ⟨false,3167,3307,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_343 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,103,103,2,2⟩, ⟨false,3313,3469,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 3571 rank5_1_prime3571 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_344 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,103,103,4,0⟩, ⟨false,3313,3389,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_345 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,103,103,4,0⟩, ⟨false,3391,3469,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_1_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_346 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,103,103,4,0⟩, ⟨false,3391,3401,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 3391 3401 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,103,103,4,0⟩, ⟨false,3391,3391,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_347 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,103,103,4,0⟩, ⟨false,3403,3413,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 3407 3403 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,103,103,4,0⟩, ⟨false,3407,3413,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_348 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,103,103,4,0⟩, ⟨false,3391,3429,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 3413 3429 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,103,103,4,0⟩, ⟨false,3391,3413,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 3401 rank5_1_346 rank5_1_347

theorem rank5_1_349 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,103,103,4,0⟩, ⟨false,3431,3469,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 3433 3431 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,103,103,4,0⟩, ⟨false,3433,3469,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_350 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,103,103,4,0⟩, ⟨false,3391,3469,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 3429 rank5_1_348 rank5_1_349

theorem rank5_1_351 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,103,103,4,0⟩, ⟨false,3391,3469,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_1_345 rank5_1_350

theorem rank5_1_352 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,103,103,4,0⟩, ⟨false,3313,3469,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 3389 rank5_1_344 rank5_1_351

theorem rank5_1_353 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,103,103,2,0⟩, ⟨false,3313,3469,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .exponent 2 rank5_1_343 rank5_1_352

theorem rank5_1_354 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,103,103,2,0⟩, ⟨false,3165,3469,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 3167 3165 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,103,103,2,0⟩, ⟨false,3167,3469,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 3311 rank5_1_342 rank5_1_353

theorem rank5_1_355 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,103,103,2,0⟩, ⟨false,2909,3469,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 3163 rank5_1_341 rank5_1_354

theorem rank5_1_356 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,103,103,2,0⟩, ⟨false,2909,3469,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_1_340 rank5_1_355

theorem rank5_1_357 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,103,103,2,0⟩, ⟨false,2909,3487,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 3469 3487 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,103,103,2,0⟩, ⟨false,2909,3469,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_1_339 rank5_1_356

theorem rank5_1_358 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,103,103,2,0⟩, ⟨false,3489,4357,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 3491 3489 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,103,103,2,0⟩, ⟨false,3491,4357,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_359 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,103,103,2,0⟩, ⟨false,2909,4357,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 3487 rank5_1_357 rank5_1_358

end OddPerfect.SpoofBox
