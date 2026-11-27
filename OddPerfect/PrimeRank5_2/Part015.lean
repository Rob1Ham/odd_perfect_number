module

public import OddPerfect.PrimeRank5_2.Part014
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_336 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,163,181,2,0⟩, ⟨false,541,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_337 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,163,171,2,0⟩, ⟨false,541,709,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 167 171 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,163,167,2,0⟩, ⟨false,541,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_338 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,173,175,2,0⟩, ⟨false,541,613,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 173 175 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,173,173,2,0⟩, ⟨false,541,613,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_339 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨true,17,17,1,1⟩, ⟨false,179,181,2,0⟩, ⟨false,541,571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_2_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_340 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,179,181,2,0⟩, ⟨false,541,547,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_341 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,179,179,2,0⟩, ⟨false,541,547,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_342 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,181,181,2,0⟩, ⟨false,541,543,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 541 543 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,181,181,2,0⟩, ⟨false,541,541,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_343 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,181,181,2,0⟩, ⟨false,545,547,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 547 545 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,181,181,2,0⟩, ⟨false,547,547,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_344 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,181,181,2,0⟩, ⟨false,541,547,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 543 rank5_2_342 rank5_2_343

theorem rank5_2_345 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,179,181,2,0⟩, ⟨false,541,547,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 179 rank5_2_341 rank5_2_344

theorem rank5_2_346 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,179,181,2,0⟩, ⟨false,541,555,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 547 555 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,179,181,2,0⟩, ⟨false,541,547,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_2_340 rank5_2_345

theorem rank5_2_347 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,179,181,2,0⟩, ⟨false,557,571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_348 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,179,179,2,0⟩, ⟨false,557,559,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 557 559 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,179,179,2,0⟩, ⟨false,557,557,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_349 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,179,179,2,0⟩, ⟨false,561,563,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 563 561 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,179,179,2,0⟩, ⟨false,563,563,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_350 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,179,179,2,0⟩, ⟨false,557,563,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 559 rank5_2_348 rank5_2_349

theorem rank5_2_351 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,179,179,2,0⟩, ⟨false,565,571,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 569 565 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,179,179,2,0⟩, ⟨false,569,571,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_352 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,179,179,2,0⟩, ⟨false,557,571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 563 rank5_2_350 rank5_2_351

theorem rank5_2_353 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,181,181,2,0⟩, ⟨false,557,571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_354 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,179,181,2,0⟩, ⟨false,557,571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 179 rank5_2_352 rank5_2_353

theorem rank5_2_355 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,179,181,2,0⟩, ⟨false,557,571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_2_347 rank5_2_354

theorem rank5_2_356 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,179,181,2,0⟩, ⟨false,541,571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 555 rank5_2_346 rank5_2_355

theorem rank5_2_357 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,179,181,2,0⟩, ⟨false,541,573,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 571 573 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,179,181,2,0⟩, ⟨false,541,571,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_2_339 rank5_2_356

theorem rank5_2_358 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,179,181,2,0⟩, ⟨false,575,613,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 577 575 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,179,181,2,0⟩, ⟨false,577,613,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_359 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,177,181,2,0⟩, ⟨false,541,613,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 179 177 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,179,181,2,0⟩, ⟨false,541,613,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 573 rank5_2_357 rank5_2_358

end OddPerfect.SpoofBox
