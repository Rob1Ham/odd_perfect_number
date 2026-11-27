module

public import OddPerfect.PrimeRank5_1.Part015
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_360 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,101,103,2,0⟩, ⟨false,2907,4357,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2909 2907 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,101,103,2,0⟩, ⟨false,2909,4357,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 101 rank5_1_338 rank5_1_359

theorem rank5_1_361 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,101,103,2,0⟩, ⟨false,2179,4357,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2905 rank5_1_337 rank5_1_360

theorem rank5_1_362 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,101,101,2,0⟩, ⟨false,4363,8719,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_363 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,103,103,2,0⟩, ⟨false,4363,8719,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_364 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,101,103,2,0⟩, ⟨false,4363,8725,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 8719 8725 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,101,103,2,0⟩, ⟨false,4363,8719,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 101 rank5_1_362 rank5_1_363

theorem rank5_1_365 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,4⟩, ⟨false,101,101,2,0⟩, ⟨false,8731,17449,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 3221 rank5_1_prime3221 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_366 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,101,101,2,0⟩, ⟨false,8731,17449,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_367 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,101,101,2,2⟩, ⟨false,8731,9973,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 10303 rank5_1_prime10303 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_368 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,101,101,4,0⟩, ⟨false,8731,9309,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 9293 9309 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,101,101,4,0⟩, ⟨false,8731,9293,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_369 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,101,101,4,0⟩, ⟨false,9311,9973,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_1_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_370 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,101,101,4,0⟩, ⟨false,9311,9973,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_371 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,101,101,4,0⟩, ⟨false,9311,9973,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_1_369 rank5_1_370

theorem rank5_1_372 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,101,101,4,0⟩, ⟨false,8731,9973,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 9309 rank5_1_368 rank5_1_371

theorem rank5_1_373 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,101,101,2,0⟩, ⟨false,8731,9975,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 9973 9975 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,101,101,2,0⟩, ⟨false,8731,9973,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .exponent 2 rank5_1_367 rank5_1_372

theorem rank5_1_374 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,101,101,2,0⟩, ⟨false,9977,11633,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 10007 9977 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,101,101,2,0⟩, ⟨false,10007,11633,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_375 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,101,101,2,0⟩, ⟨false,8731,11637,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 11633 11637 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,101,101,2,0⟩, ⟨false,8731,11633,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 9975 rank5_1_373 rank5_1_374

theorem rank5_1_376 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,101,101,2,0⟩, ⟨false,11639,17449,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 11657 11639 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,101,101,2,0⟩, ⟨false,11657,17449,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_377 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,101,101,2,0⟩, ⟨false,8731,17449,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 11637 rank5_1_375 rank5_1_376

theorem rank5_1_378 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,101,101,2,0⟩, ⟨false,8731,17449,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_1_366 rank5_1_377

theorem rank5_1_379 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,101,101,2,0⟩, ⟨false,8731,17461,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 17449 17461 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,101,101,2,0⟩, ⟨false,8731,17449,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_1_365 rank5_1_378

theorem rank5_1_380 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,101,101,2,0⟩, ⟨false,17463,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 17467 17463 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,101,101,2,0⟩, ⟨false,17467,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_381 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,101,101,2,0⟩, ⟨false,8731,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 17461 rank5_1_379 rank5_1_380

theorem rank5_1_382 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,103,103,2,0⟩, ⟨false,8731,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_383 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,101,103,2,0⟩, ⟨false,8727,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 8731 8727 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,101,103,2,0⟩, ⟨false,8731,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 101 rank5_1_381 rank5_1_382

end OddPerfect.SpoofBox
