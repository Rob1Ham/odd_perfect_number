module

public import OddPerfect.PrimeRank5_3.Part017
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_3_408 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,369,541,1,0⟩, ⟨false,379,557,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 373 369 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,541,1,0⟩, ⟨false,379,557,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 451 rank5_3_398 rank5_3_407

theorem rank5_3_409 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,541,1,0⟩, ⟨false,375,557,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 379 375 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,541,1,0⟩, ⟨false,379,557,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 365 rank5_3_397 rank5_3_408

theorem rank5_3_410 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,541,1,0⟩, ⟨false,281,557,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 373 rank5_3_396 rank5_3_409

theorem rank5_3_411 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨true,277,541,1,0⟩, ⟨false,281,561,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 557 561 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨true,277,541,1,0⟩, ⟨false,281,557,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 2 rank5_3_395 rank5_3_410

theorem rank5_3_412 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,2⟩, ⟨true,277,541,1,0⟩, ⟨false,563,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 307 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_413 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,353,1,0⟩, ⟨false,563,749,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 743 749 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,353,1,0⟩, ⟨false,563,743,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_414 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,353,1,0⟩, ⟨false,751,1123,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_415 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,309,1,0⟩, ⟨false,751,1123,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 293 309 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,293,1,0⟩, ⟨false,751,1123,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_416 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,353,1,0⟩, ⟨false,751,899,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 887 899 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,353,1,0⟩, ⟨false,751,887,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_417 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,329,1,0⟩, ⟨false,907,1123,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 317 329 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,317,1,0⟩, ⟨false,907,1123,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_418 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨true,337,353,1,0⟩, ⟨false,907,997,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_419 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,337,341,1,0⟩, ⟨false,907,997,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 337 341 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,337,337,1,0⟩, ⟨false,907,997,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 3 13 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_420 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,349,353,1,0⟩, ⟨false,907,947,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_421 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,349,353,1,0⟩, ⟨false,907,925,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 919 925 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,349,353,1,0⟩, ⟨false,907,919,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_422 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,349,349,1,0⟩, ⟨false,929,947,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 7 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_423 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,353,353,1,0⟩, ⟨false,929,947,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 59 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_424 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,349,353,1,0⟩, ⟨false,927,947,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 929 927 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,349,353,1,0⟩, ⟨false,929,947,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 349 rank5_3_422 rank5_3_423

theorem rank5_3_425 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,349,353,1,0⟩, ⟨false,907,947,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 925 rank5_3_421 rank5_3_424

theorem rank5_3_426 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,349,353,1,0⟩, ⟨false,907,949,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 947 949 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,349,353,1,0⟩, ⟨false,907,947,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_3_420 rank5_3_425

theorem rank5_3_427 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,349,353,1,0⟩, ⟨false,953,997,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_428 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,349,349,1,0⟩, ⟨false,953,971,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 7 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_429 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,353,353,1,0⟩, ⟨false,953,971,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 59 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_430 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,349,353,1,0⟩, ⟨false,953,973,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 971 973 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,349,353,1,0⟩, ⟨false,953,971,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 349 rank5_3_428 rank5_3_429

theorem rank5_3_431 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,349,353,1,0⟩, ⟨false,975,997,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 977 975 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,349,353,1,0⟩, ⟨false,977,997,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
