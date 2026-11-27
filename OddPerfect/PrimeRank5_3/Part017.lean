module

public import OddPerfect.PrimeRank5_3.Part016
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_3_384 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,137,181,1,0⟩, ⟨false,263,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 153 rank5_3_382 rank5_3_383

theorem rank5_3_385 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,137,181,1,0⟩, ⟨false,351,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 353 351 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,137,181,1,0⟩, ⟨false,353,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_386 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,4,0⟩, ⟨true,137,181,1,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 349 rank5_3_384 rank5_3_385

theorem rank5_3_387 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,2,0⟩, ⟨true,137,181,1,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 2 rank5_3_349 rank5_3_386

theorem rank5_3_388 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,2,0⟩, ⟨true,185,269,1,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 193 185 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,2,0⟩, ⟨true,193,269,1,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_389 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,2,0⟩, ⟨true,137,269,1,0⟩, ⟨false,263,525,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 523 525 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,2,0⟩, ⟨true,137,269,1,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 181 rank5_3_387 rank5_3_388

theorem rank5_3_390 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,2,0⟩, ⟨true,137,269,1,0⟩, ⟨false,527,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 541 527 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,2,0⟩, ⟨true,137,269,1,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_391 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,19,19,2,0⟩, ⟨true,137,269,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 525 rank5_3_389 rank5_3_390

theorem rank5_3_392 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨true,137,269,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 4 rank5_3_348 rank5_3_391

theorem rank5_3_393 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,19,2,0⟩, ⟨true,137,273,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 269 273 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,19,2,0⟩, ⟨true,137,269,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .base 17 rank5_3_347 rank5_3_392

theorem rank5_3_394 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,4⟩, ⟨false,17,17,2,0⟩, ⟨true,277,0,1,0⟩, ⟨false,281,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 11 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_395 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,2⟩, ⟨true,277,541,1,0⟩, ⟨false,281,557,2,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 2 4 307 (by norm_num) (Nat.odd_iff.mpr (by decide)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,2⟩, ⟨true,277,541,1,0⟩, ⟨false,307,307,2,0⟩] : Vector Slot 5)
  apply covered_prime_upper _ 3 293 306 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,2⟩, ⟨true,277,293,1,0⟩, ⟨false,307,307,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_396 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,373,1,0⟩, ⟨false,281,373,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 353 372 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,353,1,0⟩, ⟨false,281,373,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_397 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,365,1,0⟩, ⟨false,379,557,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 353 365 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,353,1,0⟩, ⟨false,379,557,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_398 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,449,1,0⟩, ⟨false,379,451,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 449 451 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,449,1,0⟩, ⟨false,379,449,2,0⟩] : Vector Slot 5)
  apply covered_prime_upper _ 3 433 448 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,433,1,0⟩, ⟨false,379,449,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_399 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,441,1,0⟩, ⟨false,457,557,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 433 441 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,433,1,0⟩, ⟨false,457,557,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_400 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,541,1,0⟩, ⟨false,457,557,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_401 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,501,1,0⟩, ⟨false,457,501,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 499 501 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,501,1,0⟩, ⟨false,457,499,2,0⟩] : Vector Slot 5)
  apply covered_prime_upper _ 3 461 498 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,461,1,0⟩, ⟨false,457,499,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_402 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,489,1,0⟩, ⟨false,503,557,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 461 489 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,461,1,0⟩, ⟨false,503,557,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_403 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,493,541,1,0⟩, ⟨false,503,557,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 509 493 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,509,541,1,0⟩, ⟨false,503,557,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 4 521 510 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,509,541,1,0⟩, ⟨false,521,557,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_404 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,541,1,0⟩, ⟨false,503,557,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 489 rank5_3_402 rank5_3_403

theorem rank5_3_405 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,541,1,0⟩, ⟨false,457,557,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 501 rank5_3_401 rank5_3_404

theorem rank5_3_406 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,445,541,1,0⟩, ⟨false,457,557,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 449 445 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,449,541,1,0⟩, ⟨false,457,557,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_3_400 rank5_3_405

theorem rank5_3_407 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,541,1,0⟩, ⟨false,453,557,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 457 453 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,541,1,0⟩, ⟨false,457,557,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 441 rank5_3_399 rank5_3_406

end OddPerfect.SpoofBox
