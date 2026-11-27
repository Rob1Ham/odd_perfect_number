module

public import OddPerfect.PrimeRank5_4.Part022
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_528 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨true,56973,71161,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 56989 56973 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨true,56989,71161,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 63289 rank5_4_490 rank5_4_527

theorem rank5_4_529 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨true,47497,71161,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 56969 rank5_4_489 rank5_4_528

theorem rank5_4_530 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨true,47497,71161,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 8 rank5_4_488 rank5_4_529

theorem rank5_4_531 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨true,47497,71161,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_4_487 rank5_4_530

theorem rank5_4_532 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨true,47453,71161,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 47497 47453 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨true,47497,71161,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_4_486 rank5_4_531

theorem rank5_4_533 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨true,35593,71185,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 71161 71185 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨true,35593,71161,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 47449 rank5_4_485 rank5_4_532

theorem rank5_4_534 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨true,71189,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 71209 71189 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨true,71209,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_535 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨true,35581,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 35593 35581 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨true,35593,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 71185 rank5_4_533 rank5_4_534

theorem rank5_4_536 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,259,2,0⟩, ⟨true,17789,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 257 259 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨true,17789,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 35577 rank5_4_484 rank5_4_535

theorem rank5_4_537 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,261,263,2,0⟩, ⟨true,17789,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 263 261 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,263,2,0⟩, ⟨true,17789,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_538 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,263,2,0⟩, ⟨true,17789,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 259 rank5_4_536 rank5_4_537

theorem rank5_4_539 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,263,2,0⟩, ⟨true,17789,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_4_483 rank5_4_538

theorem rank5_4_540 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,263,2,0⟩, ⟨true,8893,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 17785 rank5_4_482 rank5_4_539

theorem rank5_4_541 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,251,263,2,0⟩, ⟨true,8893,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 255 rank5_4_455 rank5_4_540

theorem rank5_4_542 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,251,263,2,0⟩, ⟨true,8885,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 8893 8885 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,251,263,2,0⟩, ⟨true,8893,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_4_454 rank5_4_541

theorem rank5_4_543 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,251,263,2,0⟩, ⟨true,4429,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 4441 4429 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,251,263,2,0⟩, ⟨true,4441,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 8881 rank5_4_453 rank5_4_542

theorem rank5_4_544 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,243,263,2,0⟩, ⟨true,2213,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 251 243 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,251,263,2,0⟩, ⟨true,2213,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 4425 rank5_4_450 rank5_4_543

theorem rank5_4_545 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,223,263,2,0⟩, ⟨true,2213,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 241 rank5_4_449 rank5_4_544

theorem rank5_4_546 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,223,263,2,0⟩, ⟨true,2189,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2213 2189 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,223,263,2,0⟩, ⟨true,2213,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_4_448 rank5_4_545

theorem rank5_4_547 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,223,265,2,0⟩, ⟨true,1093,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 263 265 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,223,263,2,0⟩, ⟨true,1093,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 2185 rank5_4_447 rank5_4_546

theorem rank5_4_548 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,331,2,0⟩, ⟨true,1093,2161,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_549 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,293,2,0⟩, ⟨true,1093,1449,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1433 1449 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,293,2,0⟩, ⟨true,1093,1433,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_550 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,279,2,0⟩, ⟨true,1453,2161,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 277 279 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,277,2,0⟩, ⟨true,1453,2161,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_551 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,293,2,0⟩, ⟨true,1453,1737,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1733 1737 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,293,2,0⟩, ⟨true,1453,1733,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
