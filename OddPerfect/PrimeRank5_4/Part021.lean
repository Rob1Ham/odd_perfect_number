module

public import OddPerfect.PrimeRank5_4.Part020
import OddPerfect.PrimeRank5_4.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_480 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,261,263,2,0⟩, ⟨true,8893,17761,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 263 261 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,263,2,0⟩, ⟨true,8893,17761,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 11849 rank5_4_478 rank5_4_479

theorem rank5_4_481 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,263,2,0⟩, ⟨true,8893,17761,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 259 rank5_4_457 rank5_4_480

theorem rank5_4_482 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,263,2,0⟩, ⟨true,8893,17785,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 17761 17785 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,263,2,0⟩, ⟨true,8893,17761,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_4_456 rank5_4_481

theorem rank5_4_483 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,263,2,0⟩, ⟨true,17789,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_484 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨true,17789,35577,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 35573 35577 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨true,17789,35573,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_485 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨true,35593,47449,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 47441 47449 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨true,35593,47441,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_486 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,4⟩, ⟨false,257,257,2,0⟩, ⟨true,47497,71161,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 88741 rank5_4_prime88741 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_487 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨true,47497,71161,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_4_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_488 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,8⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨true,47497,71161,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_489 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨true,47497,56969,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 56957 56969 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨true,47497,56957,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_490 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨true,56989,63289,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 63281 63289 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨true,56989,63281,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_491 : PrimeCovered (#v[⟨false,3,3,14,14⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,0⟩, ⟨true,63313,66977,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_492 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,2,2⟩, ⟨true,63313,66977,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 61 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_493 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨true,63313,65093,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 65089 65093 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨true,63313,65089,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_494 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,10⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65101,65993,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 12207031 rank5_4_prime12207031 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_495 : PrimeCovered (#v[⟨false,3,3,16,16⟩, ⟨false,5,5,12,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65101,65537,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 1871 rank5_4_prime1871 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_496 : PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨false,5,5,12,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65101,65317,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 65309 65317 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨false,5,5,12,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65101,65309,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_497 : PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨false,5,5,12,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65353,65441,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 65437 65441 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨false,5,5,12,0⟩, ⟨false,17,17,6,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65353,65437,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_498 : PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨false,5,5,12,0⟩, ⟨false,17,17,6,6⟩, ⟨false,257,257,4,0⟩, ⟨true,65449,65537,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 25646167 rank5_4_prime25646167 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_499 : PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨false,5,5,12,0⟩, ⟨false,17,17,8,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65449,65489,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 65449 65489 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨false,5,5,12,0⟩, ⟨false,17,17,8,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65449,65449,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_500 : PrimeCovered (#v[⟨false,3,3,18,18⟩, ⟨false,5,5,12,0⟩, ⟨false,17,17,8,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65497,65537,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 1597 rank5_4_prime1597 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_501 : PrimeCovered (#v[⟨false,3,3,20,0⟩, ⟨false,5,5,12,12⟩, ⟨false,17,17,8,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65497,65513,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 65497 65513 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,20,0⟩, ⟨false,5,5,12,12⟩, ⟨false,17,17,8,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65497,65497,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 32749 rank5_4_prime32749 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_502 : PrimeCovered (#v[⟨false,3,3,20,0⟩, ⟨false,5,5,12,12⟩, ⟨false,17,17,8,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65521,65525,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 65521 65525 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,20,0⟩, ⟨false,5,5,12,12⟩, ⟨false,17,17,8,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65521,65521,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 181 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_503 : PrimeCovered (#v[⟨false,3,3,20,0⟩, ⟨false,5,5,12,12⟩, ⟨false,17,17,8,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65529,65537,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 65537 65529 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,20,0⟩, ⟨false,5,5,12,12⟩, ⟨false,17,17,8,0⟩, ⟨false,257,257,4,0⟩, ⟨true,65537,65537,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end OddPerfect.SpoofBox
