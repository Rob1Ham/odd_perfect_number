module

public import OddPerfect.PrimeRank5_2.Part022
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_528 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,313,313,2,0⟩, ⟨false,1419,1439,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1423 1419 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,313,313,2,0⟩, ⟨false,1423,1439,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_529 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,313,313,2,0⟩, ⟨false,1399,1439,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1417 rank5_2_527 rank5_2_528

theorem rank5_2_530 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,313,313,2,0⟩, ⟨false,1361,1439,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1397 rank5_2_520 rank5_2_529

theorem rank5_2_531 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,315,317,2,0⟩, ⟨false,1361,1439,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 317 315 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,317,317,2,0⟩, ⟨false,1361,1439,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_532 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,313,317,2,0⟩, ⟨false,1361,1439,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 313 rank5_2_530 rank5_2_531

theorem rank5_2_533 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,313,317,2,0⟩, ⟨false,1361,1439,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_2_519 rank5_2_532

theorem rank5_2_534 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,307,317,2,0⟩, ⟨false,1339,1439,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1361 1339 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,307,317,2,0⟩, ⟨false,1361,1439,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 311 rank5_2_518 rank5_2_533

theorem rank5_2_535 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,307,317,2,0⟩, ⟨false,1249,1439,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1337 rank5_2_515 rank5_2_534

theorem rank5_2_536 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,307,317,2,0⟩, ⟨false,1239,1439,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1249 1239 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,307,317,2,0⟩, ⟨false,1249,1439,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_2_498 rank5_2_535

theorem rank5_2_537 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,305,317,2,0⟩, ⟨false,1087,1439,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 307 305 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,307,317,2,0⟩, ⟨false,1087,1439,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1237 rank5_2_497 rank5_2_536

theorem rank5_2_538 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,317,2,0⟩, ⟨false,1087,1445,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1439 1445 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,317,2,0⟩, ⟨false,1087,1439,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 303 rank5_2_496 rank5_2_537

theorem rank5_2_539 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1447,1733,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_540 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨true,17,17,5,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1741,2161,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_2_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_541 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1741,1927,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1913 1927 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1741,1913,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_542 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1931,2161,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_543 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1931,1983,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1979 1983 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1931,1979,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_544 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,293,2,0⟩, ⟨false,1987,2011,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_545 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,293,2,0⟩, ⟨false,2017,2039,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_2_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_546 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,8⟩, ⟨true,17,17,5,0⟩, ⟨false,293,293,2,0⟩, ⟨false,2017,2039,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_547 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,293,2,0⟩, ⟨false,2017,2021,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2017 2021 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,293,2,0⟩, ⟨false,2017,2017,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_548 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,293,2,0⟩, ⟨false,2023,2027,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2027 2023 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,293,2,0⟩, ⟨false,2027,2027,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_549 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,293,2,0⟩, ⟨false,2017,2027,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2021 rank5_2_547 rank5_2_548

theorem rank5_2_550 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,293,2,0⟩, ⟨false,2029,2039,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_551 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,293,2,0⟩, ⟨false,2017,2039,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2027 rank5_2_549 rank5_2_550

end OddPerfect.SpoofBox
