module

public import OddPerfect.PrimeRank5_1.Part017
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_408 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,107,107,2,2⟩, ⟨false,1511,1531,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_409 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,107,107,4,0⟩, ⟨false,1511,1531,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_1_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_410 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,107,107,4,0⟩, ⟨false,1511,1519,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1511 1519 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,107,107,4,0⟩, ⟨false,1511,1511,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_411 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,107,107,4,0⟩, ⟨false,1521,1531,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1523 1521 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,107,107,4,0⟩, ⟨false,1523,1531,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_412 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,107,107,4,0⟩, ⟨false,1511,1531,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1519 rank5_1_410 rank5_1_411

theorem rank5_1_413 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,107,107,4,0⟩, ⟨false,1511,1531,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_1_409 rank5_1_412

theorem rank5_1_414 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,107,107,2,0⟩, ⟨false,1511,1539,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1531 1539 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,107,107,2,0⟩, ⟨false,1511,1531,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .exponent 2 rank5_1_408 rank5_1_413

theorem rank5_1_415 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,107,107,2,0⟩, ⟨false,1541,1571,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1543 1541 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,107,107,2,0⟩, ⟨false,1543,1571,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_416 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,107,107,2,0⟩, ⟨false,1507,1571,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1511 1507 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,107,107,2,0⟩, ⟨false,1511,1571,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1539 rank5_1_414 rank5_1_415

theorem rank5_1_417 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,107,107,2,0⟩, ⟨false,1447,1571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1505 rank5_1_407 rank5_1_416

theorem rank5_1_418 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,6,0⟩, ⟨false,107,107,2,0⟩, ⟨false,1447,1571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_1_406 rank5_1_417

theorem rank5_1_419 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,107,107,2,0⟩, ⟨false,1447,1577,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1571 1577 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,107,107,2,0⟩, ⟨false,1447,1571,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_1_405 rank5_1_418

theorem rank5_1_420 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,107,107,2,0⟩, ⟨false,1579,1733,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_421 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,107,107,2,0⟩, ⟨false,1447,1733,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1577 rank5_1_419 rank5_1_420

theorem rank5_1_422 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,109,109,2,0⟩, ⟨false,1447,1733,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_423 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,107,109,2,0⟩, ⟨false,1447,1733,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 107 rank5_1_421 rank5_1_422

theorem rank5_1_424 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,107,109,2,0⟩, ⟨false,1735,2161,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1741 1735 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,107,109,2,0⟩, ⟨false,1741,2161,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_425 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,107,109,2,0⟩, ⟨false,1447,2161,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1733 rank5_1_423 rank5_1_424

theorem rank5_1_426 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,107,109,2,0⟩, ⟨false,1087,2161,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1445 rank5_1_404 rank5_1_425

theorem rank5_1_427 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,111,113,2,0⟩, ⟨false,1087,2161,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 113 111 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,113,113,2,0⟩, ⟨false,1087,2161,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_428 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,107,113,2,0⟩, ⟨false,1087,2161,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 109 rank5_1_426 rank5_1_427

theorem rank5_1_429 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,107,113,2,0⟩, ⟨false,1087,2173,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2161 2173 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,107,113,2,0⟩, ⟨false,1087,2161,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_1_389 rank5_1_428

theorem rank5_1_430 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,107,113,2,0⟩, ⟨false,2175,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2179 2175 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,107,113,2,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_431 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,105,113,2,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 107 105 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,4,0⟩, ⟨false,107,113,2,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 2173 rank5_1_429 rank5_1_430

end OddPerfect.SpoofBox
