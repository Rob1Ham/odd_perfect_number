module

public import OddPerfect.PrimeRank5_2.Part017
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_408 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,163,211,2,0⟩, ⟨false,541,1081,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1069 1081 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,163,211,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 183 rank5_2_406 rank5_2_407

theorem rank5_2_409 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,163,211,2,0⟩, ⟨false,1083,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1087 1083 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,163,211,2,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_410 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,163,215,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 211 215 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,163,211,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1081 rank5_2_408 rank5_2_409

theorem rank5_2_411 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,217,317,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 223 217 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,223,317,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_412 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,163,317,2,0⟩, ⟨false,527,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 541 527 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,163,317,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 215 rank5_2_410 rank5_2_411

theorem rank5_2_413 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,163,317,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 525 rank5_2_335 rank5_2_412

theorem rank5_2_414 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,1⟩, ⟨false,163,325,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 317 325 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,1⟩, ⟨false,163,317,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 4 rank5_2_198 rank5_2_413

theorem rank5_2_415 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,1⟩, ⟨false,327,0,2,0⟩, ⟨false,327,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 331 327 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,1⟩, ⟨false,331,0,2,0⟩, ⟨false,327,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 4 337 332 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,1⟩, ⟨false,331,0,2,0⟩, ⟨false,337,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_416 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,1⟩, ⟨false,163,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 325 rank5_2_414 rank5_2_415

theorem rank5_2_417 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,1⟩, ⟨false,159,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 163 159 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,1⟩, ⟨false,163,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 6 rank5_2_197 rank5_2_416

theorem rank5_2_418 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,1⟩, ⟨false,79,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 157 rank5_2_194 rank5_2_417

theorem rank5_2_419 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,5,0⟩, ⟨false,79,157,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_420 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,4⟩, ⟨true,17,17,5,0⟩, ⟨false,163,317,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_421 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,163,215,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 211 215 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,163,211,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_422 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,223,261,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 257 261 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,223,257,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_423 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,287,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 283 287 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,283,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_424 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,289,317,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 293 289 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,317,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_425 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,317,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 287 rank5_2_423 rank5_2_424

theorem rank5_2_426 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,217,317,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 223 217 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,223,317,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 261 rank5_2_422 rank5_2_425

theorem rank5_2_427 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,163,317,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 215 rank5_2_421 rank5_2_426

theorem rank5_2_428 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,5,0⟩, ⟨false,163,325,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 317 325 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,5,0⟩, ⟨false,163,317,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  apply covered_force_base _ 0 4 1093 rank5_2_prime1093 (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,5,0⟩, ⟨false,163,317,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 4 rank5_2_420 rank5_2_427

theorem rank5_2_429 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,4⟩, ⟨true,17,17,5,0⟩, ⟨false,331,0,2,0⟩, ⟨false,337,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_430 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,661,2,0⟩, ⟨false,337,0,2,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 0 4 1093 rank5_2_prime1093 (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,661,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_431 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,663,0,2,0⟩, ⟨false,663,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 673 663 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,673,0,2,0⟩, ⟨false,663,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 4 677 674 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,673,0,2,0⟩, ⟨false,677,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
