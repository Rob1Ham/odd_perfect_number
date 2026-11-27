module

public import OddPerfect.PrimeRank5_4.Part017
import OddPerfect.PrimeRank5_4.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_408 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨false,83,163,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 109 rank5_4_330 rank5_4_407

theorem rank5_4_409 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,19,2,0⟩, ⟨false,83,163,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .base 17 rank5_4_199 rank5_4_408

theorem rank5_4_410 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,19,2,0⟩, ⟨false,83,165,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 163 165 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,19,2,0⟩, ⟨false,83,163,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 6 rank5_4_198 rank5_4_409

theorem rank5_4_411 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,167,333,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 331 333 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,167,331,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  apply covered_force_base _ 0 4 1093 rank5_4_prime1093 (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,167,331,2,0⟩, ⟨true,1093,1093,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 547 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_412 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,4⟩, ⟨false,17,17,2,0⟩, ⟨false,337,0,2,0⟩, ⟨true,349,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_413 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,2⟩, ⟨false,337,0,2,0⟩, ⟨true,349,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 307 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_414 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,673,2,0⟩, ⟨true,349,0,1,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 0 4 1093 rank5_4_prime1093 (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,673,2,0⟩, ⟨true,1093,1093,1,0⟩] : Vector Slot 5)
  apply covered_force_base _ 4 3 547 (by norm_num) (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,547,547,2,0⟩, ⟨true,1093,1093,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_415 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,675,0,2,0⟩, ⟨true,677,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 677 675 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,677,0,2,0⟩, ⟨true,677,0,1,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 4 701 678 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,677,0,2,0⟩, ⟨true,701,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_416 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,0,2,0⟩, ⟨true,349,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 673 rank5_4_414 rank5_4_415

theorem rank5_4_417 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨false,337,0,2,0⟩, ⟨true,349,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 2 rank5_4_413 rank5_4_416

theorem rank5_4_418 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,335,0,2,0⟩, ⟨true,337,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 337 335 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,337,0,2,0⟩, ⟨true,337,0,1,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 4 349 338 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,337,0,2,0⟩, ⟨true,349,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 4 rank5_4_412 rank5_4_417

theorem rank5_4_419 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,167,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 333 rank5_4_411 rank5_4_418

theorem rank5_4_420 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨false,167,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_421 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨false,17,19,2,0⟩, ⟨false,167,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .base 17 rank5_4_419 rank5_4_420

theorem rank5_4_422 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,4⟩, ⟨false,17,17,2,0⟩, ⟨false,167,331,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_423 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨false,167,331,2,0⟩, ⟨true,269,537,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 521 537 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨false,167,331,2,0⟩, ⟨true,269,521,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_424 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨true,541,1081,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1069 1081 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨true,541,1069,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_425 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨true,1093,2161,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_426 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨true,1093,1237,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_4_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_427 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨true,1093,1157,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1153 1157 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨true,1093,1153,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_428 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨true,1161,1237,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1181 1161 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨true,1181,1237,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_429 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨true,1093,1237,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1157 rank5_4_427 rank5_4_428

theorem rank5_4_430 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨true,1093,1237,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 6 rank5_4_426 rank5_4_429

theorem rank5_4_431 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨true,1241,1433,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1249 1241 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨true,1249,1433,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
