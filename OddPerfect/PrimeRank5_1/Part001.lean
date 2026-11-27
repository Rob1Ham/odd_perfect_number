module

public import OddPerfect.PrimeCover
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_0 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,11,13,2,0⟩, ⟨false,13,15,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 13 15 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,11,13,2,0⟩, ⟨false,13,13,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_upper _ 2 11 12 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,2,0⟩, ⟨false,13,13,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,2,2⟩, ⟨false,17,19,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 61 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_1_2 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,17,17,2,2⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 3 4 307 (by norm_num) (Nat.odd_iff.mpr (by decide)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_3 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_4 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,17,17,4,0⟩, ⟨false,353,383,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_5 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,17,17,4,0⟩, ⟨false,389,403,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 401 403 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,17,17,4,0⟩, ⟨false,389,401,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_6 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,17,17,4,0⟩, ⟨false,409,413,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 409 413 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,17,17,4,0⟩, ⟨false,409,409,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_7 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,17,17,4,0⟩, ⟨false,415,421,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 419 415 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,421,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_8 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,17,17,4,0⟩, ⟨false,405,421,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 409 405 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,17,17,4,0⟩, ⟨false,409,421,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 413 rank5_1_6 rank5_1_7

theorem rank5_1_9 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,17,17,4,0⟩, ⟨false,385,421,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 389 385 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,17,17,4,0⟩, ⟨false,389,421,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 403 rank5_1_5 rank5_1_8

theorem rank5_1_10 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,17,17,4,0⟩, ⟨false,353,421,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 383 rank5_1_4 rank5_1_9

theorem rank5_1_11 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,17,17,4,0⟩, ⟨false,423,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 431 423 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,17,17,4,0⟩, ⟨false,431,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_12 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,17,17,4,0⟩, ⟨false,351,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 353 351 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,17,17,4,0⟩, ⟨false,353,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 421 rank5_1_10 rank5_1_11

theorem rank5_1_13 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 349 rank5_1_3 rank5_1_12

theorem rank5_1_14 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,263,525,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 523 525 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .exponent 2 rank5_1_2 rank5_1_13

theorem rank5_1_15 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,527,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 541 527 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_16 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 525 rank5_1_14 rank5_1_15

theorem rank5_1_17 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,19,19,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_18 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,4,0⟩, ⟨false,17,19,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 17 rank5_1_16 rank5_1_17

theorem rank5_1_19 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,2,0⟩, ⟨false,17,19,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 2 rank5_1_1 rank5_1_18

theorem rank5_1_20 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,2,0⟩, ⟨false,21,23,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 23 21 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,2,0⟩, ⟨false,23,23,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_21 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,11,13,2,0⟩, ⟨false,17,23,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 0 2 13 (by norm_num) (Nat.odd_iff.mpr (by decide)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,2,0⟩, ⟨false,17,23,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 19 rank5_1_19 rank5_1_20

theorem rank5_1_22 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,11,13,2,0⟩, ⟨false,13,23,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 15 rank5_1_0 rank5_1_21

theorem rank5_1_23 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,15,19,2,0⟩, ⟨false,15,23,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 2 17 15 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,17,19,2,0⟩, ⟨false,15,23,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 3 19 18 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,17,19,2,0⟩, ⟨false,19,23,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

end OddPerfect.SpoofBox
