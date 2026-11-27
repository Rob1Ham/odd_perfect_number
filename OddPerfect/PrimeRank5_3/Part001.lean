module

public import OddPerfect.PrimeCover
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_3_0 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,7,2,0⟩, ⟨false,7,9,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 2 7 9 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,7,2,0⟩, ⟨false,7,7,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_upper _ 1 5 6 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,7,7,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  apply covered_force_base _ 0 3 13 (by norm_num) (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,7,7,2,0⟩, ⟨true,13,13,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact covered_impossible_prime_rows _ (by decide +kernel)

theorem rank5_3_1 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,11,13,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_2 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,7,7,2,2⟩, ⟨false,11,13,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_3 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,2,2⟩, ⟨true,13,13,1,1⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_4 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨true,13,13,1,1⟩, ⟨false,263,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_5 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,7,7,4,4⟩, ⟨false,11,11,4,0⟩, ⟨true,13,13,1,1⟩, ⟨false,353,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 2801 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_6 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,7,7,6,0⟩, ⟨false,11,11,4,0⟩, ⟨true,13,13,1,1⟩, ⟨false,353,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_7 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨true,13,13,1,1⟩, ⟨false,351,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 353 351 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨true,13,13,1,1⟩, ⟨false,353,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 4 rank5_3_5 rank5_3_6

theorem rank5_3_8 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨true,13,13,1,1⟩, ⟨false,263,525,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 523 525 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨true,13,13,1,1⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 349 rank5_3_4 rank5_3_7

theorem rank5_3_9 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨true,13,13,1,1⟩, ⟨false,527,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 541 527 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨true,13,13,1,1⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_10 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,4,0⟩, ⟨true,13,13,1,1⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 525 rank5_3_8 rank5_3_9

theorem rank5_3_11 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,2,0⟩, ⟨true,13,13,1,1⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 2 rank5_3_3 rank5_3_10

theorem rank5_3_12 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,2,0⟩, ⟨true,13,13,5,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_13 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,7,7,4,0⟩, ⟨false,11,13,2,0⟩, ⟨true,13,13,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 2 11 12 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,2,0⟩, ⟨true,13,13,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .exponent 1 rank5_3_11 rank5_3_12

theorem rank5_3_14 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,7,7,4,0⟩, ⟨false,11,13,2,0⟩, ⟨true,17,17,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 0 2 13 (by norm_num) (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,7,7,4,0⟩, ⟨false,13,13,2,0⟩, ⟨true,17,17,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_15 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,7,7,4,0⟩, ⟨false,11,13,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 13 rank5_3_13 rank5_3_14

theorem rank5_3_16 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,7,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 2 rank5_3_2 rank5_3_15

theorem rank5_3_17 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .base 5 rank5_3_1 rank5_3_16

theorem rank5_3_18 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,7,2,0⟩, ⟨false,7,13,2,0⟩, ⟨true,13,25,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 17 25 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,7,2,0⟩, ⟨false,7,13,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .base 9 rank5_3_0 rank5_3_17

theorem rank5_3_19 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,2⟩, ⟨false,13,13,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 31 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_20 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,13,13,2,0⟩, ⟨true,29,37,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_21 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,13,13,2,2⟩, ⟨true,41,53,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 61 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_22 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,13,13,4,0⟩, ⟨true,41,45,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 41 45 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,13,13,4,0⟩, ⟨true,41,41,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 3 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_23 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,4⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end OddPerfect.SpoofBox
