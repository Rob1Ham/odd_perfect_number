module

public import OddPerfect.PrimeCover
import OddPerfect.PrimeRank5_4.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_0 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,7,2,0⟩, ⟨false,7,9,2,0⟩, ⟨false,11,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 2 7 9 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,7,2,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  apply covered_prime_upper _ 1 5 6 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  apply covered_force_base _ 0 3 13 (by norm_num) (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,7,7,2,0⟩, ⟨false,13,13,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact covered_impossible_prime_rows _ (by decide +kernel)

theorem rank5_4_1 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,13,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_2 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,7,7,2,2⟩, ⟨false,11,13,2,0⟩, ⟨false,13,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 1 3 19 (by norm_num) (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,7,7,2,2⟩, ⟨false,11,13,2,0⟩, ⟨false,19,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  apply covered_force_base _ 0 2 13 (by norm_num) (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,7,7,2,2⟩, ⟨false,13,13,2,0⟩, ⟨false,19,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_3 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,7,7,4,0⟩, ⟨false,11,13,2,0⟩, ⟨false,13,15,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 13 15 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,7,7,4,0⟩, ⟨false,11,13,2,0⟩, ⟨false,13,13,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  apply covered_prime_upper _ 2 11 12 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,7,7,4,0⟩, ⟨false,11,11,2,0⟩, ⟨false,13,13,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_4 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,7,7,4,0⟩, ⟨false,11,13,2,0⟩, ⟨false,17,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 0 2 13 (by norm_num) (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,7,7,4,0⟩, ⟨false,13,13,2,0⟩, ⟨false,17,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_5 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,7,7,4,0⟩, ⟨false,11,13,2,0⟩, ⟨false,13,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 15 rank5_4_3 rank5_4_4

theorem rank5_4_6 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,7,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,13,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 2 rank5_4_2 rank5_4_5

theorem rank5_4_7 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,11,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 13 12 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,13,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .base 5 rank5_4_1 rank5_4_6

theorem rank5_4_8 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,7,2,0⟩, ⟨false,7,13,2,0⟩, ⟨false,11,21,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 19 21 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,7,2,0⟩, ⟨false,7,13,2,0⟩, ⟨false,11,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .base 9 rank5_4_0 rank5_4_7

theorem rank5_4_9 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,2⟩, ⟨false,13,13,2,0⟩, ⟨false,23,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 1 3 31 (by norm_num) (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,2⟩, ⟨false,13,13,2,0⟩, ⟨false,31,31,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_10 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,13,13,2,0⟩, ⟨false,23,45,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 43 45 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,13,13,2,0⟩, ⟨false,23,43,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_11 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,13,13,2,2⟩, ⟨false,47,61,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 2 3 61 (by norm_num) (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,13,13,2,2⟩, ⟨false,61,61,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_12 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,4⟩, ⟨false,13,13,4,0⟩, ⟨false,47,61,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_13 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,49,2,0⟩, ⟨true,269,521,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 47 49 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨true,269,521,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_14 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,2,0⟩, ⟨true,269,305,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 293 305 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,2,0⟩, ⟨true,269,293,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_15 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,6⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,2,0⟩, ⟨true,313,317,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_4_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_16 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,2,2⟩, ⟨true,313,317,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_17 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,4,4⟩, ⟨false,53,53,4,0⟩, ⟨true,313,317,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 30941 rank5_4_prime30941 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_18 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,6,0⟩, ⟨false,53,53,4,0⟩, ⟨true,313,313,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 4 157 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_19 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,6,0⟩, ⟨false,53,53,4,0⟩, ⟨true,317,317,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_20 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,6,0⟩, ⟨false,53,53,4,0⟩, ⟨true,313,317,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 313 rank5_4_18 rank5_4_19

theorem rank5_4_21 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,4,0⟩, ⟨true,313,317,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 4 rank5_4_17 rank5_4_20

theorem rank5_4_22 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,2,0⟩, ⟨true,313,317,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .exponent 2 rank5_4_16 rank5_4_21

theorem rank5_4_23 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,2,0⟩, ⟨true,313,329,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 317 329 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,2,0⟩, ⟨true,313,317,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_4_15 rank5_4_22

end OddPerfect.SpoofBox
