module

public import OddPerfect.PrimeRank5_1.Part001
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_24 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,11,19,2,0⟩, ⟨false,13,25,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 23 25 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,11,19,2,0⟩, ⟨false,13,23,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .base 13 rank5_1_22 rank5_1_23

theorem rank5_1_25 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,11,19,2,0⟩, ⟨false,27,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 29 27 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,11,19,2,0⟩, ⟨false,29,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  apply covered_force_base _ 0 2 13 (by norm_num) (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,2,0⟩, ⟨false,29,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_26 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,11,21,2,0⟩, ⟨false,13,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 2 19 21 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,11,19,2,0⟩, ⟨false,13,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 25 rank5_1_24 rank5_1_25

theorem rank5_1_27 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,23,0,2,0⟩, ⟨false,23,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 29 24 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,23,0,2,0⟩, ⟨false,29,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_28 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,11,0,2,0⟩, ⟨false,13,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .base 21 rank5_1_26 rank5_1_27

theorem rank5_1_29 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,11,13,2,0⟩, ⟨false,13,23,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_30 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,15,19,2,0⟩, ⟨false,15,23,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 2 17 15 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,17,19,2,0⟩, ⟨false,15,23,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 3 19 18 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,17,19,2,0⟩, ⟨false,19,23,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_31 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,11,19,2,0⟩, ⟨false,13,25,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 23 25 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,11,19,2,0⟩, ⟨false,13,23,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .base 13 rank5_1_29 rank5_1_30

theorem rank5_1_32 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,13,13,2,0⟩, ⟨false,29,37,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_33 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,13,13,2,2⟩, ⟨false,41,53,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 61 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_34 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,13,13,4,0⟩, ⟨false,41,45,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 43 45 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,13,13,4,0⟩, ⟨false,41,43,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_35 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,49,2,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 47 49 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_36 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,5⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,263,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_37 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,263,299,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 293 299 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,263,293,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_38 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,2,2⟩, ⟨false,307,317,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_39 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,4,0⟩, ⟨false,307,311,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_40 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,4,4⟩, ⟨false,53,53,4,0⟩, ⟨false,313,317,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 30941 rank5_1_prime30941 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_41 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,6,0⟩, ⟨false,53,53,4,0⟩, ⟨false,313,313,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_42 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,6,0⟩, ⟨false,53,53,4,0⟩, ⟨false,315,317,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 317 315 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,6,0⟩, ⟨false,53,53,4,0⟩, ⟨false,317,317,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_43 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,6,0⟩, ⟨false,53,53,4,0⟩, ⟨false,313,317,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 313 rank5_1_41 rank5_1_42

theorem rank5_1_44 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,4,0⟩, ⟨false,313,317,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 4 rank5_1_40 rank5_1_43

theorem rank5_1_45 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,4,0⟩, ⟨false,307,317,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 311 rank5_1_39 rank5_1_44

theorem rank5_1_46 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,307,325,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 317 325 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,307,317,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .exponent 2 rank5_1_38 rank5_1_45

theorem rank5_1_47 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,327,349,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 331 327 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨true,5,5,9,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,2,0⟩, ⟨false,331,349,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
