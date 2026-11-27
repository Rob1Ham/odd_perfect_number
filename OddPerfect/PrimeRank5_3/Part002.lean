module

public import OddPerfect.PrimeRank5_3.Part001
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_3_24 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,263,277,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_25 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,6⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,281,293,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_26 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,4,4⟩, ⟨true,53,53,1,1⟩, ⟨false,281,283,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 30941 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_27 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,6,0⟩, ⟨true,53,53,1,1⟩, ⟨false,281,281,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_28 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,6,0⟩, ⟨true,53,53,1,1⟩, ⟨false,283,283,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_29 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,6,0⟩, ⟨true,53,53,1,1⟩, ⟨false,281,283,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 281 rank5_3_27 rank5_3_28

theorem rank5_3_30 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,281,285,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 283 285 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,281,283,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_3_26 rank5_3_29

theorem rank5_3_31 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,287,293,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 293 287 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,293,293,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_32 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,281,293,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 285 rank5_3_30 rank5_3_31

theorem rank5_3_33 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,279,293,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 281 279 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,281,293,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_3_25 rank5_3_32

theorem rank5_3_34 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,263,299,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 293 299 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,263,293,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 277 rank5_3_24 rank5_3_33

theorem rank5_3_35 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,301,349,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 307 301 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,307,349,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_36 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,263,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 299 rank5_3_34 rank5_3_35

theorem rank5_3_37 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,351,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 353 351 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,353,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_38 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,263,525,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 523 525 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 349 rank5_3_36 rank5_3_37

theorem rank5_3_39 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,527,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 541 527 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_40 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 525 rank5_3_38 rank5_3_39

theorem rank5_3_41 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 4 rank5_3_23 rank5_3_40

theorem rank5_3_42 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,4⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,5,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_43 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,5,0⟩, ⟨false,263,299,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 293 299 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,5,0⟩, ⟨false,263,293,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_44 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,6⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,5,0⟩, ⟨false,307,317,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_45 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,5,0⟩, ⟨false,307,311,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_46 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,4,4⟩, ⟨true,53,53,5,0⟩, ⟨false,313,317,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 30941 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_47 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,6,0⟩, ⟨true,53,53,5,0⟩, ⟨false,313,313,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
