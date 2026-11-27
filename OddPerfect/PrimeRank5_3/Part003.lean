module

public import OddPerfect.PrimeRank5_3.Part002
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_3_48 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,6,0⟩, ⟨true,53,53,5,0⟩, ⟨false,315,317,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 317 315 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,6,0⟩, ⟨true,53,53,5,0⟩, ⟨false,317,317,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_49 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,6,0⟩, ⟨true,53,53,5,0⟩, ⟨false,313,317,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 313 rank5_3_47 rank5_3_48

theorem rank5_3_50 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,5,0⟩, ⟨false,313,317,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 4 rank5_3_46 rank5_3_49

theorem rank5_3_51 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,8,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,5,0⟩, ⟨false,307,317,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 311 rank5_3_45 rank5_3_50

theorem rank5_3_52 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,5,0⟩, ⟨false,307,325,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 317 325 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,5,0⟩, ⟨false,307,317,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_3_44 rank5_3_51

theorem rank5_3_53 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,5,0⟩, ⟨false,327,349,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 331 327 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,5,0⟩, ⟨false,331,349,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_54 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,5,0⟩, ⟨false,301,349,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 307 301 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,5,0⟩, ⟨false,307,349,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 325 rank5_3_52 rank5_3_53

theorem rank5_3_55 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,5,0⟩, ⟨false,263,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 299 rank5_3_43 rank5_3_54

theorem rank5_3_56 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,5,0⟩, ⟨false,351,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 353 351 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,5,0⟩, ⟨false,353,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_57 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,5,0⟩, ⟨false,263,525,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 523 525 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,5,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 349 rank5_3_55 rank5_3_56

theorem rank5_3_58 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,5,0⟩, ⟨false,527,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 541 527 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,5,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_59 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,5,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 525 rank5_3_57 rank5_3_58

theorem rank5_3_60 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,5,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 4 rank5_3_42 rank5_3_59

theorem rank5_3_61 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,13,13,4,0⟩, ⟨true,49,53,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 53 49 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,13,13,4,0⟩, ⟨true,53,53,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .exponent 1 rank5_3_41 rank5_3_60

theorem rank5_3_62 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,13,13,4,0⟩, ⟨true,41,53,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 45 rank5_3_22 rank5_3_61

theorem rank5_3_63 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,13,13,2,0⟩, ⟨true,41,53,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 2 rank5_3_21 rank5_3_62

theorem rank5_3_64 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,13,13,2,0⟩, ⟨true,29,57,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 53 57 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,13,13,2,0⟩, ⟨true,29,53,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 37 rank5_3_20 rank5_3_63

theorem rank5_3_65 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,13,13,2,0⟩, ⟨true,61,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_66 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,13,13,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 57 rank5_3_64 rank5_3_65

theorem rank5_3_67 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,13,13,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 2 rank5_3_19 rank5_3_66

theorem rank5_3_68 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,7,7,2,0⟩, ⟨false,13,13,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_69 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,7,2,0⟩, ⟨false,7,13,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 0 2 13 (by norm_num) (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,7,2,0⟩, ⟨false,13,13,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .base 5 rank5_3_67 rank5_3_68

theorem rank5_3_70 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,7,2,0⟩, ⟨false,7,13,2,0⟩, ⟨true,13,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 25 rank5_3_18 rank5_3_69

theorem rank5_3_71 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,7,2,0⟩, ⟨false,15,0,2,0⟩, ⟨true,17,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 2 17 15 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,7,2,0⟩, ⟨false,17,0,2,0⟩, ⟨true,17,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 3 29 18 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,7,2,0⟩, ⟨false,17,0,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end OddPerfect.SpoofBox
