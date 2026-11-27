module

public import OddPerfect.PrimeRank5_4.Part002
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_48 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨true,2189,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2213 2189 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨true,2213,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_49 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨true,1085,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1093 1085 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨true,1093,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 2185 rank5_4_47 rank5_4_48

theorem rank5_4_50 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,49,2,0⟩, ⟨true,541,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 47 49 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,47,2,0⟩, ⟨true,541,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1081 rank5_4_30 rank5_4_49

theorem rank5_4_51 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,51,53,2,0⟩, ⟨true,541,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 53 51 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,53,53,2,0⟩, ⟨true,541,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_52 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,53,2,0⟩, ⟨true,541,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 49 rank5_4_50 rank5_4_51

theorem rank5_4_53 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,53,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 537 rank5_4_29 rank5_4_52

theorem rank5_4_54 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,55,61,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 59 55 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,59,61,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_55 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,6,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,61,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 53 rank5_4_53 rank5_4_54

theorem rank5_4_56 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,13,13,4,0⟩, ⟨false,47,61,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 4 rank5_4_12 rank5_4_55

theorem rank5_4_57 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,13,13,2,0⟩, ⟨false,47,61,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 2 rank5_4_11 rank5_4_56

theorem rank5_4_58 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,13,13,2,0⟩, ⟨false,63,89,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 67 63 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,13,13,2,0⟩, ⟨false,67,89,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_59 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,13,13,2,0⟩, ⟨false,47,93,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 89 93 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,13,13,2,0⟩, ⟨false,47,89,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 61 rank5_4_57 rank5_4_58

theorem rank5_4_60 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,13,13,2,0⟩, ⟨false,95,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 97 95 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,13,13,2,0⟩, ⟨false,97,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_61 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,13,13,2,0⟩, ⟨false,47,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 93 rank5_4_59 rank5_4_60

theorem rank5_4_62 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,13,13,2,0⟩, ⟨false,23,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 45 rank5_4_10 rank5_4_61

theorem rank5_4_63 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,13,13,2,0⟩, ⟨false,23,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 2 rank5_4_9 rank5_4_62

theorem rank5_4_64 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,7,7,2,0⟩, ⟨false,13,13,2,0⟩, ⟨false,23,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_65 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,7,2,0⟩, ⟨false,7,13,2,0⟩, ⟨false,23,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 0 2 13 (by norm_num) (Nat.odd_iff.mpr (by decide)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,7,2,0⟩, ⟨false,13,13,2,0⟩, ⟨false,23,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .base 5 rank5_4_63 rank5_4_64

theorem rank5_4_66 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,7,2,0⟩, ⟨false,7,13,2,0⟩, ⟨false,11,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 21 rank5_4_8 rank5_4_65

theorem rank5_4_67 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,7,2,0⟩, ⟨false,15,0,2,0⟩, ⟨false,15,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 2 17 15 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,7,2,0⟩, ⟨false,17,0,2,0⟩, ⟨false,15,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 3 19 18 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,7,2,0⟩, ⟨false,17,0,2,0⟩, ⟨false,19,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_4_68 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,9,2,0⟩, ⟨false,7,0,2,0⟩, ⟨false,11,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 1 7 9 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,7,2,0⟩, ⟨false,7,0,2,0⟩, ⟨false,11,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .base 13 rank5_4_66 rank5_4_67

theorem rank5_4_69 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,11,0,2,0⟩, ⟨false,11,0,2,0⟩, ⟨false,11,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 2 13 12 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,11,0,2,0⟩, ⟨false,13,0,2,0⟩, ⟨false,11,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 3 17 14 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,11,0,2,0⟩, ⟨false,13,0,2,0⟩, ⟨false,17,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_70 : PrimeCovered (#v[⟨false,3,3,2,2⟩, ⟨false,5,0,2,0⟩, ⟨false,7,0,2,0⟩, ⟨false,11,0,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .base 9 rank5_4_68 rank5_4_69

theorem rank5_4_71 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,7,2,0⟩, ⟨false,7,9,2,0⟩, ⟨false,11,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 2 7 9 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,7,2,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  apply covered_prime_upper _ 1 5 6 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact covered_impossible_prime_rows _ (by decide +kernel)

end OddPerfect.SpoofBox
