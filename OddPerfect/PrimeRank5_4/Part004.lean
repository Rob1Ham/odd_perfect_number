module

public import OddPerfect.PrimeRank5_4.Part003
import OddPerfect.PrimeRank5_4.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_72 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,13,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_73 : PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨false,7,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,13,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 0 2 11 (by norm_num) (Nat.odd_iff.mpr (by decide)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,4⟩, ⟨false,7,7,2,0⟩, ⟨false,11,11,2,0⟩, ⟨false,13,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_74 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,7,7,2,2⟩, ⟨false,11,11,2,0⟩, ⟨false,19,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_75 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,7,7,2,2⟩, ⟨false,13,13,2,0⟩, ⟨false,19,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 0 4 1093 rank5_4_prime1093 (Nat.odd_iff.mpr (by decide)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,7,7,2,2⟩, ⟨false,13,13,2,0⟩, ⟨false,19,19,2,0⟩, ⟨true,1093,1093,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 547 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_4_76 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,2,2⟩, ⟨false,13,13,2,2⟩, ⟨false,19,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 61 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_4_77 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,2,2⟩, ⟨false,13,13,4,0⟩, ⟨false,19,19,2,2⟩, ⟨true,269,521,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 127 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_4_78 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,2,2⟩, ⟨false,13,13,4,0⟩, ⟨false,19,19,4,0⟩, ⟨true,269,353,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_79 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,7,7,2,2⟩, ⟨false,13,13,4,0⟩, ⟨false,19,19,4,0⟩, ⟨true,373,521,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 757 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_4_80 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,7,7,2,2⟩, ⟨false,13,13,4,0⟩, ⟨false,19,19,4,0⟩, ⟨true,373,397,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_81 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,7,7,2,2⟩, ⟨false,13,13,4,0⟩, ⟨false,19,19,4,0⟩, ⟨true,401,413,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 409 413 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,7,7,2,2⟩, ⟨false,13,13,4,0⟩, ⟨false,19,19,4,0⟩, ⟨true,401,409,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_82 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,7,7,2,2⟩, ⟨false,13,13,4,0⟩, ⟨false,19,19,4,0⟩, ⟨true,421,433,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_4_83 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,7,7,2,2⟩, ⟨false,13,13,4,0⟩, ⟨false,19,19,4,0⟩, ⟨true,421,425,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 421 425 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,7,7,2,2⟩, ⟨false,13,13,4,0⟩, ⟨false,19,19,4,0⟩, ⟨true,421,421,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 211 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_4_84 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,7,7,2,2⟩, ⟨false,13,13,4,0⟩, ⟨false,19,19,4,0⟩, ⟨true,429,433,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 433 429 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,7,7,2,2⟩, ⟨false,13,13,4,0⟩, ⟨false,19,19,4,0⟩, ⟨true,433,433,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 31 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_4_85 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,7,7,2,2⟩, ⟨false,13,13,4,0⟩, ⟨false,19,19,4,0⟩, ⟨true,421,433,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 425 rank5_4_83 rank5_4_84

theorem rank5_4_86 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,7,7,2,2⟩, ⟨false,13,13,4,0⟩, ⟨false,19,19,4,0⟩, ⟨true,417,433,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 421 417 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,7,7,2,2⟩, ⟨false,13,13,4,0⟩, ⟨false,19,19,4,0⟩, ⟨true,421,433,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_4_82 rank5_4_85

theorem rank5_4_87 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,7,7,2,2⟩, ⟨false,13,13,4,0⟩, ⟨false,19,19,4,0⟩, ⟨true,401,433,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 413 rank5_4_81 rank5_4_86

theorem rank5_4_88 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,7,7,2,2⟩, ⟨false,13,13,4,0⟩, ⟨false,19,19,4,0⟩, ⟨true,373,433,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 397 rank5_4_80 rank5_4_87

theorem rank5_4_89 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,7,7,2,2⟩, ⟨false,13,13,4,0⟩, ⟨false,19,19,4,0⟩, ⟨true,437,521,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 449 437 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,7,7,2,2⟩, ⟨false,13,13,4,0⟩, ⟨false,19,19,4,0⟩, ⟨true,449,521,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_90 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,7,7,2,2⟩, ⟨false,13,13,4,0⟩, ⟨false,19,19,4,0⟩, ⟨true,373,521,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 433 rank5_4_88 rank5_4_89

theorem rank5_4_91 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,2,2⟩, ⟨false,13,13,4,0⟩, ⟨false,19,19,4,0⟩, ⟨true,357,521,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 373 357 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,2,2⟩, ⟨false,13,13,4,0⟩, ⟨false,19,19,4,0⟩, ⟨true,373,521,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_4_79 rank5_4_90

theorem rank5_4_92 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,2,2⟩, ⟨false,13,13,4,0⟩, ⟨false,19,19,4,0⟩, ⟨true,269,521,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 353 rank5_4_78 rank5_4_91

theorem rank5_4_93 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,2,2⟩, ⟨false,13,13,4,0⟩, ⟨false,19,19,2,0⟩, ⟨true,269,537,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 521 537 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,2,2⟩, ⟨false,13,13,4,0⟩, ⟨false,19,19,2,0⟩, ⟨true,269,521,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .exponent 2 rank5_4_77 rank5_4_92

theorem rank5_4_94 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,2,2⟩, ⟨false,13,13,4,0⟩, ⟨false,19,19,2,0⟩, ⟨true,541,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_95 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,7,7,2,2⟩, ⟨false,13,13,4,0⟩, ⟨false,19,19,2,0⟩, ⟨true,269,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 537 rank5_4_93 rank5_4_94

end OddPerfect.SpoofBox
