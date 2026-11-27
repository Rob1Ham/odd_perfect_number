module

public import OddPerfect.PrimeRank5_2.Part002
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_48 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,157,2,0⟩, ⟨false,719,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 859 rank5_2_24 rank5_2_47

theorem rank5_2_49 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,157,2,0⟩, ⟨false,719,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 8 rank5_2_23 rank5_2_48

theorem rank5_2_50 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,143,157,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 149 143 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,149,157,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 717 rank5_2_22 rank5_2_49

theorem rank5_2_51 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,131,157,2,0⟩, ⟨false,541,1081,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1069 1081 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,131,157,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 141 rank5_2_21 rank5_2_50

theorem rank5_2_52 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,131,139,2,0⟩, ⟨false,1087,2173,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2161 2173 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,131,139,2,0⟩, ⟨false,1087,2161,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_53 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,131,139,2,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_54 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,131,139,2,0⟩, ⟨false,2179,4357,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_55 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,131,133,2,0⟩, ⟨false,4363,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 131 133 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,131,131,2,0⟩, ⟨false,4363,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_56 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨true,17,17,1,1⟩, ⟨false,137,139,2,0⟩, ⟨false,4363,8719,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_2_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_57 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,139,2,0⟩, ⟨false,4363,5815,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5813 5815 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,139,2,0⟩, ⟨false,4363,5813,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_58 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,2,0⟩, ⟨false,5821,8719,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_59 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,2,0⟩, ⟨false,5821,8719,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_60 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,2,0⟩, ⟨false,5821,6069,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 6067 6069 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,2,0⟩, ⟨false,5821,6067,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_61 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,2,0⟩, ⟨false,6073,6343,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_2_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_62 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,8⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,2,0⟩, ⟨false,6073,6343,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_63 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,2,0⟩, ⟨false,6073,6205,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 6203 6205 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,2,0⟩, ⟨false,6073,6203,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_64 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,2,2⟩, ⟨false,6211,6343,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_65 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,4,0⟩, ⟨false,6211,6239,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 6229 6239 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,4,0⟩, ⟨false,6211,6229,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_66 : PrimeCovered (#v[⟨false,3,3,14,14⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,4,0⟩, ⟨false,6247,6271,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_67 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,10⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,4,0⟩, ⟨false,6247,6257,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 12207031 rank5_2_prime12207031 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_68 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,4,0⟩, ⟨false,6247,6251,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 6247 6251 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,4,0⟩, ⟨false,6247,6247,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_69 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,4,0⟩, ⟨false,6253,6257,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 6257 6253 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,4,0⟩, ⟨false,6257,6257,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_70 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,4,0⟩, ⟨false,6247,6257,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 6251 rank5_2_68 rank5_2_69

theorem rank5_2_71 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,4,0⟩, ⟨false,6247,6257,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 10 rank5_2_67 rank5_2_70

end OddPerfect.SpoofBox
