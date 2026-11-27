module

public import OddPerfect.PrimeRank5_2.Part003
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_72 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,4,0⟩, ⟨false,6259,6271,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 6263 6259 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,4,0⟩, ⟨false,6263,6271,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_73 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,4,0⟩, ⟨false,6247,6271,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 6257 rank5_2_71 rank5_2_72

theorem rank5_2_74 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,4,0⟩, ⟨false,6241,6271,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 6247 6241 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,4,0⟩, ⟨false,6247,6271,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 14 rank5_2_66 rank5_2_73

theorem rank5_2_75 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,4,0⟩, ⟨false,6211,6275,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 6271 6275 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,4,0⟩, ⟨false,6211,6271,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 6239 rank5_2_65 rank5_2_74

theorem rank5_2_76 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,4,0⟩, ⟨false,6277,6343,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_77 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,4,0⟩, ⟨false,6211,6343,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 6275 rank5_2_75 rank5_2_76

theorem rank5_2_78 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,2,0⟩, ⟨false,6207,6343,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 6211 6207 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,2,0⟩, ⟨false,6211,6343,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .exponent 2 rank5_2_64 rank5_2_77

theorem rank5_2_79 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,2,0⟩, ⟨false,6073,6343,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 6205 rank5_2_63 rank5_2_78

theorem rank5_2_80 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,2,0⟩, ⟨false,6073,6343,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 8 rank5_2_62 rank5_2_79

theorem rank5_2_81 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,2,0⟩, ⟨false,6071,6343,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 6073 6071 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,2,0⟩, ⟨false,6073,6343,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 12 rank5_2_61 rank5_2_80

theorem rank5_2_82 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,2,0⟩, ⟨false,5821,6345,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 6343 6345 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,2,0⟩, ⟨false,5821,6343,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 6069 rank5_2_60 rank5_2_81

theorem rank5_2_83 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,2,0⟩, ⟨false,6347,6977,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 6353 6347 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,2,0⟩, ⟨false,6353,6977,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_84 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,2,0⟩, ⟨false,5821,6981,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 6977 6981 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,2,0⟩, ⟨false,5821,6977,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 6345 rank5_2_82 rank5_2_83

theorem rank5_2_85 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,2,0⟩, ⟨false,6983,8719,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_86 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,2,0⟩, ⟨false,5821,8719,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 6981 rank5_2_84 rank5_2_85

theorem rank5_2_87 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,2,0⟩, ⟨false,5821,8719,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_2_59 rank5_2_86

theorem rank5_2_88 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,139,2,0⟩, ⟨false,5817,8719,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5821 5817 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,139,2,0⟩, ⟨false,5821,8719,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 137 rank5_2_58 rank5_2_87

theorem rank5_2_89 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,139,2,0⟩, ⟨false,4363,8719,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 5815 rank5_2_57 rank5_2_88

theorem rank5_2_90 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,139,2,0⟩, ⟨false,4363,8725,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 8719 8725 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,139,2,0⟩, ⟨false,4363,8719,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_2_56 rank5_2_89

theorem rank5_2_91 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨true,17,17,1,1⟩, ⟨false,137,139,2,0⟩, ⟨false,8731,0,2,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 1 4 19531 rank5_2_prime19531 (Nat.odd_iff.mpr (by decide)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨true,17,17,1,1⟩, ⟨false,137,139,2,0⟩, ⟨false,19531,19531,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_92 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,2,0⟩, ⟨false,8731,17449,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_2_93 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,2,0⟩, ⟨false,8731,17449,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_94 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,2,0⟩, ⟨false,8731,17449,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_2_92 rank5_2_93

theorem rank5_2_95 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,139,139,2,0⟩, ⟨false,8731,17449,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
