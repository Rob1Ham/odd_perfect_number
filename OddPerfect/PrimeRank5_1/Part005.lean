module

public import OddPerfect.PrimeRank5_1.Part004
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_96 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,1,1⟩, ⟨false,17,19,2,0⟩, ⟨false,23,23,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 0 4 1093 rank5_1_prime1093 (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,1,1⟩, ⟨false,17,19,2,0⟩, ⟨false,23,23,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .base 17 rank5_1_94 rank5_1_95

theorem rank5_1_97 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,2,0⟩, ⟨false,23,23,2,0⟩, ⟨false,263,525,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 523 525 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,2,0⟩, ⟨false,23,23,2,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_98 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,2,2⟩, ⟨false,23,23,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 307 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_99 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,2,0⟩, ⟨false,541,1081,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1069 1081 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,2,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_100 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,2,2⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_101 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,1087,2173,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2161 2173 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,1087,2161,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_102 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_103 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,2179,2905,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2903 2905 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,2179,2903,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_104 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,2909,3469,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 3851 rank5_1_prime3851 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_105 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,2909,3469,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_106 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,2909,3487,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 3469 3487 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,2909,3469,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_1_104 rank5_1_105

theorem rank5_1_107 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,3491,4357,2,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 0 4 3851 rank5_1_prime3851 (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,3851,3851,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_108 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,4⟩, ⟨false,23,23,4,0⟩, ⟨false,3491,3571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 88741 rank5_1_prime88741 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_109 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,6,0⟩, ⟨false,23,23,4,0⟩, ⟨false,3491,3571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_1_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_110 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,6,0⟩, ⟨false,23,23,4,0⟩, ⟨false,3491,3509,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 3499 3509 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,6,0⟩, ⟨false,23,23,4,0⟩, ⟨false,3491,3499,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_111 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,6,0⟩, ⟨false,23,23,4,4⟩, ⟨false,3511,3529,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 292561 rank5_1_prime292561 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_112 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,6,0⟩, ⟨false,23,23,6,0⟩, ⟨false,3511,3519,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 3517 3519 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,6,0⟩, ⟨false,23,23,6,0⟩, ⟨false,3511,3517,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_113 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,6,0⟩, ⟨false,23,23,6,0⟩, ⟨false,3521,3529,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 3527 3521 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,6,0⟩, ⟨false,23,23,6,0⟩, ⟨false,3527,3529,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_114 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,6,0⟩, ⟨false,23,23,6,0⟩, ⟨false,3511,3529,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 3519 rank5_1_112 rank5_1_113

theorem rank5_1_115 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,6,0⟩, ⟨false,23,23,4,0⟩, ⟨false,3511,3529,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .exponent 4 rank5_1_111 rank5_1_114

theorem rank5_1_116 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,6,0⟩, ⟨false,23,23,4,0⟩, ⟨false,3491,3529,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 3509 rank5_1_110 rank5_1_115

theorem rank5_1_117 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,6,0⟩, ⟨false,23,23,4,0⟩, ⟨false,3531,3571,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 3533 3531 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,6,0⟩, ⟨false,23,23,4,0⟩, ⟨false,3533,3571,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_118 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,6,0⟩, ⟨false,23,23,4,0⟩, ⟨false,3491,3571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 3529 rank5_1_116 rank5_1_117

theorem rank5_1_119 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,6,0⟩, ⟨false,23,23,4,0⟩, ⟨false,3491,3571,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_1_109 rank5_1_118

end OddPerfect.SpoofBox
