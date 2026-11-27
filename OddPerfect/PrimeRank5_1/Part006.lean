module

public import OddPerfect.PrimeRank5_1.Part005
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_120 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,3491,3573,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 3571 3573 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,3491,3571,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_1_108 rank5_1_119

theorem rank5_1_121 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,3575,3659,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 3581 3575 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,3581,3659,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_122 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,3491,3667,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 3659 3667 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,3491,3659,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 3573 rank5_1_120 rank5_1_121

theorem rank5_1_123 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,3669,3863,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 3671 3669 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,3671,3863,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_124 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,3491,3875,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 3863 3875 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,3491,3863,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 3667 rank5_1_122 rank5_1_123

theorem rank5_1_125 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,3877,4357,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_126 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,3491,4357,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 3875 rank5_1_124 rank5_1_125

theorem rank5_1_127 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,3489,4357,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 3491 3489 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,3491,4357,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_1_107 rank5_1_126

theorem rank5_1_128 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,2907,4357,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2909 2907 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,2909,4357,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 3487 rank5_1_106 rank5_1_127

theorem rank5_1_129 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,2179,4357,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2905 rank5_1_103 rank5_1_128

theorem rank5_1_130 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,4359,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 4363 4359 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,4363,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_131 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 4357 rank5_1_129 rank5_1_130

theorem rank5_1_132 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,2175,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2179 2175 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_1_102 rank5_1_131

theorem rank5_1_133 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,4,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2173 rank5_1_101 rank5_1_132

theorem rank5_1_134 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,2,0⟩, ⟨false,1083,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1087 1083 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,2,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .exponent 2 rank5_1_100 rank5_1_133

theorem rank5_1_135 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,4,0⟩, ⟨false,23,23,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1081 rank5_1_99 rank5_1_134

theorem rank5_1_136 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,2,0⟩, ⟨false,23,23,2,0⟩, ⟨false,527,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 541 527 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,2,0⟩, ⟨false,23,23,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 2 rank5_1_98 rank5_1_135

theorem rank5_1_137 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,17,2,0⟩, ⟨false,23,23,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 525 rank5_1_97 rank5_1_136

theorem rank5_1_138 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,19,19,2,0⟩, ⟨false,23,23,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_139 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,19,2,0⟩, ⟨false,23,23,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .base 17 rank5_1_137 rank5_1_138

theorem rank5_1_140 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,19,2,0⟩, ⟨false,21,23,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 23 21 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,19,2,0⟩, ⟨false,23,23,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 6 rank5_1_96 rank5_1_139

theorem rank5_1_141 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,1,1⟩, ⟨false,15,19,2,0⟩, ⟨false,15,23,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 2 17 15 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,19,2,0⟩, ⟨false,15,23,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 3 19 18 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,1,1⟩, ⟨false,17,19,2,0⟩, ⟨false,19,23,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 19 rank5_1_91 rank5_1_140

theorem rank5_1_142 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,19,2,0⟩, ⟨false,13,23,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .base 13 rank5_1_90 rank5_1_141

theorem rank5_1_143 : PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,19,2,0⟩, ⟨false,13,25,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 23 25 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,4,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,19,2,0⟩, ⟨false,13,23,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 4 rank5_1_89 rank5_1_142

end OddPerfect.SpoofBox
