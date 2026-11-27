module

public import OddPerfect.PrimeRank5_3.Part005
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_3_120 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,541,613,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_121 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,617,659,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_122 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,23,23,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,661,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_123 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,23,23,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,661,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_124 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,661,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 6 rank5_3_122 rank5_3_123

theorem rank5_3_125 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,615,709,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 617 615 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,617,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 659 rank5_3_121 rank5_3_124

theorem rank5_3_126 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,541,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 613 rank5_3_120 rank5_3_125

theorem rank5_3_127 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,541,717,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 709 717 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,541,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_3_119 rank5_3_126

theorem rank5_3_128 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,719,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_129 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,4,0⟩, ⟨true,53,53,1,1⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 717 rank5_3_127 rank5_3_128

theorem rank5_3_130 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨true,53,53,1,1⟩, ⟨false,541,1081,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 1069 1081 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨true,53,53,1,1⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 2 rank5_3_118 rank5_3_129

theorem rank5_3_131 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨true,53,53,1,1⟩, ⟨false,1083,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1087 1083 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨true,53,53,1,1⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_132 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨true,53,53,1,1⟩, ⟨false,527,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 541 527 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨true,53,53,1,1⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1081 rank5_3_130 rank5_3_131

theorem rank5_3_133 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨true,53,53,1,1⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 525 rank5_3_117 rank5_3_132

theorem rank5_3_134 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,23,2,0⟩, ⟨true,53,53,1,1⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 4 rank5_3_116 rank5_3_133

theorem rank5_3_135 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,4⟩, ⟨false,23,23,2,0⟩, ⟨true,53,53,5,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_136 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨true,53,53,5,0⟩, ⟨false,263,525,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 523 525 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨true,53,53,5,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_137 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,2⟩, ⟨true,53,53,5,0⟩, ⟨false,541,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_138 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,4,0⟩, ⟨true,53,53,5,0⟩, ⟨false,541,717,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 709 717 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,4,0⟩, ⟨true,53,53,5,0⟩, ⟨false,541,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_139 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,4,0⟩, ⟨true,53,53,5,0⟩, ⟨false,719,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_140 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,4,0⟩, ⟨true,53,53,5,0⟩, ⟨false,719,859,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_141 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,23,23,4,0⟩, ⟨true,53,53,5,0⟩, ⟨false,863,953,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_3_142 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,23,23,4,0⟩, ⟨true,53,53,5,0⟩, ⟨false,863,953,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_143 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,4,0⟩, ⟨true,53,53,5,0⟩, ⟨false,863,955,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 953 955 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,4,0⟩, ⟨true,53,53,5,0⟩, ⟨false,863,953,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_3_141 rank5_3_142

end OddPerfect.SpoofBox
