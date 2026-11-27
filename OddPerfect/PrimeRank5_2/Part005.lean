module

public import OddPerfect.PrimeRank5_2.Part004
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_96 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,139,2,0⟩, ⟨false,8731,17461,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 17449 17461 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,139,2,0⟩, ⟨false,8731,17449,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 137 rank5_2_94 rank5_2_95

theorem rank5_2_97 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,2,0⟩, ⟨false,17467,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_98 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,2,0⟩, ⟨false,17467,19949,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_2_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_99 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,8⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,2,0⟩, ⟨false,17467,19949,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_100 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,2,2⟩, ⟨false,17467,18617,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_101 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,4,0⟩, ⟨false,17467,18023,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 18013 18023 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,4,0⟩, ⟨false,17467,18013,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_102 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,4,0⟩, ⟨false,18041,18323,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 18313 18323 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,4,0⟩, ⟨false,18041,18313,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_103 : PrimeCovered (#v[⟨false,3,3,14,14⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,4,0⟩, ⟨false,18329,18617,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_104 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,4,0⟩, ⟨false,18329,18471,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 18461 18471 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,4,0⟩, ⟨false,18329,18461,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_105 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,10⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,4,0⟩, ⟨false,18481,18541,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 12207031 rank5_2_prime12207031 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_106 : PrimeCovered (#v[⟨false,3,3,16,16⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,4,0⟩, ⟨false,18481,18503,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 1871 rank5_2_prime1871 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_107 : PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,4,0⟩, ⟨false,18481,18491,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 18481 18491 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,4,0⟩, ⟨false,18481,18481,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_108 : PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,4,0⟩, ⟨false,18493,18497,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 18493 18497 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,4,0⟩, ⟨false,18493,18493,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_109 : PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,4,0⟩, ⟨false,18499,18503,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 18503 18499 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,4,0⟩, ⟨false,18503,18503,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_110 : PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,4,0⟩, ⟨false,18493,18503,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 18497 rank5_2_108 rank5_2_109

theorem rank5_2_111 : PrimeCovered (#v[⟨false,3,3,18,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,4,0⟩, ⟨false,18481,18503,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 18491 rank5_2_107 rank5_2_110

theorem rank5_2_112 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,4,0⟩, ⟨false,18481,18509,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 18503 18509 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,4,0⟩, ⟨false,18481,18503,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 16 rank5_2_106 rank5_2_111

theorem rank5_2_113 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,4,0⟩, ⟨false,18511,18541,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 18517 18511 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,4,0⟩, ⟨false,18517,18541,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_114 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,12,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,4,0⟩, ⟨false,18481,18541,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 18509 rank5_2_112 rank5_2_113

theorem rank5_2_115 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,4,0⟩, ⟨false,18481,18547,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 18541 18547 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,4,0⟩, ⟨false,18481,18541,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 10 rank5_2_105 rank5_2_114

theorem rank5_2_116 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,4,0⟩, ⟨false,18549,18617,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 18553 18549 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,4,0⟩, ⟨false,18553,18617,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_117 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,4,0⟩, ⟨false,18473,18617,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 18481 18473 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,4,0⟩, ⟨false,18481,18617,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 18547 rank5_2_115 rank5_2_116

theorem rank5_2_118 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,4,0⟩, ⟨false,18329,18617,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 18471 rank5_2_104 rank5_2_117

theorem rank5_2_119 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,4,0⟩, ⟨false,18325,18617,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 18329 18325 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,1,1⟩, ⟨false,137,137,4,0⟩, ⟨false,18329,18617,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 14 rank5_2_103 rank5_2_118

end OddPerfect.SpoofBox
