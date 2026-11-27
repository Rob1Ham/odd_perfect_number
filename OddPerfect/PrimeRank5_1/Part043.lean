module

public import OddPerfect.PrimeRank5_1.Part042
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_1008 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,283,2,0⟩, ⟨false,2909,3487,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 3469 3487 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,283,2,0⟩, ⟨false,2909,3469,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_1_986 rank5_1_1007

theorem rank5_1_1009 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,283,2,0⟩, ⟨false,3489,4357,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 3491 3489 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,283,2,0⟩, ⟨false,3491,4357,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1010 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,283,2,0⟩, ⟨false,2909,4357,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 3487 rank5_1_1008 rank5_1_1009

theorem rank5_1_1011 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,283,2,0⟩, ⟨false,2907,4357,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2909 2907 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,283,2,0⟩, ⟨false,2909,4357,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 275 rank5_1_985 rank5_1_1010

theorem rank5_1_1012 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,283,2,0⟩, ⟨false,2179,4357,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2905 rank5_1_984 rank5_1_1011

theorem rank5_1_1013 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,283,2,0⟩, ⟨false,2179,4357,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 269 rank5_1_939 rank5_1_1012

theorem rank5_1_1014 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,261,2,0⟩, ⟨false,4363,8719,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 257 261 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,257,2,0⟩, ⟨false,4363,8719,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1015 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,269,2,0⟩, ⟨false,4363,5813,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1016 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,265,2,0⟩, ⟨false,4363,5813,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 263 265 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,263,263,2,0⟩, ⟨false,4363,5813,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1017 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,269,2,0⟩, ⟨false,4363,4983,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 4973 4983 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,269,2,0⟩, ⟨false,4363,4973,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1018 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,269,2,0⟩, ⟨false,4987,5161,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5153 5161 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,269,2,0⟩, ⟨false,4987,5153,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1019 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,4⟩, ⟨false,269,269,2,0⟩, ⟨false,5167,5351,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 88741 rank5_1_prime88741 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1020 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5167,5351,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_1_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1021 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5167,5257,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5237 5257 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5167,5237,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1022 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,9⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5261,5303,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1023 : PrimeCovered (#v[⟨false,3,3,14,14⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5261,5281,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1024 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,2⟩, ⟨false,5261,5281,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_1025 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,4,0⟩, ⟨false,5261,5269,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5261 5269 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,4,0⟩, ⟨false,5261,5261,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1026 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,4,0⟩, ⟨false,5273,5275,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5273 5275 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,4,0⟩, ⟨false,5273,5273,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1027 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,4,0⟩, ⟨false,5277,5281,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5279 5277 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,4,0⟩, ⟨false,5279,5281,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1028 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,4,0⟩, ⟨false,5271,5281,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5273 5271 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,4,0⟩, ⟨false,5273,5281,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 5275 rank5_1_1026 rank5_1_1027

theorem rank5_1_1029 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,4,0⟩, ⟨false,5261,5281,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 5269 rank5_1_1025 rank5_1_1028

theorem rank5_1_1030 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5261,5281,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .exponent 2 rank5_1_1024 rank5_1_1029

theorem rank5_1_1031 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5261,5281,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 14 rank5_1_1023 rank5_1_1030

end OddPerfect.SpoofBox
