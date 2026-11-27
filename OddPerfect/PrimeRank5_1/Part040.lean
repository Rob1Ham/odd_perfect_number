module

public import OddPerfect.PrimeRank5_1.Part039
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_936 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,5⟩, ⟨false,17,17,4,0⟩, ⟨false,257,337,2,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_937 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,283,2,0⟩, ⟨false,1087,2173,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2161 2173 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,283,2,0⟩, ⟨false,1087,2161,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_938 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,283,2,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_939 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,269,2,0⟩, ⟨false,2179,4357,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_940 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,275,2,0⟩, ⟨false,2179,2903,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 271 275 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,271,2,0⟩, ⟨false,2179,2903,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_941 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,283,2,0⟩, ⟨false,2179,2489,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2477 2489 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,283,2,0⟩, ⟨false,2179,2477,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_942 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,283,2,0⟩, ⟨false,2503,2903,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_943 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,279,2,0⟩, ⟨false,2503,2903,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 277 279 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,277,2,0⟩, ⟨false,2503,2903,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_944 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,283,2,0⟩, ⟨false,2503,2591,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_945 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,281,2,0⟩, ⟨false,2593,2687,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_946 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2593,2639,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2633 2639 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2593,2633,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_947 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,4⟩, ⟨false,283,283,2,0⟩, ⟨false,2647,2687,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 88741 rank5_1_prime88741 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_948 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2647,2687,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_1_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_949 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2647,2665,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2663 2665 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2647,2663,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_950 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,9⟩, ⟨false,17,17,6,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2671,2677,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_951 : PrimeCovered (#v[⟨false,3,3,14,14⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2671,2677,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_952 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2671,2673,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2671 2673 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2671,2671,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_953 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2675,2677,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2677 2675 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2677,2677,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_954 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2671,2677,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2673 rank5_1_952 rank5_1_953

theorem rank5_1_955 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2671,2677,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 14 rank5_1_951 rank5_1_954

theorem rank5_1_956 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2671,2677,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 9 rank5_1_950 rank5_1_955

theorem rank5_1_957 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2679,2687,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2683 2679 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2683,2687,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_958 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2667,2687,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2671 2667 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2671,2687,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 2677 rank5_1_956 rank5_1_957

theorem rank5_1_959 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2647,2687,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2665 rank5_1_949 rank5_1_958

end OddPerfect.SpoofBox
