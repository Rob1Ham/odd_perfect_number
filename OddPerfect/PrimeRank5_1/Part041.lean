module

public import OddPerfect.PrimeRank5_1.Part040
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_960 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2647,2687,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_1_948 rank5_1_959

theorem rank5_1_961 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2641,2687,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2647 2641 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2647,2687,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_1_947 rank5_1_960

theorem rank5_1_962 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2593,2687,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2639 rank5_1_946 rank5_1_961

theorem rank5_1_963 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,283,2,0⟩, ⟨false,2593,2687,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 281 rank5_1_945 rank5_1_962

theorem rank5_1_964 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,283,2,0⟩, ⟨false,2503,2687,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2591 rank5_1_944 rank5_1_963

theorem rank5_1_965 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,281,2,0⟩, ⟨false,2689,2791,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_966 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2689,2791,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_967 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,283,2,0⟩, ⟨false,2689,2791,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 281 rank5_1_965 rank5_1_966

theorem rank5_1_968 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,281,2,0⟩, ⟨false,2797,2849,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2843 2849 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,281,2,0⟩, ⟨false,2797,2843,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_969 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,4⟩, ⟨false,281,281,2,0⟩, ⟨false,2851,2903,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 88741 rank5_1_prime88741 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_970 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,281,281,2,0⟩, ⟨false,2851,2903,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_1_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_971 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,281,281,2,0⟩, ⟨false,2851,2875,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2861 2875 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,281,281,2,0⟩, ⟨false,2851,2861,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_972 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,281,281,2,0⟩, ⟨false,2877,2903,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2879 2877 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,281,281,2,0⟩, ⟨false,2879,2903,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_973 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,281,281,2,0⟩, ⟨false,2851,2903,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2875 rank5_1_971 rank5_1_972

theorem rank5_1_974 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,281,281,2,0⟩, ⟨false,2851,2903,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_1_970 rank5_1_973

theorem rank5_1_975 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,281,2,0⟩, ⟨false,2851,2903,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 4 rank5_1_969 rank5_1_974

theorem rank5_1_976 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,281,2,0⟩, ⟨false,2797,2903,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2849 rank5_1_968 rank5_1_975

theorem rank5_1_977 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2797,2903,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_978 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,283,2,0⟩, ⟨false,2793,2903,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2797 2793 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,283,2,0⟩, ⟨false,2797,2903,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 281 rank5_1_976 rank5_1_977

theorem rank5_1_979 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,283,2,0⟩, ⟨false,2689,2903,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2791 rank5_1_967 rank5_1_978

theorem rank5_1_980 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,283,2,0⟩, ⟨false,2503,2903,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2687 rank5_1_964 rank5_1_979

theorem rank5_1_981 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,283,2,0⟩, ⟨false,2503,2903,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 279 rank5_1_943 rank5_1_980

theorem rank5_1_982 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,283,2,0⟩, ⟨false,2491,2903,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2503 2491 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,283,2,0⟩, ⟨false,2503,2903,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_1_942 rank5_1_981

theorem rank5_1_983 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,283,2,0⟩, ⟨false,2179,2903,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2489 rank5_1_941 rank5_1_982

end OddPerfect.SpoofBox
