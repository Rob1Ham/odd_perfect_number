module

public import OddPerfect.PrimeRank5_1.Part041
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_984 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,283,2,0⟩, ⟨false,2179,2905,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2903 2905 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,283,2,0⟩, ⟨false,2179,2903,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 275 rank5_1_940 rank5_1_983

theorem rank5_1_985 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,275,2,0⟩, ⟨false,2909,4357,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 271 275 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,271,271,2,0⟩, ⟨false,2909,4357,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_986 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,283,2,0⟩, ⟨false,2909,3469,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_987 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,277,2,0⟩, ⟨false,2909,3163,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_988 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3167,3311,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 3307 3311 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3167,3307,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_989 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,4⟩, ⟨false,277,277,2,0⟩, ⟨false,3313,3389,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 88741 rank5_1_prime88741 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_990 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3313,3389,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_1_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_991 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3313,3349,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 3347 3349 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3313,3347,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_992 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,9⟩, ⟨false,17,17,6,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3359,3373,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_993 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3359,3365,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 3361 3365 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3359,3361,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_994 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3367,3373,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 3371 3367 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3371,3373,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_995 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,13,0⟩, ⟨false,17,17,6,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3359,3373,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 3365 rank5_1_993 rank5_1_994

theorem rank5_1_996 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3359,3373,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 9 rank5_1_992 rank5_1_995

theorem rank5_1_997 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3375,3389,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 3389 3375 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3389,3389,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_998 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3351,3389,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 3359 3351 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3359,3389,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 3373 rank5_1_996 rank5_1_997

theorem rank5_1_999 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3313,3389,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 3349 rank5_1_991 rank5_1_998

theorem rank5_1_1000 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,6,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3313,3389,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_1_990 rank5_1_999

theorem rank5_1_1001 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3313,3389,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 4 rank5_1_989 rank5_1_1000

theorem rank5_1_1002 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3391,3469,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1003 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3313,3469,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 3389 rank5_1_1001 rank5_1_1002

theorem rank5_1_1004 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3165,3469,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 3167 3165 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3167,3469,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 3311 rank5_1_988 rank5_1_1003

theorem rank5_1_1005 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,279,2,0⟩, ⟨false,2909,3469,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 277 279 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,277,2,0⟩, ⟨false,2909,3469,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 3163 rank5_1_987 rank5_1_1004

theorem rank5_1_1006 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,281,283,2,0⟩, ⟨false,2909,3469,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_1007 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,283,2,0⟩, ⟨false,2909,3469,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 279 rank5_1_1005 rank5_1_1006

end OddPerfect.SpoofBox
