module

public import OddPerfect.PrimeRank5_2.Part026
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_624 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,281,281,2,0⟩, ⟨false,2851,2903,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_2_618 rank5_2_623

theorem rank5_2_625 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,281,281,2,0⟩, ⟨false,2797,2903,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2849 rank5_2_617 rank5_2_624

theorem rank5_2_626 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2797,2903,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_627 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,281,283,2,0⟩, ⟨false,2793,2903,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2797 2793 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,281,283,2,0⟩, ⟨false,2797,2903,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 281 rank5_2_625 rank5_2_626

theorem rank5_2_628 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,281,283,2,0⟩, ⟨false,2689,2903,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2791 rank5_2_616 rank5_2_627

theorem rank5_2_629 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,281,283,2,0⟩, ⟨false,2503,2903,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2687 rank5_2_613 rank5_2_628

theorem rank5_2_630 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,283,2,0⟩, ⟨false,2503,2903,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 279 rank5_2_594 rank5_2_629

theorem rank5_2_631 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,283,2,0⟩, ⟨false,2491,2903,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2503 2491 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,283,2,0⟩, ⟨false,2503,2903,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_2_593 rank5_2_630

theorem rank5_2_632 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,283,2,0⟩, ⟨false,2179,2903,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2489 rank5_2_592 rank5_2_631

theorem rank5_2_633 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,283,2,0⟩, ⟨false,2179,2905,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2903 2905 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,283,2,0⟩, ⟨false,2179,2903,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_2_591 rank5_2_632

theorem rank5_2_634 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨true,17,17,5,0⟩, ⟨false,277,283,2,0⟩, ⟨false,2909,4357,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_2_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_635 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,283,2,0⟩, ⟨false,2909,3469,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_636 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,277,2,0⟩, ⟨false,2909,3163,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_637 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3167,3311,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 3307 3311 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3167,3307,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_638 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3313,3389,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_2_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_639 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,8⟩, ⟨true,17,17,5,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3313,3389,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_640 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3313,3349,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 3347 3349 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3313,3347,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_641 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3359,3365,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 3361 3365 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3359,3361,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_642 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3367,3373,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 3371 3367 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3371,3373,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_643 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3359,3373,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 3365 rank5_2_641 rank5_2_642

theorem rank5_2_644 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3375,3389,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 3389 3375 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3389,3389,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_645 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3351,3389,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 3359 3351 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3359,3389,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 3373 rank5_2_643 rank5_2_644

theorem rank5_2_646 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3313,3389,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 3349 rank5_2_640 rank5_2_645

theorem rank5_2_647 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,277,2,0⟩, ⟨false,3313,3389,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 8 rank5_2_639 rank5_2_646

end OddPerfect.SpoofBox
