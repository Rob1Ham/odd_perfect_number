module

public import OddPerfect.PrimeRank5_1.Part032
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_768 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,139,2,0⟩, ⟨false,353,421,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_769 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,127,2,0⟩, ⟨false,353,383,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_770 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,131,131,2,0⟩, ⟨false,353,359,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_771 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,131,131,2,0⟩, ⟨false,353,355,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 353 355 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,131,131,2,0⟩, ⟨false,353,353,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_772 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,131,131,2,0⟩, ⟨false,357,359,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 359 357 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,131,131,2,0⟩, ⟨false,359,359,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_773 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,131,131,2,0⟩, ⟨false,353,359,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 355 rank5_1_771 rank5_1_772

theorem rank5_1_774 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,131,131,2,0⟩, ⟨false,353,359,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_1_770 rank5_1_773

theorem rank5_1_775 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,131,131,2,0⟩, ⟨false,361,367,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 367 361 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,131,131,2,0⟩, ⟨false,367,367,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_776 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,131,131,2,0⟩, ⟨false,353,367,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 359 rank5_1_774 rank5_1_775

theorem rank5_1_777 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,131,131,2,0⟩, ⟨false,369,383,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 373 369 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,131,131,2,0⟩, ⟨false,373,383,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_778 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,129,131,2,0⟩, ⟨false,353,383,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 131 129 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,131,131,2,0⟩, ⟨false,353,383,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 367 rank5_1_776 rank5_1_777

theorem rank5_1_779 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,131,2,0⟩, ⟨false,353,383,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 127 rank5_1_769 rank5_1_778

theorem rank5_1_780 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,127,2,0⟩, ⟨false,389,401,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_781 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,127,2,0⟩, ⟨false,389,393,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 389 393 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,127,2,0⟩, ⟨false,389,389,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_782 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,127,2,0⟩, ⟨false,395,401,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 397 395 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,127,2,0⟩, ⟨false,397,401,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_783 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,127,2,0⟩, ⟨false,389,401,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 393 rank5_1_781 rank5_1_782

theorem rank5_1_784 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,127,2,0⟩, ⟨false,389,403,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 401 403 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,127,2,0⟩, ⟨false,389,401,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_1_780 rank5_1_783

theorem rank5_1_785 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,127,2,0⟩, ⟨false,405,421,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 409 405 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,127,2,0⟩, ⟨false,409,421,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_786 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,127,2,0⟩, ⟨false,389,421,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 403 rank5_1_784 rank5_1_785

theorem rank5_1_787 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,129,131,2,0⟩, ⟨false,389,421,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 131 129 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,131,131,2,0⟩, ⟨false,389,421,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_788 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,131,2,0⟩, ⟨false,385,421,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 389 385 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,131,2,0⟩, ⟨false,389,421,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 127 rank5_1_786 rank5_1_787

theorem rank5_1_789 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,131,2,0⟩, ⟨false,353,421,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 383 rank5_1_779 rank5_1_788

theorem rank5_1_790 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,133,139,2,0⟩, ⟨false,353,421,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 137 133 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,137,139,2,0⟩, ⟨false,353,421,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_791 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,139,2,0⟩, ⟨false,353,421,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 131 rank5_1_789 rank5_1_790

end OddPerfect.SpoofBox
