module

public import OddPerfect.PrimeRank5_2.Part032
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_768 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,439,2,0⟩, ⟨false,457,673,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_769 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,377,2,0⟩, ⟨false,457,673,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 373 377 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,373,2,0⟩, ⟨false,457,673,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_770 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,439,2,0⟩, ⟨false,457,543,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 541 543 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,439,2,0⟩, ⟨false,457,541,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_771 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,405,2,0⟩, ⟨false,547,673,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 401 405 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,401,2,0⟩, ⟨false,547,673,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_772 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,439,2,0⟩, ⟨false,547,603,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 601 603 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,439,2,0⟩, ⟨false,547,601,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_773 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨true,17,17,5,0⟩, ⟨false,409,439,2,0⟩, ⟨false,607,673,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_2_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_774 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,421,2,0⟩, ⟨false,607,637,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 631 637 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,421,2,0⟩, ⟨false,607,631,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_775 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,421,2,0⟩, ⟨false,641,673,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_776 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,413,2,0⟩, ⟨false,641,653,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 409 413 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,409,2,0⟩, ⟨false,641,653,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_777 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,419,421,2,0⟩, ⟨false,641,645,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 643 645 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,419,421,2,0⟩, ⟨false,641,643,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_778 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,419,421,2,0⟩, ⟨false,647,649,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 647 649 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,419,421,2,0⟩, ⟨false,647,647,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_779 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,419,419,2,0⟩, ⟨false,653,653,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_780 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,421,421,2,0⟩, ⟨false,653,653,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_781 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,419,421,2,0⟩, ⟨false,651,653,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 653 651 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,419,421,2,0⟩, ⟨false,653,653,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 419 rank5_2_779 rank5_2_780

theorem rank5_2_782 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,419,421,2,0⟩, ⟨false,647,653,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 649 rank5_2_778 rank5_2_781

theorem rank5_2_783 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,415,421,2,0⟩, ⟨false,641,653,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 419 415 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,419,421,2,0⟩, ⟨false,641,653,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 645 rank5_2_777 rank5_2_782

theorem rank5_2_784 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,421,2,0⟩, ⟨false,641,655,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 653 655 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,421,2,0⟩, ⟨false,641,653,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 413 rank5_2_776 rank5_2_783

theorem rank5_2_785 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,413,2,0⟩, ⟨false,659,673,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 409 413 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,409,2,0⟩, ⟨false,659,673,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_786 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,415,421,2,0⟩, ⟨false,659,673,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 419 415 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,419,421,2,0⟩, ⟨false,659,673,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_787 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,421,2,0⟩, ⟨false,657,673,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 659 657 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,421,2,0⟩, ⟨false,659,673,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 413 rank5_2_785 rank5_2_786

theorem rank5_2_788 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,421,2,0⟩, ⟨false,641,673,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 655 rank5_2_784 rank5_2_787

theorem rank5_2_789 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,421,2,0⟩, ⟨false,639,673,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 641 639 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,421,2,0⟩, ⟨false,641,673,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_2_775 rank5_2_788

theorem rank5_2_790 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,423,2,0⟩, ⟨false,607,673,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 421 423 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,421,2,0⟩, ⟨false,607,673,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 637 rank5_2_774 rank5_2_789

theorem rank5_2_791 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,431,439,2,0⟩, ⟨false,607,631,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end OddPerfect.SpoofBox
