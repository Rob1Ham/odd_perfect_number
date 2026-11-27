module

public import OddPerfect.PrimeRank5_2.Part033
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_792 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,431,433,2,0⟩, ⟨false,607,617,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_793 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,439,439,2,0⟩, ⟨false,607,611,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 607 611 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,439,439,2,0⟩, ⟨false,607,607,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_794 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,439,439,2,0⟩, ⟨false,613,617,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_795 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,435,439,2,0⟩, ⟨false,607,617,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 439 435 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,439,439,2,0⟩, ⟨false,607,617,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 611 rank5_2_793 rank5_2_794

theorem rank5_2_796 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,431,439,2,0⟩, ⟨false,607,617,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 433 rank5_2_792 rank5_2_795

theorem rank5_2_797 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,431,433,2,0⟩, ⟨false,619,623,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 619 623 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,431,433,2,0⟩, ⟨false,619,619,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_798 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,431,433,2,0⟩, ⟨false,625,631,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 631 625 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,431,433,2,0⟩, ⟨false,631,631,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_799 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,431,433,2,0⟩, ⟨false,619,631,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 623 rank5_2_797 rank5_2_798

theorem rank5_2_800 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,435,439,2,0⟩, ⟨false,619,631,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 439 435 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,439,439,2,0⟩, ⟨false,619,631,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_801 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,431,439,2,0⟩, ⟨false,619,631,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 433 rank5_2_799 rank5_2_800

theorem rank5_2_802 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,431,439,2,0⟩, ⟨false,607,631,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 617 rank5_2_796 rank5_2_801

theorem rank5_2_803 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,431,439,2,0⟩, ⟨false,607,637,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 631 637 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,431,439,2,0⟩, ⟨false,607,631,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_2_791 rank5_2_802

theorem rank5_2_804 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,431,439,2,0⟩, ⟨false,639,673,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 641 639 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,431,439,2,0⟩, ⟨false,641,673,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_805 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,425,439,2,0⟩, ⟨false,607,673,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 431 425 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,431,439,2,0⟩, ⟨false,607,673,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 637 rank5_2_803 rank5_2_804

theorem rank5_2_806 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,439,2,0⟩, ⟨false,607,673,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 423 rank5_2_790 rank5_2_805

theorem rank5_2_807 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,439,2,0⟩, ⟨false,605,673,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 607 605 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,439,2,0⟩, ⟨false,607,673,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_2_773 rank5_2_806

theorem rank5_2_808 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,407,439,2,0⟩, ⟨false,547,673,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 409 407 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,409,439,2,0⟩, ⟨false,547,673,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 603 rank5_2_772 rank5_2_807

theorem rank5_2_809 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,439,2,0⟩, ⟨false,545,673,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 547 545 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,439,2,0⟩, ⟨false,547,673,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 405 rank5_2_771 rank5_2_808

theorem rank5_2_810 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,379,439,2,0⟩, ⟨false,457,673,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 543 rank5_2_770 rank5_2_809

theorem rank5_2_811 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,439,2,0⟩, ⟨false,457,673,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 377 rank5_2_769 rank5_2_810

theorem rank5_2_812 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,439,2,0⟩, ⟨false,451,673,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 457 451 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,439,2,0⟩, ⟨false,457,673,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_2_768 rank5_2_811

theorem rank5_2_813 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,441,2,0⟩, ⟨false,337,673,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 439 441 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,439,2,0⟩, ⟨false,337,673,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 449 rank5_2_767 rank5_2_812

theorem rank5_2_814 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,661,2,0⟩, ⟨false,449,673,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_815 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,477,2,0⟩, ⟨false,449,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 467 477 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,467,2,0⟩, ⟨false,449,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
