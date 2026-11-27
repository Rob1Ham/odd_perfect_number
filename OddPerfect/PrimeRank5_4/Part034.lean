module

public import OddPerfect.PrimeRank5_4.Part033
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_792 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,431,433,2,0⟩, ⟨true,613,625,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 617 625 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,431,433,2,0⟩, ⟨true,613,617,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_793 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,431,433,2,0⟩, ⟨true,629,641,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 641 629 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,431,433,2,0⟩, ⟨true,641,641,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 107 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_794 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,427,433,2,0⟩, ⟨true,613,641,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 431 427 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,431,433,2,0⟩, ⟨true,613,641,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 625 rank5_4_792 rank5_4_793

theorem rank5_4_795 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,433,2,0⟩, ⟨true,613,641,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 425 rank5_4_791 rank5_4_794

theorem rank5_4_796 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,433,2,0⟩, ⟨true,613,641,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_4_790 rank5_4_795

theorem rank5_4_797 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,433,2,0⟩, ⟨true,653,677,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_798 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,421,2,0⟩, ⟨true,653,653,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 4 109 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_799 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,421,2,0⟩, ⟨true,657,661,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 661 657 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,421,2,0⟩, ⟨true,661,661,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 331 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_800 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,421,2,0⟩, ⟨true,653,661,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 653 rank5_4_798 rank5_4_799

theorem rank5_4_801 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,421,2,0⟩, ⟨true,665,677,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 673 665 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,421,2,0⟩, ⟨true,673,677,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_802 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,425,2,0⟩, ⟨true,653,677,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 421 425 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,421,2,0⟩, ⟨true,653,677,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 661 rank5_4_800 rank5_4_801

theorem rank5_4_803 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,427,433,2,0⟩, ⟨true,653,677,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 431 427 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,431,433,2,0⟩, ⟨true,653,677,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_804 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,433,2,0⟩, ⟨true,653,677,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 425 rank5_4_802 rank5_4_803

theorem rank5_4_805 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,433,2,0⟩, ⟨true,645,677,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 653 645 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,433,2,0⟩, ⟨true,653,677,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_4_797 rank5_4_804

theorem rank5_4_806 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,433,2,0⟩, ⟨true,613,677,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 641 rank5_4_796 rank5_4_805

theorem rank5_4_807 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,435,449,2,0⟩, ⟨true,613,677,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 439 435 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,439,449,2,0⟩, ⟨true,613,677,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_808 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,449,2,0⟩, ⟨true,613,677,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 433 rank5_4_806 rank5_4_807

theorem rank5_4_809 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,449,2,0⟩, ⟨true,613,677,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 6 rank5_4_789 rank5_4_808

theorem rank5_4_810 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,417,449,2,0⟩, ⟨true,557,677,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 419 417 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,419,449,2,0⟩, ⟨true,557,677,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 609 rank5_4_788 rank5_4_809

theorem rank5_4_811 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,389,449,2,0⟩, ⟨true,549,677,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 557 549 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,389,449,2,0⟩, ⟨true,557,677,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 415 rank5_4_775 rank5_4_810

theorem rank5_4_812 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,387,449,2,0⟩, ⟨true,461,677,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 389 387 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,389,449,2,0⟩, ⟨true,461,677,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 545 rank5_4_770 rank5_4_811

theorem rank5_4_813 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,449,2,0⟩, ⟨true,461,677,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 385 rank5_4_769 rank5_4_812

theorem rank5_4_814 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,449,2,0⟩, ⟨true,461,677,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 8 rank5_4_768 rank5_4_813

theorem rank5_4_815 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,337,449,2,0⟩, ⟨true,349,677,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 457 rank5_4_767 rank5_4_814

end OddPerfect.SpoofBox
