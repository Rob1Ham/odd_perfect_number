module

public import OddPerfect.PrimeRank5_1.Part034
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_816 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,149,167,2,0⟩, ⟨false,263,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 299 rank5_1_814 rank5_1_815

theorem rank5_1_817 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,4,0⟩, ⟨false,149,167,2,0⟩, ⟨false,263,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 5 rank5_1_797 rank5_1_816

theorem rank5_1_818 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,4,0⟩, ⟨false,149,167,2,0⟩, ⟨false,351,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 353 351 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,4,0⟩, ⟨false,149,167,2,0⟩, ⟨false,353,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_819 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,4,0⟩, ⟨false,145,167,2,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 149 145 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,4,0⟩, ⟨false,149,167,2,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 349 rank5_1_817 rank5_1_818

theorem rank5_1_820 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,167,2,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 143 rank5_1_796 rank5_1_819

theorem rank5_1_821 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,2,0⟩, ⟨false,127,167,2,0⟩, ⟨false,263,525,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 523 525 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,2,0⟩, ⟨false,127,167,2,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 2 rank5_1_747 rank5_1_820

theorem rank5_1_822 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,2,0⟩, ⟨false,127,167,2,0⟩, ⟨false,527,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 541 527 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,2,0⟩, ⟨false,127,167,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_823 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,2,0⟩, ⟨false,127,167,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 525 rank5_1_821 rank5_1_822

theorem rank5_1_824 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,2,0⟩, ⟨false,169,251,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 173 169 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,2,0⟩, ⟨false,173,251,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_825 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,2,0⟩, ⟨false,127,251,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 167 rank5_1_823 rank5_1_824

theorem rank5_1_826 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,19,2,0⟩, ⟨false,127,251,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .base 17 rank5_1_734 rank5_1_825

theorem rank5_1_827 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,19,2,0⟩, ⟨false,127,253,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 251 253 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,19,2,0⟩, ⟨false,127,251,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 6 rank5_1_721 rank5_1_826

theorem rank5_1_828 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,2⟩, ⟨false,257,509,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 2 3 307 (by norm_num) (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,2⟩, ⟨false,307,307,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_829 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,5,5⟩, ⟨false,17,17,4,0⟩, ⟨false,257,337,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_830 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,291,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 283 291 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,283,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_831 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,293,337,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_832 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,9,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,337,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 291 rank5_1_830 rank5_1_831

theorem rank5_1_833 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,341,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 337 341 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,337,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 5 rank5_1_829 rank5_1_832

theorem rank5_1_834 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,4,0⟩, ⟨false,343,509,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 347 343 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,4,0⟩, ⟨false,347,509,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_835 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,4,0⟩, ⟨false,257,509,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 341 rank5_1_833 rank5_1_834

theorem rank5_1_836 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,257,513,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 509 513 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,257,509,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  apply covered_force_base _ 0 4 1093 rank5_1_prime1093 (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,257,509,2,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 2 rank5_1_828 rank5_1_835

theorem rank5_1_837 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,515,0,2,0⟩, ⟨false,515,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 521 515 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,521,0,2,0⟩, ⟨false,515,0,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 4 523 522 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,521,0,2,0⟩, ⟨false,523,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_838 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,257,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 513 rank5_1_836 rank5_1_837

theorem rank5_1_839 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,2,0⟩, ⟨false,257,0,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
