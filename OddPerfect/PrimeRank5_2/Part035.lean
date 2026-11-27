module

public import OddPerfect.PrimeRank5_2.Part034
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_816 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨true,17,17,5,0⟩, ⟨false,479,521,2,0⟩, ⟨false,487,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_2_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_817 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,479,499,2,0⟩, ⟨false,487,503,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_818 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,479,499,2,0⟩, ⟨false,509,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_819 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,479,499,2,0⟩, ⟨false,509,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_820 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,479,499,2,0⟩, ⟨false,505,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 509 505 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,479,499,2,0⟩, ⟨false,509,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_2_818 rank5_2_819

theorem rank5_2_821 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,479,499,2,0⟩, ⟨false,487,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 503 rank5_2_817 rank5_2_820

theorem rank5_2_822 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,503,521,2,0⟩, ⟨false,509,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_823 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,503,509,2,0⟩, ⟨false,509,515,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 509 515 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,503,509,2,0⟩, ⟨false,509,509,2,0⟩] : Vector Slot 5)
  apply covered_prime_upper _ 3 503 508 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,503,503,2,0⟩, ⟨false,509,509,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_824 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,503,509,2,0⟩, ⟨false,517,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 521 517 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,503,509,2,0⟩, ⟨false,521,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_825 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,503,511,2,0⟩, ⟨false,509,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 509 511 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,503,509,2,0⟩, ⟨false,509,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 515 rank5_2_823 rank5_2_824

theorem rank5_2_826 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,513,521,2,0⟩, ⟨false,513,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 521 513 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,521,521,2,0⟩, ⟨false,513,523,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 4 523 522 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,521,521,2,0⟩, ⟨false,523,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_827 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,503,521,2,0⟩, ⟨false,509,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 511 rank5_2_825 rank5_2_826

theorem rank5_2_828 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,501,521,2,0⟩, ⟨false,501,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 503 501 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,503,521,2,0⟩, ⟨false,501,523,2,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 4 509 504 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,503,521,2,0⟩, ⟨false,509,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_2_822 rank5_2_827

theorem rank5_2_829 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,479,521,2,0⟩, ⟨false,487,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 499 rank5_2_821 rank5_2_828

theorem rank5_2_830 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,479,521,2,0⟩, ⟨false,479,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 487 480 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,479,521,2,0⟩, ⟨false,487,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_2_816 rank5_2_829

theorem rank5_2_831 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,523,2,0⟩, ⟨false,449,537,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 523 537 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,523,2,0⟩, ⟨false,449,523,2,0⟩] : Vector Slot 5)
  apply covered_prime_upper _ 3 521 522 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,521,2,0⟩, ⟨false,449,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 477 rank5_2_815 rank5_2_830

theorem rank5_2_832 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨true,17,17,5,0⟩, ⟨false,443,479,2,0⟩, ⟨false,541,599,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_2_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_833 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,459,2,0⟩, ⟨false,541,563,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 457 459 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,443,457,2,0⟩, ⟨false,541,563,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_834 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,461,479,2,0⟩, ⟨false,541,563,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_835 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,461,469,2,0⟩, ⟨false,541,563,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 467 469 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,461,467,2,0⟩, ⟨false,541,563,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_836 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,479,479,2,0⟩, ⟨false,541,551,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 547 551 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,479,479,2,0⟩, ⟨false,541,547,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_837 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,479,479,2,0⟩, ⟨false,553,563,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 557 553 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,479,479,2,0⟩, ⟨false,557,563,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_838 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,471,479,2,0⟩, ⟨false,541,563,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 479 471 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,479,479,2,0⟩, ⟨false,541,563,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 551 rank5_2_836 rank5_2_837

theorem rank5_2_839 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,461,479,2,0⟩, ⟨false,541,563,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 469 rank5_2_835 rank5_2_838

end OddPerfect.SpoofBox
