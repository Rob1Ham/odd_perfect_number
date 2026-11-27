module

public import OddPerfect.PrimeRank5_4.Part034
import OddPerfect.PrimeRank5_4.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_816 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,673,2,0⟩, ⟨true,461,677,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_817 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,497,2,0⟩, ⟨true,461,497,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 461 497 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,497,2,0⟩, ⟨true,461,461,1,0⟩] : Vector Slot 5)
  apply covered_prime_upper _ 3 457 460 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,457,2,0⟩, ⟨true,461,461,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_818 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨false,457,487,2,0⟩, ⟨true,509,541,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_4_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_819 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,471,2,0⟩, ⟨true,509,541,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 467 471 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,467,2,0⟩, ⟨true,509,541,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_820 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,479,487,2,0⟩, ⟨true,509,521,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_821 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,479,487,2,0⟩, ⟨true,525,541,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 541 525 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,479,487,2,0⟩, ⟨true,541,541,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 271 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_822 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,473,487,2,0⟩, ⟨true,509,541,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 479 473 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,479,487,2,0⟩, ⟨true,509,541,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 521 rank5_4_820 rank5_4_821

theorem rank5_4_823 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,487,2,0⟩, ⟨true,509,541,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 471 rank5_4_819 rank5_4_822

theorem rank5_4_824 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,487,2,0⟩, ⟨true,509,541,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 6 rank5_4_818 rank5_4_823

theorem rank5_4_825 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨false,491,523,2,0⟩, ⟨true,509,541,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_4_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_826 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,491,503,2,0⟩, ⟨true,509,521,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_827 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,491,495,2,0⟩, ⟨true,509,521,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 491 495 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,491,491,2,0⟩, ⟨true,509,521,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_828 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,499,503,2,0⟩, ⟨true,509,513,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 509 513 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,499,503,2,0⟩, ⟨true,509,509,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_829 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,499,503,2,0⟩, ⟨true,517,521,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 521 517 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,499,503,2,0⟩, ⟨true,521,521,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 29 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_830 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,497,503,2,0⟩, ⟨true,509,521,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 499 497 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,499,503,2,0⟩, ⟨true,509,521,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 513 rank5_4_828 rank5_4_829

theorem rank5_4_831 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,491,503,2,0⟩, ⟨true,509,521,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 495 rank5_4_827 rank5_4_830

theorem rank5_4_832 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,491,503,2,0⟩, ⟨true,509,521,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_4_826 rank5_4_831

theorem rank5_4_833 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,491,503,2,0⟩, ⟨true,525,541,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 541 525 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,491,503,2,0⟩, ⟨true,541,541,1,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 4 271 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_834 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,491,505,2,0⟩, ⟨true,509,541,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 503 505 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,491,503,2,0⟩, ⟨true,509,541,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 521 rank5_4_832 rank5_4_833

theorem rank5_4_835 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,507,523,2,0⟩, ⟨true,509,541,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 509 507 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,509,523,2,0⟩, ⟨true,509,541,1,0⟩] : Vector Slot 5)
  apply covered_prime_lower _ 4 521 510 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,509,523,2,0⟩, ⟨true,521,541,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_836 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,491,523,2,0⟩, ⟨true,509,541,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 505 rank5_4_834 rank5_4_835

theorem rank5_4_837 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,489,523,2,0⟩, ⟨true,509,541,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 491 489 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,491,523,2,0⟩, ⟨true,509,541,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_4_825 rank5_4_836

theorem rank5_4_838 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,523,2,0⟩, ⟨true,501,541,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 509 501 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,523,2,0⟩, ⟨true,509,541,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 487 rank5_4_824 rank5_4_837

theorem rank5_4_839 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,541,2,0⟩, ⟨true,461,545,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 541 545 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,541,2,0⟩, ⟨true,461,541,1,0⟩] : Vector Slot 5)
  apply covered_prime_upper _ 3 523 540 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,457,523,2,0⟩, ⟨true,461,541,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 497 rank5_4_817 rank5_4_838

end OddPerfect.SpoofBox
