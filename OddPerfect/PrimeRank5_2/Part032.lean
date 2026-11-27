module

public import OddPerfect.PrimeRank5_2.Part031
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_744 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,2,0⟩, ⟨false,8731,11637,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 11633 11637 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,2,0⟩, ⟨false,8731,11633,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 9975 rank5_2_742 rank5_2_743

theorem rank5_2_745 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,2,0⟩, ⟨false,11639,17449,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 11657 11639 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,2,0⟩, ⟨false,11657,17449,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_746 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,2,0⟩, ⟨false,8731,17449,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 11637 rank5_2_744 rank5_2_745

theorem rank5_2_747 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,265,2,0⟩, ⟨false,8731,17449,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 263 265 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,2,0⟩, ⟨false,8731,17449,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_2_719 rank5_2_746

theorem rank5_2_748 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,267,271,2,0⟩, ⟨false,8731,17449,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 269 267 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,271,2,0⟩, ⟨false,8731,17449,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_749 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,271,2,0⟩, ⟨false,8731,17461,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 17449 17461 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,271,2,0⟩, ⟨false,8731,17449,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 265 rank5_2_747 rank5_2_748

theorem rank5_2_750 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,271,2,0⟩, ⟨false,17463,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 17467 17463 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,271,2,0⟩, ⟨false,17467,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_751 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,271,2,0⟩, ⟨false,8731,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 17461 rank5_2_749 rank5_2_750

theorem rank5_2_752 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,271,2,0⟩, ⟨false,8727,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 8731 8727 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,271,2,0⟩, ⟨false,8731,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_2_718 rank5_2_751

theorem rank5_2_753 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,271,2,0⟩, ⟨false,4363,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 8725 rank5_2_717 rank5_2_752

theorem rank5_2_754 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,273,283,2,0⟩, ⟨false,4363,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 277 273 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,277,283,2,0⟩, ⟨false,4363,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_755 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,283,2,0⟩, ⟨false,4359,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 4363 4359 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,283,2,0⟩, ⟨false,4363,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 271 rank5_2_753 rank5_2_754

theorem rank5_2_756 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,287,2,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 283 287 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,283,2,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 4357 rank5_2_660 rank5_2_755

theorem rank5_2_757 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,289,317,2,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 293 289 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,293,317,2,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_758 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,317,2,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 287 rank5_2_756 rank5_2_757

theorem rank5_2_759 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,317,2,0⟩, ⟨false,2175,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2179 2175 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,317,2,0⟩, ⟨false,2179,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_2_585 rank5_2_758

theorem rank5_2_760 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,317,2,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2173 rank5_2_584 rank5_2_759

theorem rank5_2_761 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,223,317,2,0⟩, ⟨false,1083,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1087 1083 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,223,317,2,0⟩, ⟨false,1087,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 261 rank5_2_493 rank5_2_760

theorem rank5_2_762 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,217,317,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 223 217 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,223,317,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1081 rank5_2_438 rank5_2_761

theorem rank5_2_763 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,163,317,2,0⟩, ⟨false,527,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 541 527 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,163,317,2,0⟩, ⟨false,541,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 215 rank5_2_437 rank5_2_762

theorem rank5_2_764 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,163,317,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 525 rank5_2_436 rank5_2_763

theorem rank5_2_765 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,5,0⟩, ⟨false,163,325,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 317 325 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,5,0⟩, ⟨false,163,317,2,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 4 rank5_2_435 rank5_2_764

theorem rank5_2_766 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,4⟩, ⟨true,17,17,5,0⟩, ⟨false,331,0,2,0⟩, ⟨false,337,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_767 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,331,439,2,0⟩, ⟨false,337,449,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
