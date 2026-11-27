module

public import OddPerfect.PrimeRank5_2.Part029
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_696 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5261,5281,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .exponent 2 rank5_2_686 rank5_2_695

theorem rank5_2_697 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5261,5281,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 14 rank5_2_685 rank5_2_696

theorem rank5_2_698 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5283,5303,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5297 5283 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5297,5303,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_699 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5261,5305,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5303 5305 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5261,5303,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 5281 rank5_2_697 rank5_2_698

theorem rank5_2_700 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5307,5351,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5309 5307 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5309,5351,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_701 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5259,5351,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5261 5259 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5261,5351,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 5305 rank5_2_699 rank5_2_700

theorem rank5_2_702 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5167,5351,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 5257 rank5_2_684 rank5_2_701

theorem rank5_2_703 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5167,5351,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 8 rank5_2_683 rank5_2_702

theorem rank5_2_704 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5163,5351,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5167 5163 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,269,2,0⟩, ⟨false,5167,5351,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 12 rank5_2_682 rank5_2_703

theorem rank5_2_705 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,269,2,0⟩, ⟨false,4987,5351,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 5161 rank5_2_681 rank5_2_704

theorem rank5_2_706 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,271,271,2,0⟩, ⟨false,4987,5351,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_707 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,271,2,0⟩, ⟨false,4987,5367,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5351 5367 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,271,2,0⟩, ⟨false,4987,5351,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 269 rank5_2_705 rank5_2_706

theorem rank5_2_708 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,271,2,0⟩, ⟨false,5369,5813,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5381 5369 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,271,2,0⟩, ⟨false,5381,5813,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_709 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,271,2,0⟩, ⟨false,4985,5813,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 4987 4985 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,271,2,0⟩, ⟨false,4987,5813,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 5367 rank5_2_707 rank5_2_708

theorem rank5_2_710 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,271,2,0⟩, ⟨false,4363,5813,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 4983 rank5_2_680 rank5_2_709

theorem rank5_2_711 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,267,271,2,0⟩, ⟨false,4363,5813,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 269 267 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,271,2,0⟩, ⟨false,4363,5813,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_2_663 rank5_2_710

theorem rank5_2_712 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,271,2,0⟩, ⟨false,4363,5815,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 5813 5815 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,271,2,0⟩, ⟨false,4363,5813,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 265 rank5_2_662 rank5_2_711

theorem rank5_2_713 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,265,2,0⟩, ⟨false,5821,8719,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 263 265 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,2,0⟩, ⟨false,5821,8719,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_714 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,267,271,2,0⟩, ⟨false,5821,8719,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 269 267 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,269,271,2,0⟩, ⟨false,5821,8719,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_715 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,271,2,0⟩, ⟨false,5817,8719,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 5821 5817 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,271,2,0⟩, ⟨false,5821,8719,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 265 rank5_2_713 rank5_2_714

theorem rank5_2_716 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,271,2,0⟩, ⟨false,4363,8719,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 5815 rank5_2_712 rank5_2_715

theorem rank5_2_717 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,271,2,0⟩, ⟨false,4363,8725,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 8719 8725 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,271,2,0⟩, ⟨false,4363,8719,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_2_661 rank5_2_716

theorem rank5_2_718 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨true,17,17,5,0⟩, ⟨false,263,271,2,0⟩, ⟨false,8731,0,2,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 1 4 19531 rank5_2_prime19531 (Nat.odd_iff.mpr (by decide +kernel)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨true,17,17,5,0⟩, ⟨false,263,271,2,0⟩, ⟨false,19531,19531,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_719 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,263,263,2,0⟩, ⟨false,8731,17449,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end OddPerfect.SpoofBox
