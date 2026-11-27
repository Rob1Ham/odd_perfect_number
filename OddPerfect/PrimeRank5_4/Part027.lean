module

public import OddPerfect.PrimeRank5_4.Part026
import OddPerfect.PrimeRank5_4.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_4_624 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,317,2,0⟩, ⟨true,1741,2161,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_625 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,317,2,0⟩, ⟨true,1453,2161,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1737 rank5_4_623 rank5_4_624

theorem rank5_4_626 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,319,331,2,0⟩, ⟨true,1453,2161,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 331 319 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,331,331,2,0⟩, ⟨true,1453,2161,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_627 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,331,2,0⟩, ⟨true,1453,2161,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 317 rank5_4_625 rank5_4_626

theorem rank5_4_628 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,297,331,2,0⟩, ⟨true,1093,2161,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 307 297 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,307,331,2,0⟩, ⟨true,1093,2161,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 1449 rank5_4_610 rank5_4_627

theorem rank5_4_629 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,331,2,0⟩, ⟨true,1093,2161,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 295 rank5_4_577 rank5_4_628

theorem rank5_4_630 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,331,2,0⟩, ⟨true,1093,2185,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2161 2185 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,331,2,0⟩, ⟨true,1093,2161,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_4_548 rank5_4_629

theorem rank5_4_631 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,331,2,0⟩, ⟨true,2213,0,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_632 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,277,2,0⟩, ⟨true,2213,2949,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2917 2949 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,277,2,0⟩, ⟨true,2213,2917,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_633 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨false,269,277,2,0⟩, ⟨true,2953,4421,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 rank5_4_prime19531 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_634 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,269,271,2,0⟩, ⟨true,2953,3533,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_635 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,277,2,0⟩, ⟨true,2953,3533,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_636 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,277,2,0⟩, ⟨true,2953,3217,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_637 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,277,2,0⟩, ⟨true,3221,3289,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 3257 3289 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,277,2,0⟩, ⟨true,3221,3257,1,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_638 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,4⟩, ⟨false,277,277,2,0⟩, ⟨true,3301,3361,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 2 88741 rank5_4_prime88741 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_639 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,277,277,2,0⟩, ⟨true,3301,3361,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_4_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_640 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,8⟩, ⟨false,17,17,6,0⟩, ⟨false,277,277,2,0⟩, ⟨true,3301,3361,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_4_641 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨false,17,17,6,0⟩, ⟨false,277,277,2,0⟩, ⟨true,3301,3361,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_642 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,277,277,2,0⟩, ⟨true,3301,3361,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 8 rank5_4_640 rank5_4_641

theorem rank5_4_643 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,6,0⟩, ⟨false,277,277,2,0⟩, ⟨true,3301,3361,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_4_639 rank5_4_642

theorem rank5_4_644 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,277,2,0⟩, ⟨true,3293,3361,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 3301 3293 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,277,2,0⟩, ⟨true,3301,3361,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .exponent 4 rank5_4_638 rank5_4_643

theorem rank5_4_645 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,277,2,0⟩, ⟨true,3221,3369,1,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 3361 3369 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,277,2,0⟩, ⟨true,3221,3361,1,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 3289 rank5_4_637 rank5_4_644

theorem rank5_4_646 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,277,2,0⟩, ⟨true,3373,3533,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_4_647 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨false,277,277,2,0⟩, ⟨true,3221,3533,1,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 3369 rank5_4_645 rank5_4_646

end OddPerfect.SpoofBox
