module

public import OddPerfect.PrimeRank5_3.Part026
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_3_624 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,293,1,0⟩, ⟨false,2267,4533,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 4523 4533 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,293,1,0⟩, ⟨false,2267,4523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 3019 rank5_3_608 rank5_3_623

theorem rank5_3_625 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,293,1,0⟩, ⟨false,4535,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 4547 4535 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,293,1,0⟩, ⟨false,4547,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_626 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,309,1,0⟩, ⟨false,2267,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 293 309 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,293,1,0⟩, ⟨false,2267,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 4533 rank5_3_624 rank5_3_625

theorem rank5_3_627 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,313,353,1,0⟩, ⟨false,2267,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_628 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,353,1,0⟩, ⟨false,2267,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 309 rank5_3_626 rank5_3_627

theorem rank5_3_629 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,353,1,0⟩, ⟨false,2259,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2267 2259 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,353,1,0⟩, ⟨false,2267,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_3_593 rank5_3_628

theorem rank5_3_630 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,365,1,0⟩, ⟨false,1129,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 353 365 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,353,1,0⟩, ⟨false,1129,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 2257 rank5_3_592 rank5_3_629

theorem rank5_3_631 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,369,541,1,0⟩, ⟨false,1129,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 373 369 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,373,541,1,0⟩, ⟨false,1129,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_632 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,541,1,0⟩, ⟨false,1127,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 1129 1127 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,541,1,0⟩, ⟨false,1129,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 365 rank5_3_630 rank5_3_631

theorem rank5_3_633 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,541,1,0⟩, ⟨false,563,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 1125 rank5_3_553 rank5_3_632

theorem rank5_3_634 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨true,277,541,1,0⟩, ⟨false,563,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 2 .exponent 2 rank5_3_412 rank5_3_633

theorem rank5_3_635 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨true,277,553,1,0⟩, ⟨false,281,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 541 553 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨true,277,541,1,0⟩, ⟨false,281,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 561 rank5_3_411 rank5_3_634

theorem rank5_3_636 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨true,557,0,1,0⟩, ⟨false,557,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 563 558 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨true,557,0,1,0⟩, ⟨false,563,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_637 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,2,0⟩, ⟨true,277,0,1,0⟩, ⟨false,281,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 553 rank5_3_635 rank5_3_636

theorem rank5_3_638 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨true,277,0,1,0⟩, ⟨false,281,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 4 rank5_3_394 rank5_3_637

theorem rank5_3_639 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨true,277,0,1,0⟩, ⟨false,281,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_640 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,19,2,0⟩, ⟨true,277,0,1,0⟩, ⟨false,277,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 281 278 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,19,2,0⟩, ⟨true,277,0,1,0⟩, ⟨false,281,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 2 .base 17 rank5_3_638 rank5_3_639

theorem rank5_3_641 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,19,2,0⟩, ⟨true,137,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 273 rank5_3_393 rank5_3_640

theorem rank5_3_642 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,19,2,0⟩, ⟨true,125,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 137 125 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,19,2,0⟩, ⟨true,137,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 6 rank5_3_256 rank5_3_641

theorem rank5_3_643 : PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,21,2,0⟩, ⟨true,61,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 2 19 21 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,19,2,0⟩, ⟨true,61,0,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 121 rank5_3_233 rank5_3_642

theorem rank5_3_644 : PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨false,23,23,2,0⟩, ⟨true,61,73,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  apply covered_force_base _ 0 4 1093 (by norm_num) (Nat.odd_iff.mpr (by decide)) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨false,23,23,2,0⟩, ⟨true,61,73,1,0⟩, ⟨false,1093,1093,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_645 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,4⟩, ⟨false,23,23,2,0⟩, ⟨true,61,73,1,0⟩, ⟨false,263,0,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 11 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_646 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨true,61,65,1,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 61 65 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨true,61,61,1,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 3 31 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_647 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨true,69,73,1,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 73 69 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨false,5,5,6,0⟩, ⟨false,23,23,2,0⟩, ⟨true,73,73,1,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 3 37 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

end OddPerfect.SpoofBox
