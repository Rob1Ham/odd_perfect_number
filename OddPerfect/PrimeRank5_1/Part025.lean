module

public import OddPerfect.PrimeRank5_1.Part024
import OddPerfect.PrimeRank5_1.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_576 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,113,113,2,0⟩, ⟨false,541,613,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_577 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,113,113,2,0⟩, ⟨false,617,631,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_578 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,113,113,2,0⟩, ⟨false,617,631,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_579 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,113,113,2,0⟩, ⟨false,617,637,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 631 637 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,113,113,2,0⟩, ⟨false,617,631,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 10 rank5_1_577 rank5_1_578

theorem rank5_1_580 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,113,113,2,0⟩, ⟨false,639,659,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 641 639 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,113,113,2,0⟩, ⟨false,641,659,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_581 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,113,113,2,0⟩, ⟨false,617,659,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 637 rank5_1_579 rank5_1_580

theorem rank5_1_582 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,113,113,2,0⟩, ⟨false,661,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_583 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,113,113,2,0⟩, ⟨false,615,709,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 617 615 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,113,113,2,0⟩, ⟨false,617,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 659 rank5_1_581 rank5_1_582

theorem rank5_1_584 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,111,113,2,0⟩, ⟨false,541,709,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 113 111 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,113,113,2,0⟩, ⟨false,541,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 613 rank5_1_576 rank5_1_583

theorem rank5_1_585 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,107,113,2,0⟩, ⟨false,541,709,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 109 rank5_1_575 rank5_1_584

theorem rank5_1_586 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,107,113,2,0⟩, ⟨false,541,717,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 709 717 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,107,113,2,0⟩, ⟨false,541,709,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_1_574 rank5_1_585

theorem rank5_1_587 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,107,113,2,0⟩, ⟨false,719,1069,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_588 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,107,109,2,0⟩, ⟨false,719,781,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 773 781 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,107,109,2,0⟩, ⟨false,719,773,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_589 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,107,107,2,0⟩, ⟨false,787,859,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_590 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,109,109,2,0⟩, ⟨false,787,821,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_591 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,109,109,2,0⟩, ⟨false,787,791,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 787 791 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,109,109,2,0⟩, ⟨false,787,787,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_592 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,109,109,2,2⟩, ⟨false,797,797,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_593 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,109,109,4,0⟩, ⟨false,797,797,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_1_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_594 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,109,109,4,0⟩, ⟨false,797,797,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_595 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,109,109,4,0⟩, ⟨false,797,797,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 12 rank5_1_593 rank5_1_594

theorem rank5_1_596 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,109,109,2,0⟩, ⟨false,793,797,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 797 793 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,109,109,2,0⟩, ⟨false,797,797,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .exponent 2 rank5_1_592 rank5_1_595

theorem rank5_1_597 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,109,109,2,0⟩, ⟨false,787,803,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 797 803 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,109,109,2,0⟩, ⟨false,787,797,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 791 rank5_1_591 rank5_1_596

theorem rank5_1_598 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,109,109,2,0⟩, ⟨false,805,821,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 809 805 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,109,109,2,0⟩, ⟨false,809,821,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_599 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,109,109,2,0⟩, ⟨false,787,821,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 803 rank5_1_597 rank5_1_598

end OddPerfect.SpoofBox
