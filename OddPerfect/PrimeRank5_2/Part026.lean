module

public import OddPerfect.PrimeRank5_2.Part025
import OddPerfect.PrimeRank5_2.Witnesses
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_2_600 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2647,2665,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2663 2665 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2647,2663,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_601 : PrimeCovered (#v[⟨false,3,3,14,14⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2671,2677,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 11 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_602 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2671,2673,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2671 2673 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2671,2671,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_603 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2675,2677,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2677 2675 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2677,2677,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_604 : PrimeCovered (#v[⟨false,3,3,16,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2671,2677,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2673 rank5_2_602 rank5_2_603

theorem rank5_2_605 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2671,2677,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 14 rank5_2_601 rank5_2_604

theorem rank5_2_606 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2679,2687,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2683 2679 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2683,2687,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_607 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2667,2687,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2671 2667 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2671,2687,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 2677 rank5_2_605 rank5_2_606

theorem rank5_2_608 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2647,2687,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2665 rank5_2_600 rank5_2_607

theorem rank5_2_609 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2647,2687,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 8 rank5_2_599 rank5_2_608

theorem rank5_2_610 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2641,2687,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2647 2641 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2647,2687,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 12 rank5_2_598 rank5_2_609

theorem rank5_2_611 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2593,2687,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2639 rank5_2_597 rank5_2_610

theorem rank5_2_612 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,281,283,2,0⟩, ⟨false,2593,2687,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 281 rank5_2_596 rank5_2_611

theorem rank5_2_613 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,281,283,2,0⟩, ⟨false,2503,2687,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2591 rank5_2_595 rank5_2_612

theorem rank5_2_614 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,281,281,2,0⟩, ⟨false,2689,2791,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_615 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,283,283,2,0⟩, ⟨false,2689,2791,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_616 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,281,283,2,0⟩, ⟨false,2689,2791,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 281 rank5_2_614 rank5_2_615

theorem rank5_2_617 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,281,281,2,0⟩, ⟨false,2797,2849,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2843 2849 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,281,281,2,0⟩, ⟨false,2797,2843,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_618 : PrimeCovered (#v[⟨false,3,3,12,12⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,281,281,2,0⟩, ⟨false,2851,2903,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 797161 rank5_2_prime797161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_619 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,8⟩, ⟨true,17,17,5,0⟩, ⟨false,281,281,2,0⟩, ⟨false,2851,2903,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_2_620 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,281,281,2,0⟩, ⟨false,2851,2875,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 2861 2875 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,281,281,2,0⟩, ⟨false,2851,2861,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_621 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,281,281,2,0⟩, ⟨false,2877,2903,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 2879 2877 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,281,281,2,0⟩, ⟨false,2879,2903,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_2_622 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,10,0⟩, ⟨true,17,17,5,0⟩, ⟨false,281,281,2,0⟩, ⟨false,2851,2903,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2875 rank5_2_620 rank5_2_621

theorem rank5_2_623 : PrimeCovered (#v[⟨false,3,3,14,0⟩, ⟨false,5,5,8,0⟩, ⟨true,17,17,5,0⟩, ⟨false,281,281,2,0⟩, ⟨false,2851,2903,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 8 rank5_2_619 rank5_2_622

end OddPerfect.SpoofBox
