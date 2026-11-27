module

public import OddPerfect.PrimeRank5_3.Part025
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_3_600 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,277,1,0⟩, ⟨false,2789,3019,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 139 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_601 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,281,281,1,0⟩, ⟨false,2789,3019,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 47 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_602 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,281,1,0⟩, ⟨false,2789,3019,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 277 rank5_3_600 rank5_3_601

theorem rank5_3_603 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,281,1,0⟩, ⟨false,2591,3019,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2787 rank5_3_599 rank5_3_602

theorem rank5_3_604 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,281,1,0⟩, ⟨false,2591,3019,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_3_596 rank5_3_603

theorem rank5_3_605 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,281,1,0⟩, ⟨false,2267,3019,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 2589 rank5_3_595 rank5_3_604

theorem rank5_3_606 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,285,293,1,0⟩, ⟨false,2267,3019,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 293 285 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,293,293,1,0⟩, ⟨false,2267,3019,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 3 7 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_607 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,293,1,0⟩, ⟨false,2267,3019,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 281 rank5_3_605 rank5_3_606

theorem rank5_3_608 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,293,1,0⟩, ⟨false,2267,3019,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 1 .exponent 6 rank5_3_594 rank5_3_607

theorem rank5_3_609 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,6⟩, ⟨false,17,17,4,0⟩, ⟨true,277,293,1,0⟩, ⟨false,3023,4523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 19531 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_610 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,281,1,0⟩, ⟨false,3023,3623,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_611 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,277,1,0⟩, ⟨false,3023,3271,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 139 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_612 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,281,281,1,0⟩, ⟨false,3023,3271,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 47 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_613 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,281,1,0⟩, ⟨false,3023,3295,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 3271 3295 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,281,1,0⟩, ⟨false,3023,3271,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 277 rank5_3_611 rank5_3_612

theorem rank5_3_614 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,277,1,0⟩, ⟨false,3299,3623,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 139 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_615 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,281,281,1,0⟩, ⟨false,3299,3623,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 3 47 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_616 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,281,1,0⟩, ⟨false,3297,3623,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 3299 3297 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,281,1,0⟩, ⟨false,3299,3623,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 3 .base 277 rank5_3_614 rank5_3_615

theorem rank5_3_617 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,281,1,0⟩, ⟨false,3023,3623,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 3295 rank5_3_613 rank5_3_616

theorem rank5_3_618 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,281,1,0⟩, ⟨false,3023,3623,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_3_610 rank5_3_617

theorem rank5_3_619 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,281,1,0⟩, ⟨false,3625,4523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 3631 3625 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,281,1,0⟩, ⟨false,3631,4523,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_3_620 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,281,1,0⟩, ⟨false,3023,4523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 3623 rank5_3_618 rank5_3_619

theorem rank5_3_621 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,285,293,1,0⟩, ⟨false,3023,4523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 293 285 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,293,293,1,0⟩, ⟨false,3023,4523,2,0⟩] : Vector Slot 5)
  exact primeCovered_missing _ 3 7 (by norm_num) (by decide) (by decide +kernel) (by decide +kernel)

theorem rank5_3_622 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,8,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,293,1,0⟩, ⟨false,3023,4523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 281 rank5_3_620 rank5_3_621

theorem rank5_3_623 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,293,1,0⟩, ⟨false,3021,4523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 3023 3021 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨false,5,5,6,0⟩, ⟨false,17,17,4,0⟩, ⟨true,277,293,1,0⟩, ⟨false,3023,4523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 6 rank5_3_609 rank5_3_622

end OddPerfect.SpoofBox
