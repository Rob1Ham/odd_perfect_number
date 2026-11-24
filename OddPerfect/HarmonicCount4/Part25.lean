module

public import OddPerfect.HarmonicCount4.Part24
import Mathlib.Tactic.IntervalCases

public section

namespace OddPerfect.HarmonicSearch

open DivisorCountSearch

theorem harmonic4_480 : Closed 4 4100625 45 7685821 11 := by
  apply closed_split (a:=13) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_479
    · exact ((by decide : ¬ (11:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_13 (by decide +kernel) e (by omega)

theorem harmonic4_481 : Closed 4 200930625 135 438091797 13 := by
  apply closed_split (a:=17) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=11) (v:=10) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=11) (v:=10) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_17 (by decide +kernel) e (by omega)

theorem harmonic4_482 : Closed 4 24312605625 405 58266209001 13 := by
  apply closed_split (a:=17) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=13) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_17 (by decide +kernel) e (by omega)

theorem harmonic4_483 : Closed 4 200930625 135 438091797 11 := by
  apply closed_split (a:=13) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_481
    · exact ((by decide : ¬ (11:ℕ)^1%4=1) hres).elim
    · exact harmonic4_482
    · exact ((by decide : ¬ (11:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_13 (by decide +kernel) e (by omega)

theorem harmonic4_484 : Closed 4 4100625 45 7685821 7 := by
  apply closed_split (a:=11) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_480
    · exact ((by decide : ¬ (7:ℕ)^1%4=1) hres).elim
    · exact harmonic4_483
    · exact ((by decide : ¬ (7:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_11 (by decide +kernel) e (by omega)

theorem harmonic4_485 : Closed 4 1004653125 162 2191019922 11 := by
  apply closed_split (a:=13) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_13 (by decide +kernel) e (by omega)

theorem harmonic4_486 : Closed 4 20503125 54 38438946 7 := by
  apply closed_split (a:=11) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_by_moment envH4_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^1%4=1) hres).elim
    · exact harmonic4_485
    · exact ((by decide : ¬ (7:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_11 (by decide +kernel) e (by omega)

theorem harmonic4_487 : Closed 4 6561 9 9841 5 := by
  apply closed_split (a:=7) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_453
    · exact harmonic4_462
    · exact harmonic4_471
    · exact harmonic4_478
    · exact harmonic4_484
    · exact harmonic4_486
    · exact closed_by_moment envH4_7 (by decide +kernel)
    · exact closed_by_moment envH4_7 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_7 (by decide +kernel) e (by omega)

theorem harmonic4_488 : Closed 4 59049 11 88573 7 := by
  apply closed_split (a:=11) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_by_moment envH4_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_11 (by decide +kernel) e (by omega)

theorem harmonic4_489 : Closed 4 295245 22 531438 11 := by
  apply closed_split (a:=13) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_13 (by decide +kernel) e (by omega)

theorem harmonic4_490 : Closed 4 14467005 66 30291966 13 := by
  apply closed_split (a:=17) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_17 (by decide +kernel) e (by omega)

theorem harmonic4_491 : Closed 4 1750507605 198 4028831478 13 := by
  apply closed_split (a:=17) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_17 (by decide +kernel) e (by omega)

theorem harmonic4_492 : Closed 4 14467005 66 30291966 11 := by
  apply closed_split (a:=13) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_490
    · exact ((by decide : ¬ (11:ℕ)^1%4=1) hres).elim
    · exact harmonic4_491
    · exact ((by decide : ¬ (11:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_13 (by decide +kernel) e (by omega)

theorem harmonic4_493 : Closed 4 295245 22 531438 7 := by
  apply closed_split (a:=11) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_489
    · exact ((by decide : ¬ (7:ℕ)^1%4=1) hres).elim
    · exact harmonic4_492
    · exact ((by decide : ¬ (7:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_11 (by decide +kernel) e (by omega)

theorem harmonic4_494 : Closed 4 1476225 33 2745763 11 := by
  apply closed_split (a:=13) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_13 (by decide +kernel) e (by omega)

theorem harmonic4_495 : Closed 4 72335025 99 156508491 13 := by
  apply closed_split (a:=17) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_17 (by decide +kernel) e (by omega)

theorem harmonic4_496 : Closed 4 8752538025 297 20815629303 13 := by
  apply closed_split (a:=17) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_17 (by decide +kernel) e (by omega)

theorem harmonic4_497 : Closed 4 72335025 99 156508491 11 := by
  apply closed_split (a:=13) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_495
    · exact ((by decide : ¬ (11:ℕ)^1%4=1) hres).elim
    · exact harmonic4_496
    · exact ((by decide : ¬ (11:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_13 (by decide +kernel) e (by omega)

theorem harmonic4_498 : Closed 4 1476225 33 2745763 7 := by
  apply closed_split (a:=11) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_494
    · exact ((by decide : ¬ (7:ℕ)^1%4=1) hres).elim
    · exact harmonic4_497
    · exact ((by decide : ¬ (7:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_11 (by decide +kernel) e (by omega)

theorem harmonic4_499 : Closed 4 361675125 132 787591116 13 := by
  apply closed_split (a:=17) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_nonempty (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_17 (by decide +kernel) e (by omega)

end OddPerfect.HarmonicSearch
