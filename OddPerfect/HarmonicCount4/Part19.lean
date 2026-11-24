module

public import OddPerfect.HarmonicCount4.Part18
import Mathlib.Tactic.IntervalCases

public section

namespace OddPerfect.HarmonicSearch

open DivisorCountSearch

theorem harmonic4_360 : Closed 4 10125 20 18876 7 := by
  apply closed_split (a:=11) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_346
    · exact ((by decide : ¬ (7:ℕ)^1%4=1) hres).elim
    · exact harmonic4_356
    · exact ((by decide : ¬ (7:ℕ)^3%4=1) hres).elim
    · exact harmonic4_359
    · exact ((by decide : ¬ (7:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_11 (by decide +kernel) e (by omega)

theorem harmonic4_361 : Closed 4 50625 25 94501 13 := by
  apply closed_split (a:=17) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=11) (v:=10) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=7) (v:=6) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=11) (v:=10) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_17 (by decide +kernel) e (by omega)

theorem harmonic4_362 : Closed 4 6125625 75 12568633 13 := by
  apply closed_split (a:=17) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=7) (v:=6) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=7) (v:=6) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=7) (v:=6) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_17 (by decide +kernel) e (by omega)

theorem harmonic4_363 : Closed 4 50625 25 94501 11 := by
  apply closed_split (a:=13) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_361
    · exact ((by decide : ¬ (11:ℕ)^1%4=1) hres).elim
    · exact harmonic4_362
    · exact ((by decide : ¬ (11:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_13 (by decide +kernel) e (by omega)

theorem harmonic4_364 : Closed 4 2480625 75 5386557 13 := by
  apply closed_split (a:=17) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=11) (v:=10) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=11) (v:=10) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=11) (v:=10) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=11) (v:=10) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_17 (by decide +kernel) e (by omega)

theorem harmonic4_365 : Closed 4 300155625 225 716412081 13 := by
  apply closed_split (a:=17) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=71) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=71) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_17 (by decide +kernel) e (by omega)

theorem harmonic4_366 : Closed 4 2480625 75 5386557 11 := by
  apply closed_split (a:=13) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_364
    · exact ((by decide : ¬ (11:ℕ)^1%4=1) hres).elim
    · exact harmonic4_365
    · exact ((by decide : ¬ (11:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_13 (by decide +kernel) e (by omega)

theorem harmonic4_367 : Closed 4 121550625 125 264697301 13 := by
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

theorem harmonic4_368 : Closed 4 14707625625 375 35204741033 13 := by
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

theorem harmonic4_369 : Closed 4 121550625 125 264697301 11 := by
  apply closed_split (a:=13) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_367
    · exact ((by decide : ¬ (11:ℕ)^1%4=1) hres).elim
    · exact harmonic4_368
    · exact ((by decide : ¬ (11:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_13 (by decide +kernel) e (by omega)

theorem harmonic4_370 : Closed 4 50625 25 94501 7 := by
  apply closed_split (a:=11) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_363
    · exact ((by decide : ¬ (7:ℕ)^1%4=1) hres).elim
    · exact harmonic4_366
    · exact ((by decide : ¬ (7:ℕ)^3%4=1) hres).elim
    · exact harmonic4_369
    · exact ((by decide : ¬ (7:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_11 (by decide +kernel) e (by omega)

theorem harmonic4_371 : Closed 4 253125 30 472626 13 := by
  apply closed_split (a:=17) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=7) (v:=6) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=7) (v:=6) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=7) (v:=6) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_17 (by decide +kernel) e (by omega)

theorem harmonic4_372 : Closed 4 30628125 90 62859258 13 := by
  apply closed_split (a:=17) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=7) (v:=6) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=7) (v:=6) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_nonempty (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_17 (by decide +kernel) e (by omega)

theorem harmonic4_373 : Closed 4 253125 30 472626 11 := by
  apply closed_split (a:=13) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_371
    · exact ((by decide : ¬ (11:ℕ)^1%4=1) hres).elim
    · exact harmonic4_372
    · exact ((by decide : ¬ (11:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_13 (by decide +kernel) e (by omega)

theorem harmonic4_374 : Closed 4 12403125 90 26939682 13 := by
  apply closed_split (a:=17) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=11) (v:=10) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=11) (v:=10) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=11) (v:=10) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_17 (by decide +kernel) e (by omega)

theorem harmonic4_375 : Closed 4 1500778125 270 3582977706 13 := by
  apply closed_split (a:=17) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_17 (by decide +kernel) e (by omega)

theorem harmonic4_376 : Closed 4 12403125 90 26939682 11 := by
  apply closed_split (a:=13) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_374
    · exact ((by decide : ¬ (11:ℕ)^1%4=1) hres).elim
    · exact harmonic4_375
    · exact ((by decide : ¬ (11:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_13 (by decide +kernel) e (by omega)

theorem harmonic4_377 : Closed 4 607753125 150 1323825426 13 := by
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

theorem harmonic4_378 : Closed 4 607753125 150 1323825426 11 := by
  apply closed_split (a:=13) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_377
    · exact ((by decide : ¬ (11:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_13 (by decide +kernel) e (by omega)

theorem harmonic4_379 : Closed 4 253125 30 472626 7 := by
  apply closed_split (a:=11) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_373
    · exact ((by decide : ¬ (7:ℕ)^1%4=1) hres).elim
    · exact harmonic4_376
    · exact ((by decide : ¬ (7:ℕ)^3%4=1) hres).elim
    · exact harmonic4_378
    · exact ((by decide : ¬ (7:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_11 (by decide +kernel) e (by omega)

end OddPerfect.HarmonicSearch
