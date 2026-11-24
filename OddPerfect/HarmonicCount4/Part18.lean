module

public import OddPerfect.HarmonicCount4.Part17
import Mathlib.Tactic.IntervalCases

public section

namespace OddPerfect.HarmonicSearch

open DivisorCountSearch

theorem harmonic4_340 : Closed 4 4862025 75 10506551 13 := by
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

theorem harmonic4_341 : Closed 4 588305025 225 1397371283 13 := by
  apply closed_split (a:=17) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=31) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_17 (by decide +kernel) e (by omega)

theorem harmonic4_342 : Closed 4 4862025 75 10506551 11 := by
  apply closed_split (a:=13) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_340
    · exact ((by decide : ¬ (11:ℕ)^1%4=1) hres).elim
    · exact harmonic4_341
    · exact ((by decide : ¬ (11:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_13 (by decide +kernel) e (by omega)

theorem harmonic4_343 : Closed 4 2025 15 3751 7 := by
  apply closed_split (a:=11) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_326
    · exact ((by decide : ¬ (7:ℕ)^1%4=1) hres).elim
    · exact harmonic4_339
    · exact ((by decide : ¬ (7:ℕ)^3%4=1) hres).elim
    · exact harmonic4_342
    · exact ((by decide : ¬ (7:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_11 (by decide +kernel) e (by omega)

theorem harmonic4_344 : Closed 4 10125 20 18876 13 := by
  apply closed_split (a:=17) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=11) (v:=10) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=7) (v:=6) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=11) (v:=10) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=7) (v:=6) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_17 (by decide +kernel) e (by omega)

theorem harmonic4_345 : Closed 4 1225125 60 2510508 13 := by
  apply closed_split (a:=17) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=7) (v:=6) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=7) (v:=6) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=7) (v:=6) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=7) (v:=6) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_17 (by decide +kernel) e (by omega)

theorem harmonic4_346 : Closed 4 10125 20 18876 11 := by
  apply closed_split (a:=13) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_344
    · exact ((by decide : ¬ (11:ℕ)^1%4=1) hres).elim
    · exact harmonic4_345
    · exact ((by decide : ¬ (11:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_13 (by decide +kernel) e (by omega)

theorem harmonic4_347 : Closed 4 496125 60 1075932 13 := by
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

theorem harmonic4_348 : Closed 4 780404625 360 2003385384 19 := by
  apply closed_split (a:=23) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^1%4=1) hres).elim
    · exact closed_owed_prime (r:=127) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_23 (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_23 (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_23 (by decide +kernel) e (by omega)

theorem harmonic4_349 : Closed 4 13266878625 720 36060936912 19 := by
  apply closed_split (a:=23) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^1%4=1) hres).elim
    · exact closed_owed_prime (r:=127) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_23 (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_23 (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_23 (by decide +kernel) e (by omega)

theorem harmonic4_350 : Closed 4 780404625 360 2003385384 17 := by
  apply closed_split (a:=19) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_348
    · exact harmonic4_349
    · exact closed_owed_prime (r:=307) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_nonempty (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_19 (by decide +kernel)
    · exact closed_by_moment envH4_19 (by decide +kernel)
    · exact closed_by_moment envH4_19 (by decide +kernel)
    · exact closed_by_moment envH4_19 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_19 (by decide +kernel) e (by omega)

theorem harmonic4_351 : Closed 4 10145260125 540 26187108948 19 := by
  apply closed_split (a:=23) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^1%4=1) hres).elim
    · exact closed_owed_prime (r:=61) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_23 (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_23 (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_23 (by decide +kernel) e (by omega)

theorem harmonic4_352 : Closed 4 172469422125 1080 471367961064 19 := by
  apply closed_split (a:=23) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^1%4=1) hres).elim
    · exact closed_owed_prime (r:=61) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_23 (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_23 (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_23 (by decide +kernel) e (by omega)

theorem harmonic4_353 : Closed 4 10145260125 540 26187108948 17 := by
  apply closed_split (a:=19) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_351
    · exact harmonic4_352
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_19 (by decide +kernel)
    · exact closed_by_moment envH4_19 (by decide +kernel)
    · exact closed_by_moment envH4_19 (by decide +kernel)
    · exact closed_by_moment envH4_19 (by decide +kernel)
    · exact closed_by_moment envH4_19 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_19 (by decide +kernel) e (by omega)

theorem harmonic4_354 : Closed 4 60031125 180 143098956 13 := by
  apply closed_split (a:=17) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=13) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact harmonic4_350
    · exact harmonic4_353
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_17 (by decide +kernel) e (by omega)

theorem harmonic4_355 : Closed 4 7263766125 300 17327884860 13 := by
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

theorem harmonic4_356 : Closed 4 496125 60 1075932 11 := by
  apply closed_split (a:=13) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_347
    · exact ((by decide : ¬ (11:ℕ)^1%4=1) hres).elim
    · exact harmonic4_354
    · exact ((by decide : ¬ (11:ℕ)^3%4=1) hres).elim
    · exact harmonic4_355
    · exact ((by decide : ¬ (11:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_13 (by decide +kernel) e (by omega)

theorem harmonic4_357 : Closed 4 24310125 100 52871676 13 := by
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

theorem harmonic4_358 : Closed 4 2941525125 300 7031932908 13 := by
  apply closed_split (a:=17) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=13) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_17 (by decide +kernel) e (by omega)

theorem harmonic4_359 : Closed 4 24310125 100 52871676 11 := by
  apply closed_split (a:=13) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_357
    · exact ((by decide : ¬ (11:ℕ)^1%4=1) hres).elim
    · exact harmonic4_358
    · exact ((by decide : ¬ (11:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_13 (by decide +kernel) e (by omega)

end OddPerfect.HarmonicSearch
