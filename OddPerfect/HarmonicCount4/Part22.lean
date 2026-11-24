module

public import OddPerfect.HarmonicCount4.Part21
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.HarmonicSearch

open DivisorCountSearch

theorem harmonic4_420 : Closed 4 91125 28 170508 11 := by
  apply closed_split (a:=13) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_418
    · exact ((by decide : ¬ (11:ℕ)^1%4=1) hres).elim
    · exact harmonic4_419
    · exact ((by decide : ¬ (11:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_13 (by decide +kernel) e (by omega)

theorem harmonic4_421 : Closed 4 4465125 84 9718956 13 := by
  apply closed_split (a:=17) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=13) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=1093) (v:=12) (by decide) (by decide) (by norm_num) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=1093) (v:=12) (by decide) (by decide) (by norm_num) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_17 (by decide +kernel) e (by omega)

theorem harmonic4_422 : Closed 4 540280125 252 1292621148 13 := by
  apply closed_split (a:=17) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=13) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=1093) (v:=12) (by decide) (by decide) (by norm_num) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_17 (by decide +kernel) e (by omega)

theorem harmonic4_423 : Closed 4 4465125 84 9718956 11 := by
  apply closed_split (a:=13) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_421
    · exact ((by decide : ¬ (11:ℕ)^1%4=1) hres).elim
    · exact harmonic4_422
    · exact ((by decide : ¬ (11:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_13 (by decide +kernel) e (by omega)

theorem harmonic4_424 : Closed 4 218791125 140 477592908 13 := by
  apply closed_split (a:=17) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=13) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=1093) (v:=12) (by decide) (by decide) (by norm_num) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_17 (by decide +kernel) e (by omega)

theorem harmonic4_425 : Closed 4 26473726125 420 63519856764 13 := by
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

theorem harmonic4_426 : Closed 4 218791125 140 477592908 11 := by
  apply closed_split (a:=13) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_424
    · exact ((by decide : ¬ (11:ℕ)^1%4=1) hres).elim
    · exact harmonic4_425
    · exact ((by decide : ¬ (11:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_13 (by decide +kernel) e (by omega)

theorem harmonic4_427 : Closed 4 91125 28 170508 7 := by
  apply closed_split (a:=11) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_420
    · exact ((by decide : ¬ (7:ℕ)^1%4=1) hres).elim
    · exact harmonic4_423
    · exact ((by decide : ¬ (7:ℕ)^3%4=1) hres).elim
    · exact harmonic4_426
    · exact ((by decide : ¬ (7:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_11 (by decide +kernel) e (by omega)

theorem harmonic4_428 : Closed 4 455625 35 853633 13 := by
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

theorem harmonic4_429 : Closed 4 55130625 105 113533189 13 := by
  apply closed_split (a:=17) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_nonempty (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_17 (by decide +kernel) e (by omega)

theorem harmonic4_430 : Closed 4 455625 35 853633 11 := by
  apply closed_split (a:=13) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_428
    · exact ((by decide : ¬ (11:ℕ)^1%4=1) hres).elim
    · exact harmonic4_429
    · exact ((by decide : ¬ (11:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_13 (by decide +kernel) e (by omega)

theorem harmonic4_431 : Closed 4 22325625 105 48657081 13 := by
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

theorem harmonic4_432 : Closed 4 2701400625 315 6471391773 13 := by
  apply closed_split (a:=17) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=71) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_17 (by decide +kernel) e (by omega)

theorem harmonic4_433 : Closed 4 22325625 105 48657081 11 := by
  apply closed_split (a:=13) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_431
    · exact ((by decide : ¬ (11:ℕ)^1%4=1) hres).elim
    · exact harmonic4_432
    · exact ((by decide : ¬ (11:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_13 (by decide +kernel) e (by omega)

theorem harmonic4_434 : Closed 4 1093955625 175 2391026033 13 := by
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

theorem harmonic4_435 : Closed 4 1093955625 175 2391026033 11 := by
  apply closed_split (a:=13) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_434
    · exact ((by decide : ¬ (11:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_13 (by decide +kernel) e (by omega)

theorem harmonic4_436 : Closed 4 455625 35 853633 7 := by
  apply closed_split (a:=11) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_430
    · exact ((by decide : ¬ (7:ℕ)^1%4=1) hres).elim
    · exact harmonic4_433
    · exact ((by decide : ¬ (7:ℕ)^3%4=1) hres).elim
    · exact harmonic4_435
    · exact ((by decide : ¬ (7:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_11 (by decide +kernel) e (by omega)

theorem harmonic4_437 : Closed 4 2278125 42 4269258 13 := by
  apply closed_split (a:=17) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=31) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=31) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_17 (by decide +kernel) e (by omega)

theorem harmonic4_438 : Closed 4 275653125 126 567811314 13 := by
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

theorem harmonic4_439 : Closed 4 2278125 42 4269258 11 := by
  apply closed_split (a:=13) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_437
    · exact ((by decide : ¬ (11:ℕ)^1%4=1) hres).elim
    · exact harmonic4_438
    · exact ((by decide : ¬ (11:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_13 (by decide +kernel) e (by omega)

end OddPerfect.HarmonicSearch
