module

public import OddPerfect.HarmonicCount4.Part25
import Mathlib.Tactic.IntervalCases

public section

namespace OddPerfect.HarmonicSearch

open DivisorCountSearch

theorem harmonic4_500 : Closed 4 361675125 132 787591116 11 := by
  apply closed_split (a:=13) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_499
    · exact ((by decide : ¬ (11:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_13 (by decide +kernel) e (by omega)

theorem harmonic4_501 : Closed 4 7381125 44 13817388 7 := by
  apply closed_split (a:=11) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_by_moment envH4_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^1%4=1) hres).elim
    · exact harmonic4_500
    · exact ((by decide : ¬ (7:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_11 (by decide +kernel) e (by omega)

theorem harmonic4_502 : Closed 4 36905625 55 69175513 7 := by
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

theorem harmonic4_503 : Closed 4 59049 11 88573 5 := by
  apply closed_split (a:=7) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_488
    · exact harmonic4_493
    · exact harmonic4_498
    · exact harmonic4_501
    · exact harmonic4_502
    · exact closed_by_moment envH4_7 (by decide +kernel)
    · exact closed_by_moment envH4_7 (by decide +kernel)
    · exact closed_by_moment envH4_7 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_7 (by decide +kernel) e (by omega)

theorem harmonic4_504 : Closed 4 1 1 1 3 := by
  apply closed_split (a:=5) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 12
  · interval_cases e
    · exact harmonic4_45
    · exact ((by decide : ¬ (3:ℕ)^1%4=1) hres).elim
    · exact harmonic4_285
    · exact ((by decide : ¬ (3:ℕ)^3%4=1) hres).elim
    · exact harmonic4_388
    · exact ((by decide : ¬ (3:ℕ)^5%4=1) hres).elim
    · exact harmonic4_447
    · exact ((by decide : ¬ (3:ℕ)^7%4=1) hres).elim
    · exact harmonic4_487
    · exact ((by decide : ¬ (3:ℕ)^9%4=1) hres).elim
    · exact harmonic4_503
    · exact ((by decide : ¬ (3:ℕ)^11%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=12) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_5 (by decide +kernel) e (by omega)

end OddPerfect.HarmonicSearch
