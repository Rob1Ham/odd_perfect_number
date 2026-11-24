module

public import OddPerfect.HarmonicCount3.Envelopes
import Mathlib.Tactic.IntervalCases

public section

namespace OddPerfect.HarmonicSearch

open DivisorCountSearch

theorem harmonic3_0 : Closed 3 1 1 1 7 := by
  apply closed_split (a:=11) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_by_moment envH3_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH3_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH3_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH3_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH3_11 (by decide +kernel) e (by omega)

theorem harmonic3_1 : Closed 3 5 2 6 7 := by
  apply closed_split (a:=11) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=3) (v:=2) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH3_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH3_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH3_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH3_11 (by decide +kernel) e (by omega)

theorem harmonic3_2 : Closed 3 25 3 31 7 := by
  apply closed_split (a:=11) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_nonempty (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH3_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH3_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH3_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH3_11 (by decide +kernel) e (by omega)

theorem harmonic3_3 : Closed 3 1 1 1 5 := by
  apply closed_split (a:=7) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic3_0
    · exact harmonic3_1
    · exact harmonic3_2
    · exact closed_by_moment envH3_7 (by decide +kernel)
    · exact closed_by_moment envH3_7 (by decide +kernel)
    · exact closed_by_moment envH3_7 (by decide +kernel)
    · exact closed_by_moment envH3_7 (by decide +kernel)
    · exact closed_by_moment envH3_7 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH3_7 (by decide +kernel) e (by omega)

theorem harmonic3_4 : Closed 3 9 3 13 13 := by
  apply closed_split (a:=17) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=13) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_nonempty (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH3_17 (by decide +kernel)
    · exact closed_by_moment envH3_17 (by decide +kernel)
    · exact closed_by_moment envH3_17 (by decide +kernel)
    · exact closed_by_moment envH3_17 (by decide +kernel)
    · exact closed_by_moment envH3_17 (by decide +kernel)
    · exact closed_by_moment envH3_17 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH3_17 (by decide +kernel) e (by omega)

theorem harmonic3_5 : Closed 3 9 3 13 11 := by
  apply closed_split (a:=13) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic3_4
    · exact ((by decide : ¬ (11:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH3_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH3_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH3_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH3_13 (by decide +kernel) e (by omega)

theorem harmonic3_6 : Closed 3 9 3 13 7 := by
  apply closed_split (a:=11) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic3_5
    · exact ((by decide : ¬ (7:ℕ)^1%4=1) hres).elim
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH3_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH3_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH3_11 (by decide +kernel) e (by omega)

theorem harmonic3_7 : Closed 3 45 6 78 13 := by
  apply closed_split (a:=17) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=13) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=7) (v:=6) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH3_17 (by decide +kernel)
    · exact closed_by_moment envH3_17 (by decide +kernel)
    · exact closed_by_moment envH3_17 (by decide +kernel)
    · exact closed_by_moment envH3_17 (by decide +kernel)
    · exact closed_by_moment envH3_17 (by decide +kernel)
    · exact closed_by_moment envH3_17 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH3_17 (by decide +kernel) e (by omega)

theorem harmonic3_8 : Closed 3 45 6 78 11 := by
  apply closed_split (a:=13) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic3_7
    · exact ((by decide : ¬ (11:ℕ)^1%4=1) hres).elim
    · exact closed_nonempty (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH3_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH3_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH3_13 (by decide +kernel) e (by omega)

theorem harmonic3_9 : Closed 3 45 6 78 7 := by
  apply closed_split (a:=11) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic3_8
    · exact ((by decide : ¬ (7:ℕ)^1%4=1) hres).elim
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH3_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH3_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH3_11 (by decide +kernel) e (by omega)

theorem harmonic3_10 : Closed 3 225 9 403 7 := by
  apply closed_split (a:=11) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=31) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^1%4=1) hres).elim
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH3_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH3_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH3_11 (by decide +kernel) e (by omega)

theorem harmonic3_11 : Closed 3 1125 12 2028 7 := by
  apply closed_split (a:=11) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=13) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH3_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH3_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH3_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH3_11 (by decide +kernel) e (by omega)

theorem harmonic3_12 : Closed 3 9 3 13 5 := by
  apply closed_split (a:=7) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic3_6
    · exact harmonic3_9
    · exact harmonic3_10
    · exact harmonic3_11
    · exact closed_by_moment envH3_7 (by decide +kernel)
    · exact closed_by_moment envH3_7 (by decide +kernel)
    · exact closed_by_moment envH3_7 (by decide +kernel)
    · exact closed_by_moment envH3_7 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH3_7 (by decide +kernel) e (by omega)

theorem harmonic3_13 : Closed 3 81 5 121 7 := by
  apply closed_split (a:=11) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=11) (v:=10) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH3_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH3_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH3_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH3_11 (by decide +kernel) e (by omega)

theorem harmonic3_14 : Closed 3 405 10 726 7 := by
  apply closed_split (a:=11) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=11) (v:=10) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^1%4=1) hres).elim
    · exact closed_nonempty (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH3_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH3_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH3_11 (by decide +kernel) e (by omega)

theorem harmonic3_15 : Closed 3 2025 15 3751 7 := by
  apply closed_split (a:=11) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=11) (v:=10) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH3_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH3_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH3_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH3_11 (by decide +kernel) e (by omega)

theorem harmonic3_16 : Closed 3 81 5 121 5 := by
  apply closed_split (a:=7) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic3_13
    · exact harmonic3_14
    · exact harmonic3_15
    · exact closed_by_moment envH3_7 (by decide +kernel)
    · exact closed_by_moment envH3_7 (by decide +kernel)
    · exact closed_by_moment envH3_7 (by decide +kernel)
    · exact closed_by_moment envH3_7 (by decide +kernel)
    · exact closed_by_moment envH3_7 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH3_7 (by decide +kernel) e (by omega)

theorem harmonic3_17 : Closed 3 1 1 1 3 := by
  apply closed_split (a:=5) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic3_3
    · exact ((by decide : ¬ (3:ℕ)^1%4=1) hres).elim
    · exact harmonic3_12
    · exact ((by decide : ¬ (3:ℕ)^3%4=1) hres).elim
    · exact harmonic3_16
    · exact ((by decide : ¬ (3:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH3_5 (by decide +kernel)
    · exact ((by decide : ¬ (3:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH3_5 (by decide +kernel) e (by omega)

end OddPerfect.HarmonicSearch
