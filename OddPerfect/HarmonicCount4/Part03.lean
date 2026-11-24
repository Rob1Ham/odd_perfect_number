module

public import OddPerfect.HarmonicCount4.Part02
import Mathlib.Tactic.IntervalCases

public section

namespace OddPerfect.HarmonicSearch

open DivisorCountSearch

theorem harmonic4_40 : Closed 4 3705625 45 5920761 13 := by
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

theorem harmonic4_41 : Closed 4 30625 15 44517 11 := by
  apply closed_split (a:=13) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_39
    · exact ((by decide : ¬ (11:ℕ)^1%4=1) hres).elim
    · exact harmonic4_40
    · exact ((by decide : ¬ (11:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_13 (by decide +kernel) e (by omega)

theorem harmonic4_42 : Closed 4 625 5 781 7 := by
  apply closed_split (a:=11) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_38
    · exact ((by decide : ¬ (7:ℕ)^1%4=1) hres).elim
    · exact harmonic4_41
    · exact ((by decide : ¬ (7:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_11 (by decide +kernel) e (by omega)

theorem harmonic4_43 : Closed 4 153125 18 222642 11 := by
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

theorem harmonic4_44 : Closed 4 3125 6 3906 7 := by
  apply closed_split (a:=11) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_by_moment envH4_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^1%4=1) hres).elim
    · exact harmonic4_43
    · exact ((by decide : ¬ (7:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_11 (by decide +kernel) e (by omega)

theorem harmonic4_45 : Closed 4 1 1 1 5 := by
  apply closed_split (a:=7) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_5
    · exact harmonic4_20
    · exact harmonic4_29
    · exact harmonic4_36
    · exact harmonic4_42
    · exact harmonic4_44
    · exact closed_by_moment envH4_7 (by decide +kernel)
    · exact closed_by_moment envH4_7 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_7 (by decide +kernel) e (by omega)

theorem harmonic4_46 : Closed 4 1521 9 2379 61 := by
  apply closed_split (a:=67) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=61) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_nonempty (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_67 (by decide +kernel)
    · exact closed_by_moment envH4_67 (by decide +kernel)
    · exact closed_by_moment envH4_67 (by decide +kernel)
    · exact closed_by_moment envH4_67 (by decide +kernel)
    · exact closed_by_moment envH4_67 (by decide +kernel)
    · exact closed_by_moment envH4_67 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_67 (by decide +kernel) e (by omega)

theorem harmonic4_47 : Closed 4 1521 9 2379 59 := by
  apply closed_split (a:=61) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_46
    · exact ((by decide : ¬ (59:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_61 (by decide +kernel)
    · exact ((by decide : ¬ (59:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_61 (by decide +kernel)
    · exact ((by decide : ¬ (59:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_61 (by decide +kernel)
    · exact ((by decide : ¬ (59:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_61 (by decide +kernel) e (by omega)

theorem harmonic4_48 : Closed 4 1521 9 2379 53 := by
  apply closed_split (a:=59) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_47
    · exact closed_nonempty (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_59 (by decide +kernel) e (by omega)

theorem harmonic4_49 : Closed 4 1521 9 2379 47 := by
  apply closed_split (a:=53) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_48
    · exact ((by decide : ¬ (47:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_53 (by decide +kernel)
    · exact ((by decide : ¬ (47:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_53 (by decide +kernel)
    · exact ((by decide : ¬ (47:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_53 (by decide +kernel)
    · exact ((by decide : ¬ (47:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_53 (by decide +kernel) e (by omega)

theorem harmonic4_50 : Closed 4 1521 9 2379 43 := by
  apply closed_split (a:=47) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_49
    · exact ((by decide : ¬ (43:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_47 (by decide +kernel)
    · exact ((by decide : ¬ (43:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_47 (by decide +kernel)
    · exact ((by decide : ¬ (43:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_47 (by decide +kernel)
    · exact ((by decide : ¬ (43:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_47 (by decide +kernel) e (by omega)

theorem harmonic4_51 : Closed 4 1521 9 2379 41 := by
  apply closed_split (a:=43) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_50
    · exact closed_nonempty (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_43 (by decide +kernel) e (by omega)

theorem harmonic4_52 : Closed 4 1521 9 2379 37 := by
  apply closed_split (a:=41) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_51
    · exact closed_nonempty (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_41 (by decide +kernel)
    · exact closed_by_moment envH4_41 (by decide +kernel)
    · exact closed_by_moment envH4_41 (by decide +kernel)
    · exact closed_by_moment envH4_41 (by decide +kernel)
    · exact closed_by_moment envH4_41 (by decide +kernel)
    · exact closed_by_moment envH4_41 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_41 (by decide +kernel) e (by omega)

theorem harmonic4_53 : Closed 4 1521 9 2379 31 := by
  apply closed_split (a:=37) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_52
    · exact ((by decide : ¬ (31:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_37 (by decide +kernel)
    · exact ((by decide : ¬ (31:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_37 (by decide +kernel)
    · exact ((by decide : ¬ (31:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_37 (by decide +kernel)
    · exact ((by decide : ¬ (31:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_37 (by decide +kernel) e (by omega)

theorem harmonic4_54 : Closed 4 1521 9 2379 29 := by
  apply closed_split (a:=31) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_53
    · exact closed_owed_prime (r:=5) (v:=4) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_31 (by decide +kernel)
    · exact closed_by_moment envH4_31 (by decide +kernel)
    · exact closed_by_moment envH4_31 (by decide +kernel)
    · exact closed_by_moment envH4_31 (by decide +kernel)
    · exact closed_by_moment envH4_31 (by decide +kernel)
    · exact closed_by_moment envH4_31 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_31 (by decide +kernel) e (by omega)

theorem harmonic4_55 : Closed 4 1521 9 2379 23 := by
  apply closed_split (a:=29) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_54
    · exact ((by decide : ¬ (23:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_29 (by decide +kernel)
    · exact ((by decide : ¬ (23:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_29 (by decide +kernel)
    · exact ((by decide : ¬ (23:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_29 (by decide +kernel)
    · exact ((by decide : ¬ (23:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_29 (by decide +kernel) e (by omega)

theorem harmonic4_56 : Closed 4 1521 9 2379 19 := by
  apply closed_split (a:=23) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_55
    · exact ((by decide : ¬ (19:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_23 (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_23 (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_23 (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_23 (by decide +kernel) e (by omega)

theorem harmonic4_57 : Closed 4 25857 18 42822 61 := by
  apply closed_split (a:=67) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_nonempty (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_nonempty (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_67 (by decide +kernel)
    · exact closed_by_moment envH4_67 (by decide +kernel)
    · exact closed_by_moment envH4_67 (by decide +kernel)
    · exact closed_by_moment envH4_67 (by decide +kernel)
    · exact closed_by_moment envH4_67 (by decide +kernel)
    · exact closed_by_moment envH4_67 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_67 (by decide +kernel) e (by omega)

theorem harmonic4_58 : Closed 4 25857 18 42822 59 := by
  apply closed_split (a:=61) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_57
    · exact ((by decide : ¬ (59:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_61 (by decide +kernel)
    · exact ((by decide : ¬ (59:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_61 (by decide +kernel)
    · exact ((by decide : ¬ (59:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_61 (by decide +kernel)
    · exact ((by decide : ¬ (59:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_61 (by decide +kernel) e (by omega)

theorem harmonic4_59 : Closed 4 25857 18 42822 53 := by
  apply closed_split (a:=59) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_58
    · exact closed_nonempty (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_59 (by decide +kernel) e (by omega)

end OddPerfect.HarmonicSearch
