module

public import OddPerfect.HarmonicCount4.Part05
import Mathlib.Tactic.IntervalCases

public section

namespace OddPerfect.HarmonicSearch

open DivisorCountSearch

theorem harmonic4_100 : Closed 4 7605 18 14274 31 := by
  apply closed_split (a:=37) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_99
    · exact ((by decide : ¬ (31:ℕ)^1%4=1) hres).elim
    · exact closed_nonempty (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (31:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_37 (by decide +kernel)
    · exact ((by decide : ¬ (31:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_37 (by decide +kernel)
    · exact ((by decide : ¬ (31:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_37 (by decide +kernel) e (by omega)

theorem harmonic4_101 : Closed 4 220545 36 428220 61 := by
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

theorem harmonic4_102 : Closed 4 220545 36 428220 59 := by
  apply closed_split (a:=61) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_101
    · exact ((by decide : ¬ (59:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_61 (by decide +kernel)
    · exact ((by decide : ¬ (59:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_61 (by decide +kernel)
    · exact ((by decide : ¬ (59:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_61 (by decide +kernel)
    · exact ((by decide : ¬ (59:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_61 (by decide +kernel) e (by omega)

theorem harmonic4_103 : Closed 4 220545 36 428220 53 := by
  apply closed_split (a:=59) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_102
    · exact closed_nonempty (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_59 (by decide +kernel) e (by omega)

theorem harmonic4_104 : Closed 4 220545 36 428220 47 := by
  apply closed_split (a:=53) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_103
    · exact ((by decide : ¬ (47:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_53 (by decide +kernel)
    · exact ((by decide : ¬ (47:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_53 (by decide +kernel)
    · exact ((by decide : ¬ (47:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_53 (by decide +kernel)
    · exact ((by decide : ¬ (47:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_53 (by decide +kernel) e (by omega)

theorem harmonic4_105 : Closed 4 220545 36 428220 43 := by
  apply closed_split (a:=47) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_104
    · exact ((by decide : ¬ (43:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_47 (by decide +kernel)
    · exact ((by decide : ¬ (43:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_47 (by decide +kernel)
    · exact ((by decide : ¬ (43:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_47 (by decide +kernel)
    · exact ((by decide : ¬ (43:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_47 (by decide +kernel) e (by omega)

theorem harmonic4_106 : Closed 4 220545 36 428220 41 := by
  apply closed_split (a:=43) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_105
    · exact closed_owed_prime (r:=7) (v:=6) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_43 (by decide +kernel) e (by omega)

theorem harmonic4_107 : Closed 4 220545 36 428220 37 := by
  apply closed_split (a:=41) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_106
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_41 (by decide +kernel)
    · exact closed_by_moment envH4_41 (by decide +kernel)
    · exact closed_by_moment envH4_41 (by decide +kernel)
    · exact closed_by_moment envH4_41 (by decide +kernel)
    · exact closed_by_moment envH4_41 (by decide +kernel)
    · exact closed_by_moment envH4_41 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_41 (by decide +kernel) e (by omega)

theorem harmonic4_108 : Closed 4 220545 36 428220 31 := by
  apply closed_split (a:=37) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_107
    · exact ((by decide : ¬ (31:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_37 (by decide +kernel)
    · exact ((by decide : ¬ (31:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_37 (by decide +kernel)
    · exact ((by decide : ¬ (31:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_37 (by decide +kernel)
    · exact ((by decide : ¬ (31:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_37 (by decide +kernel) e (by omega)

theorem harmonic4_109 : Closed 4 7605 18 14274 29 := by
  apply closed_split (a:=31) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_100
    · exact harmonic4_108
    · exact closed_nonempty (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_31 (by decide +kernel)
    · exact closed_by_moment envH4_31 (by decide +kernel)
    · exact closed_by_moment envH4_31 (by decide +kernel)
    · exact closed_by_moment envH4_31 (by decide +kernel)
    · exact closed_by_moment envH4_31 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_31 (by decide +kernel) e (by omega)

theorem harmonic4_110 : Closed 4 7605 18 14274 23 := by
  apply closed_split (a:=29) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_109
    · exact ((by decide : ¬ (23:ℕ)^1%4=1) hres).elim
    · exact closed_owed_prime (r:=7) (v:=6) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (23:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_29 (by decide +kernel)
    · exact ((by decide : ¬ (23:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_29 (by decide +kernel)
    · exact ((by decide : ¬ (23:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_29 (by decide +kernel) e (by omega)

theorem harmonic4_111 : Closed 4 7605 18 14274 19 := by
  apply closed_split (a:=23) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_110
    · exact ((by decide : ¬ (19:ℕ)^1%4=1) hres).elim
    · exact closed_owed_prime (r:=61) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_23 (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_23 (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_23 (by decide +kernel) e (by omega)

theorem harmonic4_112 : Closed 4 129285 36 256932 61 := by
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

theorem harmonic4_113 : Closed 4 129285 36 256932 59 := by
  apply closed_split (a:=61) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_112
    · exact ((by decide : ¬ (59:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_61 (by decide +kernel)
    · exact ((by decide : ¬ (59:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_61 (by decide +kernel)
    · exact ((by decide : ¬ (59:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_61 (by decide +kernel)
    · exact ((by decide : ¬ (59:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_61 (by decide +kernel) e (by omega)

theorem harmonic4_114 : Closed 4 6852105 72 13874328 61 := by
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

theorem harmonic4_115 : Closed 4 6852105 72 13874328 59 := by
  apply closed_split (a:=61) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_114
    · exact ((by decide : ¬ (59:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_61 (by decide +kernel)
    · exact ((by decide : ¬ (59:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_61 (by decide +kernel)
    · exact ((by decide : ¬ (59:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_61 (by decide +kernel)
    · exact ((by decide : ¬ (59:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_61 (by decide +kernel) e (by omega)

theorem harmonic4_116 : Closed 4 129285 36 256932 53 := by
  apply closed_split (a:=59) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_113
    · exact harmonic4_115
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_59 (by decide +kernel) e (by omega)

theorem harmonic4_117 : Closed 4 129285 36 256932 47 := by
  apply closed_split (a:=53) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_116
    · exact ((by decide : ¬ (47:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_53 (by decide +kernel)
    · exact ((by decide : ¬ (47:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_53 (by decide +kernel)
    · exact ((by decide : ¬ (47:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_53 (by decide +kernel)
    · exact ((by decide : ¬ (47:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_53 (by decide +kernel) e (by omega)

theorem harmonic4_118 : Closed 4 129285 36 256932 43 := by
  apply closed_split (a:=47) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_117
    · exact ((by decide : ¬ (43:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_47 (by decide +kernel)
    · exact ((by decide : ¬ (43:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_47 (by decide +kernel)
    · exact ((by decide : ¬ (43:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_47 (by decide +kernel)
    · exact ((by decide : ¬ (43:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_47 (by decide +kernel) e (by omega)

theorem harmonic4_119 : Closed 4 129285 36 256932 41 := by
  apply closed_split (a:=43) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_118
    · exact closed_owed_prime (r:=7) (v:=6) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_43 (by decide +kernel) e (by omega)

end OddPerfect.HarmonicSearch
