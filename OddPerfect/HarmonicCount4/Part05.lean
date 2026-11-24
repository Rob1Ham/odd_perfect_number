module

public import OddPerfect.HarmonicCount4.Part04
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

namespace OddPerfect.HarmonicSearch

open DivisorCountSearch

theorem harmonic4_80 : Closed 4 11792781 108 24835356 19 := by
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

theorem harmonic4_81 : Closed 4 693693 54 1379742 17 := by
  apply closed_split (a:=19) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_79
    · exact harmonic4_80
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_19 (by decide +kernel)
    · exact closed_by_moment envH4_19 (by decide +kernel)
    · exact closed_by_moment envH4_19 (by decide +kernel)
    · exact closed_by_moment envH4_19 (by decide +kernel)
    · exact closed_by_moment envH4_19 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_19 (by decide +kernel) e (by omega)

theorem harmonic4_82 : Closed 4 9018009 81 18035199 19 := by
  apply closed_split (a:=23) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^1%4=1) hres).elim
    · exact closed_nonempty (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_23 (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_23 (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_23 (by decide +kernel) e (by omega)

theorem harmonic4_83 : Closed 4 153306153 162 324633582 19 := by
  apply closed_split (a:=23) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^1%4=1) hres).elim
    · exact closed_nonempty (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_23 (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_23 (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_23 (by decide +kernel) e (by omega)

theorem harmonic4_84 : Closed 4 9018009 81 18035199 17 := by
  apply closed_split (a:=19) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_82
    · exact harmonic4_83
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_19 (by decide +kernel)
    · exact closed_by_moment envH4_19 (by decide +kernel)
    · exact closed_by_moment envH4_19 (by decide +kernel)
    · exact closed_by_moment envH4_19 (by decide +kernel)
    · exact closed_by_moment envH4_19 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_19 (by decide +kernel) e (by omega)

theorem harmonic4_85 : Closed 4 53361 27 98553 13 := by
  apply closed_split (a:=17) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=13) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact harmonic4_81
    · exact harmonic4_84
    · exact closed_owed_prime (r:=5) (v:=4) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_17 (by decide +kernel) e (by omega)

theorem harmonic4_86 : Closed 4 441 9 741 11 := by
  apply closed_split (a:=13) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_78
    · exact ((by decide : ¬ (11:ℕ)^1%4=1) hres).elim
    · exact harmonic4_85
    · exact ((by decide : ¬ (11:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_13 (by decide +kernel) e (by omega)

theorem harmonic4_87 : Closed 4 21609 15 36413 13 := by
  apply closed_split (a:=17) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=13) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=2801) (v:=12) (by decide) (by decide) (by norm_num) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=61) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_17 (by decide +kernel) e (by omega)

theorem harmonic4_88 : Closed 4 2614689 45 4842929 13 := by
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

theorem harmonic4_89 : Closed 4 21609 15 36413 11 := by
  apply closed_split (a:=13) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_87
    · exact ((by decide : ¬ (11:ℕ)^1%4=1) hres).elim
    · exact harmonic4_88
    · exact ((by decide : ¬ (11:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_13 (by decide +kernel) e (by omega)

theorem harmonic4_90 : Closed 4 9 3 13 7 := by
  apply closed_split (a:=11) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_71
    · exact ((by decide : ¬ (7:ℕ)^1%4=1) hres).elim
    · exact harmonic4_86
    · exact ((by decide : ¬ (7:ℕ)^3%4=1) hres).elim
    · exact harmonic4_89
    · exact ((by decide : ¬ (7:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_11 (by decide +kernel)
    · exact ((by decide : ¬ (7:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_11 (by decide +kernel) e (by omega)

theorem harmonic4_91 : Closed 4 7605 18 14274 61 := by
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

theorem harmonic4_92 : Closed 4 7605 18 14274 59 := by
  apply closed_split (a:=61) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_91
    · exact ((by decide : ¬ (59:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_61 (by decide +kernel)
    · exact ((by decide : ¬ (59:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_61 (by decide +kernel)
    · exact ((by decide : ¬ (59:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_61 (by decide +kernel)
    · exact ((by decide : ¬ (59:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_61 (by decide +kernel) e (by omega)

theorem harmonic4_93 : Closed 4 403065 36 770796 61 := by
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

theorem harmonic4_94 : Closed 4 403065 36 770796 59 := by
  apply closed_split (a:=61) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_93
    · exact ((by decide : ¬ (59:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_61 (by decide +kernel)
    · exact ((by decide : ¬ (59:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_61 (by decide +kernel)
    · exact ((by decide : ¬ (59:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_61 (by decide +kernel)
    · exact ((by decide : ¬ (59:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_61 (by decide +kernel) e (by omega)

theorem harmonic4_95 : Closed 4 7605 18 14274 53 := by
  apply closed_split (a:=59) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_92
    · exact harmonic4_94
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_59 (by decide +kernel) e (by omega)

theorem harmonic4_96 : Closed 4 7605 18 14274 47 := by
  apply closed_split (a:=53) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_95
    · exact ((by decide : ¬ (47:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_53 (by decide +kernel)
    · exact ((by decide : ¬ (47:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_53 (by decide +kernel)
    · exact ((by decide : ¬ (47:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_53 (by decide +kernel)
    · exact ((by decide : ¬ (47:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_53 (by decide +kernel) e (by omega)

theorem harmonic4_97 : Closed 4 7605 18 14274 43 := by
  apply closed_split (a:=47) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_96
    · exact ((by decide : ¬ (43:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_47 (by decide +kernel)
    · exact ((by decide : ¬ (43:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_47 (by decide +kernel)
    · exact ((by decide : ¬ (43:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_47 (by decide +kernel)
    · exact ((by decide : ¬ (43:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_47 (by decide +kernel) e (by omega)

theorem harmonic4_98 : Closed 4 7605 18 14274 41 := by
  apply closed_split (a:=43) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_97
    · exact closed_owed_prime (r:=7) (v:=6) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_43 (by decide +kernel) e (by omega)

theorem harmonic4_99 : Closed 4 7605 18 14274 37 := by
  apply closed_split (a:=41) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_98
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_41 (by decide +kernel)
    · exact closed_by_moment envH4_41 (by decide +kernel)
    · exact closed_by_moment envH4_41 (by decide +kernel)
    · exact closed_by_moment envH4_41 (by decide +kernel)
    · exact closed_by_moment envH4_41 (by decide +kernel)
    · exact closed_by_moment envH4_41 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_41 (by decide +kernel) e (by omega)

end OddPerfect.HarmonicSearch
