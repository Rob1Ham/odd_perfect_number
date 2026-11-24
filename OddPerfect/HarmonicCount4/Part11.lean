module

public import OddPerfect.HarmonicCount4.Part10
import Mathlib.Tactic.IntervalCases

public section

namespace OddPerfect.HarmonicSearch

open DivisorCountSearch

theorem harmonic4_200 : Closed 4 190125 36 371124 41 := by
  apply closed_split (a:=43) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_199
    · exact closed_owed_prime (r:=7) (v:=6) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_43 (by decide +kernel) e (by omega)

theorem harmonic4_201 : Closed 4 190125 36 371124 37 := by
  apply closed_split (a:=41) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_200
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_41 (by decide +kernel)
    · exact closed_by_moment envH4_41 (by decide +kernel)
    · exact closed_by_moment envH4_41 (by decide +kernel)
    · exact closed_by_moment envH4_41 (by decide +kernel)
    · exact closed_by_moment envH4_41 (by decide +kernel)
    · exact closed_by_moment envH4_41 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_41 (by decide +kernel) e (by omega)

theorem harmonic4_202 : Closed 4 190125 36 371124 31 := by
  apply closed_split (a:=37) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_201
    · exact ((by decide : ¬ (31:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_37 (by decide +kernel)
    · exact ((by decide : ¬ (31:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_37 (by decide +kernel)
    · exact ((by decide : ¬ (31:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_37 (by decide +kernel)
    · exact ((by decide : ¬ (31:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_37 (by decide +kernel) e (by omega)

theorem harmonic4_203 : Closed 4 5513625 72 11133720 61 := by
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

theorem harmonic4_204 : Closed 4 5513625 72 11133720 59 := by
  apply closed_split (a:=61) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_203
    · exact ((by decide : ¬ (59:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_61 (by decide +kernel)
    · exact ((by decide : ¬ (59:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_61 (by decide +kernel)
    · exact ((by decide : ¬ (59:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_61 (by decide +kernel)
    · exact ((by decide : ¬ (59:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_61 (by decide +kernel) e (by omega)

theorem harmonic4_205 : Closed 4 5513625 72 11133720 53 := by
  apply closed_split (a:=59) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_204
    · exact closed_nonempty (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_59 (by decide +kernel) e (by omega)

theorem harmonic4_206 : Closed 4 5513625 72 11133720 47 := by
  apply closed_split (a:=53) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_205
    · exact ((by decide : ¬ (47:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_53 (by decide +kernel)
    · exact ((by decide : ¬ (47:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_53 (by decide +kernel)
    · exact ((by decide : ¬ (47:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_53 (by decide +kernel)
    · exact ((by decide : ¬ (47:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_53 (by decide +kernel) e (by omega)

theorem harmonic4_207 : Closed 4 5513625 72 11133720 43 := by
  apply closed_split (a:=47) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_206
    · exact ((by decide : ¬ (43:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_47 (by decide +kernel)
    · exact ((by decide : ¬ (43:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_47 (by decide +kernel)
    · exact ((by decide : ¬ (43:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_47 (by decide +kernel)
    · exact ((by decide : ¬ (43:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_47 (by decide +kernel) e (by omega)

theorem harmonic4_208 : Closed 4 5513625 72 11133720 41 := by
  apply closed_split (a:=43) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_207
    · exact closed_nonempty (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
    · exact closed_by_moment envH4_43 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_43 (by decide +kernel) e (by omega)

theorem harmonic4_209 : Closed 4 5513625 72 11133720 37 := by
  apply closed_split (a:=41) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_208
    · exact closed_nonempty (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_41 (by decide +kernel)
    · exact closed_by_moment envH4_41 (by decide +kernel)
    · exact closed_by_moment envH4_41 (by decide +kernel)
    · exact closed_by_moment envH4_41 (by decide +kernel)
    · exact closed_by_moment envH4_41 (by decide +kernel)
    · exact closed_by_moment envH4_41 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_41 (by decide +kernel) e (by omega)

theorem harmonic4_210 : Closed 4 5513625 72 11133720 31 := by
  apply closed_split (a:=37) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_209
    · exact ((by decide : ¬ (31:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_37 (by decide +kernel)
    · exact ((by decide : ¬ (31:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_37 (by decide +kernel)
    · exact ((by decide : ¬ (31:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_37 (by decide +kernel)
    · exact ((by decide : ¬ (31:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_37 (by decide +kernel) e (by omega)

theorem harmonic4_211 : Closed 4 190125 36 371124 29 := by
  apply closed_split (a:=31) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_202
    · exact harmonic4_210
    · exact closed_by_moment envH4_31 (by decide +kernel)
    · exact closed_by_moment envH4_31 (by decide +kernel)
    · exact closed_by_moment envH4_31 (by decide +kernel)
    · exact closed_by_moment envH4_31 (by decide +kernel)
    · exact closed_by_moment envH4_31 (by decide +kernel)
    · exact closed_by_moment envH4_31 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_31 (by decide +kernel) e (by omega)

theorem harmonic4_212 : Closed 4 190125 36 371124 23 := by
  apply closed_split (a:=29) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_211
    · exact ((by decide : ¬ (23:ℕ)^1%4=1) hres).elim
    · exact closed_nonempty (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (23:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_29 (by decide +kernel)
    · exact ((by decide : ¬ (23:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_29 (by decide +kernel)
    · exact ((by decide : ¬ (23:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_29 (by decide +kernel) e (by omega)

theorem harmonic4_213 : Closed 4 190125 36 371124 19 := by
  apply closed_split (a:=23) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_212
    · exact ((by decide : ¬ (19:ℕ)^1%4=1) hres).elim
    · exact closed_owed_prime (r:=61) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_23 (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_23 (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_23 (by decide +kernel) e (by omega)

theorem harmonic4_214 : Closed 4 3232125 72 6680232 61 := by
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

theorem harmonic4_215 : Closed 4 3232125 72 6680232 59 := by
  apply closed_split (a:=61) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_214
    · exact ((by decide : ¬ (59:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_61 (by decide +kernel)
    · exact ((by decide : ¬ (59:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_61 (by decide +kernel)
    · exact ((by decide : ¬ (59:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_61 (by decide +kernel)
    · exact ((by decide : ¬ (59:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_61 (by decide +kernel) e (by omega)

theorem harmonic4_216 : Closed 4 3232125 72 6680232 53 := by
  apply closed_split (a:=59) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_215
    · exact closed_nonempty (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
    · exact closed_by_moment envH4_59 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_59 (by decide +kernel) e (by omega)

theorem harmonic4_217 : Closed 4 3232125 72 6680232 47 := by
  apply closed_split (a:=53) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_216
    · exact ((by decide : ¬ (47:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_53 (by decide +kernel)
    · exact ((by decide : ¬ (47:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_53 (by decide +kernel)
    · exact ((by decide : ¬ (47:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_53 (by decide +kernel)
    · exact ((by decide : ¬ (47:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_53 (by decide +kernel) e (by omega)

theorem harmonic4_218 : Closed 4 3232125 72 6680232 43 := by
  apply closed_split (a:=47) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_217
    · exact ((by decide : ¬ (43:ℕ)^1%4=1) hres).elim
    · exact closed_by_moment envH4_47 (by decide +kernel)
    · exact ((by decide : ¬ (43:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_47 (by decide +kernel)
    · exact ((by decide : ¬ (43:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_47 (by decide +kernel)
    · exact ((by decide : ¬ (43:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_47 (by decide +kernel) e (by omega)

theorem harmonic4_219 : Closed 4 3232125 72 6680232 41 := by
  apply closed_split (a:=43) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_218
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
