module

public import OddPerfect.HarmonicCount4.Part08
import Mathlib.Tactic.IntervalCases

public section

namespace OddPerfect.HarmonicSearch

open DivisorCountSearch

theorem harmonic4_160 : Closed 4 45 6 78 7 := by
  apply closed_split (a:=11) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_137
    · exact ((by decide : ¬ (7:ℕ)^1%4=1) hres).elim
    · exact harmonic4_155
    · exact ((by decide : ¬ (7:ℕ)^3%4=1) hres).elim
    · exact harmonic4_158
    · exact ((by decide : ¬ (7:ℕ)^5%4=1) hres).elim
    · exact harmonic4_159
    · exact ((by decide : ¬ (7:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_11 (by decide +kernel) e (by omega)

theorem harmonic4_161 : Closed 4 38025 27 73749 31 := by
  apply closed_split (a:=37) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=31) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (31:ℕ)^1%4=1) hres).elim
    · exact closed_nonempty (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (31:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_37 (by decide +kernel)
    · exact ((by decide : ¬ (31:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_37 (by decide +kernel)
    · exact ((by decide : ¬ (31:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_37 (by decide +kernel) e (by omega)

theorem harmonic4_162 : Closed 4 38025 27 73749 29 := by
  apply closed_split (a:=31) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_161
    · exact closed_owed_prime (r:=31) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_nonempty (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_31 (by decide +kernel)
    · exact closed_by_moment envH4_31 (by decide +kernel)
    · exact closed_by_moment envH4_31 (by decide +kernel)
    · exact closed_by_moment envH4_31 (by decide +kernel)
    · exact closed_by_moment envH4_31 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_31 (by decide +kernel) e (by omega)

theorem harmonic4_163 : Closed 4 38025 27 73749 23 := by
  apply closed_split (a:=29) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_162
    · exact ((by decide : ¬ (23:ℕ)^1%4=1) hres).elim
    · exact closed_owed_prime (r:=7) (v:=6) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (23:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_29 (by decide +kernel)
    · exact ((by decide : ¬ (23:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_29 (by decide +kernel)
    · exact ((by decide : ¬ (23:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_29 (by decide +kernel) e (by omega)

theorem harmonic4_164 : Closed 4 38025 27 73749 19 := by
  apply closed_split (a:=23) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_163
    · exact ((by decide : ¬ (19:ℕ)^1%4=1) hres).elim
    · exact closed_owed_prime (r:=31) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_23 (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_23 (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_23 (by decide +kernel) e (by omega)

theorem harmonic4_165 : Closed 4 646425 54 1327482 31 := by
  apply closed_split (a:=37) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=31) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (31:ℕ)^1%4=1) hres).elim
    · exact closed_nonempty (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (31:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_37 (by decide +kernel)
    · exact ((by decide : ¬ (31:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_37 (by decide +kernel)
    · exact ((by decide : ¬ (31:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_37 (by decide +kernel) e (by omega)

theorem harmonic4_166 : Closed 4 646425 54 1327482 29 := by
  apply closed_split (a:=31) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_165
    · exact closed_owed_prime (r:=31) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_nonempty (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_31 (by decide +kernel)
    · exact closed_by_moment envH4_31 (by decide +kernel)
    · exact closed_by_moment envH4_31 (by decide +kernel)
    · exact closed_by_moment envH4_31 (by decide +kernel)
    · exact closed_by_moment envH4_31 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_31 (by decide +kernel) e (by omega)

theorem harmonic4_167 : Closed 4 646425 54 1327482 23 := by
  apply closed_split (a:=29) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_166
    · exact ((by decide : ¬ (23:ℕ)^1%4=1) hres).elim
    · exact closed_owed_prime (r:=7) (v:=6) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (23:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_29 (by decide +kernel)
    · exact ((by decide : ¬ (23:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_29 (by decide +kernel)
    · exact ((by decide : ¬ (23:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_29 (by decide +kernel) e (by omega)

theorem harmonic4_168 : Closed 4 646425 54 1327482 19 := by
  apply closed_split (a:=23) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_167
    · exact ((by decide : ¬ (19:ℕ)^1%4=1) hres).elim
    · exact closed_owed_prime (r:=31) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_23 (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_23 (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_23 (by decide +kernel) e (by omega)

theorem harmonic4_169 : Closed 4 38025 27 73749 17 := by
  apply closed_split (a:=19) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_164
    · exact harmonic4_168
    · exact closed_owed_prime (r:=31) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_19 (by decide +kernel)
    · exact closed_by_moment envH4_19 (by decide +kernel)
    · exact closed_by_moment envH4_19 (by decide +kernel)
    · exact closed_by_moment envH4_19 (by decide +kernel)
    · exact closed_by_moment envH4_19 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_19 (by decide +kernel) e (by omega)

theorem harmonic4_170 : Closed 4 225 9 403 13 := by
  apply closed_split (a:=17) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=13) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=7) (v:=6) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact harmonic4_169
    · exact closed_owed_prime (r:=7) (v:=6) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_17 (by decide +kernel) e (by omega)

theorem harmonic4_171 : Closed 4 27225 27 53599 13 := by
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

theorem harmonic4_172 : Closed 4 3294225 45 6490315 13 := by
  apply closed_split (a:=17) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=13) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=7) (v:=6) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
    · exact closed_by_moment envH4_17 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_17 (by decide +kernel) e (by omega)

theorem harmonic4_173 : Closed 4 225 9 403 11 := by
  apply closed_split (a:=13) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_170
    · exact ((by decide : ¬ (11:ℕ)^1%4=1) hres).elim
    · exact harmonic4_171
    · exact ((by decide : ¬ (11:ℕ)^3%4=1) hres).elim
    · exact harmonic4_172
    · exact ((by decide : ¬ (11:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_13 (by decide +kernel)
    · exact ((by decide : ¬ (11:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_13 (by decide +kernel) e (by omega)

theorem harmonic4_174 : Closed 4 143325 54 321594 19 := by
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

theorem harmonic4_175 : Closed 4 2436525 108 5788692 19 := by
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

theorem harmonic4_176 : Closed 4 143325 54 321594 17 := by
  apply closed_split (a:=19) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_174
    · exact harmonic4_175
    · exact closed_owed_prime (r:=307) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_19 (by decide +kernel)
    · exact closed_by_moment envH4_19 (by decide +kernel)
    · exact closed_by_moment envH4_19 (by decide +kernel)
    · exact closed_by_moment envH4_19 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_19 (by decide +kernel) e (by omega)

theorem harmonic4_177 : Closed 4 1863225 81 4203693 19 := by
  apply closed_split (a:=23) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^1%4=1) hres).elim
    · exact closed_owed_prime (r:=31) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_23 (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_23 (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_23 (by decide +kernel) e (by omega)

theorem harmonic4_178 : Closed 4 31674825 162 75666474 19 := by
  apply closed_split (a:=23) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^1%4=1) hres).elim
    · exact closed_owed_prime (r:=31) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^3%4=1) hres).elim
    · exact closed_by_moment envH4_23 (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^5%4=1) hres).elim
    · exact closed_by_moment envH4_23 (by decide +kernel)
    · exact ((by decide : ¬ (19:ℕ)^7%4=1) hres).elim
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_23 (by decide +kernel) e (by omega)

theorem harmonic4_179 : Closed 4 1863225 81 4203693 17 := by
  apply closed_split (a:=19) (by decide) (by decide +kernel)
  intro e hres
  by_cases h : e < 8
  · interval_cases e
    · exact harmonic4_177
    · exact harmonic4_178
    · exact closed_owed_prime (r:=31) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_owed_prime (r:=19) (v:=12) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact closed_by_moment envH4_19 (by decide +kernel)
    · exact closed_by_moment envH4_19 (by decide +kernel)
    · exact closed_by_moment envH4_19 (by decide +kernel)
    · exact closed_by_moment envH4_19 (by decide +kernel)
  · apply closed_of_plain
    exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) envH4_19 (by decide +kernel) e (by omega)

end OddPerfect.HarmonicSearch
