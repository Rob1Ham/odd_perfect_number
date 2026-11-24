module

public import OddPerfect.DivisorCount3.Part01
import Mathlib.Tactic.IntervalCases

public section

namespace OddPerfect.DivisorCountSearch

theorem node3_20 : Closed 3 883576 14175 30 11 := by
  apply closed_of_split (a:=13) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound3_13_4_1 (by decide +kernel)
    · exact close_nonempty (k:=3) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound3_13_3_1 (by decide +kernel) e (by omega)

theorem node3_21 : Closed 3 883576 2025 15 7 := by
  apply closed_of_split (a:=11) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound3_11_4_1 (by decide +kernel)
    · exact node3_20
    · exact close_envelope (by decide) (by decide) bound3_11_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_11_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_11_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_11_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_11_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_11_3_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound3_11_3_1 (by decide +kernel) e (by omega)

theorem node3_22 : Closed 3 883576 81 5 5 := by
  apply closed_of_split (a:=7) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound3_7_4_1 (by decide +kernel)
    · exact node3_19
    · exact node3_21
    · exact close_envelope (by decide) (by decide) bound3_7_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_7_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_7_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_7_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_7_3_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound3_7_3_1 (by decide +kernel) e (by omega)

theorem node3_23 : Closed 3 883576 1 1 3 := by
  apply closed_of_split (a:=5) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound3_5_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_5_4_1 (by decide +kernel)
    · exact node3_8
    · exact node3_16
    · exact node3_22
    · exact close_envelope (by decide) (by decide) bound3_5_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_5_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_5_3_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound3_5_3_1 (by decide +kernel) e (by omega)

end OddPerfect.DivisorCountSearch
