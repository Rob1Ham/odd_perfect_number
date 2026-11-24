module

public import OddPerfect.DivisorCount4.Part05
import Mathlib.Tactic.IntervalCases

public section

namespace OddPerfect.DivisorCountSearch

theorem node4_100 : Closed 4 883086389887727026 3618239625 576 19 := by
  apply closed_of_split (a:=23) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_23_5_1 (by decide +kernel)
    · exact node4_99
    · exact close_envelope (by decide) (by decide) bound4_23_5_1 (by decide +kernel)
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_23_4_1 (by decide +kernel) e (by omega)

theorem node4_101 : Closed 4 883086389887727026 212837625 288 17 := by
  apply closed_of_split (a:=19) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_19_5_1 (by decide +kernel)
    · exact node4_100
    · exact close_envelope (by decide) (by decide) bound4_19_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_19_4_1 (by decide +kernel) e (by omega)

theorem node4_102 : Closed 4 883086389887727026 16372125 144 13 := by
  apply closed_of_split (a:=17) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_17_5_1 (by decide +kernel)
    · exact node4_101
    · exact close_envelope (by decide) (by decide) bound4_17_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_17_4_1 (by decide +kernel) e (by omega)

theorem node4_103 : Closed 4 883086389887727026 1488375 72 11 := by
  apply closed_of_split (a:=13) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_13_5_1 (by decide +kernel)
    · exact node4_102
    · exact close_envelope (by decide) (by decide) bound4_13_38_7 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_13_4_1 (by decide +kernel) e (by omega)

theorem node4_104 : Closed 4 883086389887727026 30375 24 7 := by
  apply closed_of_split (a:=11) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_11_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_11_38_7 (by decide +kernel)
    · exact node4_103
    · exact close_envelope (by decide) (by decide) bound4_11_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_11_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_11_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_11_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_11_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_11_4_1 (by decide +kernel) e (by omega)

theorem node4_105 : Closed 4 883086389887727026 243 6 5 := by
  apply closed_of_split (a:=7) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_7_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_7_38_7 (by decide +kernel)
    · exact node4_95
    · exact node4_104
    · exact close_envelope (by decide) (by decide) bound4_7_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_7_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_7_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_7_5_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_7_4_1 (by decide +kernel) e (by omega)

theorem node4_106 : Closed 4 883086389887727026 1 1 3 := by
  apply closed_of_split (a:=5) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_5_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_5_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_5_38_7 (by decide +kernel)
    · exact node4_25
    · exact node4_81
    · exact node4_105
    · exact close_envelope (by decide) (by decide) bound4_5_38_7 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_5_5_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_5_5_1 (by decide +kernel) e (by omega)

end OddPerfect.DivisorCountSearch
