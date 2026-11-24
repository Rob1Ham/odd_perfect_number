module

public import OddPerfect.DivisorCount2.Envelopes
import Mathlib.Tactic.IntervalCases

public section

namespace OddPerfect.DivisorCountSearch

theorem node2_0 : Closed 2 16 3 2 5 := by
  apply closed_of_split (a:=7) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_nonempty (k:=2) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_nonempty (k:=2) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound2_7_2_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound2_7_2_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound2_7_2_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound2_7_2_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound2_7_2_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound2_7_2_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound2_7_2_1 (by decide +kernel) e (by omega)

theorem node2_1 : Closed 2 16 1 1 3 := by
  apply closed_of_split (a:=5) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound2_5_2_1 (by decide +kernel)
    · exact node2_0
    · exact close_envelope (by decide) (by decide) bound2_5_2_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound2_5_2_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound2_5_2_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound2_5_2_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound2_5_2_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound2_5_2_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound2_5_2_1 (by decide +kernel) e (by omega)

end OddPerfect.DivisorCountSearch
