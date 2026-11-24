module

public import OddPerfect.DivisorCount4.Envelopes
import Mathlib.Tactic.IntervalCases

public section

namespace OddPerfect.DivisorCountSearch

theorem node4_0 : Closed 4 883086389887727026 1295119365014475 9216 43 := by
  apply closed_of_split (a:=47) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_nonempty (k:=38) (s:=7) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_47_4_1 (by decide +kernel) e (by omega)

theorem node4_1 : Closed 4 883086389887727026 31588277195475 4608 41 := by
  apply closed_of_split (a:=43) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_43_38_7 (by decide +kernel)
    · exact node4_0
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_43_4_1 (by decide +kernel) e (by omega)

theorem node4_2 : Closed 4 883086389887727026 1168766256232575 9216 47 := by
  apply closed_of_split (a:=53) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_nonempty (k:=38) (s:=7) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_53_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_53_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_53_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_53_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_53_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_53_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_53_4_1 (by decide +kernel) e (by omega)

theorem node4_3 : Closed 4 883086389887727026 1168766256232575 9216 43 := by
  apply closed_of_split (a:=47) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact node4_2
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_47_4_1 (by decide +kernel) e (by omega)

theorem node4_4 : Closed 4 883086389887727026 1168766256232575 9216 41 := by
  apply closed_of_split (a:=43) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact node4_3
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_43_4_1 (by decide +kernel) e (by omega)

theorem node4_5 : Closed 4 883086389887727026 31588277195475 4608 37 := by
  apply closed_of_split (a:=41) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact node4_1
    · exact node4_4
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_41_4_1 (by decide +kernel) e (by omega)

theorem node4_6 : Closed 4 883086389887727026 1018976683725 2304 31 := by
  apply closed_of_split (a:=37) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_37_38_7 (by decide +kernel)
    · exact node4_5
    · exact close_envelope (by decide) (by decide) bound4_37_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_37_4_1 (by decide +kernel) e (by omega)

theorem node4_7 : Closed 4 883086389887727026 35137127025 1152 29 := by
  apply closed_of_split (a:=31) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_31_38_7 (by decide +kernel)
    · exact node4_6
    · exact close_envelope (by decide) (by decide) bound4_31_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_31_4_1 (by decide +kernel) e (by omega)

theorem node4_8 : Closed 4 883086389887727026 1527701175 576 23 := by
  apply closed_of_split (a:=29) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_29_38_7 (by decide +kernel)
    · exact node4_7
    · exact close_envelope (by decide) (by decide) bound4_29_5_1 (by decide +kernel)
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_29_4_1 (by decide +kernel) e (by omega)

theorem node4_9 : Closed 4 883086389887727026 80405325 288 19 := by
  apply closed_of_split (a:=23) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_23_38_7 (by decide +kernel)
    · exact node4_8
    · exact close_envelope (by decide) (by decide) bound4_23_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_23_4_1 (by decide +kernel) e (by omega)

theorem node4_10 : Closed 4 883086389887727026 4729725 144 17 := by
  apply closed_of_split (a:=19) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_19_38_7 (by decide +kernel)
    · exact node4_9
    · exact close_envelope (by decide) (by decide) bound4_19_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_19_4_1 (by decide +kernel) e (by omega)

theorem node4_11 : Closed 4 883086389887727026 363825 72 13 := by
  apply closed_of_split (a:=17) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_17_5_1 (by decide +kernel)
    · exact node4_10
    · exact close_envelope (by decide) (by decide) bound4_17_38_7 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_17_4_1 (by decide +kernel) e (by omega)

theorem node4_12 : Closed 4 883086389887727026 33075 36 11 := by
  apply closed_of_split (a:=13) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_13_5_1 (by decide +kernel)
    · exact node4_11
    · exact close_envelope (by decide) (by decide) bound4_13_38_7 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_13_4_1 (by decide +kernel) e (by omega)

theorem node4_13 : Closed 4 883086389887727026 675 12 7 := by
  apply closed_of_split (a:=11) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_11_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_11_38_7 (by decide +kernel)
    · exact node4_12
    · exact close_envelope (by decide) (by decide) bound4_11_38_7 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_11_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_11_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_11_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_11_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_11_4_1 (by decide +kernel) e (by omega)

theorem node4_14 : Closed 4 883086389887727026 5843831281162875 12288 43 := by
  apply closed_of_split (a:=47) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_nonempty (k:=38) (s:=7) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_47_4_1 (by decide +kernel) e (by omega)

theorem node4_15 : Closed 4 883086389887727026 5843831281162875 12288 41 := by
  apply closed_of_split (a:=43) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact node4_14
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_43_4_1 (by decide +kernel) e (by omega)

theorem node4_16 : Closed 4 883086389887727026 157941385977375 6144 37 := by
  apply closed_of_split (a:=41) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_41_38_7 (by decide +kernel)
    · exact node4_15
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_41_4_1 (by decide +kernel) e (by omega)

theorem node4_17 : Closed 4 883086389887727026 5094883418625 3072 31 := by
  apply closed_of_split (a:=37) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_37_38_7 (by decide +kernel)
    · exact node4_16
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_37_4_1 (by decide +kernel) e (by omega)

theorem node4_18 : Closed 4 883086389887727026 175685635125 1536 29 := by
  apply closed_of_split (a:=31) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_31_38_7 (by decide +kernel)
    · exact node4_17
    · exact close_envelope (by decide) (by decide) bound4_31_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_31_4_1 (by decide +kernel) e (by omega)

theorem node4_19 : Closed 4 883086389887727026 7638505875 768 23 := by
  apply closed_of_split (a:=29) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_29_38_7 (by decide +kernel)
    · exact node4_18
    · exact close_envelope (by decide) (by decide) bound4_29_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_29_4_1 (by decide +kernel) e (by omega)

end OddPerfect.DivisorCountSearch
