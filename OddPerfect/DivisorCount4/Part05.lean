module

public import OddPerfect.DivisorCount4.Part04
import Mathlib.Tactic.IntervalCases

public section

namespace OddPerfect.DivisorCountSearch

theorem node4_80 : Closed 4 883086389887727026 10125 20 7 := by
  apply closed_of_split (a:=11) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_11_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_11_38_7 (by decide +kernel)
    · exact node4_79
    · exact close_envelope (by decide) (by decide) bound4_11_38_7 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_11_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_11_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_11_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_11_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_11_4_1 (by decide +kernel) e (by omega)

theorem node4_81 : Closed 4 883086389887727026 81 5 5 := by
  apply closed_of_split (a:=7) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_7_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_7_38_7 (by decide +kernel)
    · exact node4_58
    · exact node4_80
    · exact close_envelope (by decide) (by decide) bound4_7_38_7 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_7_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_7_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_7_5_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_7_4_1 (by decide +kernel) e (by omega)

theorem node4_82 : Closed 4 883086389887727026 11656074285130275 13824 43 := by
  apply closed_of_split (a:=47) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_nonempty (k:=5) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_47_4_1 (by decide +kernel) e (by omega)

theorem node4_83 : Closed 4 883086389887727026 284294494759275 6912 41 := by
  apply closed_of_split (a:=43) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_43_38_7 (by decide +kernel)
    · exact node4_82
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_43_4_1 (by decide +kernel) e (by omega)

theorem node4_84 : Closed 4 883086389887727026 10518896306093175 13824 47 := by
  apply closed_of_split (a:=53) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_nonempty (k:=5) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_53_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_53_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_53_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_53_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_53_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_53_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_53_4_1 (by decide +kernel) e (by omega)

theorem node4_85 : Closed 4 883086389887727026 10518896306093175 13824 43 := by
  apply closed_of_split (a:=47) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact node4_84
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_47_4_1 (by decide +kernel) e (by omega)

theorem node4_86 : Closed 4 883086389887727026 10518896306093175 13824 41 := by
  apply closed_of_split (a:=43) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact node4_85
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_43_4_1 (by decide +kernel) e (by omega)

theorem node4_87 : Closed 4 883086389887727026 284294494759275 6912 37 := by
  apply closed_of_split (a:=41) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact node4_83
    · exact node4_86
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_41_4_1 (by decide +kernel) e (by omega)

theorem node4_88 : Closed 4 883086389887727026 9170790153525 3456 31 := by
  apply closed_of_split (a:=37) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_37_38_7 (by decide +kernel)
    · exact node4_87
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_37_4_1 (by decide +kernel) e (by omega)

theorem node4_89 : Closed 4 883086389887727026 316234143225 1728 29 := by
  apply closed_of_split (a:=31) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_31_38_7 (by decide +kernel)
    · exact node4_88
    · exact close_envelope (by decide) (by decide) bound4_31_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_31_4_1 (by decide +kernel) e (by omega)

theorem node4_90 : Closed 4 883086389887727026 13749310575 864 23 := by
  apply closed_of_split (a:=29) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_29_38_7 (by decide +kernel)
    · exact node4_89
    · exact close_envelope (by decide) (by decide) bound4_29_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_29_4_1 (by decide +kernel) e (by omega)

theorem node4_91 : Closed 4 883086389887727026 723647925 432 19 := by
  apply closed_of_split (a:=23) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_23_38_7 (by decide +kernel)
    · exact node4_90
    · exact close_envelope (by decide) (by decide) bound4_23_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_23_4_1 (by decide +kernel) e (by omega)

theorem node4_92 : Closed 4 883086389887727026 42567525 216 17 := by
  apply closed_of_split (a:=19) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_19_5_1 (by decide +kernel)
    · exact node4_91
    · exact close_envelope (by decide) (by decide) bound4_19_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_19_4_1 (by decide +kernel) e (by omega)

theorem node4_93 : Closed 4 883086389887727026 3274425 108 13 := by
  apply closed_of_split (a:=17) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_17_5_1 (by decide +kernel)
    · exact node4_92
    · exact close_envelope (by decide) (by decide) bound4_17_38_7 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_17_4_1 (by decide +kernel) e (by omega)

theorem node4_94 : Closed 4 883086389887727026 297675 54 11 := by
  apply closed_of_split (a:=13) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_13_5_1 (by decide +kernel)
    · exact node4_93
    · exact close_envelope (by decide) (by decide) bound4_13_38_7 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_13_4_1 (by decide +kernel) e (by omega)

theorem node4_95 : Closed 4 883086389887727026 6075 18 7 := by
  apply closed_of_split (a:=11) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_11_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_11_38_7 (by decide +kernel)
    · exact node4_94
    · exact close_envelope (by decide) (by decide) bound4_11_38_7 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_11_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_11_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_11_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_11_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_11_4_1 (by decide +kernel) e (by omega)

theorem node4_96 : Closed 4 883086389887727026 1421472473796375 9216 37 := by
  apply closed_of_split (a:=41) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_41_38_7 (by decide +kernel)
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_41_4_1 (by decide +kernel) e (by omega)

theorem node4_97 : Closed 4 883086389887727026 45853950767625 4608 31 := by
  apply closed_of_split (a:=37) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_37_38_7 (by decide +kernel)
    · exact node4_96
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_37_4_1 (by decide +kernel) e (by omega)

theorem node4_98 : Closed 4 883086389887727026 1581170716125 2304 29 := by
  apply closed_of_split (a:=31) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_31_38_7 (by decide +kernel)
    · exact node4_97
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_31_4_1 (by decide +kernel) e (by omega)

theorem node4_99 : Closed 4 883086389887727026 68746552875 1152 23 := by
  apply closed_of_split (a:=29) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_29_38_7 (by decide +kernel)
    · exact node4_98
    · exact close_envelope (by decide) (by decide) bound4_29_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_29_4_1 (by decide +kernel) e (by omega)

end OddPerfect.DivisorCountSearch
