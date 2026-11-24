module

public import OddPerfect.DivisorCount4.Part02
import Mathlib.Tactic.IntervalCases

public section

namespace OddPerfect.DivisorCountSearch

theorem node4_40 : Closed 4 883086389887727026 3506298768697725 11520 47 := by
  apply closed_of_split (a:=53) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_53_6_1 (by decide +kernel)
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_53_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_53_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_53_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_53_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_53_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_53_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_53_4_1 (by decide +kernel) e (by omega)

theorem node4_41 : Closed 4 883086389887727026 3506298768697725 11520 43 := by
  apply closed_of_split (a:=47) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact node4_40
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_47_4_1 (by decide +kernel) e (by omega)

theorem node4_42 : Closed 4 883086389887727026 3506298768697725 11520 41 := by
  apply closed_of_split (a:=43) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact node4_41
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_43_4_1 (by decide +kernel) e (by omega)

theorem node4_43 : Closed 4 883086389887727026 94764831586425 5760 37 := by
  apply closed_of_split (a:=41) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact node4_39
    · exact node4_42
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_41_4_1 (by decide +kernel) e (by omega)

theorem node4_44 : Closed 4 883086389887727026 3056930051175 2880 31 := by
  apply closed_of_split (a:=37) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_37_38_7 (by decide +kernel)
    · exact node4_43
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_37_4_1 (by decide +kernel) e (by omega)

theorem node4_45 : Closed 4 883086389887727026 105411381075 1440 29 := by
  apply closed_of_split (a:=31) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_31_38_7 (by decide +kernel)
    · exact node4_44
    · exact close_envelope (by decide) (by decide) bound4_31_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_31_4_1 (by decide +kernel) e (by omega)

theorem node4_46 : Closed 4 883086389887727026 4583103525 720 23 := by
  apply closed_of_split (a:=29) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_29_38_7 (by decide +kernel)
    · exact node4_45
    · exact close_envelope (by decide) (by decide) bound4_29_5_1 (by decide +kernel)
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_29_4_1 (by decide +kernel) e (by omega)

theorem node4_47 : Closed 4 883086389887727026 241215975 360 19 := by
  apply closed_of_split (a:=23) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_23_38_7 (by decide +kernel)
    · exact node4_46
    · exact close_envelope (by decide) (by decide) bound4_23_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_23_4_1 (by decide +kernel) e (by omega)

theorem node4_48 : Closed 4 883086389887727026 14189175 180 17 := by
  apply closed_of_split (a:=19) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_19_38_7 (by decide +kernel)
    · exact node4_47
    · exact close_envelope (by decide) (by decide) bound4_19_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_19_4_1 (by decide +kernel) e (by omega)

theorem node4_49 : Closed 4 883086389887727026 1091475 90 13 := by
  apply closed_of_split (a:=17) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_17_5_1 (by decide +kernel)
    · exact node4_48
    · exact close_envelope (by decide) (by decide) bound4_17_38_7 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_17_4_1 (by decide +kernel) e (by omega)

theorem node4_50 : Closed 4 883086389887727026 1042413147450675 8640 37 := by
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

theorem node4_51 : Closed 4 883086389887727026 33626230562925 4320 31 := by
  apply closed_of_split (a:=37) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_37_38_7 (by decide +kernel)
    · exact node4_50
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_37_4_1 (by decide +kernel) e (by omega)

theorem node4_52 : Closed 4 883086389887727026 1159525191825 2160 29 := by
  apply closed_of_split (a:=31) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_31_38_7 (by decide +kernel)
    · exact node4_51
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_31_4_1 (by decide +kernel) e (by omega)

theorem node4_53 : Closed 4 883086389887727026 50414138775 1080 23 := by
  apply closed_of_split (a:=29) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_29_38_7 (by decide +kernel)
    · exact node4_52
    · exact close_envelope (by decide) (by decide) bound4_29_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_29_4_1 (by decide +kernel) e (by omega)

theorem node4_54 : Closed 4 883086389887727026 2653375725 540 19 := by
  apply closed_of_split (a:=23) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_23_5_1 (by decide +kernel)
    · exact node4_53
    · exact close_envelope (by decide) (by decide) bound4_23_5_1 (by decide +kernel)
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_23_4_1 (by decide +kernel) e (by omega)

theorem node4_55 : Closed 4 883086389887727026 156080925 270 17 := by
  apply closed_of_split (a:=19) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_19_5_1 (by decide +kernel)
    · exact node4_54
    · exact close_envelope (by decide) (by decide) bound4_19_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_19_4_1 (by decide +kernel) e (by omega)

theorem node4_56 : Closed 4 883086389887727026 12006225 135 13 := by
  apply closed_of_split (a:=17) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_17_5_1 (by decide +kernel)
    · exact node4_55
    · exact close_envelope (by decide) (by decide) bound4_17_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_17_4_1 (by decide +kernel) e (by omega)

theorem node4_57 : Closed 4 883086389887727026 99225 45 11 := by
  apply closed_of_split (a:=13) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_13_5_1 (by decide +kernel)
    · exact node4_49
    · exact node4_56
    · exact close_envelope (by decide) (by decide) bound4_13_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_13_4_1 (by decide +kernel) e (by omega)

theorem node4_58 : Closed 4 883086389887727026 2025 15 7 := by
  apply closed_of_split (a:=11) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_11_5_1 (by decide +kernel)
    · exact node4_35
    · exact node4_57
    · exact close_envelope (by decide) (by decide) bound4_11_38_7 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_11_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_11_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_11_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_11_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_11_4_1 (by decide +kernel) e (by omega)

theorem node4_59 : Closed 4 883086389887727026 473824157932125 7680 43 := by
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

end OddPerfect.DivisorCountSearch
