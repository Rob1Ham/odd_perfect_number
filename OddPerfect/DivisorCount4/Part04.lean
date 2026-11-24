module

public import OddPerfect.DivisorCount4.Part03
import Mathlib.Tactic.IntervalCases

public section

namespace OddPerfect.DivisorCountSearch

theorem node4_60 : Closed 4 883086389887727026 19426790475217125 15360 43 := by
  apply closed_of_split (a:=47) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_47_4_1 (by decide +kernel) e (by omega)

theorem node4_61 : Closed 4 883086389887727026 473824157932125 7680 41 := by
  apply closed_of_split (a:=43) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact node4_59
    · exact node4_60
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_43_4_1 (by decide +kernel) e (by omega)

theorem node4_62 : Closed 4 883086389887727026 17531493843488625 15360 47 := by
  apply closed_of_split (a:=53) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_53_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_53_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_53_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_53_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_53_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_53_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_53_4_1 (by decide +kernel) e (by omega)

theorem node4_63 : Closed 4 883086389887727026 17531493843488625 15360 43 := by
  apply closed_of_split (a:=47) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact node4_62
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_47_4_1 (by decide +kernel) e (by omega)

theorem node4_64 : Closed 4 883086389887727026 17531493843488625 15360 41 := by
  apply closed_of_split (a:=43) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact node4_63
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_43_4_1 (by decide +kernel) e (by omega)

theorem node4_65 : Closed 4 883086389887727026 473824157932125 7680 37 := by
  apply closed_of_split (a:=41) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact node4_61
    · exact node4_64
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_41_4_1 (by decide +kernel) e (by omega)

theorem node4_66 : Closed 4 883086389887727026 15284650255875 3840 31 := by
  apply closed_of_split (a:=37) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_37_38_7 (by decide +kernel)
    · exact node4_65
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_37_4_1 (by decide +kernel) e (by omega)

theorem node4_67 : Closed 4 883086389887727026 527056905375 1920 29 := by
  apply closed_of_split (a:=31) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_31_38_7 (by decide +kernel)
    · exact node4_66
    · exact close_envelope (by decide) (by decide) bound4_31_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_31_4_1 (by decide +kernel) e (by omega)

theorem node4_68 : Closed 4 883086389887727026 22915517625 960 23 := by
  apply closed_of_split (a:=29) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_29_38_7 (by decide +kernel)
    · exact node4_67
    · exact close_envelope (by decide) (by decide) bound4_29_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_29_4_1 (by decide +kernel) e (by omega)

theorem node4_69 : Closed 4 883086389887727026 1206079875 480 19 := by
  apply closed_of_split (a:=23) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_23_38_7 (by decide +kernel)
    · exact node4_68
    · exact close_envelope (by decide) (by decide) bound4_23_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_23_4_1 (by decide +kernel) e (by omega)

theorem node4_70 : Closed 4 883086389887727026 70945875 240 17 := by
  apply closed_of_split (a:=19) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_19_5_1 (by decide +kernel)
    · exact node4_69
    · exact close_envelope (by decide) (by decide) bound4_19_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_19_4_1 (by decide +kernel) e (by omega)

theorem node4_71 : Closed 4 883086389887727026 5457375 120 13 := by
  apply closed_of_split (a:=17) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_17_5_1 (by decide +kernel)
    · exact node4_70
    · exact close_envelope (by decide) (by decide) bound4_17_38_7 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_17_4_1 (by decide +kernel) e (by omega)

theorem node4_72 : Closed 4 883086389887727026 5212065737253375 11520 37 := by
  apply closed_of_split (a:=41) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_nonempty (k:=5) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_41_4_1 (by decide +kernel) e (by omega)

theorem node4_73 : Closed 4 883086389887727026 168131152814625 5760 31 := by
  apply closed_of_split (a:=37) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_37_38_7 (by decide +kernel)
    · exact node4_72
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_37_4_1 (by decide +kernel) e (by omega)

theorem node4_74 : Closed 4 883086389887727026 5797625959125 2880 29 := by
  apply closed_of_split (a:=31) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_31_38_7 (by decide +kernel)
    · exact node4_73
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_31_4_1 (by decide +kernel) e (by omega)

theorem node4_75 : Closed 4 883086389887727026 252070693875 1440 23 := by
  apply closed_of_split (a:=29) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_29_5_1 (by decide +kernel)
    · exact node4_74
    · exact close_envelope (by decide) (by decide) bound4_29_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_29_4_1 (by decide +kernel) e (by omega)

theorem node4_76 : Closed 4 883086389887727026 13266878625 720 19 := by
  apply closed_of_split (a:=23) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_23_5_1 (by decide +kernel)
    · exact node4_75
    · exact close_envelope (by decide) (by decide) bound4_23_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_23_4_1 (by decide +kernel) e (by omega)

theorem node4_77 : Closed 4 883086389887727026 780404625 360 17 := by
  apply closed_of_split (a:=19) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_19_5_1 (by decide +kernel)
    · exact node4_76
    · exact close_envelope (by decide) (by decide) bound4_19_5_1 (by decide +kernel)
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_19_4_1 (by decide +kernel) e (by omega)

theorem node4_78 : Closed 4 883086389887727026 60031125 180 13 := by
  apply closed_of_split (a:=17) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_17_5_1 (by decide +kernel)
    · exact node4_77
    · exact close_envelope (by decide) (by decide) bound4_17_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_17_4_1 (by decide +kernel) e (by omega)

theorem node4_79 : Closed 4 883086389887727026 496125 60 11 := by
  apply closed_of_split (a:=13) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_13_5_1 (by decide +kernel)
    · exact node4_71
    · exact node4_78
    · exact close_envelope (by decide) (by decide) bound4_13_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_13_4_1 (by decide +kernel) e (by omega)

end OddPerfect.DivisorCountSearch
