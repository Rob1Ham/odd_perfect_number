module

public import OddPerfect.DivisorCount4.Part01
import Mathlib.Tactic.IntervalCases

public section

namespace OddPerfect.DivisorCountSearch

theorem node4_20 : Closed 4 883086389887727026 402026625 384 19 := by
  apply closed_of_split (a:=23) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_23_38_7 (by decide +kernel)
    · exact node4_19
    · exact close_envelope (by decide) (by decide) bound4_23_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_23_4_1 (by decide +kernel) e (by omega)

theorem node4_21 : Closed 4 883086389887727026 23648625 192 17 := by
  apply closed_of_split (a:=19) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_19_5_1 (by decide +kernel)
    · exact node4_20
    · exact close_envelope (by decide) (by decide) bound4_19_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_19_4_1 (by decide +kernel) e (by omega)

theorem node4_22 : Closed 4 883086389887727026 1819125 96 13 := by
  apply closed_of_split (a:=17) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_17_5_1 (by decide +kernel)
    · exact node4_21
    · exact close_envelope (by decide) (by decide) bound4_17_38_7 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_5_1 (by decide +kernel)
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_17_4_1 (by decide +kernel) e (by omega)

theorem node4_23 : Closed 4 883086389887727026 165375 48 11 := by
  apply closed_of_split (a:=13) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_13_5_1 (by decide +kernel)
    · exact node4_22
    · exact close_envelope (by decide) (by decide) bound4_13_38_7 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_13_4_1 (by decide +kernel) e (by omega)

theorem node4_24 : Closed 4 883086389887727026 3375 16 7 := by
  apply closed_of_split (a:=11) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_11_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_11_38_7 (by decide +kernel)
    · exact node4_23
    · exact close_envelope (by decide) (by decide) bound4_11_38_7 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_11_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_11_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_11_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_11_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_11_4_1 (by decide +kernel) e (by omega)

theorem node4_25 : Closed 4 883086389887727026 27 4 5 := by
  apply closed_of_split (a:=7) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_7_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_7_38_7 (by decide +kernel)
    · exact node4_13
    · exact node4_24
    · exact close_envelope (by decide) (by decide) bound4_7_38_7 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_7_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_7_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_7_5_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_7_4_1 (by decide +kernel) e (by omega)

theorem node4_26 : Closed 4 883086389887727026 20536892788086675 15360 43 := by
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

theorem node4_27 : Closed 4 883086389887727026 500899824099675 7680 41 := by
  apply closed_of_split (a:=43) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_43_38_7 (by decide +kernel)
    · exact node4_26
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_43_4_1 (by decide +kernel) e (by omega)

theorem node4_28 : Closed 4 883086389887727026 13537833083775 3840 37 := by
  apply closed_of_split (a:=41) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_41_38_7 (by decide +kernel)
    · exact node4_27
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_41_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_41_4_1 (by decide +kernel) e (by omega)

theorem node4_29 : Closed 4 883086389887727026 436704293025 1920 31 := by
  apply closed_of_split (a:=37) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_37_38_7 (by decide +kernel)
    · exact node4_28
    · exact close_envelope (by decide) (by decide) bound4_37_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_37_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_37_4_1 (by decide +kernel) e (by omega)

theorem node4_30 : Closed 4 883086389887727026 15058768725 960 29 := by
  apply closed_of_split (a:=31) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_31_38_7 (by decide +kernel)
    · exact node4_29
    · exact close_envelope (by decide) (by decide) bound4_31_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_31_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_31_4_1 (by decide +kernel) e (by omega)

theorem node4_31 : Closed 4 883086389887727026 654729075 480 23 := by
  apply closed_of_split (a:=29) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_29_38_7 (by decide +kernel)
    · exact node4_30
    · exact close_envelope (by decide) (by decide) bound4_29_5_1 (by decide +kernel)
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_29_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_29_4_1 (by decide +kernel) e (by omega)

theorem node4_32 : Closed 4 883086389887727026 34459425 240 19 := by
  apply closed_of_split (a:=23) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_23_38_7 (by decide +kernel)
    · exact node4_31
    · exact close_envelope (by decide) (by decide) bound4_23_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_23_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_23_4_1 (by decide +kernel) e (by omega)

theorem node4_33 : Closed 4 883086389887727026 2027025 120 17 := by
  apply closed_of_split (a:=19) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_19_38_7 (by decide +kernel)
    · exact node4_32
    · exact close_envelope (by decide) (by decide) bound4_19_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_19_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_19_4_1 (by decide +kernel) e (by omega)

theorem node4_34 : Closed 4 883086389887727026 155925 60 13 := by
  apply closed_of_split (a:=17) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_17_5_1 (by decide +kernel)
    · exact node4_33
    · exact close_envelope (by decide) (by decide) bound4_17_38_7 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_17_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_17_4_1 (by decide +kernel) e (by omega)

theorem node4_35 : Closed 4 883086389887727026 14175 30 11 := by
  apply closed_of_split (a:=13) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound4_13_5_1 (by decide +kernel)
    · exact node4_34
    · exact close_envelope (by decide) (by decide) bound4_13_38_7 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_5_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_13_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_13_4_1 (by decide +kernel) e (by omega)

theorem node4_36 : Closed 4 883086389887727026 94764831586425 5760 43 := by
  apply closed_of_split (a:=47) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_nonempty (k:=38) (s:=7) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_nonempty (k:=38) (s:=7) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_47_4_1 (by decide +kernel) e (by omega)

theorem node4_37 : Closed 4 883086389887727026 3885358095043425 11520 47 := by
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

theorem node4_38 : Closed 4 883086389887727026 3885358095043425 11520 43 := by
  apply closed_of_split (a:=47) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact node4_37
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_47_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_47_4_1 (by decide +kernel) e (by omega)

theorem node4_39 : Closed 4 883086389887727026 94764831586425 5760 41 := by
  apply closed_of_split (a:=43) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact node4_36
    · exact node4_38
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound4_43_4_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound4_43_4_1 (by decide +kernel) e (by omega)

end OddPerfect.DivisorCountSearch
