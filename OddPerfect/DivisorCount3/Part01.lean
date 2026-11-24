module

public import OddPerfect.DivisorCount3.Envelopes
import Mathlib.Tactic.IntervalCases

public section

namespace OddPerfect.DivisorCountSearch

theorem node3_0 : Closed 3 883576 45045 48 19 := by
  apply closed_of_split (a:=23) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_nonempty (k:=3) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_nonempty (k:=3) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_23_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_23_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_23_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_23_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_23_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_23_3_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound3_23_3_1 (by decide +kernel) e (by omega)

theorem node3_1 : Closed 3 883576 45045 48 17 := by
  apply closed_of_split (a:=19) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact node3_0
    · exact close_nonempty (k:=3) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_19_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_19_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_19_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_19_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_19_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_19_3_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound3_19_3_1 (by decide +kernel) e (by omega)

theorem node3_2 : Closed 3 883576 3465 24 13 := by
  apply closed_of_split (a:=17) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound3_17_4_1 (by decide +kernel)
    · exact node3_1
    · exact close_envelope (by decide) (by decide) bound3_17_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_17_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_17_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_17_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_17_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_17_3_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound3_17_3_1 (by decide +kernel) e (by omega)

theorem node3_3 : Closed 3 883576 315 12 11 := by
  apply closed_of_split (a:=13) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound3_13_4_1 (by decide +kernel)
    · exact node3_2
    · exact close_nonempty (k:=3) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound3_13_3_1 (by decide +kernel) e (by omega)

theorem node3_4 : Closed 3 883576 45 6 7 := by
  apply closed_of_split (a:=11) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound3_11_4_1 (by decide +kernel)
    · exact node3_3
    · exact close_envelope (by decide) (by decide) bound3_11_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_11_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_11_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_11_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_11_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_11_3_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound3_11_3_1 (by decide +kernel) e (by omega)

theorem node3_5 : Closed 3 883576 17325 36 13 := by
  apply closed_of_split (a:=17) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_nonempty (k:=3) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_17_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_17_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_17_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_17_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_17_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_17_3_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound3_17_3_1 (by decide +kernel) e (by omega)

theorem node3_6 : Closed 3 883576 1575 18 11 := by
  apply closed_of_split (a:=13) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound3_13_4_1 (by decide +kernel)
    · exact node3_5
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound3_13_3_1 (by decide +kernel) e (by omega)

theorem node3_7 : Closed 3 883576 225 9 7 := by
  apply closed_of_split (a:=11) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound3_11_4_1 (by decide +kernel)
    · exact node3_6
    · exact close_envelope (by decide) (by decide) bound3_11_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_11_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_11_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_11_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_11_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_11_3_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound3_11_3_1 (by decide +kernel) e (by omega)

theorem node3_8 : Closed 3 883576 9 3 5 := by
  apply closed_of_split (a:=7) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound3_7_4_1 (by decide +kernel)
    · exact node3_4
    · exact node3_7
    · exact close_envelope (by decide) (by decide) bound3_7_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_7_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_7_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_7_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_7_3_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound3_7_3_1 (by decide +kernel) e (by omega)

theorem node3_9 : Closed 3 883576 10395 32 13 := by
  apply closed_of_split (a:=17) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_nonempty (k:=4) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_nonempty (k:=3) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_17_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_17_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_17_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_17_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_17_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_17_3_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound3_17_3_1 (by decide +kernel) e (by omega)

theorem node3_10 : Closed 3 883576 945 16 11 := by
  apply closed_of_split (a:=13) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound3_13_4_1 (by decide +kernel)
    · exact node3_9
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound3_13_3_1 (by decide +kernel) e (by omega)

theorem node3_11 : Closed 3 883576 135 8 7 := by
  apply closed_of_split (a:=11) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound3_11_4_1 (by decide +kernel)
    · exact node3_10
    · exact close_envelope (by decide) (by decide) bound3_11_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_11_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_11_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_11_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_11_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_11_3_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound3_11_3_1 (by decide +kernel) e (by omega)

theorem node3_12 : Closed 3 883576 51975 48 17 := by
  apply closed_of_split (a:=19) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_nonempty (k:=3) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_nonempty (k:=3) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_19_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_19_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_19_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_19_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_19_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_19_3_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound3_19_3_1 (by decide +kernel) e (by omega)

theorem node3_13 : Closed 3 883576 51975 48 13 := by
  apply closed_of_split (a:=17) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact node3_12
    · exact close_nonempty (k:=3) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_17_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_17_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_17_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_17_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_17_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_17_3_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound3_17_3_1 (by decide +kernel) e (by omega)

theorem node3_14 : Closed 3 883576 4725 24 11 := by
  apply closed_of_split (a:=13) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound3_13_4_1 (by decide +kernel)
    · exact node3_13
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound3_13_3_1 (by decide +kernel) e (by omega)

theorem node3_15 : Closed 3 883576 675 12 7 := by
  apply closed_of_split (a:=11) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound3_11_4_1 (by decide +kernel)
    · exact node3_14
    · exact close_envelope (by decide) (by decide) bound3_11_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_11_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_11_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_11_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_11_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_11_3_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound3_11_3_1 (by decide +kernel) e (by omega)

theorem node3_16 : Closed 3 883576 27 4 5 := by
  apply closed_of_split (a:=7) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound3_7_4_1 (by decide +kernel)
    · exact node3_11
    · exact node3_15
    · exact close_envelope (by decide) (by decide) bound3_7_4_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_7_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_7_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_7_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_7_3_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound3_7_3_1 (by decide +kernel) e (by omega)

theorem node3_17 : Closed 3 883576 31185 40 13 := by
  apply closed_of_split (a:=17) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_nonempty (k:=3) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_nonempty (k:=3) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_17_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_17_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_17_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_17_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_17_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_17_3_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound3_17_3_1 (by decide +kernel) e (by omega)

theorem node3_18 : Closed 3 883576 2835 20 11 := by
  apply closed_of_split (a:=13) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound3_13_4_1 (by decide +kernel)
    · exact node3_17
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_13_3_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound3_13_3_1 (by decide +kernel) e (by omega)

theorem node3_19 : Closed 3 883576 405 10 7 := by
  apply closed_of_split (a:=11) (by decide) (by decide +kernel)
  intro e
  by_cases h : e<8
  · interval_cases e
    · exact close_envelope (by decide) (by decide) bound3_11_4_1 (by decide +kernel)
    · exact node3_18
    · exact close_nonempty (k:=3) (s:=1) (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_11_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_11_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_11_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_11_3_1 (by decide +kernel)
    · exact close_envelope (by decide) (by decide) bound3_11_3_1 (by decide +kernel)
  · exact close_exponent_tail (H:=8) (by decide) (by decide) (by decide) (by decide +kernel)
      (by decide) bound3_11_3_1 (by decide +kernel) e (by omega)

end OddPerfect.DivisorCountSearch
