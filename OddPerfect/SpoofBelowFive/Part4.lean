module

public import OddPerfect.SpoofBelowFive.Part3

public section

namespace OddPerfect.SpoofBox

private def r4_3_2_rows : Vector Slot 4 := #v[⟨false,3,5,2,0⟩, ⟨false,3,5,2,0⟩, ⟨false,3,5,2,0⟩, ⟨true,5,9,1,0⟩]
private theorem r4_3_2 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_2_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_2_rows
  decide +kernel

private def r4_3_4_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,3,3,2,0⟩, ⟨false,3,3,2,0⟩, ⟨true,13,0,1,0⟩]
private theorem r4_3_4 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_4_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_4_rows
  decide +kernel

private def r4_3_6_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨true,13,0,1,0⟩]
private theorem r4_3_6 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_6_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_6_rows
  decide +kernel

private def r4_3_8_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨true,13,0,1,0⟩]
private theorem r4_3_8 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_8_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_8_rows
  decide +kernel

private def r4_3_11_rows : Vector Slot 4 := #v[⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨true,13,17,1,0⟩]
private theorem r4_3_11 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_11_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_11_rows
  decide +kernel

private def r4_3_13_rows : Vector Slot 4 := #v[⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,5,5,2,2⟩, ⟨true,21,25,1,0⟩]
private theorem r4_3_13 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_13_rows := by
  apply verifyCover_sound "ECdHAIAACHAIAAA".toUTF8 "AAAAIAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 5 0 r4_3_13_rows
  decide +kernel

private def r4_3_28_rows : Vector Slot 4 := #v[⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,5,5,4,0⟩, ⟨true,21,25,1,0⟩]
private theorem r4_3_28 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_28_rows := by
  apply verifyCover_sound "ECHAIAAAA".toUTF8 "AAAAIAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 5 0 r4_3_28_rows
  decide +kernel

private def r4_3_12_rows : Vector Slot 4 := #v[⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨true,21,25,1,0⟩]
private theorem r4_3_12 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_12_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_12_rows (2 : Fin 4)
    Axis.exponent r4_3_13 r4_3_28

private def r4_3_10_rows : Vector Slot 4 := #v[⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨true,13,25,1,0⟩]
private theorem r4_3_10 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_10_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_10_rows (3 : Fin 4)
    Axis.base r4_3_11 r4_3_12

private def r4_3_39_rows : Vector Slot 4 := #v[⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨true,29,37,1,0⟩]
private theorem r4_3_39 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_39_rows := by
  apply verifyCover_sound "GEACAHAAECAHAACHAAA".toUTF8 "AAAAIAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAEAAAACAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 5 0 r4_3_39_rows
  decide +kernel

private def r4_3_58_rows : Vector Slot 4 := #v[⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨true,41,57,1,0⟩]
private theorem r4_3_58 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_58_rows := by
  apply verifyCover_sound "GAEACAHHIGEACAAECAAAAAA".toUTF8 "AAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAQAAAAOAAAAMAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 10 0 r4_3_58_rows
  decide +kernel

private def r4_3_38_rows : Vector Slot 4 := #v[⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨true,29,57,1,0⟩]
private theorem r4_3_38 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_38_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_38_rows (3 : Fin 4)
    Axis.base r4_3_39 r4_3_58

private def r4_3_81_rows : Vector Slot 4 := #v[⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨true,61,0,1,0⟩]
private theorem r4_3_81 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_81_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_81_rows
  decide +kernel

private def r4_3_37_rows : Vector Slot 4 := #v[⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨true,29,0,1,0⟩]
private theorem r4_3_37 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_37_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_37_rows (3 : Fin 4)
    Axis.base r4_3_38 r4_3_81

private def r4_3_9_rows : Vector Slot 4 := #v[⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨true,13,0,1,0⟩]
private theorem r4_3_9 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_9_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_9_rows (3 : Fin 4)
    Axis.base r4_3_10 r4_3_37

private def r4_3_7_rows : Vector Slot 4 := #v[⟨false,3,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨true,13,0,1,0⟩]
private theorem r4_3_7 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_7_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_7_rows (0 : Fin 4)
    Axis.base r4_3_8 r4_3_9

private def r4_3_5_rows : Vector Slot 4 := #v[⟨false,3,5,2,0⟩, ⟨false,3,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨true,13,0,1,0⟩]
private theorem r4_3_5 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_5_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_5_rows (1 : Fin 4)
    Axis.base r4_3_6 r4_3_7

private def r4_3_3_rows : Vector Slot 4 := #v[⟨false,3,5,2,0⟩, ⟨false,3,5,2,0⟩, ⟨false,3,5,2,0⟩, ⟨true,13,0,1,0⟩]
private theorem r4_3_3 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_3_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_3_rows (2 : Fin 4)
    Axis.base r4_3_4 r4_3_5

private def r4_3_1_rows : Vector Slot 4 := #v[⟨false,3,5,2,0⟩, ⟨false,3,5,2,0⟩, ⟨false,3,5,2,0⟩, ⟨true,5,0,1,0⟩]
private theorem r4_3_1 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_1_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_1_rows (3 : Fin 4)
    Axis.base r4_3_2 r4_3_3

private def r4_3_84_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,3,3,2,0⟩, ⟨false,7,0,2,0⟩, ⟨true,9,0,1,0⟩]
private theorem r4_3_84 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_84_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_84_rows
  decide +kernel

private def r4_3_88_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,7,13,2,0⟩, ⟨true,9,17,1,0⟩]
private theorem r4_3_88 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_88_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_88_rows
  decide +kernel

private def r4_3_90_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,7,9,2,0⟩, ⟨true,21,0,1,0⟩]
private theorem r4_3_90 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_90_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_90_rows
  decide +kernel

private def r4_3_92_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,11,13,2,0⟩, ⟨true,21,41,1,0⟩]
private theorem r4_3_92 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_92_rows := by
  apply verifyCover_sound "CHAFAHEHAIAAAEAAA".toUTF8 "AAAAQAAAACAAAAAAAAACAAAAAAAAAIAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAACAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 8 0 r4_3_92_rows
  decide +kernel

private def r4_3_112_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,11,11,2,0⟩, ⟨true,45,89,1,0⟩]
private theorem r4_3_112 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_112_rows := by
  apply verifyCover_sound "HAEHHAHGAAAAA".toUTF8 "AAAACAAAAAAAAAKAAAAIAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 7 0 r4_3_112_rows
  decide +kernel

private def r4_3_125_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,13,13,2,0⟩, ⟨true,45,89,1,0⟩]
private theorem r4_3_125 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_125_rows := by
  apply verifyCover_sound "HEAHHIAGAEAAAAA".toUTF8 "AAAAOAAAACAAAAAAAAAKAAAAIAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 8 0 r4_3_125_rows
  decide +kernel

private def r4_3_111_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,11,13,2,0⟩, ⟨true,45,89,1,0⟩]
private theorem r4_3_111 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_111_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_111_rows (2 : Fin 4)
    Axis.base r4_3_112 r4_3_125

private def r4_3_143_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,2⟩, ⟨false,11,11,2,0⟩, ⟨true,93,185,1,0⟩]
private theorem r4_3_143 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_143_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_143_rows
  decide +kernel

private def r4_3_145_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,11,11,2,0⟩, ⟨true,93,121,1,0⟩]
private theorem r4_3_145 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_145_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_145_rows
  decide +kernel

private def r4_3_148_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,11,11,2,0⟩, ⟨true,125,133,1,0⟩]
private theorem r4_3_148 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_148_rows := by
  apply verifyCover_sound "GHEAAEAHIbAAA".toUTF8 "AAAAMAAAAEAAAACAAAAAAAAAAAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 6 0 r4_3_148_rows
  decide +kernel

private def r4_3_161_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,11,11,2,0⟩, ⟨true,137,149,1,0⟩]
private theorem r4_3_161 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_161_rows := by
  apply verifyCover_sound "GAHEHIAAAAA".toUTF8 "AAAACAAAAAAAAAIAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 6 0 r4_3_161_rows
  decide +kernel

private def r4_3_147_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,11,11,2,0⟩, ⟨true,125,149,1,0⟩]
private theorem r4_3_147 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_147_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_147_rows (3 : Fin 4)
    Axis.base r4_3_148 r4_3_161

private def r4_3_172_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,11,11,2,0⟩, ⟨true,153,185,1,0⟩]
private theorem r4_3_172 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_172_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_172_rows
  decide +kernel

private def r4_3_146_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,11,11,2,0⟩, ⟨true,125,185,1,0⟩]
private theorem r4_3_146 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_146_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_146_rows (3 : Fin 4)
    Axis.base r4_3_147 r4_3_172

private def r4_3_144_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,11,11,2,0⟩, ⟨true,93,185,1,0⟩]
private theorem r4_3_144 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_144_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_144_rows (3 : Fin 4)
    Axis.base r4_3_145 r4_3_146

private def r4_3_142_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,11,11,2,0⟩, ⟨true,93,185,1,0⟩]
private theorem r4_3_142 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_142_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_142_rows (1 : Fin 4)
    Axis.exponent r4_3_143 r4_3_144

private def r4_3_173_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,11,11,2,0⟩, ⟨true,189,0,1,0⟩]
private theorem r4_3_173 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_173_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_173_rows
  decide +kernel

private def r4_3_141_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,11,11,2,0⟩, ⟨true,93,0,1,0⟩]
private theorem r4_3_141 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_141_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_141_rows (3 : Fin 4)
    Axis.base r4_3_142 r4_3_173

private def r4_3_174_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,13,13,2,0⟩, ⟨true,93,0,1,0⟩]
private theorem r4_3_174 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_174_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_174_rows
  decide +kernel

private def r4_3_140_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,11,13,2,0⟩, ⟨true,93,0,1,0⟩]
private theorem r4_3_140 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_140_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_140_rows (2 : Fin 4)
    Axis.base r4_3_141 r4_3_174

private def r4_3_110_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,11,13,2,0⟩, ⟨true,45,0,1,0⟩]
private theorem r4_3_110 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_110_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_110_rows (3 : Fin 4)
    Axis.base r4_3_111 r4_3_140

private def r4_3_175_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,11,13,2,0⟩, ⟨true,45,0,1,0⟩]
private theorem r4_3_175 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_175_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_175_rows
  decide +kernel

private def r4_3_109_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,11,13,2,0⟩, ⟨true,45,0,1,0⟩]
private theorem r4_3_109 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_109_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_109_rows (0 : Fin 4)
    Axis.exponent r4_3_110 r4_3_175

private def r4_3_91_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,11,13,2,0⟩, ⟨true,21,0,1,0⟩]
private theorem r4_3_91 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_91_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_91_rows (3 : Fin 4)
    Axis.base r4_3_92 r4_3_109

private def r4_3_89_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,7,13,2,0⟩, ⟨true,21,0,1,0⟩]
private theorem r4_3_89 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_89_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_89_rows (2 : Fin 4)
    Axis.base r4_3_90 r4_3_91

private def r4_3_87_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,7,13,2,0⟩, ⟨true,9,0,1,0⟩]
private theorem r4_3_87 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_87_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_87_rows (3 : Fin 4)
    Axis.base r4_3_88 r4_3_89

private def r4_3_181_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,15,19,2,0⟩, ⟨true,17,21,1,0⟩]
private theorem r4_3_181 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_181_rows := by
  apply verifyCover_sound "FAHAEAFAIAA".toUTF8 "AAAACAAAAAAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 6 0 r4_3_181_rows
  decide +kernel

private def r4_3_192_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,15,19,2,0⟩, ⟨true,25,33,1,0⟩]
private theorem r4_3_192 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_192_rows := by
  apply verifyCover_sound "FHEAAEAHIEcAAAA".toUTF8 "AAAAOAAAAEAAAACAAAAAAAAAAAAAACAAAAAAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 7 0 r4_3_192_rows
  decide +kernel

private def r4_3_180_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,15,19,2,0⟩, ⟨true,17,33,1,0⟩]
private theorem r4_3_180 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_180_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_180_rows (3 : Fin 4)
    Axis.base r4_3_181 r4_3_192

private def r4_3_207_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,21,29,2,0⟩, ⟨true,21,33,1,0⟩]
private theorem r4_3_207 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_207_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_207_rows
  decide +kernel

private def r4_3_179_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,15,29,2,0⟩, ⟨true,17,33,1,0⟩]
private theorem r4_3_179 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_179_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_179_rows (2 : Fin 4)
    Axis.base r4_3_180 r4_3_207

private def r4_3_209_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,15,19,2,0⟩, ⟨true,17,33,1,0⟩]
private theorem r4_3_209 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_209_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_209_rows
  decide +kernel

private def r4_3_211_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,21,25,2,0⟩, ⟨true,21,25,1,0⟩]
private theorem r4_3_211 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_211_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_211_rows
  decide +kernel

private def r4_3_213_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,21,23,2,0⟩, ⟨true,29,33,1,0⟩]
private theorem r4_3_213 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_213_rows := by
  apply verifyCover_sound "EFACHAAAA".toUTF8 "AAAAIAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 5 0 r4_3_213_rows
  decide +kernel

private def r4_3_223_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,2⟩, ⟨false,25,29,2,0⟩, ⟨true,29,33,1,0⟩]
private theorem r4_3_223 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_223_rows := by
  apply verifyCover_sound "FCAHAACAHFIACAAAA".toUTF8 "AAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAACAAAAAAAAAIAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 7 0 r4_3_223_rows
  decide +kernel

private def r4_3_241_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,25,25,2,0⟩, ⟨true,29,33,1,0⟩]
private theorem r4_3_241 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_241_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_241_rows
  decide +kernel

private def r4_3_242_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,27,29,2,0⟩, ⟨true,29,33,1,0⟩]
private theorem r4_3_242 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_242_rows := by
  apply verifyCover_sound "CHFAIEcAAAHAFAICAECcAAA".toUTF8 "AAAAKAAAAIAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAAIAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 8 0 r4_3_242_rows
  decide +kernel

private def r4_3_240_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,25,29,2,0⟩, ⟨true,29,33,1,0⟩]
private theorem r4_3_240 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_240_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_240_rows (2 : Fin 4)
    Axis.base r4_3_241 r4_3_242

private def r4_3_222_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,25,29,2,0⟩, ⟨true,29,33,1,0⟩]
private theorem r4_3_222 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_222_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_222_rows (1 : Fin 4)
    Axis.exponent r4_3_223 r4_3_240

private def r4_3_212_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,21,29,2,0⟩, ⟨true,29,33,1,0⟩]
private theorem r4_3_212 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_212_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_212_rows (2 : Fin 4)
    Axis.base r4_3_213 r4_3_222

private def r4_3_210_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,21,29,2,0⟩, ⟨true,21,33,1,0⟩]
private theorem r4_3_210 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_210_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_210_rows (3 : Fin 4)
    Axis.base r4_3_211 r4_3_212

private def r4_3_208_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,15,29,2,0⟩, ⟨true,17,33,1,0⟩]
private theorem r4_3_208 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_208_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_208_rows (2 : Fin 4)
    Axis.base r4_3_209 r4_3_210

private def r4_3_178_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,15,29,2,0⟩, ⟨true,17,33,1,0⟩]
private theorem r4_3_178 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_178_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_178_rows (0 : Fin 4)
    Axis.exponent r4_3_179 r4_3_208

private def r4_3_266_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,15,29,2,0⟩, ⟨true,37,0,1,0⟩]
private theorem r4_3_266 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_266_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_266_rows
  decide +kernel

private def r4_3_270_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,15,15,2,0⟩, ⟨true,37,73,1,0⟩]
private theorem r4_3_270 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_270_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_270_rows
  decide +kernel

private def r4_3_272_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,17,19,2,0⟩, ⟨true,37,49,1,0⟩]
private theorem r4_3_272 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_272_rows := by
  apply verifyCover_sound "EFAHACAAA".toUTF8 "AAAAIAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 5 0 r4_3_272_rows
  decide +kernel

private def r4_3_283_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,2⟩, ⟨false,17,17,2,0⟩, ⟨true,53,73,1,0⟩]
private theorem r4_3_283 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_283_rows := by
  apply verifyCover_sound "HCHAHAIcAACAA".toUTF8 "AAAAKAAAAIAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAACAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 6 0 r4_3_283_rows
  decide +kernel

private def r4_3_296_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,2⟩, ⟨false,19,19,2,0⟩, ⟨true,53,73,1,0⟩]
private theorem r4_3_296 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_296_rows := by
  apply verifyCover_sound "HCAHCIAGAAIGaAAAA".toUTF8 "AAAAQAAAACAAAAAAAAAMAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 7 0 r4_3_296_rows
  decide +kernel

private def r4_3_282_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,2⟩, ⟨false,17,19,2,0⟩, ⟨true,53,73,1,0⟩]
private theorem r4_3_282 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_282_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_282_rows (2 : Fin 4)
    Axis.base r4_3_283 r4_3_296

private def r4_3_313_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,19,2,0⟩, ⟨true,53,73,1,0⟩]
private theorem r4_3_313 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_313_rows := by
  apply verifyCover_sound "FAHACHAHEAIAGAEAAAA".toUTF8 "AAAACAAAAAAAAACAAAAAAAAAOAAAACAAAAAAAAAKAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 10 0 r4_3_313_rows
  decide +kernel

private def r4_3_281_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,17,19,2,0⟩, ⟨true,53,73,1,0⟩]
private theorem r4_3_281 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_281_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_281_rows (1 : Fin 4)
    Axis.exponent r4_3_282 r4_3_313

private def r4_3_271_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,17,19,2,0⟩, ⟨true,37,73,1,0⟩]
private theorem r4_3_271 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_271_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_271_rows (3 : Fin 4)
    Axis.base r4_3_272 r4_3_281

private def r4_3_269_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,15,19,2,0⟩, ⟨true,37,73,1,0⟩]
private theorem r4_3_269 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_269_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_269_rows (2 : Fin 4)
    Axis.base r4_3_270 r4_3_271

private def r4_3_334_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,15,15,2,0⟩, ⟨true,77,153,1,0⟩]
private theorem r4_3_334 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_334_rows := by
  apply verifyCover_sound "EHACHAHHGdAAAAA".toUTF8 "AAAAOAAAACAAAAAAAAAKAAAACAAAAAAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 8 0 r4_3_334_rows
  decide +kernel

private def r4_3_352_rows : Vector Slot 4 := #v[⟨false,3,3,4,4⟩, ⟨false,5,5,2,2⟩, ⟨false,15,15,2,0⟩, ⟨true,157,313,1,0⟩]
private theorem r4_3_352 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_352_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_352_rows
  decide +kernel

private def r4_3_354_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨false,5,5,2,2⟩, ⟨false,15,15,2,0⟩, ⟨true,157,209,1,0⟩]
private theorem r4_3_354 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_354_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_354_rows
  decide +kernel

private def r4_3_356_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨false,5,5,2,2⟩, ⟨false,15,15,2,0⟩, ⟨true,213,253,1,0⟩]
private theorem r4_3_356 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_356_rows := by
  apply verifyCover_sound "HACHGAAGAHAAA".toUTF8 "AAAACAAAAAAAAAKAAAAEAAAACAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 6 0 r4_3_356_rows
  decide +kernel

private def r4_3_369_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨false,5,5,2,2⟩, ⟨false,15,15,2,0⟩, ⟨true,257,313,1,0⟩]
private theorem r4_3_369 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_369_rows := by
  apply verifyCover_sound "HCAHGHCAAAAGAHAHCAAAA".toUTF8 "AAAAUAAAACAAAAAAAAAIAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 8 0 r4_3_369_rows
  decide +kernel

private def r4_3_355_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨false,5,5,2,2⟩, ⟨false,15,15,2,0⟩, ⟨true,213,313,1,0⟩]
private theorem r4_3_355 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_355_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_355_rows (3 : Fin 4)
    Axis.base r4_3_356 r4_3_369

private def r4_3_353_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨false,5,5,2,2⟩, ⟨false,15,15,2,0⟩, ⟨true,157,313,1,0⟩]
private theorem r4_3_353 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_353_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_353_rows (3 : Fin 4)
    Axis.base r4_3_354 r4_3_355

private def r4_3_351_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,2⟩, ⟨false,15,15,2,0⟩, ⟨true,157,313,1,0⟩]
private theorem r4_3_351 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_351_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_351_rows (0 : Fin 4)
    Axis.exponent r4_3_352 r4_3_353

private def r4_3_390_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,2⟩, ⟨false,15,15,2,0⟩, ⟨true,317,0,1,0⟩]
private theorem r4_3_390 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_390_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_390_rows
  decide +kernel

private def r4_3_350_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,2⟩, ⟨false,15,15,2,0⟩, ⟨true,157,0,1,0⟩]
private theorem r4_3_350 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_350_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_350_rows (3 : Fin 4)
    Axis.base r4_3_351 r4_3_390

private def r4_3_391_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,15,15,2,0⟩, ⟨true,157,0,1,0⟩]
private theorem r4_3_391 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_391_rows := by
  apply verifyCover_sound "HACHAHAHAHEGdAAEGAAAA".toUTF8 "AAAACAAAAAAAAASAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 9 0 r4_3_391_rows
  decide +kernel

private def r4_3_349_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,15,15,2,0⟩, ⟨true,157,0,1,0⟩]
private theorem r4_3_349 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_349_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_349_rows (1 : Fin 4)
    Axis.exponent r4_3_350 r4_3_391

private def r4_3_333_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,15,15,2,0⟩, ⟨true,77,0,1,0⟩]
private theorem r4_3_333 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_333_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_333_rows (3 : Fin 4)
    Axis.base r4_3_334 r4_3_349

private def r4_3_414_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,2⟩, ⟨false,17,19,2,0⟩, ⟨true,77,153,1,0⟩]
private theorem r4_3_414 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_414_rows := by
  apply verifyCover_sound "FHCAHHAHCGAIAAAAAAA".toUTF8 "AAAASAAAAQAAAACAAAAAAAAAMAAAACAAAAAAAAAIAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 10 0 r4_3_414_rows
  decide +kernel

private def r4_3_434_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨true,77,153,1,0⟩]
private theorem r4_3_434 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_434_rows := by
  apply verifyCover_sound "HACHHAHAEHGdAAHAGIAAAAA".toUTF8 "AAAACAAAAAAAAAUAAAASAAAACAAAAAAAAACAAAAAAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 10 0 r4_3_434_rows
  decide +kernel

private def r4_3_459_rows : Vector Slot 4 := #v[⟨false,3,3,4,4⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨true,77,101,1,0⟩]
private theorem r4_3_459 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_459_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_459_rows
  decide +kernel

private def r4_3_461_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨true,77,85,1,0⟩]
private theorem r4_3_461 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_461_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_461_rows
  decide +kernel

private def r4_3_462_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨true,89,101,1,0⟩]
private theorem r4_3_462 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_462_rows := by
  apply verifyCover_sound "HHCEGAIAAAACAEGAIACAAAA".toUTF8 "AAAAWAAAAKAAAAIAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAAAAAACAAAAAAAAAIAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 8 0 r4_3_462_rows
  decide +kernel

private def r4_3_460_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨true,77,101,1,0⟩]
private theorem r4_3_460 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_460_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_460_rows (3 : Fin 4)
    Axis.base r4_3_461 r4_3_462

private def r4_3_458_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨true,77,101,1,0⟩]
private theorem r4_3_458 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_458_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_458_rows (0 : Fin 4)
    Axis.exponent r4_3_459 r4_3_460

private def r4_3_485_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨true,105,153,1,0⟩]
private theorem r4_3_485 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_485_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_485_rows
  decide +kernel

private def r4_3_457_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨true,77,153,1,0⟩]
private theorem r4_3_457 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_457_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_457_rows (3 : Fin 4)
    Axis.base r4_3_458 r4_3_485

private def r4_3_433_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,19,2,0⟩, ⟨true,77,153,1,0⟩]
private theorem r4_3_433 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_433_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_433_rows (2 : Fin 4)
    Axis.base r4_3_434 r4_3_457

private def r4_3_413_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,17,19,2,0⟩, ⟨true,77,153,1,0⟩]
private theorem r4_3_413 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_413_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_413_rows (1 : Fin 4)
    Axis.exponent r4_3_414 r4_3_433

private def r4_3_487_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,2⟩, ⟨false,17,19,2,0⟩, ⟨true,157,0,1,0⟩]
private theorem r4_3_487 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_487_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_487_rows
  decide +kernel

private def r4_3_491_rows : Vector Slot 4 := #v[⟨false,3,3,4,4⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨true,157,313,1,0⟩]
private theorem r4_3_491 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_491_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_491_rows
  decide +kernel

private def r4_3_493_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨true,157,209,1,0⟩]
private theorem r4_3_493 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_493_rows := by
  apply verifyCover_sound "HAHACEHAGAAAA".toUTF8 "AAAACAAAAAAAAACAAAAAAAAAIAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 7 0 r4_3_493_rows
  decide +kernel

private def r4_3_509_rows : Vector Slot 4 := #v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨true,213,229,1,0⟩]
private theorem r4_3_509 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_509_rows := by
  apply verifyCover_sound "HEGAHIAAAAEAGAHAHAIAEAA".toUTF8 "AAAAKAAAAIAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 8 0 r4_3_509_rows
  decide +kernel

private def r4_3_532_rows : Vector Slot 4 := #v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨true,213,229,1,0⟩]
private theorem r4_3_532 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_532_rows := by
  apply verifyCover_sound "HAEGHAHCAIAAAAA".toUTF8 "AAAACAAAAAAAAAMAAAAKAAAACAAAAAAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 8 0 r4_3_532_rows
  decide +kernel

private def r4_3_508_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨true,213,229,1,0⟩]
private theorem r4_3_508 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_508_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_508_rows (0 : Fin 4)
    Axis.exponent r4_3_509 r4_3_532

private def r4_3_548_rows : Vector Slot 4 := #v[⟨false,3,3,6,6⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨true,233,253,1,0⟩]
private theorem r4_3_548 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_548_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_548_rows
  decide +kernel

private def r4_3_550_rows : Vector Slot 4 := #v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨true,233,241,1,0⟩]
private theorem r4_3_550 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_550_rows := by
  apply verifyCover_sound "EGAHCIAAAAGHAHACAAA".toUTF8 "AAAAKAAAACAAAAAAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAIAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 6 0 r4_3_550_rows
  decide +kernel

private def r4_3_569_rows : Vector Slot 4 := #v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨true,245,253,1,0⟩]
private theorem r4_3_569 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_569_rows := by
  apply verifyCover_sound "EAGAHAHACAA".toUTF8 "AAAACAAAAAAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 6 0 r4_3_569_rows
  decide +kernel

private def r4_3_549_rows : Vector Slot 4 := #v[⟨false,3,3,8,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨true,233,253,1,0⟩]
private theorem r4_3_549 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_549_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_549_rows (3 : Fin 4)
    Axis.base r4_3_550 r4_3_569

private def r4_3_547_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨true,233,253,1,0⟩]
private theorem r4_3_547 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_547_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_547_rows (0 : Fin 4)
    Axis.exponent r4_3_548 r4_3_549

private def r4_3_507_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨true,213,253,1,0⟩]
private theorem r4_3_507 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_507_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_507_rows (3 : Fin 4)
    Axis.base r4_3_508 r4_3_547

private def r4_3_580_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨true,257,313,1,0⟩]
private theorem r4_3_580 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_580_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_580_rows
  decide +kernel

private def r4_3_506_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨true,213,313,1,0⟩]
private theorem r4_3_506 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_506_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_506_rows (3 : Fin 4)
    Axis.base r4_3_507 r4_3_580

private def r4_3_492_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨true,157,313,1,0⟩]
private theorem r4_3_492 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_492_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_492_rows (3 : Fin 4)
    Axis.base r4_3_493 r4_3_506

private def r4_3_490_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨true,157,313,1,0⟩]
private theorem r4_3_490 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_490_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_490_rows (0 : Fin 4)
    Axis.exponent r4_3_491 r4_3_492

private def r4_3_581_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨true,317,0,1,0⟩]
private theorem r4_3_581 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_581_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_581_rows
  decide +kernel

private def r4_3_489_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨true,157,0,1,0⟩]
private theorem r4_3_489 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_489_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_489_rows (3 : Fin 4)
    Axis.base r4_3_490 r4_3_581

private def r4_3_582_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,19,19,2,0⟩, ⟨true,157,0,1,0⟩]
private theorem r4_3_582 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_582_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_582_rows
  decide +kernel

private def r4_3_488_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,19,2,0⟩, ⟨true,157,0,1,0⟩]
private theorem r4_3_488 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_488_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_488_rows (2 : Fin 4)
    Axis.base r4_3_489 r4_3_582

private def r4_3_486_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,17,19,2,0⟩, ⟨true,157,0,1,0⟩]
private theorem r4_3_486 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_486_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_486_rows (1 : Fin 4)
    Axis.exponent r4_3_487 r4_3_488

private def r4_3_412_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,17,19,2,0⟩, ⟨true,77,0,1,0⟩]
private theorem r4_3_412 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_412_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_412_rows (3 : Fin 4)
    Axis.base r4_3_413 r4_3_486

private def r4_3_332_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,15,19,2,0⟩, ⟨true,77,0,1,0⟩]
private theorem r4_3_332 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_332_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_332_rows (2 : Fin 4)
    Axis.base r4_3_333 r4_3_412

private def r4_3_268_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,15,19,2,0⟩, ⟨true,37,0,1,0⟩]
private theorem r4_3_268 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_268_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_268_rows (3 : Fin 4)
    Axis.base r4_3_269 r4_3_332

private def r4_3_587_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,2⟩, ⟨false,21,23,2,0⟩, ⟨true,37,49,1,0⟩]
private theorem r4_3_587 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_587_rows := by
  apply verifyCover_sound "HFCAHAICAAAAA".toUTF8 "AAAAMAAAAKAAAACAAAAAAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 7 0 r4_3_587_rows
  decide +kernel

private def r4_3_601_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,21,23,2,0⟩, ⟨true,37,41,1,0⟩]
private theorem r4_3_601 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_601_rows := by
  apply verifyCover_sound "FACHAIAAA".toUTF8 "AAAACAAAAAAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 5 0 r4_3_601_rows
  decide +kernel

private def r4_3_611_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,21,21,2,0⟩, ⟨true,45,49,1,0⟩]
private theorem r4_3_611 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_611_rows := by
  apply verifyCover_sound "CHAIEcAAA".toUTF8 "AAAAIAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 5 0 r4_3_611_rows
  decide +kernel

private def r4_3_620_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,23,2,0⟩, ⟨true,45,49,1,0⟩]
private theorem r4_3_620 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_620_rows := by
  apply verifyCover_sound "CAHACIAEAGAAIEAGCAAAA".toUTF8 "AAAACAAAAAAAAACAAAAAAAAAIAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAIAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 8 0 r4_3_620_rows
  decide +kernel

private def r4_3_610_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,21,23,2,0⟩, ⟨true,45,49,1,0⟩]
private theorem r4_3_610 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_610_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_610_rows (2 : Fin 4)
    Axis.base r4_3_611 r4_3_620

private def r4_3_600_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,21,23,2,0⟩, ⟨true,37,49,1,0⟩]
private theorem r4_3_600 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_600_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_600_rows (3 : Fin 4)
    Axis.base r4_3_601 r4_3_610

private def r4_3_586_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,21,23,2,0⟩, ⟨true,37,49,1,0⟩]
private theorem r4_3_586 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_586_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_586_rows (1 : Fin 4)
    Axis.exponent r4_3_587 r4_3_600

private def r4_3_642_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,2⟩, ⟨false,21,23,2,0⟩, ⟨true,53,73,1,0⟩]
private theorem r4_3_642 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_642_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_642_rows
  decide +kernel

private def r4_3_643_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,21,23,2,0⟩, ⟨true,53,73,1,0⟩]
private theorem r4_3_643 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_643_rows := by
  apply verifyCover_sound "HFCAHAHACEIAGAAIGAAAAAA".toUTF8 "AAAAWAAAAUAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAMAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 10 0 r4_3_643_rows
  decide +kernel

private def r4_3_641_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,21,23,2,0⟩, ⟨true,53,73,1,0⟩]
private theorem r4_3_641 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_641_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_641_rows (1 : Fin 4)
    Axis.exponent r4_3_642 r4_3_643

private def r4_3_585_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,21,23,2,0⟩, ⟨true,37,73,1,0⟩]
private theorem r4_3_585 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_585_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_585_rows (3 : Fin 4)
    Axis.base r4_3_586 r4_3_641

private def r4_3_668_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,2⟩, ⟨false,25,29,2,0⟩, ⟨true,37,49,1,0⟩]
private theorem r4_3_668 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_668_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_668_rows
  decide +kernel

private def r4_3_671_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,25,25,2,0⟩, ⟨true,37,41,1,0⟩]
private theorem r4_3_671 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_671_rows := by
  apply verifyCover_sound "CAHAICAEGAAAA".toUTF8 "AAAACAAAAAAAAACAAAAAAAAAIAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 7 0 r4_3_671_rows
  decide +kernel

private def r4_3_684_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,27,29,2,0⟩, ⟨true,37,41,1,0⟩]
private theorem r4_3_684 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_684_rows := by
  apply verifyCover_sound "CAFHIACEAAAAA".toUTF8 "AAAACAAAAAAAAAKAAAAIAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 7 0 r4_3_684_rows
  decide +kernel

private def r4_3_670_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,25,29,2,0⟩, ⟨true,37,41,1,0⟩]
private theorem r4_3_670 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_670_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_670_rows (2 : Fin 4)
    Axis.base r4_3_671 r4_3_684

private def r4_3_697_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,25,29,2,0⟩, ⟨true,45,49,1,0⟩]
private theorem r4_3_697 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_697_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_697_rows
  decide +kernel

private def r4_3_669_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,25,29,2,0⟩, ⟨true,37,49,1,0⟩]
private theorem r4_3_669 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_669_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_669_rows (3 : Fin 4)
    Axis.base r4_3_670 r4_3_697

private def r4_3_667_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,25,29,2,0⟩, ⟨true,37,49,1,0⟩]
private theorem r4_3_667 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_667_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_667_rows (1 : Fin 4)
    Axis.exponent r4_3_668 r4_3_669

private def r4_3_698_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,25,29,2,0⟩, ⟨true,53,73,1,0⟩]
private theorem r4_3_698 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_698_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_698_rows
  decide +kernel

private def r4_3_666_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,25,29,2,0⟩, ⟨true,37,73,1,0⟩]
private theorem r4_3_666 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_666_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_666_rows (3 : Fin 4)
    Axis.base r4_3_667 r4_3_698

private def r4_3_584_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,21,29,2,0⟩, ⟨true,37,73,1,0⟩]
private theorem r4_3_584 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_584_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_584_rows (2 : Fin 4)
    Axis.base r4_3_585 r4_3_666

private def r4_3_699_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,21,29,2,0⟩, ⟨true,77,0,1,0⟩]
private theorem r4_3_699 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_699_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_699_rows
  decide +kernel

private def r4_3_583_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,21,29,2,0⟩, ⟨true,37,0,1,0⟩]
private theorem r4_3_583 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_583_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_583_rows (3 : Fin 4)
    Axis.base r4_3_584 r4_3_699

private def r4_3_267_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,15,29,2,0⟩, ⟨true,37,0,1,0⟩]
private theorem r4_3_267 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_267_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_267_rows (2 : Fin 4)
    Axis.base r4_3_268 r4_3_583

private def r4_3_265_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,15,29,2,0⟩, ⟨true,37,0,1,0⟩]
private theorem r4_3_265 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_265_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_265_rows (0 : Fin 4)
    Axis.exponent r4_3_266 r4_3_267

private def r4_3_177_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,15,29,2,0⟩, ⟨true,17,0,1,0⟩]
private theorem r4_3_177 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_177_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_177_rows (3 : Fin 4)
    Axis.base r4_3_178 r4_3_265

private def r4_3_700_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,31,0,2,0⟩, ⟨true,33,0,1,0⟩]
private theorem r4_3_700 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_700_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_700_rows
  decide +kernel

private def r4_3_176_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,15,0,2,0⟩, ⟨true,17,0,1,0⟩]
private theorem r4_3_176 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_176_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_176_rows (2 : Fin 4)
    Axis.base r4_3_177 r4_3_700

private def r4_3_86_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,7,0,2,0⟩, ⟨true,9,0,1,0⟩]
private theorem r4_3_86 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_86_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_86_rows (2 : Fin 4)
    Axis.base r4_3_87 r4_3_176

private def r4_3_701_rows : Vector Slot 4 := #v[⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,7,0,2,0⟩, ⟨true,9,0,1,0⟩]
private theorem r4_3_701 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_701_rows := by
  apply verifyCover_sound "FHFHFIECAAAAAAAAA".toUTF8 "AAAAQAAAAOAAAAMAAAAKAAAAIAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 9 0 r4_3_701_rows
  decide +kernel

private def r4_3_85_rows : Vector Slot 4 := #v[⟨false,3,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,7,0,2,0⟩, ⟨true,9,0,1,0⟩]
private theorem r4_3_85 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_85_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_85_rows (0 : Fin 4)
    Axis.base r4_3_86 r4_3_701

private def r4_3_83_rows : Vector Slot 4 := #v[⟨false,3,5,2,0⟩, ⟨false,3,5,2,0⟩, ⟨false,7,0,2,0⟩, ⟨true,9,0,1,0⟩]
private theorem r4_3_83 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_83_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_83_rows (1 : Fin 4)
    Axis.base r4_3_84 r4_3_85

private def r4_3_724_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,7,9,2,0⟩, ⟨false,7,9,2,0⟩, ⟨true,9,9,1,0⟩]
private theorem r4_3_724 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_724_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_724_rows
  decide +kernel

private def r4_3_726_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,7,9,2,0⟩, ⟨false,7,9,2,0⟩, ⟨true,13,17,1,0⟩]
private theorem r4_3_726 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_726_rows := by
  apply verifyCover_sound "FADHAIEcAAA".toUTF8 "AAAACAAAAAAAAAIAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 6 0 r4_3_726_rows
  decide +kernel

private def r4_3_737_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,9,2,0⟩, ⟨false,7,9,2,0⟩, ⟨true,13,17,1,0⟩]
private theorem r4_3_737 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_737_rows := by
  apply verifyCover_sound "FADAHACIGAEAAAA".toUTF8 "AAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAIAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 8 0 r4_3_737_rows
  decide +kernel

private def r4_3_725_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,7,9,2,0⟩, ⟨false,7,9,2,0⟩, ⟨true,13,17,1,0⟩]
private theorem r4_3_725 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_725_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_725_rows (0 : Fin 4)
    Axis.exponent r4_3_726 r4_3_737

private def r4_3_723_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,7,9,2,0⟩, ⟨false,7,9,2,0⟩, ⟨true,9,17,1,0⟩]
private theorem r4_3_723 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_723_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_723_rows (3 : Fin 4)
    Axis.base r4_3_724 r4_3_725

private def r4_3_754_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,7,9,2,0⟩, ⟨false,11,13,2,0⟩, ⟨true,13,17,1,0⟩]
private theorem r4_3_754 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_754_rows := by
  apply verifyCover_sound "DHFIAAAAA".toUTF8 "AAAAIAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 5 0 r4_3_754_rows
  decide +kernel

private def r4_3_764_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨true,13,17,1,0⟩]
private theorem r4_3_764 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_764_rows := by
  apply verifyCover_sound "HAFACIAEGAAAIECcAAA".toUTF8 "AAAACAAAAAAAAACAAAAAAAAAIAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 7 0 r4_3_764_rows
  decide +kernel

private def r4_3_783_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,9,9,2,0⟩, ⟨false,11,13,2,0⟩, ⟨true,13,17,1,0⟩]
private theorem r4_3_783 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_783_rows := by
  apply verifyCover_sound "HFIACEAAAAA".toUTF8 "AAAAKAAAAIAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 6 0 r4_3_783_rows
  decide +kernel

private def r4_3_763_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,9,2,0⟩, ⟨false,11,13,2,0⟩, ⟨true,13,17,1,0⟩]
private theorem r4_3_763 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_763_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_763_rows (1 : Fin 4)
    Axis.base r4_3_764 r4_3_783

private def r4_3_753_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,7,9,2,0⟩, ⟨false,11,13,2,0⟩, ⟨true,13,17,1,0⟩]
private theorem r4_3_753 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_753_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_753_rows (0 : Fin 4)
    Axis.exponent r4_3_754 r4_3_763

private def r4_3_794_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,11,13,2,0⟩, ⟨true,13,17,1,0⟩]
private theorem r4_3_794 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_794_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_794_rows
  decide +kernel

private def r4_3_752_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,7,13,2,0⟩, ⟨false,11,13,2,0⟩, ⟨true,13,17,1,0⟩]
private theorem r4_3_752 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_752_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_752_rows (1 : Fin 4)
    Axis.base r4_3_753 r4_3_794

private def r4_3_722_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,7,13,2,0⟩, ⟨false,7,13,2,0⟩, ⟨true,9,17,1,0⟩]
private theorem r4_3_722 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_722_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_722_rows (2 : Fin 4)
    Axis.base r4_3_723 r4_3_752

private def r4_3_797_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,7,9,2,0⟩, ⟨false,7,9,2,0⟩, ⟨true,21,41,1,0⟩]
private theorem r4_3_797 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_797_rows := by
  apply verifyCover_sound "CFAAFADHAHACEHAGdAAAA".toUTF8 "AAAAEAAAACAAAAAAAAAAAAAACAAAAAAAAAOAAAACAAAAAAAAACAAAAAAAAAIAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 10 0 r4_3_797_rows
  decide +kernel

private def r4_3_819_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,7,9,2,0⟩, ⟨false,7,9,2,0⟩, ⟨true,45,0,1,0⟩]
private theorem r4_3_819 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_819_rows := by
  apply verifyCover_sound "FHHHGEAAAGAEAAAAA".toUTF8 "AAAAQAAAAOAAAAMAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 7 0 r4_3_819_rows
  decide +kernel

private def r4_3_837_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,7,7,2,0⟩, ⟨true,45,0,1,0⟩]
private theorem r4_3_837 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_837_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_837_rows
  decide +kernel

private def r4_3_842_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,9,9,2,0⟩, ⟨true,45,49,1,0⟩]
private theorem r4_3_842 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_842_rows := by
  apply verifyCover_sound "CEAHAGAAEHAGCdAAA".toUTF8 "AAAAIAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAIAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 6 0 r4_3_842_rows
  decide +kernel

private def r4_3_859_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,9,9,2,0⟩, ⟨true,53,57,1,0⟩]
private theorem r4_3_859 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_859_rows := by
  apply verifyCover_sound "CAEGAHCAICAAAAGHACIAAAA".toUTF8 "AAAACAAAAAAAAAMAAAACAAAAAAAAAIAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAIAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 8 0 r4_3_859_rows
  decide +kernel

private def r4_3_841_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,9,9,2,0⟩, ⟨true,45,57,1,0⟩]
private theorem r4_3_841 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_841_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_841_rows (3 : Fin 4)
    Axis.base r4_3_842 r4_3_859

private def r4_3_882_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,9,9,2,0⟩, ⟨true,61,89,1,0⟩]
private theorem r4_3_882 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_882_rows := by
  apply verifyCover_sound "HCAEAHGACIEAAAAAA".toUTF8 "AAAAQAAAACAAAAAAAAACAAAAAAAAAKAAAACAAAAAAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 9 0 r4_3_882_rows
  decide +kernel

private def r4_3_840_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,9,9,2,0⟩, ⟨true,45,89,1,0⟩]
private theorem r4_3_840 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_840_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_840_rows (3 : Fin 4)
    Axis.base r4_3_841 r4_3_882

private def r4_3_899_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,9,9,2,0⟩, ⟨true,93,0,1,0⟩]
private theorem r4_3_899 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_899_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_899_rows
  decide +kernel

private def r4_3_839_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,9,9,2,0⟩, ⟨true,45,0,1,0⟩]
private theorem r4_3_839 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_839_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_839_rows (3 : Fin 4)
    Axis.base r4_3_840 r4_3_899

private def r4_3_900_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,9,9,2,0⟩, ⟨false,9,9,2,0⟩, ⟨true,45,0,1,0⟩]
private theorem r4_3_900 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_900_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_900_rows
  decide +kernel

private def r4_3_838_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,9,2,0⟩, ⟨false,9,9,2,0⟩, ⟨true,45,0,1,0⟩]
private theorem r4_3_838 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_838_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_838_rows (1 : Fin 4)
    Axis.base r4_3_839 r4_3_900

private def r4_3_836_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,9,2,0⟩, ⟨false,7,9,2,0⟩, ⟨true,45,0,1,0⟩]
private theorem r4_3_836 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_836_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_836_rows (2 : Fin 4)
    Axis.base r4_3_837 r4_3_838

private def r4_3_818_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,7,9,2,0⟩, ⟨false,7,9,2,0⟩, ⟨true,45,0,1,0⟩]
private theorem r4_3_818 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_818_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_818_rows (0 : Fin 4)
    Axis.exponent r4_3_819 r4_3_836

private def r4_3_796_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,7,9,2,0⟩, ⟨false,7,9,2,0⟩, ⟨true,21,0,1,0⟩]
private theorem r4_3_796 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_796_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_796_rows (3 : Fin 4)
    Axis.base r4_3_797 r4_3_818

private def r4_3_902_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,7,9,2,0⟩, ⟨false,11,13,2,0⟩, ⟨true,21,0,1,0⟩]
private theorem r4_3_902 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_902_rows := by
  apply verifyCover_sound "HCADHFHACAEAIGCAAAAAAAA".toUTF8 "AAAAWAAAACAAAAAAAAASAAAAQAAAAOAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 12 0 r4_3_902_rows
  decide +kernel

private def r4_3_925_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,11,13,2,0⟩, ⟨true,21,0,1,0⟩]
private theorem r4_3_925 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_925_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_925_rows
  decide +kernel

private def r4_3_901_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,7,13,2,0⟩, ⟨false,11,13,2,0⟩, ⟨true,21,0,1,0⟩]
private theorem r4_3_901 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_901_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_901_rows (1 : Fin 4)
    Axis.base r4_3_902 r4_3_925

private def r4_3_795_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,7,13,2,0⟩, ⟨false,7,13,2,0⟩, ⟨true,21,0,1,0⟩]
private theorem r4_3_795 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_795_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_795_rows (2 : Fin 4)
    Axis.base r4_3_796 r4_3_901

private def r4_3_721_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,7,13,2,0⟩, ⟨false,7,13,2,0⟩, ⟨true,9,0,1,0⟩]
private theorem r4_3_721 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_721_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_721_rows (3 : Fin 4)
    Axis.base r4_3_722 r4_3_795

private def r4_3_926_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,7,0,2,0⟩, ⟨false,15,0,2,0⟩, ⟨true,17,0,1,0⟩]
private theorem r4_3_926 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_926_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_926_rows
  decide +kernel

private def r4_3_720_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,7,0,2,0⟩, ⟨false,7,0,2,0⟩, ⟨true,9,0,1,0⟩]
private theorem r4_3_720 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_720_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_720_rows (2 : Fin 4)
    Axis.base r4_3_721 r4_3_926

private def r4_3_927_rows : Vector Slot 4 := #v[⟨false,5,5,2,0⟩, ⟨false,7,0,2,0⟩, ⟨false,7,0,2,0⟩, ⟨true,9,0,1,0⟩]
private theorem r4_3_927 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_927_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_927_rows
  decide +kernel

private def r4_3_719_rows : Vector Slot 4 := #v[⟨false,3,5,2,0⟩, ⟨false,7,0,2,0⟩, ⟨false,7,0,2,0⟩, ⟨true,9,0,1,0⟩]
private theorem r4_3_719 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_719_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_719_rows (0 : Fin 4)
    Axis.base r4_3_720 r4_3_927

private def r4_3_928_rows : Vector Slot 4 := #v[⟨false,7,0,2,0⟩, ⟨false,7,0,2,0⟩, ⟨false,7,0,2,0⟩, ⟨true,9,0,1,0⟩]
private theorem r4_3_928 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_928_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_3_928_rows
  decide +kernel

private def r4_3_718_rows : Vector Slot 4 := #v[⟨false,3,0,2,0⟩, ⟨false,7,0,2,0⟩, ⟨false,7,0,2,0⟩, ⟨true,9,0,1,0⟩]
private theorem r4_3_718 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_718_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_718_rows (0 : Fin 4)
    Axis.base r4_3_719 r4_3_928

private def r4_3_82_rows : Vector Slot 4 := #v[⟨false,3,0,2,0⟩, ⟨false,3,0,2,0⟩, ⟨false,7,0,2,0⟩, ⟨true,9,0,1,0⟩]
private theorem r4_3_82 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_82_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_82_rows (1 : Fin 4)
    Axis.base r4_3_83 r4_3_718

private def r4_3_0_rows : Vector Slot 4 := #v[⟨false,3,0,2,0⟩, ⟨false,3,0,2,0⟩, ⟨false,3,0,2,0⟩, ⟨true,5,0,1,0⟩]
private theorem r4_3_0 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_3_0_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_3_0_rows (2 : Fin 4)
    Axis.base r4_3_1 r4_3_82

theorem covered_4_3 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) (initial (3 : Fin 4)) := r4_3_0

end OddPerfect.SpoofBox
