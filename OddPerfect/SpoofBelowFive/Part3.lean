module

public import OddPerfect.SpoofBelowFive.Part2

public section

namespace OddPerfect.SpoofBox

private def r4_2_1_rows : Vector Slot 4 := #v[⟨false,3,5,2,0⟩, ⟨false,3,5,2,0⟩, ⟨true,5,5,1,0⟩, ⟨false,3,5,2,0⟩]
private theorem r4_2_1 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_1_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_1_rows
  decide +kernel

private def r4_2_5_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,3,3,2,0⟩, ⟨true,5,9,1,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_2_5 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_5_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_5_rows
  decide +kernel

private def r4_2_7_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨true,5,9,1,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_2_7 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_7_rows := by
  apply verifyCover_sound "HAFAHACHAHAGEdAAA".toUTF8 "AAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAKAAAACAAAAAAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 9 0 r4_2_7_rows
  decide +kernel

private def r4_2_25_rows : Vector Slot 4 := #v[⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨true,5,9,1,0⟩, ⟨false,7,13,2,0⟩]
private theorem r4_2_25 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_25_rows := by
  apply verifyCover_sound "FHAGHAECAAAAA".toUTF8 "AAAAMAAAACAAAAAAAAAIAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 7 0 r4_2_25_rows
  decide +kernel

private def r4_2_40_rows : Vector Slot 4 := #v[⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨true,5,5,1,0⟩, ⟨false,15,29,2,0⟩]
private theorem r4_2_40 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_40_rows := by
  apply verifyCover_sound "GHHEACAAAAHAHAECHAAAA".toUTF8 "AAAAKAAAAIAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 7 0 r4_2_40_rows
  decide +kernel

private def r4_2_61_rows : Vector Slot 4 := #v[⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨true,5,5,1,0⟩, ⟨false,31,0,2,0⟩]
private theorem r4_2_61 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_61_rows := by
  apply verifyCover_sound "GAHHHECAHAACHAAAEACAAAA".toUTF8 "AAAACAAAAAAAAAUAAAASAAAAMAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 8 0 r4_2_61_rows
  decide +kernel

private def r4_2_39_rows : Vector Slot 4 := #v[⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨true,5,5,1,0⟩, ⟨false,15,0,2,0⟩]
private theorem r4_2_39 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_39_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_39_rows (3 : Fin 4)
    Axis.base r4_2_40 r4_2_61

private def r4_2_84_rows : Vector Slot 4 := #v[⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨true,9,9,1,0⟩, ⟨false,15,0,2,0⟩]
private theorem r4_2_84 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_84_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_84_rows
  decide +kernel

private def r4_2_38_rows : Vector Slot 4 := #v[⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨true,5,9,1,0⟩, ⟨false,15,0,2,0⟩]
private theorem r4_2_38 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_38_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_38_rows (2 : Fin 4)
    Axis.base r4_2_39 r4_2_84

private def r4_2_24_rows : Vector Slot 4 := #v[⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨true,5,9,1,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_2_24 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_24_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_24_rows (3 : Fin 4)
    Axis.base r4_2_25 r4_2_38

private def r4_2_6_rows : Vector Slot 4 := #v[⟨false,3,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨true,5,9,1,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_2_6 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_6_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_6_rows (0 : Fin 4)
    Axis.base r4_2_7 r4_2_24

private def r4_2_4_rows : Vector Slot 4 := #v[⟨false,3,5,2,0⟩, ⟨false,3,5,2,0⟩, ⟨true,5,9,1,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_2_4 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_4_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_4_rows (1 : Fin 4)
    Axis.base r4_2_5 r4_2_6

private def r4_2_86_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,3,3,2,0⟩, ⟨true,13,0,1,0⟩, ⟨false,13,0,2,0⟩]
private theorem r4_2_86 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_86_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_86_rows
  decide +kernel

private def r4_2_89_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨true,13,25,1,0⟩, ⟨false,13,25,2,0⟩]
private theorem r4_2_89 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_89_rows := by
  apply verifyCover_sound "HACFFAHEHAAAEAHGAAAAA".toUTF8 "AAAACAAAAAAAAASAAAAQAAAACAAAAAAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 9 0 r4_2_89_rows
  decide +kernel

private def r4_2_115_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,27,35,2,0⟩]
private theorem r4_2_115 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_115_rows := by
  apply verifyCover_sound "FHEGdAAEGAHAHAAAA".toUTF8 "AAAAQAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAIAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 7 0 r4_2_115_rows
  decide +kernel

private def r4_2_132_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,37,53,2,0⟩]
private theorem r4_2_132 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_132_rows := by
  apply verifyCover_sound "FHEAGAAEAGAHHEAAAAA".toUTF8 "AAAASAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 8 0 r4_2_132_rows
  decide +kernel

private def r4_2_114_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,27,53,2,0⟩]
private theorem r4_2_114 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_114_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_114_rows (3 : Fin 4)
    Axis.base r4_2_115 r4_2_132

private def r4_2_151_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨true,21,25,1,0⟩, ⟨false,27,53,2,0⟩]
private theorem r4_2_151 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_151_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_151_rows
  decide +kernel

private def r4_2_113_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨true,13,25,1,0⟩, ⟨false,27,53,2,0⟩]
private theorem r4_2_113 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_113_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_113_rows (2 : Fin 4)
    Axis.base r4_2_114 r4_2_151

private def r4_2_153_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,27,53,2,0⟩]
private theorem r4_2_153 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_153_rows := by
  apply verifyCover_sound "HAFAHAECGdAAA".toUTF8 "AAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 7 0 r4_2_153_rows
  decide +kernel

private def r4_2_168_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,21,25,1,0⟩, ⟨false,27,29,2,0⟩]
private theorem r4_2_168 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_168_rows := by
  apply verifyCover_sound "EFACHAAAA".toUTF8 "AAAAIAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 5 0 r4_2_168_rows
  decide +kernel

private def r4_2_178_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,2⟩, ⟨true,21,25,1,0⟩, ⟨false,31,35,2,0⟩]
private theorem r4_2_178 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_178_rows := by
  apply verifyCover_sound "FCHAGdAACAHGAAA".toUTF8 "AAAAIAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 5 0 r4_2_178_rows
  decide +kernel

private def r4_2_193_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨true,21,25,1,0⟩, ⟨false,31,35,2,0⟩]
private theorem r4_2_193 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_193_rows := by
  apply verifyCover_sound "FACHAHAGAAA".toUTF8 "AAAACAAAAAAAAAIAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 6 0 r4_2_193_rows
  decide +kernel

private def r4_2_177_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,21,25,1,0⟩, ⟨false,31,35,2,0⟩]
private theorem r4_2_177 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_177_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_177_rows (1 : Fin 4)
    Axis.exponent r4_2_178 r4_2_193

private def r4_2_167_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,21,25,1,0⟩, ⟨false,27,35,2,0⟩]
private theorem r4_2_167 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_167_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_167_rows (3 : Fin 4)
    Axis.base r4_2_168 r4_2_177

private def r4_2_206_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,2⟩, ⟨true,21,25,1,0⟩, ⟨false,37,43,2,0⟩]
private theorem r4_2_206 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_206_rows := by
  apply verifyCover_sound "FCAHGHAAAGAHAAA".toUTF8 "AAAAOAAAACAAAAAAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 6 0 r4_2_206_rows
  decide +kernel

private def r4_2_221_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨true,21,25,1,0⟩, ⟨false,37,43,2,0⟩]
private theorem r4_2_221 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_221_rows := by
  apply verifyCover_sound "FACAHGHACEAAAAGAHAA".toUTF8 "AAAACAAAAAAAAACAAAAAAAAAKAAAAIAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 8 0 r4_2_221_rows
  decide +kernel

private def r4_2_205_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,21,25,1,0⟩, ⟨false,37,43,2,0⟩]
private theorem r4_2_205 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_205_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_205_rows (1 : Fin 4)
    Axis.exponent r4_2_206 r4_2_221

private def r4_2_240_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,21,25,1,0⟩, ⟨false,45,53,2,0⟩]
private theorem r4_2_240 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_240_rows := by
  apply verifyCover_sound "EAFCHGHEdAAAGAHAAAA".toUTF8 "AAAACAAAAAAAAAQAAAAOAAAAIAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 8 0 r4_2_240_rows
  decide +kernel

private def r4_2_204_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,21,25,1,0⟩, ⟨false,37,53,2,0⟩]
private theorem r4_2_204 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_204_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_204_rows (3 : Fin 4)
    Axis.base r4_2_205 r4_2_240

private def r4_2_166_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,21,25,1,0⟩, ⟨false,27,53,2,0⟩]
private theorem r4_2_166 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_166_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_166_rows (3 : Fin 4)
    Axis.base r4_2_167 r4_2_204

private def r4_2_152_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,13,25,1,0⟩, ⟨false,27,53,2,0⟩]
private theorem r4_2_152 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_152_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_152_rows (2 : Fin 4)
    Axis.base r4_2_153 r4_2_166

private def r4_2_112_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨true,13,25,1,0⟩, ⟨false,27,53,2,0⟩]
private theorem r4_2_112 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_112_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_112_rows (0 : Fin 4)
    Axis.exponent r4_2_113 r4_2_152

private def r4_2_260_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨true,13,25,1,0⟩, ⟨false,55,0,2,0⟩]
private theorem r4_2_260 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_260_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_260_rows
  decide +kernel

private def r4_2_264_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,13,13,1,0⟩, ⟨false,55,109,2,0⟩]
private theorem r4_2_264 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_264_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_264_rows
  decide +kernel

private def r4_2_266_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,17,17,1,0⟩, ⟨false,55,73,2,0⟩]
private theorem r4_2_266 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_266_rows := by
  apply verifyCover_sound "EHCGAAACAGHHAHCAAAAAA".toUTF8 "AAAAUAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAACAAAAAAAAAKAAAAIAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 9 0 r4_2_266_rows
  decide +kernel

private def r4_2_288_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,2⟩, ⟨true,17,17,1,0⟩, ⟨false,75,109,2,0⟩]
private theorem r4_2_288 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_288_rows := by
  apply verifyCover_sound "HCAGAHAHCHAAAAA".toUTF8 "AAAAOAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 8 0 r4_2_288_rows
  decide +kernel

private def r4_2_303_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,0⟩, ⟨false,75,109,2,0⟩]
private theorem r4_2_303 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_303_rows := by
  apply verifyCover_sound "HCGHAHAEdAAACGAAA".toUTF8 "AAAAMAAAAKAAAAIAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAAAAAAEAAAACAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 7 0 r4_2_303_rows
  decide +kernel

private def r4_2_287_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,17,17,1,0⟩, ⟨false,75,109,2,0⟩]
private theorem r4_2_287 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_287_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_287_rows (1 : Fin 4)
    Axis.exponent r4_2_288 r4_2_303

private def r4_2_265_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,17,17,1,0⟩, ⟨false,55,109,2,0⟩]
private theorem r4_2_265 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_265_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_265_rows (3 : Fin 4)
    Axis.base r4_2_266 r4_2_287

private def r4_2_263_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,55,109,2,0⟩]
private theorem r4_2_263 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_263_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_263_rows (2 : Fin 4)
    Axis.base r4_2_264 r4_2_265

private def r4_2_321_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,13,13,1,0⟩, ⟨false,111,0,2,0⟩]
private theorem r4_2_321 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_321_rows := by
  apply verifyCover_sound "HAEGHCdACAAAA".toUTF8 "AAAACAAAAAAAAAKAAAAIAAAAEAAAACAAAAAAAAAAAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 6 0 r4_2_321_rows
  decide +kernel

private def r4_2_336_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,2⟩, ⟨true,17,17,1,0⟩, ⟨false,111,221,2,0⟩]
private theorem r4_2_336 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_336_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_336_rows
  decide +kernel

private def r4_2_339_rows : Vector Slot 4 := #v[⟨false,3,3,4,4⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,0⟩, ⟨false,111,147,2,0⟩]
private theorem r4_2_339 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_339_rows := by
  apply verifyCover_sound "GAHHAHEHAAAEAHAAA".toUTF8 "AAAACAAAAAAAAAOAAAACAAAAAAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 7 0 r4_2_339_rows
  decide +kernel

private def r4_2_358_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,1⟩, ⟨false,111,125,2,0⟩]
private theorem r4_2_358 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_358_rows := by
  apply verifyCover_sound "HACHAEdAA".toUTF8 "AAAACAAAAAAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 5 0 r4_2_358_rows
  decide +kernel

private def r4_2_367_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,1⟩, ⟨false,127,147,2,0⟩]
private theorem r4_2_367 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_367_rows := by
  apply verifyCover_sound "HHCEAHAAACAEAHAHACEAAAA".toUTF8 "AAAAWAAAAIAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 9 0 r4_2_367_rows
  decide +kernel

private def r4_2_357_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,1⟩, ⟨false,111,147,2,0⟩]
private theorem r4_2_357 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_357_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_357_rows (3 : Fin 4)
    Axis.base r4_2_358 r4_2_367

private def r4_2_390_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,5,0⟩, ⟨false,111,147,2,0⟩]
private theorem r4_2_390 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_390_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_390_rows
  decide +kernel

private def r4_2_356_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,0⟩, ⟨false,111,147,2,0⟩]
private theorem r4_2_356 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_356_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_356_rows (2 : Fin 4)
    Axis.exponent r4_2_357 r4_2_390

private def r4_2_338_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,0⟩, ⟨false,111,147,2,0⟩]
private theorem r4_2_338 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_338_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_338_rows (0 : Fin 4)
    Axis.exponent r4_2_339 r4_2_356

private def r4_2_391_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,0⟩, ⟨false,149,221,2,0⟩]
private theorem r4_2_391 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_391_rows := by
  apply verifyCover_sound "CAGAHAHAHACEHHAHAAAAA".toUTF8 "AAAACAAAAAAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAKAAAAIAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 11 0 r4_2_391_rows
  decide +kernel

private def r4_2_337_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,0⟩, ⟨false,111,221,2,0⟩]
private theorem r4_2_337 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_337_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_337_rows (3 : Fin 4)
    Axis.base r4_2_338 r4_2_391

private def r4_2_335_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,17,17,1,0⟩, ⟨false,111,221,2,0⟩]
private theorem r4_2_335 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_335_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_335_rows (1 : Fin 4)
    Axis.exponent r4_2_336 r4_2_337

private def r4_2_413_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,2⟩, ⟨true,17,17,1,0⟩, ⟨false,223,0,2,0⟩]
private theorem r4_2_413 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_413_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_413_rows
  decide +kernel

private def r4_2_416_rows : Vector Slot 4 := #v[⟨false,3,3,4,4⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,0⟩, ⟨false,223,445,2,0⟩]
private theorem r4_2_416 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_416_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_416_rows
  decide +kernel

private def r4_2_418_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,1⟩, ⟨false,223,445,2,0⟩]
private theorem r4_2_418 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_418_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_418_rows
  decide +kernel

private def r4_2_422_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,5,0⟩, ⟨false,223,237,2,0⟩]
private theorem r4_2_422 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_422_rows := by
  apply verifyCover_sound "CEAHHAHAEAAAEHAHACAHAAA".toUTF8 "AAAAMAAAACAAAAAAAAAIAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAKAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 7 0 r4_2_422_rows
  decide +kernel

private def r4_2_445_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,5,0⟩, ⟨false,239,253,2,0⟩]
private theorem r4_2_445 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_445_rows := by
  apply verifyCover_sound "CAEAHAHACHAAA".toUTF8 "AAAACAAAAAAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 7 0 r4_2_445_rows
  decide +kernel

private def r4_2_421_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,5,0⟩, ⟨false,223,253,2,0⟩]
private theorem r4_2_421 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_421_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_421_rows (3 : Fin 4)
    Axis.base r4_2_422 r4_2_445

private def r4_2_458_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,5,0⟩, ⟨false,255,297,2,0⟩]
private theorem r4_2_458 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_458_rows := by
  apply verifyCover_sound "HCAEAHHCAHECAAAAAAA".toUTF8 "AAAASAAAACAAAAAAAAACAAAAAAAAAMAAAAKAAAACAAAAAAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 10 0 r4_2_458_rows
  decide +kernel

private def r4_2_420_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,5,0⟩, ⟨false,223,297,2,0⟩]
private theorem r4_2_420 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_420_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_420_rows (3 : Fin 4)
    Axis.base r4_2_421 r4_2_458

private def r4_2_477_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,5,0⟩, ⟨false,299,445,2,0⟩]
private theorem r4_2_477 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_477_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_477_rows
  decide +kernel

private def r4_2_419_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,5,0⟩, ⟨false,223,445,2,0⟩]
private theorem r4_2_419 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_419_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_419_rows (3 : Fin 4)
    Axis.base r4_2_420 r4_2_477

private def r4_2_417_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,0⟩, ⟨false,223,445,2,0⟩]
private theorem r4_2_417 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_417_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_417_rows (2 : Fin 4)
    Axis.exponent r4_2_418 r4_2_419

private def r4_2_415_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,0⟩, ⟨false,223,445,2,0⟩]
private theorem r4_2_415 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_415_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_415_rows (0 : Fin 4)
    Axis.exponent r4_2_416 r4_2_417

private def r4_2_478_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,0⟩, ⟨false,447,0,2,0⟩]
private theorem r4_2_478 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_478_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_478_rows
  decide +kernel

private def r4_2_414_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨true,17,17,1,0⟩, ⟨false,223,0,2,0⟩]
private theorem r4_2_414 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_414_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_414_rows (3 : Fin 4)
    Axis.base r4_2_415 r4_2_478

private def r4_2_412_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,17,17,1,0⟩, ⟨false,223,0,2,0⟩]
private theorem r4_2_412 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_412_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_412_rows (1 : Fin 4)
    Axis.exponent r4_2_413 r4_2_414

private def r4_2_334_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,17,17,1,0⟩, ⟨false,111,0,2,0⟩]
private theorem r4_2_334 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_334_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_334_rows (3 : Fin 4)
    Axis.base r4_2_335 r4_2_412

private def r4_2_320_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,111,0,2,0⟩]
private theorem r4_2_320 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_320_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_320_rows (2 : Fin 4)
    Axis.base r4_2_321 r4_2_334

private def r4_2_262_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,55,0,2,0⟩]
private theorem r4_2_262 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_262_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_262_rows (3 : Fin 4)
    Axis.base r4_2_263 r4_2_320

private def r4_2_482_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,2⟩, ⟨true,21,25,1,0⟩, ⟨false,55,73,2,0⟩]
private theorem r4_2_482 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_482_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_482_rows
  decide +kernel

private def r4_2_486_rows : Vector Slot 4 := #v[⟨false,3,3,4,4⟩, ⟨false,5,5,4,0⟩, ⟨true,21,21,1,0⟩, ⟨false,55,61,2,0⟩]
private theorem r4_2_486 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_486_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_486_rows
  decide +kernel

private def r4_2_488_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,21,21,1,1⟩, ⟨false,55,61,2,0⟩]
private theorem r4_2_488 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_488_rows := by
  apply verifyCover_sound "HHCAECAIaAAAA".toUTF8 "AAAAMAAAAKAAAACAAAAAAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 7 0 r4_2_488_rows
  decide +kernel

private def r4_2_501_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,21,21,5,0⟩, ⟨false,55,61,2,0⟩]
private theorem r4_2_501 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_501_rows := by
  apply verifyCover_sound "HAHACEIAAAA".toUTF8 "AAAACAAAAAAAAACAAAAAAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 6 0 r4_2_501_rows
  decide +kernel

private def r4_2_487_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨true,21,21,1,0⟩, ⟨false,55,61,2,0⟩]
private theorem r4_2_487 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_487_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_487_rows (2 : Fin 4)
    Axis.exponent r4_2_488 r4_2_501

private def r4_2_485_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨true,21,21,1,0⟩, ⟨false,55,61,2,0⟩]
private theorem r4_2_485 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_485_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_485_rows (0 : Fin 4)
    Axis.exponent r4_2_486 r4_2_487

private def r4_2_512_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨true,21,21,1,0⟩, ⟨false,63,73,2,0⟩]
private theorem r4_2_512 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_512_rows := by
  apply verifyCover_sound "CAGAHHCAEAAAA".toUTF8 "AAAACAAAAAAAAACAAAAAAAAAIAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 7 0 r4_2_512_rows
  decide +kernel

private def r4_2_484_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨true,21,21,1,0⟩, ⟨false,55,73,2,0⟩]
private theorem r4_2_484 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_484_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_484_rows (3 : Fin 4)
    Axis.base r4_2_485 r4_2_512

private def r4_2_525_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨true,25,25,1,0⟩, ⟨false,55,73,2,0⟩]
private theorem r4_2_525 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_525_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_525_rows
  decide +kernel

private def r4_2_483_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨true,21,25,1,0⟩, ⟨false,55,73,2,0⟩]
private theorem r4_2_483 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_483_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_483_rows (2 : Fin 4)
    Axis.base r4_2_484 r4_2_525

private def r4_2_481_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,21,25,1,0⟩, ⟨false,55,73,2,0⟩]
private theorem r4_2_481 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_481_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_481_rows (1 : Fin 4)
    Axis.exponent r4_2_482 r4_2_483

private def r4_2_526_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,21,25,1,0⟩, ⟨false,75,109,2,0⟩]
private theorem r4_2_526 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_526_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_526_rows
  decide +kernel

private def r4_2_480_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,21,25,1,0⟩, ⟨false,55,109,2,0⟩]
private theorem r4_2_480 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_480_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_480_rows (3 : Fin 4)
    Axis.base r4_2_481 r4_2_526

private def r4_2_527_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,21,25,1,0⟩, ⟨false,111,0,2,0⟩]
private theorem r4_2_527 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_527_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_527_rows
  decide +kernel

private def r4_2_479_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,21,25,1,0⟩, ⟨false,55,0,2,0⟩]
private theorem r4_2_479 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_479_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_479_rows (3 : Fin 4)
    Axis.base r4_2_480 r4_2_527

private def r4_2_261_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,13,25,1,0⟩, ⟨false,55,0,2,0⟩]
private theorem r4_2_261 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_261_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_261_rows (2 : Fin 4)
    Axis.base r4_2_262 r4_2_479

private def r4_2_259_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨true,13,25,1,0⟩, ⟨false,55,0,2,0⟩]
private theorem r4_2_259 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_259_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_259_rows (0 : Fin 4)
    Axis.exponent r4_2_260 r4_2_261

private def r4_2_111_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨true,13,25,1,0⟩, ⟨false,27,0,2,0⟩]
private theorem r4_2_111 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_111_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_111_rows (3 : Fin 4)
    Axis.base r4_2_112 r4_2_259

private def r4_2_529_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,29,0,2,0⟩]
private theorem r4_2_529 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_529_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_529_rows
  decide +kernel

private def r4_2_533_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,2⟩, ⟨true,29,37,1,0⟩, ⟨false,29,37,2,0⟩]
private theorem r4_2_533 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_533_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_533_rows
  decide +kernel

private def r4_2_534_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨true,29,37,1,0⟩, ⟨false,29,37,2,0⟩]
private theorem r4_2_534 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_534_rows := by
  apply verifyCover_sound "HCHGEdAAAAFCAHGCAEAAAAA".toUTF8 "AAAAKAAAAIAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAAAAAAMAAAACAAAAAAAAAIAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 8 0 r4_2_534_rows
  decide +kernel

private def r4_2_532_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,29,37,1,0⟩, ⟨false,29,37,2,0⟩]
private theorem r4_2_532 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_532_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_532_rows (1 : Fin 4)
    Axis.exponent r4_2_533 r4_2_534

private def r4_2_557_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,29,57,1,0⟩, ⟨false,39,57,2,0⟩]
private theorem r4_2_557 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_557_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_557_rows
  decide +kernel

private def r4_2_531_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,29,57,1,0⟩, ⟨false,29,57,2,0⟩]
private theorem r4_2_531 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_531_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_531_rows (3 : Fin 4)
    Axis.base r4_2_532 r4_2_557

private def r4_2_558_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,59,0,2,0⟩]
private theorem r4_2_558 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_558_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_558_rows
  decide +kernel

private def r4_2_530_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,29,0,2,0⟩]
private theorem r4_2_530 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_530_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_530_rows (3 : Fin 4)
    Axis.base r4_2_531 r4_2_558

private def r4_2_528_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨true,29,0,1,0⟩, ⟨false,29,0,2,0⟩]
private theorem r4_2_528 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_528_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_528_rows (0 : Fin 4)
    Axis.exponent r4_2_529 r4_2_530

private def r4_2_110_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨true,13,0,1,0⟩, ⟨false,27,0,2,0⟩]
private theorem r4_2_110 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_110_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_110_rows (2 : Fin 4)
    Axis.base r4_2_111 r4_2_528

private def r4_2_88_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨true,13,0,1,0⟩, ⟨false,13,0,2,0⟩]
private theorem r4_2_88 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_88_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_88_rows (3 : Fin 4)
    Axis.base r4_2_89 r4_2_110

private def r4_2_559_rows : Vector Slot 4 := #v[⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨true,13,0,1,0⟩, ⟨false,13,0,2,0⟩]
private theorem r4_2_559 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_559_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_559_rows
  decide +kernel

private def r4_2_87_rows : Vector Slot 4 := #v[⟨false,3,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨true,13,0,1,0⟩, ⟨false,13,0,2,0⟩]
private theorem r4_2_87 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_87_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_87_rows (0 : Fin 4)
    Axis.base r4_2_88 r4_2_559

private def r4_2_85_rows : Vector Slot 4 := #v[⟨false,3,5,2,0⟩, ⟨false,3,5,2,0⟩, ⟨true,13,0,1,0⟩, ⟨false,13,0,2,0⟩]
private theorem r4_2_85 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_85_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_85_rows (1 : Fin 4)
    Axis.base r4_2_86 r4_2_87

private def r4_2_3_rows : Vector Slot 4 := #v[⟨false,3,5,2,0⟩, ⟨false,3,5,2,0⟩, ⟨true,5,0,1,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_2_3 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_3_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_3_rows (2 : Fin 4)
    Axis.base r4_2_4 r4_2_85

private def r4_2_563_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,7,13,2,0⟩, ⟨true,9,13,1,0⟩, ⟨false,7,13,2,0⟩]
private theorem r4_2_563 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_563_rows := by
  apply verifyCover_sound "HADCDFAAFHGAAAADAFAAA".toUTF8 "AAAACAAAAAAAAASAAAAMAAAAEAAAACAAAAAAAAAAAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 8 0 r4_2_563_rows
  decide +kernel

private def r4_2_590_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,7,9,2,0⟩, ⟨true,9,9,1,0⟩, ⟨false,15,29,2,0⟩]
private theorem r4_2_590 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_590_rows := by
  apply verifyCover_sound "DHHGEdAAGAHAEAAAA".toUTF8 "AAAAQAAAAOAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 7 0 r4_2_590_rows
  decide +kernel

private def r4_2_608_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨true,9,9,1,0⟩, ⟨false,15,29,2,0⟩]
private theorem r4_2_608 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_608_rows := by
  apply verifyCover_sound "HAHAGHACEdAAA".toUTF8 "AAAACAAAAAAAAACAAAAAAAAAIAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 7 0 r4_2_608_rows
  decide +kernel

private def r4_2_621_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,9,9,2,0⟩, ⟨true,9,9,1,0⟩, ⟨false,15,29,2,0⟩]
private theorem r4_2_621 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_621_rows := by
  apply verifyCover_sound "HHGCEAAAAGAHACAECIAAAAA".toUTF8 "AAAAWAAAAIAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 9 0 r4_2_621_rows
  decide +kernel

private def r4_2_607_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,9,2,0⟩, ⟨true,9,9,1,0⟩, ⟨false,15,29,2,0⟩]
private theorem r4_2_607 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_607_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_607_rows (1 : Fin 4)
    Axis.base r4_2_608 r4_2_621

private def r4_2_589_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,7,9,2,0⟩, ⟨true,9,9,1,0⟩, ⟨false,15,29,2,0⟩]
private theorem r4_2_589 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_589_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_589_rows (0 : Fin 4)
    Axis.exponent r4_2_590 r4_2_607

private def r4_2_645_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,7,9,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,15,29,2,0⟩]
private theorem r4_2_645 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_645_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_645_rows
  decide +kernel

private def r4_2_650_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨true,13,13,1,0⟩, ⟨false,15,15,2,0⟩]
private theorem r4_2_650 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_650_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_650_rows
  decide +kernel

private def r4_2_652_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨true,13,13,1,0⟩, ⟨false,17,17,2,0⟩]
private theorem r4_2_652 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_652_rows := by
  apply verifyCover_sound "GCAEAACEIAAAA".toUTF8 "AAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 5 0 r4_2_652_rows
  decide +kernel

private def r4_2_665_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨true,13,13,1,0⟩, ⟨false,19,19,2,0⟩]
private theorem r4_2_665 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_665_rows := by
  apply verifyCover_sound "GACAEACIAAA".toUTF8 "AAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 6 0 r4_2_665_rows
  decide +kernel

private def r4_2_651_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨true,13,13,1,0⟩, ⟨false,17,19,2,0⟩]
private theorem r4_2_651 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_651_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_651_rows (3 : Fin 4)
    Axis.base r4_2_652 r4_2_665

private def r4_2_649_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨true,13,13,1,0⟩, ⟨false,15,19,2,0⟩]
private theorem r4_2_649 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_649_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_649_rows (3 : Fin 4)
    Axis.base r4_2_650 r4_2_651

private def r4_2_676_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨true,17,17,1,0⟩, ⟨false,17,19,2,0⟩]
private theorem r4_2_676 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_676_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_676_rows
  decide +kernel

private def r4_2_648_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,15,19,2,0⟩]
private theorem r4_2_648 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_648_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_648_rows (2 : Fin 4)
    Axis.base r4_2_649 r4_2_676

private def r4_2_677_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,21,29,2,0⟩]
private theorem r4_2_677 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_677_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_677_rows
  decide +kernel

private def r4_2_647_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,15,29,2,0⟩]
private theorem r4_2_647 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_647_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_647_rows (3 : Fin 4)
    Axis.base r4_2_648 r4_2_677

private def r4_2_678_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,9,9,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,15,29,2,0⟩]
private theorem r4_2_678 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_678_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_678_rows
  decide +kernel

private def r4_2_646_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,9,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,15,29,2,0⟩]
private theorem r4_2_646 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_646_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_646_rows (1 : Fin 4)
    Axis.base r4_2_647 r4_2_678

private def r4_2_644_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,7,9,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,15,29,2,0⟩]
private theorem r4_2_644 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_644_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_644_rows (0 : Fin 4)
    Axis.exponent r4_2_645 r4_2_646

private def r4_2_588_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,7,9,2,0⟩, ⟨true,9,17,1,0⟩, ⟨false,15,29,2,0⟩]
private theorem r4_2_588 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_588_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_588_rows (2 : Fin 4)
    Axis.base r4_2_589 r4_2_644

private def r4_2_681_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨false,7,9,2,0⟩, ⟨true,9,9,1,0⟩, ⟨false,31,0,2,0⟩]
private theorem r4_2_681 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_681_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_681_rows
  decide +kernel

private def r4_2_685_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨true,9,9,1,0⟩, ⟨false,31,41,2,0⟩]
private theorem r4_2_685 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_685_rows := by
  apply verifyCover_sound "GHCHEAAAHAEAAAA".toUTF8 "AAAAOAAAAMAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 6 0 r4_2_685_rows
  decide +kernel

private def r4_2_701_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨true,9,9,1,1⟩, ⟨false,43,61,2,0⟩]
private theorem r4_2_701 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_701_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_701_rows
  decide +kernel

private def r4_2_703_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨true,9,9,5,0⟩, ⟨false,43,49,2,0⟩]
private theorem r4_2_703 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_703_rows := by
  apply verifyCover_sound "CEHHAAAAA".toUTF8 "AAAAIAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 5 0 r4_2_703_rows
  decide +kernel

private def r4_2_712_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨true,9,9,5,0⟩, ⟨false,51,61,2,0⟩]
private theorem r4_2_712 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_712_rows := by
  apply verifyCover_sound "CAHEHAHCAAAAEAA".toUTF8 "AAAACAAAAAAAAAKAAAAIAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAACAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 7 0 r4_2_712_rows
  decide +kernel

private def r4_2_702_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨true,9,9,5,0⟩, ⟨false,43,61,2,0⟩]
private theorem r4_2_702 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_702_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_702_rows (3 : Fin 4)
    Axis.base r4_2_703 r4_2_712

private def r4_2_700_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨true,9,9,1,0⟩, ⟨false,43,61,2,0⟩]
private theorem r4_2_700 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_700_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_700_rows (2 : Fin 4)
    Axis.exponent r4_2_701 r4_2_702

private def r4_2_684_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨true,9,9,1,0⟩, ⟨false,31,61,2,0⟩]
private theorem r4_2_684 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_684_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_684_rows (3 : Fin 4)
    Axis.base r4_2_685 r4_2_700

private def r4_2_727_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨true,9,9,1,0⟩, ⟨false,63,0,2,0⟩]
private theorem r4_2_727 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_727_rows := by
  apply verifyCover_sound "HGAHCAHEAHHCAAAAAAA".toUTF8 "AAAASAAAACAAAAAAAAAOAAAACAAAAAAAAAKAAAACAAAAAAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 10 0 r4_2_727_rows
  decide +kernel

private def r4_2_683_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨true,9,9,1,0⟩, ⟨false,31,0,2,0⟩]
private theorem r4_2_683 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_683_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_683_rows (3 : Fin 4)
    Axis.base r4_2_684 r4_2_727

private def r4_2_746_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,9,9,2,0⟩, ⟨true,9,9,1,0⟩, ⟨false,31,0,2,0⟩]
private theorem r4_2_746 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_746_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_746_rows
  decide +kernel

private def r4_2_682_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨false,7,9,2,0⟩, ⟨true,9,9,1,0⟩, ⟨false,31,0,2,0⟩]
private theorem r4_2_682 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_682_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_682_rows (1 : Fin 4)
    Axis.base r4_2_683 r4_2_746

private def r4_2_680_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,7,9,2,0⟩, ⟨true,9,9,1,0⟩, ⟨false,31,0,2,0⟩]
private theorem r4_2_680 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_680_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_680_rows (0 : Fin 4)
    Axis.exponent r4_2_681 r4_2_682

private def r4_2_747_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,7,9,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,31,0,2,0⟩]
private theorem r4_2_747 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_747_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_747_rows
  decide +kernel

private def r4_2_679_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,7,9,2,0⟩, ⟨true,9,17,1,0⟩, ⟨false,31,0,2,0⟩]
private theorem r4_2_679 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_679_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_679_rows (2 : Fin 4)
    Axis.base r4_2_680 r4_2_747

private def r4_2_587_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,7,9,2,0⟩, ⟨true,9,17,1,0⟩, ⟨false,15,0,2,0⟩]
private theorem r4_2_587 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_587_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_587_rows (3 : Fin 4)
    Axis.base r4_2_588 r4_2_679

private def r4_2_748_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,11,13,2,0⟩, ⟨true,13,17,1,0⟩, ⟨false,15,0,2,0⟩]
private theorem r4_2_748 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_748_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_748_rows
  decide +kernel

private def r4_2_586_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,7,13,2,0⟩, ⟨true,9,17,1,0⟩, ⟨false,15,0,2,0⟩]
private theorem r4_2_586 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_586_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_586_rows (1 : Fin 4)
    Axis.base r4_2_587 r4_2_748

private def r4_2_749_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,7,13,2,0⟩, ⟨true,21,0,1,0⟩, ⟨false,21,0,2,0⟩]
private theorem r4_2_749 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_749_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_749_rows
  decide +kernel

private def r4_2_585_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,7,13,2,0⟩, ⟨true,9,0,1,0⟩, ⟨false,15,0,2,0⟩]
private theorem r4_2_585 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_585_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_585_rows (2 : Fin 4)
    Axis.base r4_2_586 r4_2_749

private def r4_2_750_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,15,0,2,0⟩, ⟨true,17,0,1,0⟩, ⟨false,15,0,2,0⟩]
private theorem r4_2_750 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_750_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_750_rows
  decide +kernel

private def r4_2_584_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,7,0,2,0⟩, ⟨true,9,0,1,0⟩, ⟨false,15,0,2,0⟩]
private theorem r4_2_584 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_584_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_584_rows (1 : Fin 4)
    Axis.base r4_2_585 r4_2_750

private def r4_2_562_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨false,7,0,2,0⟩, ⟨true,9,0,1,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_2_562 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_562_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_562_rows (3 : Fin 4)
    Axis.base r4_2_563 r4_2_584

private def r4_2_751_rows : Vector Slot 4 := #v[⟨false,5,5,2,0⟩, ⟨false,7,0,2,0⟩, ⟨true,9,0,1,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_2_751 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_751_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_751_rows
  decide +kernel

private def r4_2_561_rows : Vector Slot 4 := #v[⟨false,3,5,2,0⟩, ⟨false,7,0,2,0⟩, ⟨true,9,0,1,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_2_561 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_561_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_561_rows (0 : Fin 4)
    Axis.base r4_2_562 r4_2_751

private def r4_2_752_rows : Vector Slot 4 := #v[⟨false,7,0,2,0⟩, ⟨false,7,0,2,0⟩, ⟨true,9,0,1,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_2_752 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_752_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_2_752_rows
  decide +kernel

private def r4_2_560_rows : Vector Slot 4 := #v[⟨false,3,0,2,0⟩, ⟨false,7,0,2,0⟩, ⟨true,9,0,1,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_2_560 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_560_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_560_rows (0 : Fin 4)
    Axis.base r4_2_561 r4_2_752

private def r4_2_2_rows : Vector Slot 4 := #v[⟨false,3,0,2,0⟩, ⟨false,3,0,2,0⟩, ⟨true,5,0,1,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_2_2 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_2_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_2_rows (1 : Fin 4)
    Axis.base r4_2_3 r4_2_560

private def r4_2_0_rows : Vector Slot 4 := #v[⟨false,3,0,2,0⟩, ⟨false,3,0,2,0⟩, ⟨true,5,0,1,0⟩, ⟨false,3,0,2,0⟩]
private theorem r4_2_0 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_2_0_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_2_0_rows (3 : Fin 4)
    Axis.base r4_2_1 r4_2_2

theorem covered_4_2 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) (initial (2 : Fin 4)) := r4_2_0

end OddPerfect.SpoofBox
