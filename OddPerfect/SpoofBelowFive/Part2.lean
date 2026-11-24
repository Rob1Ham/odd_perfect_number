module

public import OddPerfect.SpoofBelowFive.Part1

public section

namespace OddPerfect.SpoofBox

private def r4_1_1_rows : Vector Slot 4 := #v[⟨false,3,5,2,0⟩, ⟨true,5,5,1,0⟩, ⟨false,3,5,2,0⟩, ⟨false,3,5,2,0⟩]
private theorem r4_1_1 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_1_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_1_rows
  decide +kernel

private def r4_1_4_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨true,5,1,1,0⟩, ⟨false,3,3,2,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_1_4 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_4_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_4_rows
  decide +kernel

private def r4_1_6_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨true,5,5,1,0⟩, ⟨false,5,5,2,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_1_6 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_6_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_6_rows
  decide +kernel

private def r4_1_8_rows : Vector Slot 4 := #v[⟨false,5,5,2,0⟩, ⟨true,5,5,1,0⟩, ⟨false,5,5,2,0⟩, ⟨false,7,13,2,0⟩]
private theorem r4_1_8 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_8_rows := by
  apply verifyCover_sound "HAEHAGCAAAA".toUTF8 "AAAACAAAAAAAAAIAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 6 0 r4_1_8_rows
  decide +kernel

private def r4_1_20_rows : Vector Slot 4 := #v[⟨false,5,5,2,0⟩, ⟨true,5,5,1,0⟩, ⟨false,5,5,2,0⟩, ⟨false,15,29,2,0⟩]
private theorem r4_1_20 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_20_rows := by
  apply verifyCover_sound "EHHGACAAAAHAHAGCHAAAA".toUTF8 "AAAAKAAAAIAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 7 0 r4_1_20_rows
  decide +kernel

private def r4_1_41_rows : Vector Slot 4 := #v[⟨false,5,5,2,0⟩, ⟨true,5,5,1,0⟩, ⟨false,5,5,2,0⟩, ⟨false,31,0,2,0⟩]
private theorem r4_1_41 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_41_rows := by
  apply verifyCover_sound "EAHHHGCAHAACHAAAGACAAAA".toUTF8 "AAAACAAAAAAAAAUAAAASAAAAMAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 8 0 r4_1_41_rows
  decide +kernel

private def r4_1_19_rows : Vector Slot 4 := #v[⟨false,5,5,2,0⟩, ⟨true,5,5,1,0⟩, ⟨false,5,5,2,0⟩, ⟨false,15,0,2,0⟩]
private theorem r4_1_19 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_19_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_19_rows (3 : Fin 4)
    Axis.base r4_1_20 r4_1_41

private def r4_1_7_rows : Vector Slot 4 := #v[⟨false,5,5,2,0⟩, ⟨true,5,5,1,0⟩, ⟨false,5,5,2,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_1_7 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_7_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_7_rows (3 : Fin 4)
    Axis.base r4_1_8 r4_1_19

private def r4_1_5_rows : Vector Slot 4 := #v[⟨false,3,5,2,0⟩, ⟨true,5,5,1,0⟩, ⟨false,5,5,2,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_1_5 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_5_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_5_rows (0 : Fin 4)
    Axis.base r4_1_6 r4_1_7

private def r4_1_3_rows : Vector Slot 4 := #v[⟨false,3,5,2,0⟩, ⟨true,5,5,1,0⟩, ⟨false,3,5,2,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_1_3 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_3_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_3_rows (2 : Fin 4)
    Axis.base r4_1_4 r4_1_5

private def r4_1_68_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨true,5,9,1,0⟩, ⟨false,7,13,2,0⟩, ⟨false,7,13,2,0⟩]
private theorem r4_1_68 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_68_rows := by
  apply verifyCover_sound "DAHAFCHEAAAACAHAFEAAA".toUTF8 "AAAACAAAAAAAAACAAAAAAAAAIAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 8 0 r4_1_68_rows
  decide +kernel

private def r4_1_92_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨true,5,5,1,0⟩, ⟨false,7,9,2,0⟩, ⟨false,15,0,2,0⟩]
private theorem r4_1_92 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_92_rows := by
  apply verifyCover_sound "HAECFAHHHAHAGAHAAAAAA".toUTF8 "AAAACAAAAAAAAASAAAAQAAAACAAAAAAAAAMAAAAKAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 11 0 r4_1_92_rows
  decide +kernel

private def r4_1_114_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨true,5,5,1,0⟩, ⟨false,11,13,2,0⟩, ⟨false,15,29,2,0⟩]
private theorem r4_1_114 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_114_rows := by
  apply verifyCover_sound "ECHFAHAAFHHAAAAAA".toUTF8 "AAAAQAAAAOAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 7 0 r4_1_114_rows
  decide +kernel

private def r4_1_133_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,11,13,2,0⟩, ⟨false,31,0,2,0⟩]
private theorem r4_1_133 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_133_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_133_rows
  decide +kernel

private def r4_1_136_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,13,2,0⟩, ⟨false,31,41,2,0⟩]
private theorem r4_1_136 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_136_rows := by
  apply verifyCover_sound "FAHCHAHAAACAHAHCGAAAA".toUTF8 "AAAACAAAAAAAAAIAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 8 0 r4_1_136_rows
  decide +kernel

private def r4_1_157_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,13,2,0⟩, ⟨false,43,61,2,0⟩]
private theorem r4_1_157 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_157_rows := by
  apply verifyCover_sound "FAA".toUTF8 "AAAACAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 2 0 r4_1_157_rows
  decide +kernel

private def r4_1_135_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,13,2,0⟩, ⟨false,31,61,2,0⟩]
private theorem r4_1_135 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_135_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_135_rows (3 : Fin 4)
    Axis.base r4_1_136 r4_1_157

private def r4_1_163_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,2,0⟩, ⟨false,63,83,2,0⟩]
private theorem r4_1_163 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_163_rows := by
  apply verifyCover_sound "CHHAHAGAAAA".toUTF8 "AAAAKAAAAIAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 6 0 r4_1_163_rows
  decide +kernel

private def r4_1_175_rows : Vector Slot 4 := #v[⟨false,3,3,4,4⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,2,0⟩, ⟨false,85,125,2,0⟩]
private theorem r4_1_175 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_175_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_175_rows
  decide +kernel

private def r4_1_178_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,2,0⟩, ⟨false,85,91,2,0⟩]
private theorem r4_1_178 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_178_rows := by
  apply verifyCover_sound "HAGCdAA".toUTF8 "AAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 4 0 r4_1_178_rows
  decide +kernel

private def r4_1_185_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,2,0⟩, ⟨false,93,101,2,0⟩]
private theorem r4_1_185 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_185_rows := by
  apply verifyCover_sound "HGCAHCAAAAGACAHAHAA".toUTF8 "AAAAKAAAAIAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 6 0 r4_1_185_rows
  decide +kernel

private def r4_1_177_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,2,0⟩, ⟨false,85,101,2,0⟩]
private theorem r4_1_177 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_177_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_177_rows (3 : Fin 4)
    Axis.base r4_1_178 r4_1_185

private def r4_1_204_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,2,0⟩, ⟨false,103,125,2,0⟩]
private theorem r4_1_204 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_204_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_204_rows
  decide +kernel

private def r4_1_176_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,2,0⟩, ⟨false,85,125,2,0⟩]
private theorem r4_1_176 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_176_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_176_rows (3 : Fin 4)
    Axis.base r4_1_177 r4_1_204

private def r4_1_174_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,2,0⟩, ⟨false,85,125,2,0⟩]
private theorem r4_1_174 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_174_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_174_rows (0 : Fin 4)
    Axis.exponent r4_1_175 r4_1_176

private def r4_1_162_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,11,2,0⟩, ⟨false,63,125,2,0⟩]
private theorem r4_1_162 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_162_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_162_rows (3 : Fin 4)
    Axis.base r4_1_163 r4_1_174

private def r4_1_205_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,1,1⟩, ⟨false,13,13,2,0⟩, ⟨false,63,125,2,0⟩]
private theorem r4_1_205 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_205_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_205_rows
  decide +kernel

private def r4_1_161_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,13,2,0⟩, ⟨false,63,125,2,0⟩]
private theorem r4_1_161 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_161_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_161_rows (2 : Fin 4)
    Axis.base r4_1_162 r4_1_205

private def r4_1_206_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,13,2,0⟩, ⟨false,127,0,2,0⟩]
private theorem r4_1_206 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_206_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_206_rows
  decide +kernel

private def r4_1_160_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,13,2,0⟩, ⟨false,63,0,2,0⟩]
private theorem r4_1_160 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_160_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_160_rows (3 : Fin 4)
    Axis.base r4_1_161 r4_1_206

private def r4_1_134_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,13,2,0⟩, ⟨false,31,0,2,0⟩]
private theorem r4_1_134 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_134_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_134_rows (3 : Fin 4)
    Axis.base r4_1_135 r4_1_160

private def r4_1_132_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨true,5,5,1,1⟩, ⟨false,11,13,2,0⟩, ⟨false,31,0,2,0⟩]
private theorem r4_1_132 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_132_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_132_rows (0 : Fin 4)
    Axis.exponent r4_1_133 r4_1_134

private def r4_1_209_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,11,13,2,0⟩, ⟨false,31,61,2,0⟩]
private theorem r4_1_209 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_209_rows := by
  apply verifyCover_sound "HAFAHHHAGAAAA".toUTF8 "AAAACAAAAAAAAACAAAAAAAAAIAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 7 0 r4_1_209_rows
  decide +kernel

private def r4_1_223_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,11,13,2,0⟩, ⟨false,63,125,2,0⟩]
private theorem r4_1_223 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_223_rows := by
  apply verifyCover_sound "FAA".toUTF8 "AAAACAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 2 0 r4_1_223_rows
  decide +kernel

private def r4_1_229_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,11,11,2,0⟩, ⟨false,127,169,2,0⟩]
private theorem r4_1_229 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_229_rows := by
  apply verifyCover_sound "HHGHHAEAAAAGAHAHAHEAAAA".toUTF8 "AAAAWAAAAKAAAAIAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 8 0 r4_1_229_rows
  decide +kernel

private def r4_1_252_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,11,11,2,0⟩, ⟨false,171,253,2,0⟩]
private theorem r4_1_252 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_252_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_252_rows
  decide +kernel

private def r4_1_228_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,11,11,2,0⟩, ⟨false,127,253,2,0⟩]
private theorem r4_1_228 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_228_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_228_rows (3 : Fin 4)
    Axis.base r4_1_229 r4_1_252

private def r4_1_253_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,11,11,2,0⟩, ⟨false,255,0,2,0⟩]
private theorem r4_1_253 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_253_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_253_rows
  decide +kernel

private def r4_1_227_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,11,11,2,0⟩, ⟨false,127,0,2,0⟩]
private theorem r4_1_227 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_227_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_227_rows (3 : Fin 4)
    Axis.base r4_1_228 r4_1_253

private def r4_1_254_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,13,13,2,0⟩, ⟨false,127,0,2,0⟩]
private theorem r4_1_254 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_254_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_254_rows
  decide +kernel

private def r4_1_226_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,11,13,2,0⟩, ⟨false,127,0,2,0⟩]
private theorem r4_1_226 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_226_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_226_rows (2 : Fin 4)
    Axis.base r4_1_227 r4_1_254

private def r4_1_222_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,11,13,2,0⟩, ⟨false,63,0,2,0⟩]
private theorem r4_1_222 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_222_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_222_rows (3 : Fin 4)
    Axis.base r4_1_223 r4_1_226

private def r4_1_208_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,11,13,2,0⟩, ⟨false,31,0,2,0⟩]
private theorem r4_1_208 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_208_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_208_rows (3 : Fin 4)
    Axis.base r4_1_209 r4_1_222

private def r4_1_255_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,11,13,2,0⟩, ⟨false,31,0,2,0⟩]
private theorem r4_1_255 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_255_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_255_rows
  decide +kernel

private def r4_1_207_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨true,5,5,5,0⟩, ⟨false,11,13,2,0⟩, ⟨false,31,0,2,0⟩]
private theorem r4_1_207 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_207_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_207_rows (0 : Fin 4)
    Axis.exponent r4_1_208 r4_1_255

private def r4_1_131_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨true,5,5,1,0⟩, ⟨false,11,13,2,0⟩, ⟨false,31,0,2,0⟩]
private theorem r4_1_131 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_131_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_131_rows (1 : Fin 4)
    Axis.exponent r4_1_132 r4_1_207

private def r4_1_113_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨true,5,5,1,0⟩, ⟨false,11,13,2,0⟩, ⟨false,15,0,2,0⟩]
private theorem r4_1_113 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_113_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_113_rows (3 : Fin 4)
    Axis.base r4_1_114 r4_1_131

private def r4_1_91_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨true,5,5,1,0⟩, ⟨false,7,13,2,0⟩, ⟨false,15,0,2,0⟩]
private theorem r4_1_91 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_91_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_91_rows (2 : Fin 4)
    Axis.base r4_1_92 r4_1_113

private def r4_1_259_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨true,9,9,1,0⟩, ⟨false,9,9,2,0⟩, ⟨false,15,29,2,0⟩]
private theorem r4_1_259 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_259_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_259_rows
  decide +kernel

private def r4_1_260_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,9,9,1,0⟩, ⟨false,9,9,2,0⟩, ⟨false,15,29,2,0⟩]
private theorem r4_1_260 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_260_rows := by
  apply verifyCover_sound "HHECGAAAAEAHACAGCIAAAAA".toUTF8 "AAAAWAAAAIAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 9 0 r4_1_260_rows
  decide +kernel

private def r4_1_258_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨true,9,9,1,0⟩, ⟨false,9,9,2,0⟩, ⟨false,15,29,2,0⟩]
private theorem r4_1_258 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_258_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_258_rows (0 : Fin 4)
    Axis.exponent r4_1_259 r4_1_260

private def r4_1_283_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨true,9,9,1,0⟩, ⟨false,11,13,2,0⟩, ⟨false,15,29,2,0⟩]
private theorem r4_1_283 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_283_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_283_rows
  decide +kernel

private def r4_1_257_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨true,9,9,1,0⟩, ⟨false,9,13,2,0⟩, ⟨false,15,29,2,0⟩]
private theorem r4_1_257 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_257_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_257_rows (2 : Fin 4)
    Axis.base r4_1_258 r4_1_283

private def r4_1_284_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨true,9,9,1,0⟩, ⟨false,9,13,2,0⟩, ⟨false,31,0,2,0⟩]
private theorem r4_1_284 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_284_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_284_rows
  decide +kernel

private def r4_1_256_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨true,9,9,1,0⟩, ⟨false,9,13,2,0⟩, ⟨false,15,0,2,0⟩]
private theorem r4_1_256 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_256_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_256_rows (3 : Fin 4)
    Axis.base r4_1_257 r4_1_284

private def r4_1_90_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨true,5,9,1,0⟩, ⟨false,7,13,2,0⟩, ⟨false,15,0,2,0⟩]
private theorem r4_1_90 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_90_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_90_rows (1 : Fin 4)
    Axis.base r4_1_91 r4_1_256

private def r4_1_289_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨true,5,5,1,1⟩, ⟨false,15,29,2,0⟩, ⟨false,15,29,2,0⟩]
private theorem r4_1_289 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_289_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_289_rows
  decide +kernel

private def r4_1_291_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,1,1⟩, ⟨false,15,19,2,0⟩, ⟨false,15,19,2,0⟩]
private theorem r4_1_291 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_291_rows := by
  apply verifyCover_sound "HAFAHAFACAA".toUTF8 "AAAACAAAAAAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 6 0 r4_1_291_rows
  decide +kernel

private def r4_1_303_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,1,1⟩, ⟨false,15,19,2,0⟩, ⟨false,21,29,2,0⟩]
private theorem r4_1_303 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_303_rows := by
  apply verifyCover_sound "FHAHCGdAACAHAAHFHCAAAAA".toUTF8 "AAAAOAAAACAAAAAAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAIAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 6 0 r4_1_303_rows
  decide +kernel

private def r4_1_326_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,1,1⟩, ⟨false,21,29,2,0⟩, ⟨false,21,29,2,0⟩]
private theorem r4_1_326 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_326_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_326_rows
  decide +kernel

private def r4_1_302_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,1,1⟩, ⟨false,15,29,2,0⟩, ⟨false,21,29,2,0⟩]
private theorem r4_1_302 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_302_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_302_rows (2 : Fin 4)
    Axis.base r4_1_303 r4_1_326

private def r4_1_290_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,1,1⟩, ⟨false,15,29,2,0⟩, ⟨false,15,29,2,0⟩]
private theorem r4_1_290 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_290_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_290_rows (3 : Fin 4)
    Axis.base r4_1_291 r4_1_302

private def r4_1_288_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨true,5,5,1,1⟩, ⟨false,15,29,2,0⟩, ⟨false,15,29,2,0⟩]
private theorem r4_1_288 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_288_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_288_rows (0 : Fin 4)
    Axis.exponent r4_1_289 r4_1_290

private def r4_1_327_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨true,5,5,5,0⟩, ⟨false,15,29,2,0⟩, ⟨false,15,29,2,0⟩]
private theorem r4_1_327 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_327_rows := by
  apply verifyCover_sound "CHAFFAHFAHAAAAA".toUTF8 "AAAAOAAAACAAAAAAAAAKAAAACAAAAAAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 8 0 r4_1_327_rows
  decide +kernel

private def r4_1_287_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨true,5,5,1,0⟩, ⟨false,15,29,2,0⟩, ⟨false,15,29,2,0⟩]
private theorem r4_1_287 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_287_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_287_rows (1 : Fin 4)
    Axis.exponent r4_1_288 r4_1_327

private def r4_1_344_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨true,5,5,1,1⟩, ⟨false,15,29,2,0⟩, ⟨false,31,0,2,0⟩]
private theorem r4_1_344 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_344_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_344_rows
  decide +kernel

private def r4_1_346_rows : Vector Slot 4 := #v[⟨false,3,3,2,2⟩, ⟨true,5,5,5,0⟩, ⟨false,15,29,2,0⟩, ⟨false,31,0,2,0⟩]
private theorem r4_1_346 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_346_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_346_rows
  decide +kernel

private def r4_1_349_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,15,19,2,0⟩, ⟨false,31,61,2,0⟩]
private theorem r4_1_349 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_349_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_349_rows
  decide +kernel

private def r4_1_352_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,15,15,2,0⟩, ⟨false,63,125,2,0⟩]
private theorem r4_1_352 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_352_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_352_rows
  decide +kernel

private def r4_1_354_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,19,2,0⟩, ⟨false,63,83,2,0⟩]
private theorem r4_1_354 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_354_rows := by
  apply verifyCover_sound "FACHHAHAHGAEAAAAA".toUTF8 "AAAACAAAAAAAAAOAAAAMAAAACAAAAAAAAACAAAAAAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 9 0 r4_1_354_rows
  decide +kernel

private def r4_1_372_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,85,125,2,0⟩]
private theorem r4_1_372 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_372_rows := by
  apply verifyCover_sound "CHAHAHAHGHAEAAAGAHAAA".toUTF8 "AAAAUAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAIAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 9 0 r4_1_372_rows
  decide +kernel

private def r4_1_394_rows : Vector Slot 4 := #v[⟨false,3,3,4,4⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,2,0⟩, ⟨false,85,125,2,0⟩]
private theorem r4_1_394 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_394_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_394_rows
  decide +kernel

private def r4_1_396_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,2,0⟩, ⟨false,85,101,2,0⟩]
private theorem r4_1_396 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_396_rows := by
  apply verifyCover_sound "HHACHAGAAAHCAHAGAECAAAA".toUTF8 "AAAAKAAAACAAAAAAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAMAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 8 0 r4_1_396_rows
  decide +kernel

private def r4_1_419_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,2,0⟩, ⟨false,103,125,2,0⟩]
private theorem r4_1_419 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_419_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_419_rows
  decide +kernel

private def r4_1_395_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,2,0⟩, ⟨false,85,125,2,0⟩]
private theorem r4_1_395 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_395_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_395_rows (3 : Fin 4)
    Axis.base r4_1_396 r4_1_419

private def r4_1_393_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,2,0⟩, ⟨false,85,125,2,0⟩]
private theorem r4_1_393 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_393_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_393_rows (0 : Fin 4)
    Axis.exponent r4_1_394 r4_1_395

private def r4_1_371_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,19,2,0⟩, ⟨false,85,125,2,0⟩]
private theorem r4_1_371 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_371_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_371_rows (2 : Fin 4)
    Axis.base r4_1_372 r4_1_393

private def r4_1_353_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,19,2,0⟩, ⟨false,63,125,2,0⟩]
private theorem r4_1_353 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_353_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_353_rows (3 : Fin 4)
    Axis.base r4_1_354 r4_1_371

private def r4_1_351_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,15,19,2,0⟩, ⟨false,63,125,2,0⟩]
private theorem r4_1_351 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_351_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_351_rows (2 : Fin 4)
    Axis.base r4_1_352 r4_1_353

private def r4_1_421_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,15,15,2,0⟩, ⟨false,127,0,2,0⟩]
private theorem r4_1_421 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_421_rows := by
  apply verifyCover_sound "HACHAHAHAHAGHAHAEdAAA".toUTF8 "AAAACAAAAAAAAASAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAIAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 11 0 r4_1_421_rows
  decide +kernel

private def r4_1_445_rows : Vector Slot 4 := #v[⟨false,3,3,4,4⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,127,253,2,0⟩]
private theorem r4_1_445 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_445_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_445_rows
  decide +kernel

private def r4_1_447_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,127,169,2,0⟩]
private theorem r4_1_447 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_447_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_447_rows
  decide +kernel

private def r4_1_449_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,171,203,2,0⟩]
private theorem r4_1_449 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_449_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_449_rows
  decide +kernel

private def r4_1_451_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,205,225,2,0⟩]
private theorem r4_1_451 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_451_rows := by
  apply verifyCover_sound "CHAHGHAEAAAGAAA".toUTF8 "AAAAOAAAACAAAAAAAAAIAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAACAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 7 0 r4_1_451_rows
  decide +kernel

private def r4_1_467_rows : Vector Slot 4 := #v[⟨false,3,3,6,6⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,227,253,2,0⟩]
private theorem r4_1_467 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_467_rows := by
  apply verifyCover_sound "HHGAHEAAEAHAAAA".toUTF8 "AAAAOAAAAMAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 7 0 r4_1_467_rows
  decide +kernel

private def r4_1_483_rows : Vector Slot 4 := #v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,227,239,2,0⟩]
private theorem r4_1_483 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_483_rows := by
  apply verifyCover_sound "HAGHAECAAAA".toUTF8 "AAAACAAAAAAAAAIAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 6 0 r4_1_483_rows
  decide +kernel

private def r4_1_495_rows : Vector Slot 4 := #v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,2⟩, ⟨false,241,253,2,0⟩]
private theorem r4_1_495 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_495_rows := by
  apply verifyCover_sound "HHEACAAEACAHAAA".toUTF8 "AAAAOAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 6 0 r4_1_495_rows
  decide +kernel

private def r4_1_510_rows : Vector Slot 4 := #v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,4,0⟩, ⟨false,241,253,2,0⟩]
private theorem r4_1_510 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_510_rows := by
  apply verifyCover_sound "HAHECHAAAAECAHAACHAAA".toUTF8 "AAAACAAAAAAAAAIAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAEAAAACAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 6 0 r4_1_510_rows
  decide +kernel

private def r4_1_494_rows : Vector Slot 4 := #v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,241,253,2,0⟩]
private theorem r4_1_494 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_494_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_494_rows (2 : Fin 4)
    Axis.exponent r4_1_495 r4_1_510

private def r4_1_482_rows : Vector Slot 4 := #v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,227,253,2,0⟩]
private theorem r4_1_482 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_482_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_482_rows (3 : Fin 4)
    Axis.base r4_1_483 r4_1_494

private def r4_1_466_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,227,253,2,0⟩]
private theorem r4_1_466 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_466_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_466_rows (0 : Fin 4)
    Axis.exponent r4_1_467 r4_1_482

private def r4_1_450_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,205,253,2,0⟩]
private theorem r4_1_450 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_450_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_450_rows (3 : Fin 4)
    Axis.base r4_1_451 r4_1_466

private def r4_1_448_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,171,253,2,0⟩]
private theorem r4_1_448 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_448_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_448_rows (3 : Fin 4)
    Axis.base r4_1_449 r4_1_450

private def r4_1_446_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,127,253,2,0⟩]
private theorem r4_1_446 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_446_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_446_rows (3 : Fin 4)
    Axis.base r4_1_447 r4_1_448

private def r4_1_444_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,127,253,2,0⟩]
private theorem r4_1_444 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_444_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_444_rows (0 : Fin 4)
    Axis.exponent r4_1_445 r4_1_446

private def r4_1_531_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,2,0⟩, ⟨false,127,253,2,0⟩]
private theorem r4_1_531 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_531_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_531_rows
  decide +kernel

private def r4_1_443_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,19,2,0⟩, ⟨false,127,253,2,0⟩]
private theorem r4_1_443 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_443_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_443_rows (2 : Fin 4)
    Axis.base r4_1_444 r4_1_531

private def r4_1_534_rows : Vector Slot 4 := #v[⟨false,3,3,4,4⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,255,0,2,0⟩]
private theorem r4_1_534 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_534_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_534_rows
  decide +kernel

private def r4_1_535_rows : Vector Slot 4 := #v[⟨false,3,3,6,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,255,0,2,0⟩]
private theorem r4_1_535 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_535_rows := by
  apply verifyCover_sound "HHHHCAHGAHEACAHAAAAAAAA".toUTF8 "AAAAWAAAAUAAAASAAAAQAAAACAAAAAAAAAMAAAACAAAAAAAAAIAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 12 0 r4_1_535_rows
  decide +kernel

private def r4_1_533_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,17,2,0⟩, ⟨false,255,0,2,0⟩]
private theorem r4_1_533 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_533_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_533_rows (0 : Fin 4)
    Axis.exponent r4_1_534 r4_1_535

private def r4_1_558_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,2,0⟩, ⟨false,255,0,2,0⟩]
private theorem r4_1_558 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_558_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_558_rows
  decide +kernel

private def r4_1_532_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,19,2,0⟩, ⟨false,255,0,2,0⟩]
private theorem r4_1_532 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_532_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_532_rows (2 : Fin 4)
    Axis.base r4_1_533 r4_1_558

private def r4_1_442_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,17,19,2,0⟩, ⟨false,127,0,2,0⟩]
private theorem r4_1_442 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_442_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_442_rows (3 : Fin 4)
    Axis.base r4_1_443 r4_1_532

private def r4_1_420_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,15,19,2,0⟩, ⟨false,127,0,2,0⟩]
private theorem r4_1_420 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_420_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_420_rows (2 : Fin 4)
    Axis.base r4_1_421 r4_1_442

private def r4_1_350_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,15,19,2,0⟩, ⟨false,63,0,2,0⟩]
private theorem r4_1_350 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_350_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_350_rows (3 : Fin 4)
    Axis.base r4_1_351 r4_1_420

private def r4_1_348_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,15,19,2,0⟩, ⟨false,31,0,2,0⟩]
private theorem r4_1_348 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_348_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_348_rows (3 : Fin 4)
    Axis.base r4_1_349 r4_1_350

private def r4_1_562_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,21,23,2,0⟩, ⟨false,31,41,2,0⟩]
private theorem r4_1_562 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_562_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_562_rows
  decide +kernel

private def r4_1_564_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,25,29,2,0⟩, ⟨false,31,35,2,0⟩]
private theorem r4_1_564 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_564_rows := by
  apply verifyCover_sound "FACHFAAAHAFAHAA".toUTF8 "AAAACAAAAAAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 6 0 r4_1_564_rows
  decide +kernel

private def r4_1_579_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,25,29,2,0⟩, ⟨false,37,41,2,0⟩]
private theorem r4_1_579 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_579_rows := by
  apply verifyCover_sound "FCAACAHFAAA".toUTF8 "AAAAEAAAACAAAAAAAAAAAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 5 0 r4_1_579_rows
  decide +kernel

private def r4_1_563_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,25,29,2,0⟩, ⟨false,31,41,2,0⟩]
private theorem r4_1_563 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_563_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_563_rows (3 : Fin 4)
    Axis.base r4_1_564 r4_1_579

private def r4_1_561_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,21,29,2,0⟩, ⟨false,31,41,2,0⟩]
private theorem r4_1_561 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_561_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_561_rows (2 : Fin 4)
    Axis.base r4_1_562 r4_1_563

private def r4_1_590_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,21,29,2,0⟩, ⟨false,43,61,2,0⟩]
private theorem r4_1_590 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_590_rows := by
  apply verifyCover_sound "FHFACAHAHACGAAAFCAAAA".toUTF8 "AAAAUAAAAOAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 9 0 r4_1_590_rows
  decide +kernel

private def r4_1_560_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,21,29,2,0⟩, ⟨false,31,61,2,0⟩]
private theorem r4_1_560 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_560_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_560_rows (3 : Fin 4)
    Axis.base r4_1_561 r4_1_590

private def r4_1_611_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,21,29,2,0⟩, ⟨false,63,0,2,0⟩]
private theorem r4_1_611 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_611_rows := by
  apply verifyCover_sound "HFHFCAHHHCAAAAAAAAA".toUTF8 "AAAASAAAAQAAAAOAAAAMAAAACAAAAAAAAAIAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 10 0 r4_1_611_rows
  decide +kernel

private def r4_1_559_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,21,29,2,0⟩, ⟨false,31,0,2,0⟩]
private theorem r4_1_559 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_559_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_559_rows (3 : Fin 4)
    Axis.base r4_1_560 r4_1_611

private def r4_1_347_rows : Vector Slot 4 := #v[⟨false,3,3,4,0⟩, ⟨true,5,5,5,0⟩, ⟨false,15,29,2,0⟩, ⟨false,31,0,2,0⟩]
private theorem r4_1_347 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_347_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_347_rows (2 : Fin 4)
    Axis.base r4_1_348 r4_1_559

private def r4_1_345_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨true,5,5,5,0⟩, ⟨false,15,29,2,0⟩, ⟨false,31,0,2,0⟩]
private theorem r4_1_345 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_345_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_345_rows (0 : Fin 4)
    Axis.exponent r4_1_346 r4_1_347

private def r4_1_343_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨true,5,5,1,0⟩, ⟨false,15,29,2,0⟩, ⟨false,31,0,2,0⟩]
private theorem r4_1_343 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_343_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_343_rows (1 : Fin 4)
    Axis.exponent r4_1_344 r4_1_345

private def r4_1_630_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨true,5,5,1,0⟩, ⟨false,31,0,2,0⟩, ⟨false,31,0,2,0⟩]
private theorem r4_1_630 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_630_rows := by
  apply verifyCover_sound "EACAHHHCAHAAAAA".toUTF8 "AAAACAAAAAAAAACAAAAAAAAAKAAAAIAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 8 0 r4_1_630_rows
  decide +kernel

private def r4_1_342_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨true,5,5,1,0⟩, ⟨false,15,0,2,0⟩, ⟨false,31,0,2,0⟩]
private theorem r4_1_342 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_342_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_342_rows (2 : Fin 4)
    Axis.base r4_1_343 r4_1_630

private def r4_1_286_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨true,5,5,1,0⟩, ⟨false,15,0,2,0⟩, ⟨false,15,0,2,0⟩]
private theorem r4_1_286 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_286_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_286_rows (3 : Fin 4)
    Axis.base r4_1_287 r4_1_342

private def r4_1_645_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨true,9,9,1,0⟩, ⟨false,15,0,2,0⟩, ⟨false,15,0,2,0⟩]
private theorem r4_1_645 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_645_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_645_rows
  decide +kernel

private def r4_1_285_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨true,5,9,1,0⟩, ⟨false,15,0,2,0⟩, ⟨false,15,0,2,0⟩]
private theorem r4_1_285 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_285_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_285_rows (1 : Fin 4)
    Axis.base r4_1_286 r4_1_645

private def r4_1_89_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨true,5,9,1,0⟩, ⟨false,7,0,2,0⟩, ⟨false,15,0,2,0⟩]
private theorem r4_1_89 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_89_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_89_rows (2 : Fin 4)
    Axis.base r4_1_90 r4_1_285

private def r4_1_67_rows : Vector Slot 4 := #v[⟨false,3,3,2,0⟩, ⟨true,5,9,1,0⟩, ⟨false,7,0,2,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_1_67 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_67_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_67_rows (3 : Fin 4)
    Axis.base r4_1_68 r4_1_89

private def r4_1_648_rows : Vector Slot 4 := #v[⟨false,5,5,2,0⟩, ⟨true,5,5,1,0⟩, ⟨false,7,13,2,0⟩, ⟨false,7,13,2,0⟩]
private theorem r4_1_648 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_648_rows := by
  apply verifyCover_sound "HEHAAHAFAAFEAFHCAGAAAAA".toUTF8 "AAAAKAAAAEAAAACAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAMAAAACAAAAAAAAAIAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 8 0 r4_1_648_rows
  decide +kernel

private def r4_1_671_rows : Vector Slot 4 := #v[⟨false,5,5,2,0⟩, ⟨true,9,9,1,0⟩, ⟨false,9,13,2,0⟩, ⟨false,9,13,2,0⟩]
private theorem r4_1_671 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_671_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_671_rows
  decide +kernel

private def r4_1_647_rows : Vector Slot 4 := #v[⟨false,5,5,2,0⟩, ⟨true,5,9,1,0⟩, ⟨false,7,13,2,0⟩, ⟨false,7,13,2,0⟩]
private theorem r4_1_647 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_647_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_647_rows (1 : Fin 4)
    Axis.base r4_1_648 r4_1_671

private def r4_1_672_rows : Vector Slot 4 := #v[⟨false,5,5,2,0⟩, ⟨true,5,9,1,0⟩, ⟨false,7,0,2,0⟩, ⟨false,15,0,2,0⟩]
private theorem r4_1_672 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_672_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_672_rows
  decide +kernel

private def r4_1_646_rows : Vector Slot 4 := #v[⟨false,5,5,2,0⟩, ⟨true,5,9,1,0⟩, ⟨false,7,0,2,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_1_646 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_646_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_646_rows (3 : Fin 4)
    Axis.base r4_1_647 r4_1_672

private def r4_1_66_rows : Vector Slot 4 := #v[⟨false,3,5,2,0⟩, ⟨true,5,9,1,0⟩, ⟨false,7,0,2,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_1_66 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_66_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_66_rows (0 : Fin 4)
    Axis.base r4_1_67 r4_1_646

private def r4_1_673_rows : Vector Slot 4 := #v[⟨false,3,5,2,0⟩, ⟨true,13,0,1,0⟩, ⟨false,13,0,2,0⟩, ⟨false,13,0,2,0⟩]
private theorem r4_1_673 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_673_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_673_rows
  decide +kernel

private def r4_1_65_rows : Vector Slot 4 := #v[⟨false,3,5,2,0⟩, ⟨true,5,0,1,0⟩, ⟨false,7,0,2,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_1_65 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_65_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_65_rows (1 : Fin 4)
    Axis.base r4_1_66 r4_1_673

private def r4_1_674_rows : Vector Slot 4 := #v[⟨false,7,0,2,0⟩, ⟨true,9,0,1,0⟩, ⟨false,7,0,2,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_1_674 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_674_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_1_674_rows
  decide +kernel

private def r4_1_64_rows : Vector Slot 4 := #v[⟨false,3,0,2,0⟩, ⟨true,5,0,1,0⟩, ⟨false,7,0,2,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_1_64 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_64_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_64_rows (0 : Fin 4)
    Axis.base r4_1_65 r4_1_674

private def r4_1_2_rows : Vector Slot 4 := #v[⟨false,3,0,2,0⟩, ⟨true,5,0,1,0⟩, ⟨false,3,0,2,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_1_2 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_2_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_2_rows (2 : Fin 4)
    Axis.base r4_1_3 r4_1_64

private def r4_1_0_rows : Vector Slot 4 := #v[⟨false,3,0,2,0⟩, ⟨true,5,0,1,0⟩, ⟨false,3,0,2,0⟩, ⟨false,3,0,2,0⟩]
private theorem r4_1_0 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_1_0_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_1_0_rows (3 : Fin 4)
    Axis.base r4_1_1 r4_1_2

theorem covered_4_1 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) (initial (1 : Fin 4)) := r4_1_0

end OddPerfect.SpoofBox
