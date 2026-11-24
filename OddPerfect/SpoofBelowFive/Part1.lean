module

public import OddPerfect.SpoofCover

public section

namespace OddPerfect.SpoofBox

private def r1_0_0_rows : Vector Slot 1 := #v[⟨true,5,0,1,0⟩]
private theorem r1_0_0 : Covered (· ∈ ([] : List (Fin 1 → ℕ × ℕ))) r1_0_0_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 1 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r1_0_0_rows
  decide +kernel

theorem covered_1_0 : Covered (· ∈ ([] : List (Fin 1 → ℕ × ℕ))) (initial (0 : Fin 1)) := r1_0_0

private def r2_0_0_rows : Vector Slot 2 := #v[⟨true,5,0,1,0⟩, ⟨false,3,0,2,0⟩]
private theorem r2_0_0 : Covered (· ∈ ([] : List (Fin 2 → ℕ × ℕ))) r2_0_0_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 2 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r2_0_0_rows
  decide +kernel

theorem covered_2_0 : Covered (· ∈ ([] : List (Fin 2 → ℕ × ℕ))) (initial (0 : Fin 2)) := r2_0_0

private def r2_1_0_rows : Vector Slot 2 := #v[⟨false,3,0,2,0⟩, ⟨true,5,0,1,0⟩]
private theorem r2_1_0 : Covered (· ∈ ([] : List (Fin 2 → ℕ × ℕ))) r2_1_0_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 2 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r2_1_0_rows
  decide +kernel

theorem covered_2_1 : Covered (· ∈ ([] : List (Fin 2 → ℕ × ℕ))) (initial (1 : Fin 2)) := r2_1_0

private def r3_0_0_rows : Vector Slot 3 := #v[⟨true,5,0,1,0⟩, ⟨false,3,0,2,0⟩, ⟨false,3,0,2,0⟩]
private theorem r3_0_0 : Covered (· ∈ ([] : List (Fin 3 → ℕ × ℕ))) r3_0_0_rows := by
  apply verifyCover_sound "FFADAADDAAA".toUTF8 "AAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAEAAAACAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 3 → ℕ × ℕ))) _ (spoofRule_sound _) 4 0 r3_0_0_rows
  decide +kernel

theorem covered_3_0 : Covered (· ∈ ([] : List (Fin 3 → ℕ × ℕ))) (initial (0 : Fin 3)) := r3_0_0

private def r3_1_1_rows : Vector Slot 3 := #v[⟨false,3,5,2,0⟩, ⟨true,5,5,1,0⟩, ⟨false,3,5,2,0⟩]
private theorem r3_1_1 : Covered (· ∈ ([] : List (Fin 3 → ℕ × ℕ))) r3_1_1_rows := by
  apply verifyCover_sound "FABAA".toUTF8 "AAAACAAAAAAAAACAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 3 → ℕ × ℕ))) _ (spoofRule_sound _) 3 0 r3_1_1_rows
  decide +kernel

private def r3_1_10_rows : Vector Slot 3 := #v[⟨false,3,3,2,0⟩, ⟨true,5,9,1,0⟩, ⟨false,7,13,2,0⟩]
private theorem r3_1_10 : Covered (· ∈ ([] : List (Fin 3 → ℕ × ℕ))) r3_1_10_rows := by
  apply verifyCover_sound "DFECcAAEACAAA".toUTF8 "AAAAMAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 3 → ℕ × ℕ))) _ (spoofRule_sound _) 5 0 r3_1_10_rows
  decide +kernel

private def r3_1_23_rows : Vector Slot 3 := #v[⟨false,3,3,2,0⟩, ⟨true,5,9,1,0⟩, ⟨false,15,0,2,0⟩]
private theorem r3_1_23 : Covered (· ∈ ([] : List (Fin 3 → ℕ × ℕ))) r3_1_23_rows := by
  apply verifyCover_sound "DFEACAFFCGbAAAAAA".toUTF8 "AAAAQAAAAOAAAACAAAAAAAAACAAAAAAAAAIAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 3 → ℕ × ℕ))) _ (spoofRule_sound _) 9 0 r3_1_23_rows
  decide +kernel

private def r3_1_9_rows : Vector Slot 3 := #v[⟨false,3,3,2,0⟩, ⟨true,5,9,1,0⟩, ⟨false,7,0,2,0⟩]
private theorem r3_1_9 : Covered (· ∈ ([] : List (Fin 3 → ℕ × ℕ))) r3_1_9_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 3 → ℕ × ℕ)))) r3_1_9_rows (2 : Fin 3)
    Axis.base r3_1_10 r3_1_23

private def r3_1_40_rows : Vector Slot 3 := #v[⟨false,5,5,2,0⟩, ⟨true,5,9,1,0⟩, ⟨false,7,0,2,0⟩]
private theorem r3_1_40 : Covered (· ∈ ([] : List (Fin 3 → ℕ × ℕ))) r3_1_40_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 3 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r3_1_40_rows
  decide +kernel

private def r3_1_8_rows : Vector Slot 3 := #v[⟨false,3,5,2,0⟩, ⟨true,5,9,1,0⟩, ⟨false,7,0,2,0⟩]
private theorem r3_1_8 : Covered (· ∈ ([] : List (Fin 3 → ℕ × ℕ))) r3_1_8_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 3 → ℕ × ℕ)))) r3_1_8_rows (0 : Fin 3)
    Axis.base r3_1_9 r3_1_40

private def r3_1_41_rows : Vector Slot 3 := #v[⟨false,3,5,2,0⟩, ⟨true,13,0,1,0⟩, ⟨false,13,0,2,0⟩]
private theorem r3_1_41 : Covered (· ∈ ([] : List (Fin 3 → ℕ × ℕ))) r3_1_41_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 3 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r3_1_41_rows
  decide +kernel

private def r3_1_7_rows : Vector Slot 3 := #v[⟨false,3,5,2,0⟩, ⟨true,5,0,1,0⟩, ⟨false,7,0,2,0⟩]
private theorem r3_1_7 : Covered (· ∈ ([] : List (Fin 3 → ℕ × ℕ))) r3_1_7_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 3 → ℕ × ℕ)))) r3_1_7_rows (1 : Fin 3)
    Axis.base r3_1_8 r3_1_41

private def r3_1_42_rows : Vector Slot 3 := #v[⟨false,7,0,2,0⟩, ⟨true,9,0,1,0⟩, ⟨false,7,0,2,0⟩]
private theorem r3_1_42 : Covered (· ∈ ([] : List (Fin 3 → ℕ × ℕ))) r3_1_42_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 3 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r3_1_42_rows
  decide +kernel

private def r3_1_6_rows : Vector Slot 3 := #v[⟨false,3,0,2,0⟩, ⟨true,5,0,1,0⟩, ⟨false,7,0,2,0⟩]
private theorem r3_1_6 : Covered (· ∈ ([] : List (Fin 3 → ℕ × ℕ))) r3_1_6_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 3 → ℕ × ℕ)))) r3_1_6_rows (0 : Fin 3)
    Axis.base r3_1_7 r3_1_42

private def r3_1_0_rows : Vector Slot 3 := #v[⟨false,3,0,2,0⟩, ⟨true,5,0,1,0⟩, ⟨false,3,0,2,0⟩]
private theorem r3_1_0 : Covered (· ∈ ([] : List (Fin 3 → ℕ × ℕ))) r3_1_0_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 3 → ℕ × ℕ)))) r3_1_0_rows (2 : Fin 3)
    Axis.base r3_1_1 r3_1_6

theorem covered_3_1 : Covered (· ∈ ([] : List (Fin 3 → ℕ × ℕ))) (initial (1 : Fin 3)) := r3_1_0

private def r3_2_2_rows : Vector Slot 3 := #v[⟨false,3,5,2,0⟩, ⟨false,3,5,2,0⟩, ⟨true,5,9,1,0⟩]
private theorem r3_2_2 : Covered (· ∈ ([] : List (Fin 3 → ℕ × ℕ))) r3_2_2_rows := by
  apply verifyCover_sound "DABFACGbAAA".toUTF8 "AAAACAAAAAAAAAIAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 3 → ℕ × ℕ))) _ (spoofRule_sound _) 6 0 r3_2_2_rows
  decide +kernel

private def r3_2_13_rows : Vector Slot 3 := #v[⟨false,3,5,2,0⟩, ⟨false,3,5,2,0⟩, ⟨true,13,0,1,0⟩]
private theorem r3_2_13 : Covered (· ∈ ([] : List (Fin 3 → ℕ × ℕ))) r3_2_13_rows := by
  apply verifyCover_sound "DABFCAFFEGaAAAAAA".toUTF8 "AAAACAAAAAAAAAOAAAAMAAAACAAAAAAAAAIAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 3 → ℕ × ℕ))) _ (spoofRule_sound _) 9 0 r3_2_13_rows
  decide +kernel

private def r3_2_1_rows : Vector Slot 3 := #v[⟨false,3,5,2,0⟩, ⟨false,3,5,2,0⟩, ⟨true,5,0,1,0⟩]
private theorem r3_2_1 : Covered (· ∈ ([] : List (Fin 3 → ℕ × ℕ))) r3_2_1_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 3 → ℕ × ℕ)))) r3_2_1_rows (2 : Fin 3)
    Axis.base r3_2_2 r3_2_13

private def r3_2_30_rows : Vector Slot 3 := #v[⟨false,3,0,2,0⟩, ⟨false,7,0,2,0⟩, ⟨true,9,0,1,0⟩]
private theorem r3_2_30 : Covered (· ∈ ([] : List (Fin 3 → ℕ × ℕ))) r3_2_30_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 3 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r3_2_30_rows
  decide +kernel

private def r3_2_0_rows : Vector Slot 3 := #v[⟨false,3,0,2,0⟩, ⟨false,3,0,2,0⟩, ⟨true,5,0,1,0⟩]
private theorem r3_2_0 : Covered (· ∈ ([] : List (Fin 3 → ℕ × ℕ))) r3_2_0_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 3 → ℕ × ℕ)))) r3_2_0_rows (1 : Fin 3)
    Axis.base r3_2_1 r3_2_30

theorem covered_3_2 : Covered (· ∈ ([] : List (Fin 3 → ℕ × ℕ))) (initial (2 : Fin 3)) := r3_2_0

private def r4_0_1_rows : Vector Slot 4 := #v[⟨true,5,5,1,0⟩, ⟨false,3,5,2,0⟩, ⟨false,3,5,2,0⟩, ⟨false,3,5,2,0⟩]
private theorem r4_0_1 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_0_1_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_0_1_rows
  decide +kernel

private def r4_0_4_rows : Vector Slot 4 := #v[⟨true,5,1,1,0⟩, ⟨false,3,3,2,0⟩, ⟨false,3,3,2,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_0_4 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_0_4_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_0_4_rows
  decide +kernel

private def r4_0_6_rows : Vector Slot 4 := #v[⟨true,5,1,1,0⟩, ⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_0_6 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_0_6_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_0_6_rows
  decide +kernel

private def r4_0_8_rows : Vector Slot 4 := #v[⟨true,5,5,1,0⟩, ⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,7,13,2,0⟩]
private theorem r4_0_8 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_0_8_rows := by
  apply verifyCover_sound "HACHAGEAAAA".toUTF8 "AAAACAAAAAAAAAIAAAACAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 6 0 r4_0_8_rows
  decide +kernel

private def r4_0_20_rows : Vector Slot 4 := #v[⟨true,5,5,1,0⟩, ⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,15,29,2,0⟩]
private theorem r4_0_20 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_0_20_rows := by
  apply verifyCover_sound "CHHGAEAAAAHAHAGEHAAAA".toUTF8 "AAAAKAAAAIAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAAGAAAAEAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 7 0 r4_0_20_rows
  decide +kernel

private def r4_0_41_rows : Vector Slot 4 := #v[⟨true,5,5,1,0⟩, ⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,31,0,2,0⟩]
private theorem r4_0_41 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_0_41_rows := by
  apply verifyCover_sound "CAHHHGEAHAAEHAAAGAEAAAA".toUTF8 "AAAACAAAAAAAAAUAAAASAAAAMAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAEAAAACAAAAAAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 8 0 r4_0_41_rows
  decide +kernel

private def r4_0_19_rows : Vector Slot 4 := #v[⟨true,5,5,1,0⟩, ⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,15,0,2,0⟩]
private theorem r4_0_19 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_0_19_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_0_19_rows (3 : Fin 4)
    Axis.base r4_0_20 r4_0_41

private def r4_0_7_rows : Vector Slot 4 := #v[⟨true,5,5,1,0⟩, ⟨false,5,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_0_7 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_0_7_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_0_7_rows (3 : Fin 4)
    Axis.base r4_0_8 r4_0_19

private def r4_0_5_rows : Vector Slot 4 := #v[⟨true,5,5,1,0⟩, ⟨false,3,5,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_0_5 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_0_5_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_0_5_rows (1 : Fin 4)
    Axis.base r4_0_6 r4_0_7

private def r4_0_3_rows : Vector Slot 4 := #v[⟨true,5,5,1,0⟩, ⟨false,3,5,2,0⟩, ⟨false,3,5,2,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_0_3 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_0_3_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_0_3_rows (2 : Fin 4)
    Axis.base r4_0_4 r4_0_5

private def r4_0_66_rows : Vector Slot 4 := #v[⟨true,5,1,1,0⟩, ⟨false,3,3,2,0⟩, ⟨false,7,0,2,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_0_66 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_0_66_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_0_66_rows
  decide +kernel

private def r4_0_68_rows : Vector Slot 4 := #v[⟨true,5,5,1,0⟩, ⟨false,5,5,2,0⟩, ⟨false,7,13,2,0⟩, ⟨false,7,13,2,0⟩]
private theorem r4_0_68 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_0_68_rows := by
  apply verifyCover_sound "HCHAAHAFAAFCAFHEAGAAAAA".toUTF8 "AAAAKAAAAEAAAACAAAAAAAAAAAAAACAAAAAAAAACAAAAAAAAAAAAAAMAAAACAAAAAAAAAIAAAAGAAAACAAAAAAAAACAAAAAAAAAAAAAAAAAAAAAAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 8 0 r4_0_68_rows
  decide +kernel

private def r4_0_91_rows : Vector Slot 4 := #v[⟨true,5,5,1,0⟩, ⟨false,5,5,2,0⟩, ⟨false,7,0,2,0⟩, ⟨false,15,0,2,0⟩]
private theorem r4_0_91 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_0_91_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_0_91_rows
  decide +kernel

private def r4_0_67_rows : Vector Slot 4 := #v[⟨true,5,5,1,0⟩, ⟨false,5,5,2,0⟩, ⟨false,7,0,2,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_0_67 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_0_67_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_0_67_rows (3 : Fin 4)
    Axis.base r4_0_68 r4_0_91

private def r4_0_65_rows : Vector Slot 4 := #v[⟨true,5,5,1,0⟩, ⟨false,3,5,2,0⟩, ⟨false,7,0,2,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_0_65 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_0_65_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_0_65_rows (1 : Fin 4)
    Axis.base r4_0_66 r4_0_67

private def r4_0_92_rows : Vector Slot 4 := #v[⟨true,5,0,1,0⟩, ⟨false,7,0,2,0⟩, ⟨false,7,0,2,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_0_92 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_0_92_rows := by
  apply verifyCover_sound "A".toUTF8 "AAAAA".toUTF8
    (spoofRule ([] : List (Fin 4 → ℕ × ℕ))) _ (spoofRule_sound _) 1 0 r4_0_92_rows
  decide +kernel

private def r4_0_64_rows : Vector Slot 4 := #v[⟨true,5,0,1,0⟩, ⟨false,3,0,2,0⟩, ⟨false,7,0,2,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_0_64 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_0_64_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_0_64_rows (1 : Fin 4)
    Axis.base r4_0_65 r4_0_92

private def r4_0_2_rows : Vector Slot 4 := #v[⟨true,5,0,1,0⟩, ⟨false,3,0,2,0⟩, ⟨false,3,0,2,0⟩, ⟨false,7,0,2,0⟩]
private theorem r4_0_2 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_0_2_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_0_2_rows (2 : Fin 4)
    Axis.base r4_0_3 r4_0_64

private def r4_0_0_rows : Vector Slot 4 := #v[⟨true,5,0,1,0⟩, ⟨false,3,0,2,0⟩, ⟨false,3,0,2,0⟩, ⟨false,3,0,2,0⟩]
private theorem r4_0_0 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) r4_0_0_rows := by
  exact covered_split (keep := (· ∈ ([] : List (Fin 4 → ℕ × ℕ)))) r4_0_0_rows (3 : Fin 4)
    Axis.base r4_0_1 r4_0_2

theorem covered_4_0 : Covered (· ∈ ([] : List (Fin 4 → ℕ × ℕ))) (initial (0 : Fin 4)) := r4_0_0

end OddPerfect.SpoofBox
