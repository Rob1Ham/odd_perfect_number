module

public import OddPerfect.SizeIndex300.Seed31Part01

public section

namespace OddPerfect.IndexComponent.Size300

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def state31_54 : State := ⟨136826237089664516006784922702009751731185420030607208389400361250897049228410492159355815284093937176451398488482500741423820424077813256592898608001, 141387111659319999873677753458743410122224934031627448669047039959260284202690841898001009126897068415666445104765250766137947771547073698479328561601, 0⟩

private noncomputable def tree31_54 : AbundanceTree :=
  .round 1 [(4243, 1)]

private theorem checked31_54 : replayAbundance bank 31 185801 (10^300) 3 state31_54 tree31_54 = true := by
  decide +kernel

theorem reject31_54 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 31 ∣ N)
    (hav : Nat.Coprime 185801 N) (hx : N ≤ 10^300) (h : Valid state31_54 N) : False :=
  replayAbundance_correct ho hN hs hav hx bank bank_valid 3 h tree31_54 checked31_54

@[expose] noncomputable def state31_55 : State := ⟨1, 1, 0⟩

private theorem checked31_55 : checkChildren bank 31 185801 (10^300) state31_55 31 [state31_19, state31_20, state31_21, state31_34, state31_35, state31_36, state31_37, state31_38, state31_39, state31_40, state31_41, state31_42, state31_43, state31_44, state31_45, state31_46, state31_47, state31_48, state31_49, state31_50, state31_51, state31_52, state31_53, state31_54] = true := by
  decide +kernel

theorem reject31_55 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 31 ∣ N)
    (hav : Nat.Coprime 185801 N) (hx : N ≤ 10^300) (h : Valid state31_55 N) : False := by
  apply checkChildren_correct ho hN hs hav hx bank bank_valid h [state31_19, state31_20, state31_21, state31_34, state31_35, state31_36, state31_37, state31_38, state31_39, state31_40, state31_41, state31_42, state31_43, state31_44, state31_45, state31_46, state31_47, state31_48, state31_49, state31_50, state31_51, state31_52, state31_53, state31_54] ?_ checked31_55
  intro t ht hvalid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reject31_19 ho hN hs hav hx hvalid
  · exact reject31_20 ho hN hs hav hx hvalid
  · exact reject31_21 ho hN hs hav hx hvalid
  · exact reject31_34 ho hN hs hav hx hvalid
  · exact reject31_35 ho hN hs hav hx hvalid
  · exact reject31_36 ho hN hs hav hx hvalid
  · exact reject31_37 ho hN hs hav hx hvalid
  · exact reject31_38 ho hN hs hav hx hvalid
  · exact reject31_39 ho hN hs hav hx hvalid
  · exact reject31_40 ho hN hs hav hx hvalid
  · exact reject31_41 ho hN hs hav hx hvalid
  · exact reject31_42 ho hN hs hav hx hvalid
  · exact reject31_43 ho hN hs hav hx hvalid
  · exact reject31_44 ho hN hs hav hx hvalid
  · exact reject31_45 ho hN hs hav hx hvalid
  · exact reject31_46 ho hN hs hav hx hvalid
  · exact reject31_47 ho hN hs hav hx hvalid
  · exact reject31_48 ho hN hs hav hx hvalid
  · exact reject31_49 ho hN hs hav hx hvalid
  · exact reject31_50 ho hN hs hav hx hvalid
  · exact reject31_51 ho hN hs hav hx hvalid
  · exact reject31_52 ho hN hs hav hx hvalid
  · exact reject31_53 ho hN hs hav hx hvalid
  · exact reject31_54 ho hN hs hav hx hvalid

theorem exclude_31 {N : ℕ} (ho : Odd N) (hN : N.Perfect) (hs : 31 ∣ N)
    (hav : Nat.Coprime 185801 N) (hx : N ≤ 10^300) : False :=
  reject31_55 ho hN hs hav hx (root_valid N)

end OddPerfect.IndexComponent.Size300
