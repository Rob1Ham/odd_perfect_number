module

public import OddPerfect.SpoofBoxState
public import OddPerfect.SpoofCompletion

public section

namespace OddPerfect.SpoofBox

open Finset

/-- All coordinates except a designated last component are fixed. -/
@[expose] def fixedApart {k : ℕ} (s : Fin k → Slot) (i : Fin k) : Bool :=
  decide (∀ j, j ≠ i → 0 < (s j).baseHi ∧ 0 < (s j).expHi ∧ (s j).baseLo = (s j).baseHi ∧ (s j).expLo = (s j).expHi)

@[expose] def prefixSum {k : ℕ} (s : Fin k → Slot) (i : Fin k) : ℕ :=
  ∏ j ∈ (univ.erase i), ∑ a ∈ range ((s j).expLo+1), (s j).baseLo^a

@[expose] def prefixValue {k : ℕ} (s : Fin k → Slot) (i : Fin k) : ℕ :=
  ∏ j ∈ (univ.erase i), (s j).baseLo^(s j).expLo

@[expose] def completeBox {k : ℕ} (s : Fin k → Slot) (i j : Fin k) : ℕ × ℕ :=
  if i=j then lastSpoofComponent (prefixSum s i) (2*prefixValue s i)
  else ((s j).baseLo, (s j).expLo)

/-- Once all other slots are fixed the last slot is unique, wherever it
occurs in the sorted list. The prefix may contain repeated or composite bases. -/
theorem eq_completeBox {k : ℕ} (s : Fin k → Slot) (i : Fin k) (x : Fin k → ℕ × ℕ)
    (hx : ∀ j, (s j).Fits (x j))
    (hb : formalSigma univ (fun j => (x j).1) (fun j => (x j).2) = 2*∏ j, (x j).1^(x j).2)
    (hf : fixedApart s i) : x = completeBox s i := by
  have hother (j : Fin k) (hj : j ≠ i) : x j = ((s j).baseLo,(s j).expLo) := by
    obtain ⟨hp,hq,hbase,hexp⟩ := of_decide_eq_true hf j hj
    have hbl := (hx j).baseLo
    have hbu := (hx j).baseHi
    have hel := (hx j).expLo
    have heu := (hx j).expHi
    exact Prod.ext (by omega) (by omega)
  have hs : (∏ j ∈ univ.erase i, ∑ a ∈ range ((x j).2+1), (x j).1^a) = prefixSum s i := by
    apply prod_congr rfl
    intro j hj
    rw [hother j (mem_erase.mp hj).1]
  have hv : (∏ j ∈ univ.erase i, (x j).1^(x j).2) = prefixValue s i := by
    apply prod_congr rfl
    intro j hj
    rw [hother j (mem_erase.mp hj).1]
  have hpos : 0 < prefixSum s i := by
    apply prod_pos
    intro j _
    exact sum_pos' (by intros; omega) ⟨0,mem_range.mpr (by omega),by simp⟩
  unfold formalSigma at hb
  rw [← mul_prod_erase _ _ (mem_univ i), hs, ← mul_prod_erase _ (fun j => (x j).1^(x j).2) (mem_univ i), hv] at hb
  have hc := lastSpoofComponent_eq hpos (hx i).base (hx i).exp
    (show prefixSum s i * (∑ a ∈ range ((x i).2+1), (x i).1^a) = (2*prefixValue s i)*(x i).1^(x i).2 by
      simpa only [mul_comm, mul_assoc, mul_left_comm] using hb)
  funext j
  by_cases h : i=j
  · subst j
    simpa [completeBox] using hc.symm
  · simpa [completeBox,h] using hother j (Ne.symm h)

@[expose] def pointFits (s : Slot) (z : ℕ × ℕ) : Bool :=
  decide (1 < z.1 ∧ 0 < z.2 ∧ s.baseLo ≤ z.1 ∧ (s.baseHi=0 ∨ z.1≤s.baseHi) ∧
    s.expLo ≤ z.2 ∧ (s.expHi=0 ∨ z.2≤s.expHi) ∧
    z.1 % s.stride = 1 ∧ z.2 % s.stride = s.expResidue)

theorem pointFits_eq_true {s : Slot} {z : ℕ × ℕ} (h : s.Fits z) : pointFits s z := by
  exact decide_eq_true ⟨h.base,h.exp,h.baseLo,h.baseHi,h.expLo,h.expHi,h.baseResidue,h.expResidue⟩

/-- In a box with just one free slot, the uniquely forced tuple must fit
the box and balance. An explicitly permitted solution may also close the leaf. -/
@[expose] def lastLeaf {k : ℕ} (s : Fin k → Slot) (i : Fin k)
    (allowed : List (Fin k → ℕ × ℕ)) : Bool :=
  let y := completeBox s i
  fixedApart s i && (!(pointFits (s i) (y i)) ||
    decide (formalSigma univ (fun j => (y j).1) (fun j => (y j).2) ≠ 2*∏ j, (y j).1^(y j).2) ||
    allowed.any (fun z => decide (∀ j, z j = y j)))

theorem lastLeaf_sound {k : ℕ} (s : Fin k → Slot) (i : Fin k)
    (allowed : List (Fin k → ℕ × ℕ)) (x : Fin k → ℕ × ℕ)
    (hx : ∀ j, (s j).Fits (x j))
    (hb : formalSigma univ (fun j => (x j).1) (fun j => (x j).2) = 2*∏ j, (x j).1^(x j).2)
    (h : lastLeaf s i allowed) : x ∈ allowed := by
  obtain ⟨hf,hr⟩ := Bool.and_eq_true_iff.mp h
  obtain rfl := (eq_completeBox s i x hx hb hf).symm
  simp only [pointFits_eq_true (hx i), Bool.not_true, hb, ne_self_iff_false,
    decide_false, Bool.false_or, List.any_eq_true, decide_eq_true_eq] at hr
  obtain ⟨z,hz,heq⟩ := hr
  exact funext heq ▸ hz

end OddPerfect.SpoofBox
