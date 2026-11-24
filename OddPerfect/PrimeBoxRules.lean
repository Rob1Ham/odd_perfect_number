module

public import OddPerfect.PrimeSlots
public import OddPerfect.SpoofCover

public section

namespace OddPerfect.SpoofBox

open Finset

@[expose] def fixedBase (s : Slot) : Bool := decide (0 < s.baseHi ∧ s.baseLo=s.baseHi)
@[expose] def fixedExponent (s : Slot) : Bool := decide (0 < s.expHi ∧ s.expLo=s.expHi)
@[expose] def admitsBase (s : Slot) (b : ℕ) : Bool :=
  decide (s.baseLo≤b ∧ (s.baseHi=0 ∨ b≤s.baseHi) ∧ b%s.stride=1)

theorem fixedBase_eq {s : Slot} {z : ℕ × ℕ} (h : s.Fits z) (hf : fixedBase s) : z.1=s.baseLo := by
  obtain ⟨_,_⟩ := of_decide_eq_true hf
  have := h.baseHi
  have := h.baseLo
  omega

theorem fixedExponent_eq {s : Slot} {z : ℕ × ℕ} (h : s.Fits z) (hf : fixedExponent s) : z.2=s.expLo := by
  obtain ⟨_,_⟩ := of_decide_eq_true hf
  have := h.expHi
  have := h.expLo
  omega

theorem admitsBase_of_fits {s : Slot} {z : ℕ × ℕ} (h : s.Fits z) : admitsBase s z.1 :=
  decide_eq_true ⟨h.baseLo,h.baseHi,h.baseResidue⟩

/-- At a fixed base and exponent the geometric sum is exact. A special
slot also guarantees the factor b+1 for every allowed exponent. -/
@[expose] def delivers (s : Slot) (r : ℕ) : Bool :=
  fixedBase s && ((fixedExponent s && decide (r ∣ ∑ j ∈ range (s.expLo+1), s.baseLo^j)) ||
    (s.special && decide (r ∣ s.baseLo+1)))

theorem delivers_sound {s : Slot} {z : ℕ × ℕ} {r : ℕ} (hx : s.Fits z) (h : delivers s r) :
    r ∣ ∑ j ∈ range (z.2+1), z.1^j := by
  obtain ⟨hf,hz⟩ := Bool.and_eq_true_iff.mp h
  rw [fixedBase_eq hx hf]
  rcases Bool.or_eq_true_iff.mp hz with h | h
  · obtain ⟨he,hd⟩ := Bool.and_eq_true_iff.mp h
    rw [fixedExponent_eq hx he]
    exact of_decide_eq_true hd
  · obtain ⟨hs,hd⟩ := Bool.and_eq_true_iff.mp h
    have hr := hx.expResidue
    simp [Slot.expResidue,Slot.stride,hs] at hr
    rw [show z.2+1=2*((z.2+1)/2) by omega]
    exact (of_decide_eq_true hd).trans (succ_dvd_sum_even _ _)

@[expose] def forcesMissing {k : ℕ} (s : Fin k → Slot) (r : ℕ) : Bool :=
  decide (r.Prime ∧ Odd r ∧ (∀ j, admitsBase (s j) r = false) ∧ (∃ i, delivers (s i) r = true))

theorem covered_missing_prime {k : ℕ} (rows : Vector Slot k) (r : ℕ)
    (h : forcesMissing (fun i : Fin k => rows[i]) r) :
    Covered (fun x => ¬ GenuineSlots x) rows := by
  intro x _ hx hb hg
  obtain ⟨hr,ho,hmiss,i,hi⟩ := of_decide_eq_true h
  obtain ⟨j,hj⟩ := prime_slot_forcing hr ho hg.prime i (delivers_sound (hx i) hi) hb
  have hj' := admitsBase_of_fits (hx j)
  rw [hj,hmiss j] at hj'
  contradiction

/-- The three clauses detect a composite exact base, an impossible
strict ordering, or the simultaneously forced bases 3, 5 and 7. -/
@[expose] def impossiblePrimeRows {k : ℕ} (s : Fin k → Slot) : Bool :=
  let occurs := fun b => ∃ i, fixedBase (s i) = true ∧ (s i).baseLo=b
  decide ((∃ i, fixedBase (s i) = true ∧ ¬(s i).baseLo.Prime) ∨
    (∃ i j, i<j ∧ 0<(s j).baseHi ∧ (s j).baseHi≤(s i).baseLo) ∨
    (occurs 3 ∧ occurs 5 ∧ occurs 7))

theorem covered_impossible_prime_rows {k : ℕ} (rows : Vector Slot k)
    (h : impossiblePrimeRows (fun i : Fin k => rows[i])) :
    Covered (fun x => ¬ GenuineSlots x) rows := by
  intro x _ hx _ hg
  rcases of_decide_eq_true h with ⟨i,hi,hp⟩|⟨i,j,hij,hpos,hbound⟩|h
  · exact hp (fixedBase_eq (hx i) hi ▸ hg.prime i)
  · have hu := (hx j).baseHi.resolve_left (show rows[j].baseHi≠0 from hpos.ne')
    exact (hg.strict hij).not_ge (hu.trans (hbound.trans (hx i).baseLo))
  · have take (b : ℕ) (z : ∃ i : Fin k, fixedBase rows[i] = true ∧ rows[i].baseLo=b) :
        ∃ i, (x i).1=b := by
      obtain ⟨i,hi,hb⟩ := z
      exact ⟨i,(fixedBase_eq (hx i) hi).trans hb⟩
    exact hg.no105 ⟨take 3 h.1,take 5 h.2.1,take 7 h.2.2⟩

end OddPerfect.SpoofBox
