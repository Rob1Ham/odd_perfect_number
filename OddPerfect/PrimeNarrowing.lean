module

public import OddPerfect.PrimeBoxRules

public section

namespace OddPerfect.SpoofBox

/-- The smallest true prime is three when there are fewer than eight
distinct primes. The largest exceeds 257. Both facts apply to the very
same ordered tuple as the Euler congruences. -/
@[expose] def primeInitial {k : ℕ} (special : Fin k) : Vector Slot k :=
  Vector.ofFn (fun j : Fin k =>
    let s := (initial special)[j]
    { s with baseHi := if j.val=0 then 3 else s.baseHi
             baseLo := if j.val+1=k then max s.baseLo 258 else s.baseLo })

theorem realizing_prime_initial {k : ℕ} {x : Fin k → ℕ × ℕ} (hg : GenuineSlots x)
    (hk : k<8) (special : Fin k) (hx : ∀ i : Fin k, ((initial special)[i]).Fits (x i)) :
    ∀ j : Fin k, ((primeInitial special)[j]).Fits (x j) := by
  obtain ⟨u,hu⟩ := hg.three hk
  obtain ⟨v,hv⟩ := hg.large
  intro j
  have h := hx j
  change ((primeInitial special)[j.val]).Fits (x j)
  simp only [primeInitial, Vector.getElem_ofFn]
  have hlow : (if j.val+1=k then max ((initial special)[j]).baseLo 258
      else ((initial special)[j]).baseLo) ≤ (x j).1 := by
    split
    · rename_i hj
      exact max_le h.baseLo ((show 258 ≤ (x v).1 from hv).trans (hg.strict.monotone (show v≤j by omega)))
    · exact h.baseLo
  have hhigh : (if j.val=0 then 3 else ((initial special)[j]).baseHi)=0 ∨
      (x j).1≤(if j.val=0 then 3 else ((initial special)[j]).baseHi) := by
    by_cases hj : j.val=0
    · simp only [hj,ite_true]
      exact Or.inr ((hg.strict.monotone (show j≤u by omega)).trans hu.le)
    · simpa only [hj,ite_false] using h.baseHi
  exact { h with baseLo := hlow, baseHi := hhigh }

/-- A box covers the genuine search precisely when its formally balanced
points all violate at least one proved condition on actual primes. -/
@[expose] def PrimeCovered {k : ℕ} (rows : Vector Slot k) : Prop :=
  Covered (fun x => ¬ GenuineSlots x) rows

@[expose] def setBase {k : ℕ} (rows : Vector Slot k) (i : Fin k) (lo hi : ℕ) : Vector Slot k :=
  Vector.ofFn (fun j : Fin k => if i=j then { rows[j] with baseLo := lo, baseHi := hi } else rows[j])

theorem fits_set_base {k : ℕ} (rows : Vector Slot k) (i : Fin k) {x : Fin k → ℕ × ℕ}
    (hx : ∀ j : Fin k, rows[j].Fits (x j)) {lo hi : ℕ}
    (hl : lo ≤ (x i).1) (hu : hi=0 ∨ (x i).1 ≤ hi) :
    ∀ j : Fin k, ((setBase rows i lo hi)[j]).Fits (x j) := by
  intro j
  change ((setBase rows i lo hi)[j.val]).Fits (x j)
  simp only [setBase,Vector.getElem_ofFn]
  split
  · rename_i hi; change i=j at hi; subst j; exact { hx i with baseLo := hl, baseHi := hu }
  · exact hx j

/-- One forced prime has a unique receiving slot, even if the base and
exponent of that slot were both unknown before this inference. -/
theorem covered_force_base {k : ℕ} (rows : Vector Slot k) (source target : Fin k) (r : ℕ)
    (hr : r.Prime) (ho : Odd r) (hd : delivers rows[source] r)
    (hu : ∀ j : Fin k, admitsBase rows[j] r = true → j=target)
    (h : PrimeCovered (setBase rows target r r)) : PrimeCovered rows := by
  intro x hs hx hb hg
  obtain ⟨j,hj⟩ := prime_slot_forcing hr ho hg.prime source (delivers_sound (hx source) hd) hb
  have hf := admitsBase_of_fits (hx j)
  rw [hj] at hf
  obtain rfl := hu j hf
  exact h x hs (fits_set_base rows j hx hj.ge (Or.inr hj.le)) hb hg

@[expose] def HasFixed {k : ℕ} (rows : Vector Slot k) (b : ℕ) : Prop :=
  ∃ i : Fin k, fixedBase rows[i] = true ∧ rows[i].baseLo=b

instance {k : ℕ} (rows : Vector Slot k) (b : ℕ) : Decidable (HasFixed rows b) :=
  inferInstanceAs (Decidable (∃ i : Fin k, fixedBase rows[i] = true ∧ rows[i].baseLo=b))

theorem occurs_of_fixed {k b : ℕ} {rows : Vector Slot k} {x : Fin k → ℕ × ℕ}
    (hx : ∀ j : Fin k, rows[j].Fits (x j)) (h : HasFixed rows b) : ∃ j, (x j).1=b := by
  obtain ⟨j,hj,hb⟩ := h
  exact ⟨j,(fixedBase_eq (hx j) hj).trans hb⟩

/-- Exclude either member of the pair 5,7 when the other, and 3, are present.
Zero is a harmless sentinel because every fitted base is greater than one. -/
@[expose] def verifiedBan {k : ℕ} (rows : Vector Slot k) (b : ℕ) : Bool :=
  decide (b=0 ∨ (HasFixed rows 3 ∧ ((b=5 ∧ HasFixed rows 7) ∨ (b=7 ∧ HasFixed rows 5))))

theorem verifiedBan_sound {k b : ℕ} {rows : Vector Slot k} {x : Fin k → ℕ × ℕ}
    (hg : GenuineSlots x) (hx : ∀ j : Fin k, rows[j].Fits (x j)) (h : verifiedBan rows b) (j : Fin k) :
    (x j).1 ≠ b := by
  intro he
  rcases of_decide_eq_true h with h0|⟨h3,⟨rfl,h7⟩|⟨rfl,h5⟩⟩
  · have := (hx j).base; omega
  · exact hg.no105 ⟨occurs_of_fixed hx h3,⟨j,he⟩,occurs_of_fixed hx h7⟩
  · exact hg.no105 ⟨occurs_of_fixed hx h3,occurs_of_fixed hx h5,⟨j,he⟩⟩

/-- Look only at the integers skipped by a proposed change of endpoint. -/
@[expose] def primeGap (start width stride banned : ℕ) : Bool :=
  decide (∀ j : Fin width, ¬ (fastPrimeBool (start+j.val) = true ∧ (start+j.val)%stride=1 ∧ start+j.val≠banned))

theorem outside_prime_gap {start width stride banned p : ℕ}
    (h : primeGap start width stride banned) (hp : p.Prime) (hr : p%stride=1) (hb : p≠banned) :
    p<start ∨ start+width≤p := by
  by_contra! hc
  let j : Fin width := ⟨p-start,by omega⟩
  have he : start+j.val=p := by dsimp [j]; omega
  have hh := of_decide_eq_true h j
  rw [he] at hh
  exact hh ⟨fastPrimeBool_eq_true_iff.mpr hp,hr,hb⟩

/-- Raise a base past its predecessor and any forbidden primes in the gap. -/
theorem covered_prime_lower {k : ℕ} (rows : Vector Slot k) (i : Fin k) (lo start ban : ℕ)
    (hb : verifiedBan rows ban)
    (hs : start≤rows[i].baseLo ∨ ∃ j : Fin k, j < i ∧ start≤rows[j].baseLo+1)
    (gap : primeGap start (lo-start) rows[i].stride ban)
    (h : PrimeCovered (setBase rows i lo rows[i].baseHi)) : PrimeCovered rows := by
  intro x hm hx hf hg
  have hstart : start≤(x i).1 := by
    rcases hs with le|⟨j,hj,le⟩
    · exact le.trans (hx i).baseLo
    · have hlt : (x j).1 < (x i).1 := hg.strict hj; have := (hx j).baseLo; omega
  have hb' := verifiedBan_sound hg hx hb i
  have hend := outside_prime_gap gap (hg.prime i) (hx i).baseResidue hb'
  exact h x hm (fits_set_base rows i hx (by omega) (hx i).baseHi) hf hg

/-- Lower a base below its successor and any forbidden primes in the gap. -/
theorem covered_prime_upper {k : ℕ} (rows : Vector Slot k) (i : Fin k) (hi stop ban : ℕ)
    (hb : verifiedBan rows ban)
    (hs : (0<rows[i].baseHi ∧ rows[i].baseHi≤stop) ∨
      ∃ j : Fin k, i < j ∧ 0<rows[j].baseHi ∧ rows[j].baseHi≤stop+1)
    (gap : primeGap (hi+1) (stop-hi) rows[i].stride ban)
    (h : PrimeCovered (setBase rows i rows[i].baseLo hi)) : PrimeCovered rows := by
  intro x hm hx hf hg
  have hstop : (x i).1≤stop := by
    rcases hs with ⟨hp,le⟩|⟨j,hj,hp,le⟩
    · exact ((hx i).baseHi.resolve_left hp.ne').trans le
    · have := (hx j).baseHi.resolve_left hp.ne'; have hlt : (x i).1 < (x j).1 := hg.strict hj; omega
  have hb' := verifiedBan_sound hg hx hb i
  have hend := outside_prime_gap gap (hg.prime i) (hx i).baseResidue hb'
  exact h x hm (fits_set_base rows i hx (hx i).baseLo (Or.inr (by omega))) hf hg

end OddPerfect.SpoofBox
