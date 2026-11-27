module

public import OddPerfect.DeficientCuts

public section
namespace OddPerfect.DeficientSlots
open SpoofBox

inductive Step where
  | primeLo (i : Fin 4) (lo : ℕ)
  | primeHi (i : Fin 4) (hi : ℕ)
  | xLo (lo : ℕ)
  | xHi (hi : ℕ)
  | grow (src : Fin 5) (p : ℕ)
  | fix (src : Fin 5) (p : ℕ) (target : Fin 4)
  | dropLo (i : Fin 5) (lo : ℕ)
  | dropHi (i : Fin 5) (hi : ℕ)

inductive Tree where
  | reject
  | last (i : Fin 5)
  | missing (src : Fin 5) (p : ℕ)
  | step (s : Step) (next : Tree)
  | splitBase (i : Fin 5) (cut : ℕ) (left right : Tree)
  | splitExp (i : Fin 4) (cut : ℕ) (left right : Tree)
  | splitSpecial (cut : ℕ) (left right : Tree)
  | use (key : ℕ)

/-- A previously checked subtree is applicable only to its exact rows
and the exact divisibility assumption on its multiplier. -/
structure Known where
  rows : Vector Slot 5
  multiple : ℕ
  valid : Closed rows multiple

@[expose] def lowerStart (rows : Vector Slot 5) (i : Fin 4) : ℕ :=
  if i.val=0 then rows[i.castSucc].baseLo else
    max rows[i.castSucc].baseLo (rows[(⟨i.val-1,by omega⟩ : Fin 5)].baseLo+1)

@[expose] def upperStop (rows : Vector Slot 5) (i : Fin 4) : ℕ :=
  let after := if i.val<3 then rows[(⟨i.val+1,by omega⟩ : Fin 5)].baseHi else 0
  if after=0 then rows[i.castSucc].baseHi else cap rows[i.castSucc].baseHi (after-1)

@[expose] def delivery (rows : Vector Slot 5) (i : Fin 5) (p : ℕ) : Bool :=
  (fastPrimeBool p && decide (p%2=1)) && delivers rows[i] p

private theorem delivery_cases {rows : Vector Slot 5} {z : Fin 5 → ℕ × ℕ} (h : Real z)
    (fit : ∀ i : Fin 5, rows[i].Fits (z i)) {src : Fin 5} {p : ℕ} (ok : delivery rows src p) :
    (∃ j : Fin 4, (z j.castSucc).1=p) ∨ p∣(z 4).1 := by
  obtain ⟨num,dvd⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨hp_b,ho_b⟩ := Bool.and_eq_true_iff.mp num
  exact h.forces (fastPrimeBool_eq_true_iff.mp hp_b) (Nat.odd_iff.mpr (of_decide_eq_true ho_b))
    src (delivers_sound (fit src) dvd)

@[expose] def noPrimeSlot (rows : Vector Slot 5) (p : ℕ) : Bool :=
  decide (∀ j : Fin 4, admitsBase rows[j.castSucc] p = false)

private theorem delivered_to_multiplier {rows : Vector Slot 5} {z : Fin 5 → ℕ × ℕ} (h : Real z)
    (fit : ∀ i : Fin 5, rows[i].Fits (z i)) {src : Fin 5} {p : ℕ}
    (ok : delivery rows src p) (none : noPrimeSlot rows p) : p∣(z 4).1 := by
  rcases delivery_cases h fit ok with ⟨j,hj⟩|hid
  · have ha := admitsBase_of_fits (fit j.castSucc)
    rw [hj,of_decide_eq_true none j] at ha
    contradiction
  · exact hid

@[expose] def Step.next (s : Step) (rows : Vector Slot 5) (g : ℕ) : Vector Slot 5 × ℕ :=
  match s with
  | .primeLo i lo => (setBase rows i.castSucc lo rows[i.castSucc].baseHi,g)
  | .primeHi i hi => (setBase rows i.castSucc rows[i.castSucc].baseLo hi,g)
  | .xLo lo => (setBase rows 4 lo rows[4].baseHi,g)
  | .xHi hi => (setBase rows 4 rows[4].baseLo hi,g)
  | .grow _ p => (rows,g.lcm p)
  | .fix _ p j => (setBase rows j.castSucc p p,g)
  | .dropLo i lo => (lowerBase rows i lo,g)
  | .dropHi i hi => (upperBase rows i hi,g)

@[expose] def Step.valid (s : Step) (rows : Vector Slot 5) (g : ℕ) : Bool :=
  match s with
  | .primeLo i lo =>
    let start := lowerStart rows i
    decide (start≤rows[i.castSucc].baseLo ∨ ∃ j : Fin 4, j < i ∧ start≤rows[j.castSucc].baseLo+1) &&
      primeGap start (lo-start) rows[i.castSucc].stride 0
  | .primeHi i hi =>
    let stop := upperStop rows i
    decide ((0<rows[i.castSucc].baseHi ∧ rows[i.castSucc].baseHi≤stop) ∨
      ∃ j : Fin 4, i < j ∧ 0<rows[j.castSucc].baseHi ∧ rows[j.castSucc].baseHi≤stop+1) &&
      primeGap (hi+1) (stop-hi) rows[i.castSucc].stride 0
  | .xLo lo => decide (lo≤firstMultiplier g rows[4].baseLo)
  | .xHi hi => decide (hi=0 ∨ (0<rows[4].baseHi ∧ rows[4].baseHi<firstMultiplier g (hi+1)))
  | .grow src p => delivery rows src p && noPrimeSlot rows p
  | .fix src p j => delivery rows src p && noMultiplier rows[4] (g.lcm p) &&
      decide (∀ k : Fin 4, admitsBase rows[k.castSucc] p = true → k=j)
  | .dropLo i lo => decide (0<lo) &&
      acceptedLeaf (fun j : Fin 5 => (upperBase rows i (lo-1))[j]) [historical]
  | .dropHi i hi => acceptedLeaf (fun j : Fin 5 => (lowerBase rows i (hi+1))[j]) [historical]

theorem Step.sound (s : Step) (rows : Vector Slot 5) (g : ℕ) (ok : s.valid rows g)
    (next : Closed (s.next rows g).1 (s.next rows g).2) : Closed rows g := by
  cases s with
  | primeLo i lo =>
    obtain ⟨hs,hg⟩ := Bool.and_eq_true_iff.mp ok
    exact closed_prime_lower i lo _ (of_decide_eq_true hs) hg next
  | primeHi i hi =>
    obtain ⟨hs,hg⟩ := Bool.and_eq_true_iff.mp ok
    exact closed_prime_upper i hi _ (of_decide_eq_true hs) hg next
  | xLo lo =>
    intro z h fit hd
    exact next z h (fits_set_base rows 4 fit ((of_decide_eq_true ok).trans
      (firstMultiplier_le hd h.multiplier (fit 4).baseLo)) (fit 4).baseHi) hd
  | xHi hi =>
    intro z h fit hd
    apply next z h _ hd
    apply fits_set_base rows 4 fit (fit 4).baseLo
    rcases of_decide_eq_true ok with zero|⟨pos,lt⟩
    · exact .inl zero
    · right
      by_contra! large
      exact lt.not_ge ((firstMultiplier_le hd h.multiplier large).trans ((fit 4).baseHi.resolve_left pos.ne'))
  | grow src p =>
    obtain ⟨d,no⟩ := Bool.and_eq_true_iff.mp ok
    intro z h fit hd
    exact next z h fit (Nat.lcm_dvd hd (delivered_to_multiplier h fit d no))
  | fix src p j =>
    simp only [valid,Bool.and_eq_true,decide_eq_true_eq] at ok
    intro z h fit hd
    rcases delivery_cases h fit ok.1.1 with ⟨k,eq⟩|del
    · have haj := admitsBase_of_fits (fit k.castSucc)
      rw [eq] at haj
      obtain rfl := ok.2 k haj
      exact next z h (fits_set_base rows k.castSucc fit eq.ge (.inr eq.le)) hd
    · exact (noMultiplier_sound (fit 4) h.multiplier ok.1.2 (Nat.lcm_dvd hd del)).elim
  | dropLo i lo =>
    obtain ⟨pos,cut⟩ := Bool.and_eq_true_iff.mp ok
    have eq : lo-1+1=lo := by have := of_decide_eq_true pos; omega
    apply closed_split_base i (lo-1) (closed_leaf cut)
    rw [eq]
    exact next
  | dropHi i hi => exact closed_split_base i hi next (closed_leaf ok)

@[expose] def sameSlot (a b : Slot) : Bool :=
  a.special == b.special && a.baseLo == b.baseLo && a.baseHi == b.baseHi &&
    a.expLo == b.expLo && a.expHi == b.expHi

private theorem sameSlot_eq {a b : Slot} (h : sameSlot a b = true) : a = b := by
  cases a; cases b
  simp only [sameSlot, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  subst h1 h2 h3 h4 h5
  rfl

@[expose] def Tree.check (t : Tree) (refs : List Known) (rows : Vector Slot 5) (g : ℕ) : Bool :=
  match t with
  | .reject => acceptedLeaf (fun j : Fin 5 => rows[j]) [historical]
  | .last i => lastLeaf (fun j : Fin 5 => rows[j]) i [historical]
  | .missing src p => delivery rows src p && noPrimeSlot rows p && noMultiplier rows[4] (g.lcm p)
  | .step s t =>
    let st := s.next rows g
    s.valid rows g && t.check refs st.1 st.2
  | .splitBase i cut l r => l.check refs (upperBase rows i cut) g && r.check refs (lowerBase rows i (cut+1)) g
  | .splitExp i cut l r => decide (cut%2=0) && l.check refs (setExp rows i rows[i.castSucc].expLo cut) g &&
      r.check refs (setExp rows i (cut+2) rows[i.castSucc].expHi) g
  | .splitSpecial cut l r => decide (cut%4=1) && l.check refs (setSpecialExp rows rows[4].expLo cut) g &&
      r.check refs (setSpecialExp rows (cut+4) rows[4].expHi) g
  | .use key => match refs[key]? with
    | none => false
    | some known => sameSlot known.rows[0] rows[0] && sameSlot known.rows[1] rows[1] &&
        sameSlot known.rows[2] rows[2] && sameSlot known.rows[3] rows[3] &&
        sameSlot known.rows[4] rows[4] && decide (known.multiple = g)

theorem Tree.sound (t : Tree) (refs : List Known) (rows : Vector Slot 5) (g : ℕ)
    (ok : t.check refs rows g) : Closed rows g := by
  induction t generalizing rows g with
  | reject => exact closed_leaf ok
  | last i => exact closed_last i ok
  | missing src p =>
    simp only [check,Bool.and_eq_true] at ok
    intro z h fit hd
    exact (noMultiplier_sound (fit 4) h.multiplier ok.2
      (Nat.lcm_dvd hd (delivered_to_multiplier h fit ok.1.1 ok.1.2))).elim
  | step s t ih =>
    obtain ⟨hs,ht⟩ := Bool.and_eq_true_iff.mp ok
    exact s.sound rows g hs (ih _ _ ht)
  | splitBase i cut l r il ir =>
    obtain ⟨hl,hr⟩ := Bool.and_eq_true_iff.mp ok
    exact closed_split_base i cut (il _ _ hl) (ir _ _ hr)
  | splitExp i cut l r il ir =>
    simp only [check,Bool.and_eq_true,decide_eq_true_eq] at ok
    exact closed_split_exp i cut ok.1.1 (il _ _ ok.1.2) (ir _ _ ok.2)
  | splitSpecial cut l r il ir =>
    simp only [check,Bool.and_eq_true,decide_eq_true_eq] at ok
    exact closed_split_special cut ok.1.1 (il _ _ ok.1.2) (ir _ _ ok.2)
  | use key =>
    unfold check at ok
    split at ok
    · contradiction
    · rename_i known _
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ok
      obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, eq2⟩ := ok
      have eqr : known.rows = rows := Vector.ext fun k hk => by
        rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl|rfl|rfl|rfl|rfl
        · exact sameSlot_eq h0
        · exact sameSlot_eq h1
        · exact sameSlot_eq h2
        · exact sameSlot_eq h3
        · exact sameSlot_eq h4
      exact eqr ▸ eq2 ▸ known.valid

end OddPerfect.DeficientSlots
