module

public import OddPerfect.SpoofSplit

public section

namespace OddPerfect.SpoofBox

/-- The forking coordinate is supplied by the search program. Splitting near
the harmonic mean of the base endpoints avoids enumerating a large interval
one odd integer at a time. A zero upper bound represents infinity. -/
@[expose] def pivot (s : Slot) (a : Axis) : ℕ :=
  match a with
  | .exponent => s.expLo
  | .base =>
    let lo := s.baseLo
    let hi := s.baseHi
    let mid := if hi=0 then 2*lo else (2*lo*hi)/(lo+hi)
    let cut := lo + s.stride*((mid-lo)/s.stride)
    if hi=0 then cut else min cut (hi-s.stride)

@[expose] def emptyBox {k : ℕ} (s : Fin k → Slot) : Bool :=
  decide (∃ i, (0 < (s i).baseHi ∧ (s i).baseHi < (s i).baseLo) ∨
    (0 < (s i).expHi ∧ (s i).expHi < (s i).expLo))

private theorem emptyBox_false {k : ℕ} {s : Fin k → Slot} {x : Fin k → ℕ × ℕ}
    (hx : ∀ i, (s i).Fits (x i)) : emptyBox s = false := by
  apply decide_eq_false
  rintro ⟨i, (⟨h1,h2⟩|⟨h1,h2⟩)⟩
  · have := (hx i).baseHi
    have := (hx i).baseLo
    omega
  · have := (hx i).expHi
    have := (hx i).expLo
    omega

/-- Upper and lower endpoints fixing every slot to a permitted solution. -/
@[expose] def fixes {k : ℕ} (s : Fin k → Slot) (z : Fin k → ℕ × ℕ) : Bool :=
  decide (∀ i, 0 < (s i).baseHi ∧ 0 < (s i).expHi ∧
    (s i).baseLo = (z i).1 ∧ (s i).baseHi = (z i).1 ∧
    (s i).expLo = (z i).2 ∧ (s i).expHi = (z i).2)

private theorem fixes_eq {k : ℕ} {s : Fin k → Slot} {x z : Fin k → ℕ × ℕ}
    (hx : ∀ i, (s i).Fits (x i)) (h : fixes s z) : x=z := by
  have hall := of_decide_eq_true h
  funext i
  obtain ⟨hb,he,hbl,hbu,hel,heu⟩ := hall i
  have hbx := (hx i).baseHi
  have hby := (hx i).baseLo
  have hex := (hx i).expHi
  have hey := (hx i).expLo
  exact Prod.ext (by omega) (by omega)

@[expose] def acceptedLeaf {k : ℕ} (s : Fin k → Slot) (allowed : List (Fin k → ℕ × ℕ)) : Bool :=
  emptyBox s || rejects s || allowed.any (fixes s)

theorem acceptedLeaf_sound {k : ℕ} (s : Fin k → Slot) (allowed : List (Fin k → ℕ × ℕ))
    (x : Fin k → ℕ × ℕ) (hx : ∀ i, (s i).Fits (x i))
    (hb : formalSigma Finset.univ (fun i => (x i).1) (fun i => (x i).2) = 2*∏ i, (x i).1^(x i).2)
    (hl : acceptedLeaf s allowed) : x ∈ allowed := by
  simp only [acceptedLeaf, emptyBox_false hx, rejects_sound s x hx hb, Bool.false_or,
    List.any_eq_true] at hl
  obtain ⟨y,hy,heq⟩ := hl
  exact (fixes_eq hx heq) ▸ hy

/-- Initial rectangles for a sorted positive odd factorization. Euler
parity fixes the exceptional slot and the two residue classes throughout. -/
@[expose] def initial {k : ℕ} (special : Fin k) : Vector Slot k :=
  Vector.ofFn (fun i => if i=special then ⟨true,5,0,1,0⟩ else ⟨false,3,0,2,0⟩)

theorem realizing_initial {k : ℕ} (x : Fin k → ℕ × ℕ)
    (hx : ∀ i, 1 < (x i).1 ∧ Odd (x i).1 ∧ 0 < (x i).2)
    (hb : formalSigma Finset.univ (fun i => (x i).1) (fun i => (x i).2) = 2*∏ i, (x i).1^(x i).2) :
    ∃ i : Fin k, ∀ j : Fin k, ((initial i)[j]).Fits (x j) := by
  obtain ⟨i,_,h4,e4,hrest⟩ := formal_euler_exponents Finset.univ (fun i => (x i).1)
    (fun i => (x i).2) (fun i _ => (hx i).2.1) hb
  refine ⟨i,fun j => ?_⟩
  obtain ⟨hj,ho,he⟩ := hx j
  by_cases h : j=i
  · subst j
    change ((initial i)[i.val]).Fits (x i)
    rw [initial,Vector.getElem_ofFn,ite_eq_left (rfl : i=i)]
    exact ⟨hj,he,show 5 ≤ (x i).1 by omega,Or.inl rfl,he,Or.inl rfl,h4,e4⟩
  · have heven := Nat.even_iff.mp (hrest j (Finset.mem_univ _) h)
    have hodd := Nat.odd_iff.mp ho
    change ((initial i)[j.val]).Fits (x j)
    rw [initial,Vector.getElem_ofFn,ite_eq_right h]
    exact ⟨hj,he,show 3 ≤ (x j).1 by omega,Or.inl rfl,show 2 ≤ (x j).2 by omega,Or.inl rfl,hodd,heven⟩

end OddPerfect.SpoofBox
