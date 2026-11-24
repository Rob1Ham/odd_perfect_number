module

public import OddPerfect.SpoofBoxes

public section

namespace OddPerfect.SpoofBox

inductive Axis where
  | base | exponent
deriving DecidableEq, Repr

@[expose] def Slot.residue (s : Slot) : Axis → ℕ
  | .base => 1
  | .exponent => s.expResidue

@[expose] def Slot.roundUp (s : Slot) (a : Axis) (n : ℕ) : ℕ :=
  n + (s.residue a + s.stride - n % s.stride) % s.stride

@[expose] def Slot.roundDown (s : Slot) (a : Axis) (n : ℕ) : ℕ :=
  n - (n + s.stride - s.residue a) % s.stride

private theorem round_up_le {s : Slot} {a : Axis} {n v : ℕ} (hn : n≤v)
    (hr : v%s.stride=s.residue a) : s.roundUp a n ≤ v := by
  cases a <;> cases hb : s.special <;>
    simp only [Slot.roundUp,Slot.stride,Slot.expResidue,Slot.residue,hb,Bool.false_eq_true,
      ↓reduceIte] at * <;> omega

private theorem le_round_down {s : Slot} {a : Axis} {n v : ℕ} (hn : v≤n)
    (hr : v%s.stride=s.residue a) : v ≤ s.roundDown a n := by
  cases a <;> cases hb : s.special <;>
    simp only [Slot.roundDown,Slot.stride,Slot.expResidue,Slot.residue,hb,Bool.false_eq_true,
      ↓reduceIte] at * <;> omega

@[expose] def cap (old v : ℕ) : ℕ := if old=0 then v else min old v

private theorem le_cap {old v x : ℕ} (h : old=0 ∨ x≤old) (h' : x≤v) : x ≤ cap old v := by
  unfold cap
  split
  · exact h'
  · rename_i hn
    exact le_min (h.resolve_left hn) h'

@[expose] def Slot.lowerCut (s : Slot) (a : Axis) (n : ℕ) : Slot :=
  match a with
  | .base => {s with baseLo := max s.baseLo (s.roundUp .base n)}
  | .exponent => {s with expLo := max s.expLo (s.roundUp .exponent n)}

@[expose] def Slot.upperCut (s : Slot) (a : Axis) (n : ℕ) : Slot :=
  match a with
  | .base => {s with baseHi := cap s.baseHi (s.roundDown .base n)}
  | .exponent => {s with expHi := cap s.expHi (s.roundDown .exponent n)}

theorem Slot.Fits.raise_base {s : Slot} {z : ℕ × ℕ} (h : s.Fits z) {n : ℕ} (hn : n≤z.1) :
    (s.lowerCut .base n).Fits z :=
  { h with baseLo := max_le h.baseLo (round_up_le (a := .base) hn h.baseResidue) }

theorem Slot.Fits.raise_exp {s : Slot} {z : ℕ × ℕ} (h : s.Fits z) {n : ℕ} (hn : n≤z.2) :
    (s.lowerCut .exponent n).Fits z :=
  { h with expLo := max_le h.expLo (round_up_le (a := .exponent) hn h.expResidue) }

theorem Slot.Fits.cap_base {s : Slot} {z : ℕ × ℕ} (h : s.Fits z) {n : ℕ} (hn : z.1≤n) :
    (s.upperCut .base n).Fits z :=
  { h with baseHi := Or.inr (le_cap h.baseHi (le_round_down (a := .base) hn h.baseResidue)) }

theorem Slot.Fits.cap_exp {s : Slot} {z : ℕ × ℕ} (h : s.Fits z) {n : ℕ} (hn : z.2≤n) :
    (s.upperCut .exponent n).Fits z :=
  { h with expHi := Or.inr (le_cap h.expHi (le_round_down (a := .exponent) hn h.expResidue)) }

/-- Narrow the upper side of a split. An upper bound on an ordered base
also applies to every earlier base, including ties. -/
@[expose] def leftChild {k : ℕ} (s : Fin k → Slot) (i : Fin k) (a : Axis) (cut : ℕ) (j : Fin k) : Slot :=
  match a with
  | .base => if j≤i then (s j).upperCut .base cut else s j
  | .exponent => if j=i then (s j).upperCut .exponent cut else s j

@[expose] def rightChild {k : ℕ} (s : Fin k → Slot) (i : Fin k) (a : Axis) (cut : ℕ) (j : Fin k) : Slot :=
  match a with
  | .base => if i≤j then (s j).lowerCut .base ((s i).roundUp .base (cut+1)) else s j
  | .exponent => if j=i then (s j).lowerCut .exponent (cut+1) else s j

/-- Every realizable point passes to a child at every chosen split. -/
theorem split_covers {k : ℕ} (s : Fin k → Slot) (i : Fin k) (a : Axis) (cut : ℕ)
    (x : Fin k → ℕ × ℕ) (hs : Monotone (fun j => (x j).1)) (hx : ∀ j, (s j).Fits (x j)) :
    (∀ j, (leftChild s i a cut j).Fits (x j)) ∨ (∀ j, (rightChild s i a cut j).Fits (x j)) := by
  cases a with
  | base =>
    by_cases h : (x i).1 ≤ cut
    · left; intro j
      simp only [leftChild]
      split
      · rename_i hj
        exact (hx j).cap_base ((hs hj).trans h)
      · exact hx j
    · right; intro j
      simp only [rightChild]
      split
      · rename_i hj
        have hr := round_up_le (s := s i) (a := .base) (show cut+1 ≤ (x i).1 by omega) (hx i).baseResidue
        exact (hx j).raise_base (hr.trans (hs hj))
      · exact hx j
  | exponent =>
    by_cases h : (x i).2 ≤ cut
    · left; intro j
      simp only [leftChild]
      split
      · subst j; exact (hx i).cap_exp h
      · exact hx j
    · right; intro j
      simp only [rightChild]
      split
      · subst j; exact (hx i).raise_exp (by omega)
      · exact hx j

end OddPerfect.SpoofBox
