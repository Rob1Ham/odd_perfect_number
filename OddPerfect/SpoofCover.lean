module

public import OddPerfect.SpoofLast

public section

namespace OddPerfect.SpoofBox

/-- All ordered formally balanced points in this box satisfy the desired
classification. The predicate can also express extra conditions on prime bases. -/
@[expose] def Covered {k : ℕ} (keep : (Fin k → ℕ × ℕ) → Prop) (rows : Vector Slot k) : Prop :=
  ∀ x : Fin k → ℕ × ℕ, Monotone (fun i => (x i).1) →
    (∀ i : Fin k, (rows[i]).Fits (x i)) →
    formalSigma Finset.univ (fun i => (x i).1) (fun i => (x i).2) = 2*∏ i, (x i).1^(x i).2 →
    keep x

@[expose] def child {k : ℕ} (left : Bool) (rows : Vector Slot k) (i : Fin k) (a : Axis) : Vector Slot k :=
  let s := fun j : Fin k => rows[j]
  let cut := pivot (s i) a
  if left then Vector.ofFn (leftChild s i a cut) else Vector.ofFn (rightChild s i a cut)

theorem covered_split {k : ℕ} {keep : (Fin k → ℕ × ℕ) → Prop} (rows : Vector Slot k) (i : Fin k) (a : Axis)
    (hl : Covered keep (child true rows i a)) (hr : Covered keep (child false rows i a)) :
    Covered keep rows := by
  intro x hs hx hb
  rcases split_covers (fun j : Fin k => rows[j]) i a (pivot rows[i] a) x hs hx with h | h
  · exact hl x hs (by simpa [child] using h) hb
  · exact hr x hs (by simpa [child] using h) hb

theorem covered_standard {k : ℕ} (rows : Vector Slot k) (allowed : List (Fin k → ℕ × ℕ))
    (h : acceptedLeaf (fun j : Fin k => rows[j]) allowed) : Covered (· ∈ allowed) rows := by
  intro x _ hx hb
  exact acceptedLeaf_sound _ allowed x hx hb h

theorem covered_last {k : ℕ} (rows : Vector Slot k) (i : Fin k) (allowed : List (Fin k → ℕ × ℕ))
    (h : lastLeaf (fun j : Fin k => rows[j]) i allowed) : Covered (· ∈ allowed) rows := by
  intro x _ hx hb
  exact lastLeaf_sound _ i allowed x hx hb h

/-- Five uppercase ASCII base-26 digits per node store the offset of its
right child in node units. Independent offsets avoid replaying the left
subtree to find a right child. Malformed offsets still require both children
to cover their mathematically specified boxes. -/
@[expose] def rightJump (table : ByteArray) (n : ℕ) : ℕ :=
  let digit := fun j => (table[(5*n+j)]?.getD 65).toNat-65
  ((((digit 0 * 26 + digit 1) * 26 + digit 2) * 26 + digit 3) * 26 + digit 4)

/-- A denotes the ordinary interval rule, B onward encode split index and
axis, and lowercase bytes call the supplied leaf rules. -/
@[expose] def verifyCover {k : ℕ} (code jumps : ByteArray) (leaf : ℕ → Vector Slot k → Bool) :
    ℕ → ℕ → Vector Slot k → Bool
  | 0, _, _ => false
  | depth+1, n, rows =>
    let op := (code[n]?.getD 0).toNat
    if op=65 ∨ 97≤op then leaf op rows else
    if op<66 then false else
    if h : (op-66)/2 < k then
      let i : Fin k := ⟨_,h⟩
      let a := if (op-66)%2=0 then Axis.base else Axis.exponent
      verifyCover code jumps leaf depth (n+1) (child true rows i a) &&
      verifyCover code jumps leaf depth (n+rightJump jumps n) (child false rows i a)
    else false

theorem verifyCover_sound {k : ℕ} (code jumps : ByteArray) (leaf : ℕ → Vector Slot k → Bool)
    (keep : (Fin k → ℕ × ℕ) → Prop) (hleaf : ∀ op rows, leaf op rows → Covered keep rows)
    (d n : ℕ) (rows : Vector Slot k) (h : verifyCover code jumps leaf d n rows) : Covered keep rows := by
  induction d generalizing n rows with
  | zero => simp [verifyCover] at h
  | succ d ih =>
    unfold verifyCover at h
    dsimp only at h
    split at h
    · exact hleaf _ _ h
    · split at h
      · contradiction
      · split at h
        · exact covered_split rows _ _ (ih _ _ (Bool.and_eq_true_iff.mp h).1)
            (ih _ _ (Bool.and_eq_true_iff.mp h).2)
        · contradiction

@[expose] def spoofRule {k : ℕ} (allowed : List (Fin k → ℕ × ℕ)) (op : ℕ) (rows : Vector Slot k) : Bool :=
  if op=65 then acceptedLeaf (fun j : Fin k => rows[j]) allowed else
  if h : op-97 < k then lastLeaf (fun j : Fin k => rows[j]) ⟨_,h⟩ allowed else false

theorem spoofRule_sound {k : ℕ} (allowed : List (Fin k → ℕ × ℕ)) (op : ℕ) (rows : Vector Slot k)
    (h : spoofRule allowed op rows) : Covered (· ∈ allowed) rows := by
  unfold spoofRule at h
  split at h
  · exact covered_standard rows allowed h
  · split at h
    · exact covered_last rows _ allowed h
    · contradiction

end OddPerfect.SpoofBox
