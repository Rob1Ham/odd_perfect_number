module

public import OddPerfect.PrimeCover
public import OddPerfect.PrimeBank

public section
namespace OddPerfect.SpoofBox

/-- A complete interval certificate for genuine prime slots.
Every narrowing operation carries the endpoints it needs to verify. -/
inductive PrimeTree (k : ℕ) where
  | use (key : ℕ)
  | reject
  | impossible
  | last (i : Fin k)
  | missing (i : Fin k) (p : ℕ)
  | split (i : Fin k) (a : Axis) (cut : ℕ) (left right : PrimeTree k)
  | lower (i : Fin k) (lo start ban : ℕ) (next : PrimeTree k)
  | upper (i : Fin k) (hi stop ban : ℕ) (next : PrimeTree k)
  | force (source target : Fin k) (p : ℕ) (next : PrimeTree k)

structure PrimeKnown (k : ℕ) where
  rows : Vector Slot k
  valid : PrimeCovered rows

@[expose] def primeOK (bank : PrimeBank) (p : ℕ) : Bool :=
  if p<512 then decide p.Prime else bank.contains p

private theorem primeOK_sound (bank : PrimeBank) (hc : bank.Certified) {p : ℕ}
    (hp : primeOK bank p) : p.Prime := by
  unfold primeOK at hp
  split at hp
  · exact of_decide_eq_true hp
  · exact bank.prime_of_contains hc hp

@[expose] def PrimeTree.check {k : ℕ} (bank : PrimeBank) (refs : List (PrimeKnown k)) (rows : Vector Slot k) : PrimeTree k → Bool
  | .use key => match refs[key]? with
    | none => false
    | some known => decide (known.rows=rows)
  | .reject => acceptedLeaf (fun i : Fin k => rows[i]) []
  | .impossible => impossiblePrimeRows (fun i : Fin k => rows[i])
  | .last i => lastLeaf (fun j : Fin k => rows[j]) i [] ||
      (fixedApart (fun j : Fin k => rows[j]) i && decide (¬((completeBox (fun j : Fin k => rows[j]) i i).1).Prime))
  | .missing i p => primeOK bank p && decide (p%2=1) && delivers rows[i] p &&
      decide (∀ j : Fin k, admitsBase rows[j] p = false)
  | .split i a cut l r => l.check bank refs (childAt true rows i a cut) && r.check bank refs (childAt false rows i a cut)
  | .lower i lo start ban next =>
    verifiedBan rows ban && decide (start≤rows[i].baseLo ∨ ∃ j : Fin k, j < i ∧ start≤rows[j].baseLo+1) &&
    primeGap start (lo-start) rows[i].stride ban && next.check bank refs (setBase rows i lo rows[i].baseHi)
  | .upper i hi stop ban next =>
    verifiedBan rows ban && decide ((0<rows[i].baseHi ∧ rows[i].baseHi≤stop) ∨
      ∃ j : Fin k, i < j ∧ 0<rows[j].baseHi ∧ rows[j].baseHi≤stop+1) &&
    primeGap (hi+1) (stop-hi) rows[i].stride ban && next.check bank refs (setBase rows i rows[i].baseLo hi)
  | .force i j p next => primeOK bank p && decide (p%2=1) && delivers rows[i] p &&
    decide (∀ z : Fin k, admitsBase rows[z] p = true → z=j) && next.check bank refs (setBase rows j p p)

theorem PrimeTree.sound {k : ℕ} (bank : PrimeBank) (hc : bank.Certified) (t : PrimeTree k)
    (refs : List (PrimeKnown k)) (rows : Vector Slot k) (ok : t.check bank refs rows) : PrimeCovered rows := by
  induction t generalizing rows with
  | use key =>
    unfold check at ok
    split at ok
    · contradiction
    · rename_i known _
      exact (of_decide_eq_true ok) ▸ known.valid
  | reject => exact primeCovered_reject rows ok
  | impossible => exact covered_impossible_prime_rows rows ok
  | last i =>
    simp only [check,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at ok
    exact primeCovered_last rows i ok
  | missing i p =>
    simp only [check,Bool.and_eq_true,decide_eq_true_eq] at ok
    exact primeCovered_missing rows i p (primeOK_sound bank hc ok.1.1.1) ok.1.1.2 ok.1.2 ok.2
  | split i a c l r il ir =>
    obtain ⟨hl,hr⟩ := Bool.and_eq_true_iff.mp ok
    exact primeCovered_split rows i a c (il _ hl) (ir _ hr)
  | lower i lo start ban t ih =>
    simp only [check,Bool.and_eq_true,decide_eq_true_eq] at ok
    exact covered_prime_lower rows i lo start ban ok.1.1.1 ok.1.1.2 ok.1.2 (ih _ ok.2)
  | upper i hi stop ban t ih =>
    simp only [check,Bool.and_eq_true,decide_eq_true_eq] at ok
    exact covered_prime_upper rows i hi stop ban ok.1.1.1 ok.1.1.2 ok.1.2 (ih _ ok.2)
  | force i j p t ih =>
    simp only [check,Bool.and_eq_true,decide_eq_true_eq] at ok
    exact covered_force_base rows i j p (primeOK_sound bank hc ok.1.1.1.1)
      (Nat.odd_iff.mpr ok.1.1.1.2) ok.1.1.2 ok.1.2 (ih _ ok.2)

end OddPerfect.SpoofBox
