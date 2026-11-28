module

public import OddPerfect.FactorBudget

/-! Replay of a finite tree of exact prime-exponent cases. -/

public section

namespace OddPerfect.FactorBudget

/-- Untrusted hints select the next prime or exhibit coprime residual factors. -/
inductive Hint where
  | split (p : ℕ)
  | groups (factors : List ℕ)
  deriving Repr

/-- A lookup table for larger certificates. Its ordering changes only replay cost. -/
inductive HintTree where
  | empty
  | node (component : ℕ) (hint : Hint) (left right : HintTree)
  deriving Repr

@[expose] def HintTree.lookup (n : ℕ) : HintTree → Option Hint
  | .empty => none
  | .node k h l r => if n = k then some h else if n < k then l.lookup n else r.lookup n

/-- The exact component identifies a branch uniquely. Each split enumerates
all exponents compatible with the remaining total count. -/
@[expose] def certify (primes : List ℕ) (hints : ℕ → Option Hint) (seed budget minDistinct : ℕ) :
    ℕ → Node → Bool
  | 0, _ => false
  | fuel+1, s =>
    if s.automatic budget minDistinct then true else
    match hints s.component with
    | none => false
    | some (.groups gs) => checkGroups gs && decide (gs.prod ∣ s.forcedPart ∧
        budget+1 < s.spent + 2 * max gs.length (minDistinct-s.closed) + s.spent%2)
    | some (.split p) => decide (p ∈ primes ∧ (p ∣ s.forcedPart ∨ (p ∣ seed ∧ s.component.Coprime p))) &&
        (List.range (budget-s.spent)).all fun i => certify primes hints seed budget minDistinct fuel (s.extend p (i+1))

/-- Every accepted certificate contradicts the existence of a realizing
odd perfect number, independent of how the hints were obtained. -/
theorem certify_correct {N B w seed : ℕ} (H : Conditions N B w) (hseed : seed ∣ N)
    (primes : List ℕ) (hp : ∀ p ∈ primes, p.Prime) (hints : ℕ → Option Hint)
    (fuel : ℕ) {s : Node} {m : ℕ} (h : Realizes s N m)
    (test : certify primes hints seed B w fuel s = true) : False := by
  induction fuel generalizing s m with
  | zero => simp [certify] at test
  | succ fuel ih =>
    by_cases ha : s.automatic B w = true
    · exact automatic_false H h ha
    cases hh : hints s.component with
    | none => simp [certify, ha, hh] at test
    | some hint =>
      cases hint with
      | groups gs =>
        simp only [certify, ha, Bool.false_eq_true, ↓reduceIte, hh, Bool.and_eq_true,
          decide_eq_true_eq] at test
        have := budget_bound H h (groups_le_support H.perfect h gs test.1 test.2.1)
        omega
      | split p =>
        simp only [certify, ha, Bool.false_eq_true, ↓reduceIte, hh, Bool.and_eq_true,
          decide_eq_true_eq, List.all_eq_true, List.mem_range] at test
        have hprime := hp p test.1.1
        have hd : p ∣ m := by
          rcases test.1.2 with hpart | ⟨hds, hcop⟩
          · exact hpart.trans (forcedPart_dvd h H.perfect)
          · apply hcop.symm.dvd_of_dvd_mul_left
            rw [← h.value]
            exact hds.trans hseed
        obtain ⟨hpos, hub⟩ := exponent_bounds H h hprime hd
        have ha := test.2 (m.factorization p-1) (by omega)
        rw [Nat.sub_add_cancel hpos] at ha
        exact ih (extend_realizes H.odd.pos.ne' h hprime hd) ha

end OddPerfect.FactorBudget
