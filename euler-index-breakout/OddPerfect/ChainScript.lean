module

public import OddPerfect.ChainGroupBounds

/-! Compact factor-chain certificates keyed by the local case number. -/

public section

namespace OddPerfect.FactorBudget

/-- Children are indexed by the candidate-prime index and exponent. A
missing child has to terminate using the directly checked arithmetic tests. -/
inductive Script where
  | automatic
  | node (hint : ChoiceHint) (cases : List (ℕ × Script))

@[expose] def Script.groups (gs : List ℕ) : Script := .node (.basic (.groups gs)) []
@[expose] def Script.split (p : ℕ) (cases : List (ℕ × Script)) : Script := .node (.basic (.split p)) cases
@[expose] def Script.cut (a L g : ℕ) (cases : List (ℕ × Script)) : Script := .node (.cut a L g) cases

@[expose] def Script.hint? : Script → Option ChoiceHint
  | .automatic => none
  | .node h _ => some h

@[expose] def Script.child (i : ℕ) : Script → Script
  | .automatic => .automatic
  | .node _ cs => (cs.lookup i).getD .automatic

@[expose] def replayScript (primes : List ℕ) (seed avoid budget minDistinct c : ℕ) :
    ℕ → Node → Script → Bool
  | 0, _, _ => false
  | fuel+1, s, tree =>
    if s.automatic budget minDistinct then true else
    match prepareTightChoices primes (fun _ => tree.hint?) seed avoid budget minDistinct c s with
    | none => false
    | some ps => ps.all fun p => (List.range (budget-s.spent)).all fun i =>
        replayScript primes seed avoid budget minDistinct c fuel (s.extend p (i+1))
          (tree.child (ps.idxOf p * (budget+1) + (i+1)))

/-- Kernel soundness of the compact tree representation. Nothing about its
index ordering or the construction of the omitted children is assumed. -/
theorem replayScript_correct {N B w seed avoid c : ℕ} (H : Conditions N B w)
    (hseed : seed ∣ N) (havoid : avoid.Coprime N) (hcount : 18*N.primeFactors.card ≤ 7*B+c)
    (primes : List ℕ) (hp : ∀ p ∈ primes, p.Prime) (fuel : ℕ) {s : Node} {m : ℕ}
    (h : Realizes s N m) (tree : Script)
    (test : replayScript primes seed avoid B w c fuel s tree = true) : False := by
  induction fuel generalizing s m tree with
  | zero => simp [replayScript] at test
  | succ fuel ih =>
    by_cases ha : s.automatic B w = true
    · exact automatic_false H h ha
    cases hsteps : prepareTightChoices primes (fun _ => tree.hint?) seed avoid B w c s with
    | none => simp [replayScript, ha, hsteps] at test
    | some ps =>
      simp only [replayScript, ha, Bool.false_eq_true, ↓reduceIte, hsteps, List.all_eq_true,
        List.mem_range] at test
      obtain ⟨p, hpm, hprime, hd⟩ := prepareTightChoices_correct H hseed havoid hcount primes hp _ h hsteps
      obtain ⟨hpos, hub⟩ := exponent_bounds H h hprime hd
      have hnext := test p hpm (m.factorization p-1) (by omega)
      rw [Nat.sub_add_cancel hpos] at hnext
      exact ih (extend_realizes H.odd.pos.ne' h hprime hd) _ hnext

end OddPerfect.FactorBudget
