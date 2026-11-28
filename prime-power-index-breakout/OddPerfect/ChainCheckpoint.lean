module

public import OddPerfect.ChainScript

/-! Composition of independently checked exact-exponent subtrees. -/

public section

namespace OddPerfect.FactorBudget

/-- Check every field before transferring a cofactor to an earlier subtree proof. -/
@[expose] def Node.same (s t : Node) : Bool :=
  decide (s.component = t.component ∧ s.divisorSum = t.divisorSum ∧ s.spent = t.spent ∧ s.closed = t.closed)

private theorem eq_of_same {s t : Node} (hs : s.same t = true) : s = t := by
  cases s
  cases t
  simp [Node.same] at hs
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
  rfl

/-- A missing hint may hand its full numeric node to a separately proved subtree. -/
@[expose] def replayChunk (earlier : List Node) (primes : List ℕ) (seed avoid B w c : ℕ) :
    ℕ → Node → Script → Bool
  | 0, _, _ => false
  | fuel+1, s, tree =>
    if s.automatic B w then true else
    if tree.hint?.isNone && earlier.any s.same then true else
    match prepareTightChoices primes (fun _ => tree.hint?) seed avoid B w c s with
    | none => false
    | some ps => ps.all fun p => (List.range (B-s.spent)).all fun i =>
        replayChunk earlier primes seed avoid B w c fuel (s.extend p (i+1))
          (tree.child (ps.idxOf p * (B+1) + (i+1)))

/-- The transfer hypotheses quantify over every cofactor realizing each node. -/
theorem replayChunk_correct {N B w seed avoid c : ℕ} (H : Conditions N B w)
    (hseed : seed ∣ N) (hav : avoid.Coprime N) (hc : 18*N.primeFactors.card ≤ 7*B+c)
    (earlier : List Node) (prior : ∀ t ∈ earlier, ∀ m, Realizes t N m → False)
    (primes : List ℕ) (hp : ∀ p ∈ primes, p.Prime) (fuel : ℕ) {s : Node} {m : ℕ}
    (h : Realizes s N m) (tree : Script)
    (test : replayChunk earlier primes seed avoid B w c fuel s tree = true) : False := by
  induction fuel generalizing s m tree with
  | zero => simp [replayChunk] at test
  | succ fuel ih =>
    by_cases ha : s.automatic B w = true
    · exact automatic_false H h ha
    by_cases he : (tree.hint?.isNone && earlier.any s.same) = true
    · have hn : tree.hint?.isNone = true ∧ earlier.any s.same = true := by simpa only [Bool.and_eq_true] using he
      obtain ⟨t, ht, hm⟩ := List.any_eq_true.mp hn.2
      exact prior t ht m (eq_of_same hm ▸ h)
    cases hs : prepareTightChoices primes (fun _ => tree.hint?) seed avoid B w c s with
    | none => simp [replayChunk, ha, he, hs] at test
    | some ps =>
      simp only [replayChunk, ha, he, Bool.false_eq_true, ↓reduceIte, hs,
        List.all_eq_true, List.mem_range] at test
      obtain ⟨p, hpm, hprime, hd⟩ := prepareTightChoices_correct H hseed hav hc primes hp _ h hs
      obtain ⟨he, hu⟩ := exponent_bounds H h hprime hd
      have hnext := test p hpm (m.factorization p-1) (by omega)
      rw [Nat.sub_add_cancel he] at hnext
      exact ih (extend_realizes H.odd.pos.ne' h hprime hd) _ hnext

end OddPerfect.FactorBudget
