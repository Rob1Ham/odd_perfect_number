module

public import OddPerfect.ChainAbundancy
public import OddPerfect.CountChain

/-! Bounded factor chains with a conditional search for the least new prime. -/

public section

namespace OddPerfect.FactorBudget

/-- A node may be closed, rejected, or continued at a set of candidate primes.
Every successful continuation covers at least one actual unassigned divisor. -/
@[expose] def replayPlan (plan : Node → Option (List ℕ)) (budget minDistinct : ℕ) : ℕ → Node → Bool
  | 0, _ => false
  | n+1, s =>
    if s.automatic budget minDistinct then true else
    match plan s with
    | none => false
    | some ps => ps.all fun p => (List.range (budget-s.spent)).all fun i =>
        replayPlan plan budget minDistinct n (s.extend p (i+1))

theorem replayPlan_correct {N B w : ℕ} (H : Conditions N B w) (plan : Node → Option (List ℕ))
    (hplan : ∀ {s m ps}, Realizes s N m → plan s = some ps → ∃ p ∈ ps, p.Prime ∧ p ∣ m)
    (fuel : ℕ) {s : Node} {m : ℕ} (h : Realizes s N m) (test : replayPlan plan B w fuel s = true) : False := by
  induction fuel generalizing s m with
  | zero => simp [replayPlan] at test
  | succ fuel ih =>
    by_cases ha : s.automatic B w = true
    · exact automatic_false H h ha
    cases hps : plan s with
    | none => simp [replayPlan, ha, hps] at test
    | some ps =>
      simp only [replayPlan, ha, Bool.false_eq_true, ↓reduceIte, hps, List.all_eq_true, List.mem_range] at test
      obtain ⟨p, hp, hprime, hd⟩ := hplan h hps
      obtain ⟨hpos, hub⟩ := exponent_bounds H h hprime hd
      have hnext := test p hp (m.factorization p-1) (by omega)
      rw [Nat.sub_add_cancel hpos] at hnext
      exact ih (extend_realizes H.odd.pos.ne' h hprime hd) hnext

/-- The ordinary forcing and group rules, plus a smallest-prime cutoff. -/
inductive ChoiceHint where
  | basic (hint : Hint)
  | cut (a L g : ℕ)
  deriving Repr

/-- Balanced lookup of the arithmetic hint for a given exact component. -/
inductive ChoiceTree where
  | empty
  | node (component : ℕ) (hint : ChoiceHint) (left right : ChoiceTree)
  deriving Repr

@[expose] def ChoiceTree.lookup (n : ℕ) : ChoiceTree → Option ChoiceHint
  | .empty => none
  | .node k h l r => if n = k then some h else if n < k then l.lookup n else r.lookup n

@[expose] def Node.belowPrimes (s : Node) (avoid a : ℕ) : List ℕ :=
  (List.range a).filter fun p => decide (p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ s.component ∧ ¬ p ∣ avoid)

/-- The optional avoided divisor must be coprime to the full candidate N. -/
@[expose] def prepareChoices (primes : List ℕ) (hints : ℕ → Option ChoiceHint)
    (seed avoid budget minDistinct : ℕ) (s : Node) : Option (List ℕ) :=
  if ¬ (avoid.Coprime s.component ∧ avoid.Coprime s.forcedPart) then some [] else
  match hints s.component with
  | none => none
  | some (.basic (.groups gs)) =>
    if checkGroups gs ∧ gs.prod ∣ s.forcedPart ∧
        budget+1 < s.spent + 2*max gs.length (minDistinct-s.closed) + s.spent%2 then some [] else none
  | some (.basic (.split p)) =>
    if p ∈ primes ∧ (p ∣ s.forcedPart ∨ (p ∣ seed ∧ s.component.Coprime p)) then some [p] else none
  | some (.cut a L g) => if s.validAbundancyCut budget a L g then some (s.belowPrimes avoid a) else none

/-- A conditional cutoff covers every small residual prime. Its branches can
overlap and together include the smallest actual residual prime. -/
theorem prepareChoices_correct {N B w seed avoid : ℕ} (H : Conditions N B w) (hseed : seed ∣ N)
    (havoid : avoid.Coprime N) (primes : List ℕ) (hp : ∀ p ∈ primes, p.Prime)
    (hints : ℕ → Option ChoiceHint) {s : Node} {m : ℕ} {ps : List ℕ} (h : Realizes s N m)
    (test : prepareChoices primes hints seed avoid B w s = some ps) :
    ∃ p ∈ ps, p.Prime ∧ p ∣ m := by
  have hmN : m ∣ N := h.value ▸ Nat.dvd_mul_left _ _
  have hDN : s.component ∣ N := h.value ▸ Nat.dvd_mul_right _ _
  have hav : avoid.Coprime s.component ∧ avoid.Coprime s.forcedPart :=
    ⟨havoid.coprime_dvd_right hDN, havoid.coprime_dvd_right ((forcedPart_dvd h H.perfect).trans hmN)⟩
  cases hh : hints s.component with
  | none => simp [prepareChoices, hav, hh] at test
  | some hint =>
    cases hint with
    | basic hint =>
      cases hint with
      | groups gs =>
        simp only [prepareChoices, ite_eq_right (not_not_intro hav), hh] at test
        split at test
        · rename_i hc
          have := budget_bound H h (groups_le_support H.perfect h gs hc.1 hc.2.1)
          omega
        · contradiction
      | split p =>
        simp only [prepareChoices, ite_eq_right (not_not_intro hav), hh] at test
        split at test
        · rename_i hc
          cases test
          refine ⟨p, by simp, hp p hc.1, ?_⟩
          rcases hc.2 with hpart | ⟨hd, hcop⟩
          · exact hpart.trans (forcedPart_dvd h H.perfect)
          · apply hcop.symm.dvd_of_dvd_mul_left
            rw [← h.value]
            exact hd.trans hseed
        · contradiction
    | cut a L g =>
      simp only [prepareChoices, ite_eq_right (not_not_intro hav), hh] at test
      split at test
      · rename_i hc
        cases test
        obtain ⟨p, hpm, hsmall⟩ := exists_prime_below_abundancy_cut H h hc
        have hp' := Nat.prime_of_mem_primeFactors hpm
        have hdiv := Nat.dvd_of_mem_primeFactors hpm
        have hNdiv := hdiv.trans hmN
        have h2 : p ≠ 2 := fun eq => H.odd.not_two_dvd_nat (eq ▸ hNdiv)
        have hnD : ¬ p ∣ s.component := fun hd => hp'.not_dvd_one (h.coprime.gcd_eq_one ▸ Nat.dvd_gcd hd hdiv)
        have hnf : ¬ p ∣ avoid := fun hd => hp'.not_dvd_one (havoid.gcd_eq_one ▸ Nat.dvd_gcd hd hNdiv)
        exact ⟨p, List.mem_filter.mpr ⟨List.mem_range.mpr hsmall, decide_eq_true ⟨hp', h2, hnD, hnf⟩⟩, hp', hdiv⟩
      · contradiction

/-- Soundness of the complete exact-exponent replay with conditional cutoffs. -/
theorem exclude_of_choice_certificate {N B w seed avoid fuel : ℕ} (H : Conditions N B w)
    (hseed : seed ∣ N) (havoid : avoid.Coprime N) (primes : List ℕ) (hp : ∀ p ∈ primes, p.Prime)
    (hints : ℕ → Option ChoiceHint)
    (test : replayPlan (prepareChoices primes hints seed avoid B w) B w fuel root = true) : False :=
  replayPlan_correct H _ (prepareChoices_correct H hseed havoid primes hp hints) fuel (root_realizes N) test

end OddPerfect.FactorBudget
