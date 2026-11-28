module

public import OddPerfect.ChainPlan
public import OddPerfect.OchemRao
import OddPerfect.Cuts

/-! Sharper terminal contradictions from known coprime residual divisors. -/

public section

namespace OddPerfect.FactorBudget

open ArithmeticFunction

/-- The product of the lower divisor-sum bounds g+1 works for any pairwise
coprime groups g > 1, even incompletely factored ones. -/
theorem group_sigma_lower (gs : List ℕ) (good : checkGroups gs = true) :
    (gs.map (· + 1)).prod ≤ sigma 1 gs.prod := by
  induction gs with
  | nil => simp
  | cons a gs ih =>
    simp only [checkGroups, Bool.and_eq_true, decide_eq_true_eq] at good
    simp only [List.map_cons, List.prod_cons, isMultiplicative_sigma.map_mul_of_coprime good.1.2]
    exact Nat.mul_le_mul (self_lt_sigma_of_one_lt good.1.1) (ih good.2)

/-- Each group contributes a distinct prime to the Ochem–Rao count, and
their product gives a positive divisor to which abundance can be applied. -/
@[expose] def Node.extraGroupCheck (s : Node) (B c : ℕ) (gs : List ℕ) : Bool :=
  checkGroups gs && decide (gs.prod ∣ s.forcedPart ∧
    (7*B+c < 18*(s.closed+gs.length) ∨
      2*s.component*gs.prod < s.divisorSum*(gs.map (· + 1)).prod))

theorem extraGroupCheck_false {N B w c m : ℕ} {s : Node} (H : Conditions N B w)
    (h : Realizes s N m) (hcount : 18*N.primeFactors.card ≤ 7*B+c) (gs : List ℕ)
    (test : s.extraGroupCheck B c gs = true) : False := by
  simp only [Node.extraGroupCheck, Bool.and_eq_true, decide_eq_true_eq] at test
  obtain ⟨good, hd, hc | ha⟩ := test
  · have hg := groups_le_support H.perfect h gs good hd
    have ht : N.primeFactors.card = s.closed + m.primeFactors.card := by
      rw [← cardDistinctFactors_eq_card_primeFactors, h.value, cardDistinctFactors_mul h.coprime,
        h.closed, cardDistinctFactors_eq_card_primeFactors]
    omega
  · have hm := hd.trans (forcedPart_dvd h H.perfect)
    have hcop := h.coprime.coprime_dvd_right hm
    have hab : (s.component*gs.prod).Abundant := by
      rw [Nat.abundant_iff_sum_divisors, ← sigma_one_apply, isMultiplicative_sigma.map_mul_of_coprime hcop,
        h.sigma, ← Nat.mul_assoc]
      exact ha.trans_le (Nat.mul_le_mul_left _ (group_sigma_lower gs good))
    have hv : s.component*gs.prod ∣ N := h.value ▸ Nat.mul_dvd_mul_left _ hm
    exact (Nat.perfect_iff_not_abundant_and_not_deficient H.perfect.2.ne).mp H.perfect |>.1
      (hab.of_dvd hv H.perfect.2.ne')

/-- A richer group cutoff can be added to an existing choice table. -/
@[expose] def prepareTightChoices (primes : List ℕ) (hints : ℕ → Option ChoiceHint)
    (seed avoid B w c : ℕ) (s : Node) : Option (List ℕ) :=
  match hints s.component with
  | some (.basic (.groups gs)) => if s.extraGroupCheck B c gs then some [] else
      prepareChoices primes hints seed avoid B w s
  | _ => prepareChoices primes hints seed avoid B w s

theorem prepareTightChoices_correct {N B w seed avoid c : ℕ} (H : Conditions N B w)
    (hseed : seed ∣ N) (havoid : avoid.Coprime N) (hcount : 18*N.primeFactors.card ≤ 7*B+c)
    (primes : List ℕ) (hp : ∀ p ∈ primes, p.Prime) (hints : ℕ → Option ChoiceHint)
    {s : Node} {m : ℕ} {ps : List ℕ} (h : Realizes s N m)
    (hsteps : prepareTightChoices primes hints seed avoid B w c s = some ps) :
    ∃ p ∈ ps, p.Prime ∧ p ∣ m := by
  unfold prepareTightChoices at hsteps
  split at hsteps
  · rename_i gs hh
    split at hsteps
    · rename_i hgroup
      exact False.elim (extraGroupCheck_false H h hcount gs hgroup)
    · exact prepareChoices_correct H hseed havoid primes hp hints h hsteps
  · exact prepareChoices_correct H hseed havoid primes hp hints h hsteps

theorem exclude_of_tight_choice_certificate {N B w seed avoid c fuel : ℕ} (H : Conditions N B w)
    (hseed : seed ∣ N) (havoid : avoid.Coprime N) (hcount : 18*N.primeFactors.card ≤ 7*B+c)
    (primes : List ℕ) (hp : ∀ p ∈ primes, p.Prime) (hints : ℕ → Option ChoiceHint)
    (test : replayPlan (prepareTightChoices primes hints seed avoid B w c) B w fuel root = true) : False :=
  replayPlan_correct H _ (prepareTightChoices_correct H hseed havoid hcount primes hp hints) fuel
    (root_realizes N) test

end OddPerfect.FactorBudget
