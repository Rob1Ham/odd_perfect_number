module

public import OddPerfect.HarmonicResidual
public import OddPerfect.PrimeBank

public section

namespace OddPerfect.HarmonicChain
open FactorBudget

/-- Proposed nodes for the smooth divisor-count branch. The absent entry
of a child table requests all the ordinary arithmetic terminal checks. -/
inductive Tree where
  | done
  | raise (pairs : List (ℕ × ℕ))
  | component (p e : ℕ) (pairs : List (ℕ × ℕ))
  | split (p : ℕ) (byExponent : List (ℕ × Tree))
  | three (absent : Tree) (byExponent : List (ℕ × Tree))
  | owed (r b L : ℕ) (byBase : List (ℕ × List (ℕ × Tree)))

@[expose] def stripped (s : Node) : ℕ := s.divisorSum / s.divisorSum.gcd (6^128)

private theorem stripped_dvd (s : Node) : stripped s ∣ s.divisorSum :=
  Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)

@[expose] def autoTest (s : Node) : Bool :=
  decide (10^24 < s.component.lcm (stripped s) ∨
    ¬ s.component.Coprime (stripped s / (stripped s).gcd s.component))

theorem auto_closed {s : Node} (hc : (stripped s).Coprime 6) (test : autoTest s) :
    Closed 3 s := by
  rcases of_decide_eq_true test with large|short
  · exact closed_size [] (stripped_dvd s) hc (by simp) large
  · intro n m H h
    have hd := (Nat.dvd_lcm_right _ _).trans (forced_dvd H h (stripped_dvd s) hc)
    rw [h.value] at hd
    have hz : 0 < stripped s := Nat.pos_of_ne_zero (by
      intro eq
      rw [eq,zero_dvd_iff,←h.value] at hd
      exact H.odd.pos.ne' hd)
    have g := Nat.dvd_gcd (Nat.dvd_mul_right (stripped s) m) hd
    rw [Nat.gcd_mul_right] at g
    exact short (h.coprime.coprime_dvd_right ((Nat.div_dvd_iff_dvd_mul
      (Nat.gcd_dvd_left _ _) (Nat.gcd_pos_of_pos_left _ hz)).2 g))

instance (p e : ℕ) : Decidable (Allowed p e) :=
  inferInstanceAs (Decidable (0<e ∧ p^e<10^15 ∧ p^e%4=1))

@[expose] def allExps (p r : ℕ) (test : ℕ → Bool) : Bool :=
  goodLengths.all fun e => if Allowed p e ∧ r∣e+1 then test e else true

theorem allExps_sound {p r e : ℕ} {test : ℕ→Bool} (h : allExps p r test)
    (ha : Allowed p e) (hg : e∈goodLengths) (hd : r∣e+1) : test e := by
  have he := List.all_eq_true.mp h e hg
  simpa [ha,hd] using he

@[expose] def run (bank : PrimeBank) : ℕ → Node → ℕ → Bool → Tree → Bool
  | 0, _, _, _, _ => false
  | fuel+1, s, T, ban, tree =>
    let c := stripped s
    if ¬c.Coprime 6 then false else if autoTest s then true else
    match tree with
    | .done => false
    | .raise zs => (zs.all fun z => bank.contains z.1) && decide (10^24 < raised (s.component.lcm c) zs)
    | .component p e zs => (zs.all fun z => bank.contains z.1) && bank.contains p &&
        decide (0<e ∧ p^e ∣ raised (s.component.lcm c) zs ∧ 10^15 ≤ p^e)
    | .split p cs => bank.contains p && decide (p∣c ∧ ¬p∣s.component) &&
        allExps p 1 (fun e => run bank fuel (s.extend p e) (T*(e+1)) ban ((cs.lookup e).getD .done))
    | .three a cs => !ban && run bank fuel s T true a &&
        allExps 3 1 (fun e => run bank fuel (s.extend 3 e) (T*(e+1)) false ((cs.lookup e).getD .done))
    | .owed r b L cs =>
        bank.contains r && decide (r^b ∣ s.divisorSum / s.divisorSum.gcd (s.component*T) ∧
          (r=2 ∨ r∣s.component ∨ (r=3 ∧ ban=true)) ∧ 0<L ∧ 10^24<s.component*L^((r-1)*b)) &&
        (List.range L).all fun p =>
          if p.Prime ∧ 3≤p ∧ ¬p∣s.component ∧ (ban=true → p≠3) then
            allExps p r (fun e => run bank fuel (s.extend p e) (T*(e+1)) ban
              ((((cs.lookup p).getD []).lookup e).getD .done))
          else true

theorem run_sound (bank : PrimeBank) (hp : bank.Certified) (fuel : ℕ)
    {s : Node} {T : ℕ} {ban : Bool} (tree : Tree) (test : run bank fuel s T ban tree) :
    Refined s T ban := by
  induction fuel generalizing s T ban tree with
  | zero => simp [run] at test
  | succ fuel ih =>
    by_cases hc : (stripped s).Coprime 6
    · by_cases hauto : autoTest s
      · exact refine_closed (auto_closed hc hauto)
      · cases tree with
        | done => simp [run,hc,hauto] at test
        | raise zs =>
          simp only [run,ite_eq_right (not_not_intro hc),ite_eq_right hauto,Bool.and_eq_true,
            List.all_eq_true,decide_eq_true_eq] at test
          exact refine_closed (closed_size zs (stripped_dvd s) hc
            (fun z hm => bank.prime_of_contains hp (test.1 z hm)) test.2)
        | component p e zs =>
          simp only [run,ite_eq_right (not_not_intro hc),ite_eq_right hauto,Bool.and_eq_true,
            List.all_eq_true,decide_eq_true_eq] at test
          exact refine_closed (closed_component zs (stripped_dvd s) hc
            (fun z hm => bank.prime_of_contains hp (test.1.1 z hm)) (bank.prime_of_contains hp test.1.2)
            test.2.1 test.2.2.1 test.2.2.2)
        | split p cs =>
          simp only [run,ite_eq_right (not_not_intro hc),ite_eq_right hauto,Bool.and_eq_true,
            decide_eq_true_eq] at test
          apply refined_forced (bank.prime_of_contains hp test.1.1) (stripped_dvd s) hc
            test.1.2.1 test.1.2.2
          exact fun e ha hg => ih _ (allExps_sound test.2 ha hg (one_dvd _))
        | three a cs =>
          cases ban
          · simp only [run,ite_eq_right (not_not_intro hc),ite_eq_right hauto,Bool.not_false,Bool.true_and,
              Bool.and_eq_true] at test
            apply refined_three_cases (ih _ test.1)
            exact fun e ha hg => ih _ (allExps_sound test.2 ha hg (one_dvd _))
          · simp [run,hc,hauto] at test
        | owed r b L cs =>
          simp only [run,ite_eq_right (not_not_intro hc),ite_eq_right hauto,Bool.and_eq_true,
            decide_eq_true_eq,List.all_eq_true,List.mem_range] at test
          apply refined_owed (bank.prime_of_contains hp test.1.1) test.1.2.1
            test.1.2.2.1 test.1.2.2.2.1 test.1.2.2.2.2
          intro p hpr h3 hlt hnew hban e ha hg hd
          have h := test.2 p hlt
          rw [ite_eq_left (And.intro hpr ⟨h3,hnew,hban⟩)] at h
          exact ih _ (allExps_sound h ha hg hd)
    · simp [run,hc] at test

end OddPerfect.HarmonicChain
