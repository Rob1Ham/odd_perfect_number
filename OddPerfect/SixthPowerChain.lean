module

public import OddPerfect.FactorBudget
import Mathlib.Tactic.IntervalCases

public section

namespace OddPerfect.SixthPowerChain
open FactorBudget ArithmeticFunction

/-- The hypotheses used in the sixth-power-free special case of Fletcher,
Nielsen and Ochem's factor-chain sieve. The integer k bounds the least prime. -/
structure Hyp (N k : ℕ) : Prop where
  odd : Odd N
  perfect : N.Perfect
  least : k ≤ N.minFac
  free : ∀ p : ℕ, p.Prime → ¬ p^6 ∣ N

@[expose] def Closed (k : ℕ) (s : Node) : Prop := ∀ N m, Hyp N k → Realizes s N m → False

/-- These three tests need no bound on the total number of factors. -/
@[expose] def impossible (s : Node) : Prop :=
  4 ∣ s.divisorSum ∨ 2*s.component < s.divisorSum ∨ ¬s.component.Coprime s.forcedPart

instance (s : Node) : Decidable (impossible s) := inferInstanceAs (Decidable (_ ∨ _ ∨ _))

theorem closed_impossible {k : ℕ} {s : Node} (test : impossible s) : Closed k s := by
  intro N m H h
  apply automatic_false (B:=cardFactors N) (w:=0) ⟨H.odd,H.perfect,le_rfl,Nat.zero_le _⟩ h
  apply decide_eq_true
  rcases test with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))

theorem closed_smaller {k q : ℕ} {s : Node} (h2 : 2≤q) (hq : q<k)
    (hd : q∣s.forcedPart) : Closed k s := by
  intro N m H h
  have hn := (hd.trans (forcedPart_dvd h H.perfect)).trans (h.value ▸ dvd_mul_left m s.component)
  exact hq.not_ge (H.least.trans (Nat.minFac_le_of_dvd h2 hn))

theorem closed_sixth {k q : ℕ} {s : Node} (hq : q.Prime)
    (hd : q^6∣s.forcedPart) : Closed k s := by
  intro N m H h
  exact H.free q hq ((hd.trans (forcedPart_dvd h H.perfect)).trans (h.value ▸ dvd_mul_left m s.component))

/-- Each chosen prime has one of exactly five positive exponents under
the sixth-power-free hypothesis. -/
theorem split {N m p k : ℕ} {s : Node} (H : Hyp N k) (h : Realizes s N m)
    (hp : p.Prime) (hd : p∣m) (children : ∀ e : Fin 5, Closed k (s.extend p (e.val+1))) : False := by
  let e := m.factorization p
  have hm := (mul_ne_zero_iff.mp (h.value ▸ H.odd.pos.ne')).2
  have he : 0 < e := hp.factorization_pos_of_dvd hm hd
  have hb : e<6 := by
    by_contra! hbad
    exact H.free p hp (((hp.pow_dvd_iff_le_factorization hm).mpr hbad).trans (h.value ▸ dvd_mul_left m _))
  obtain hchild := extend_realizes H.odd.pos.ne' h hp hd
  have h := children ⟨e-1,by omega⟩
  dsimp only at h
  rw [Nat.sub_add_cancel he] at h
  exact h N _ H hchild

theorem closed_split {k p : ℕ} {s : Node} (hp : p.Prime) (hd : p∣s.forcedPart)
    (children : ∀ e : Fin 5, Closed k (s.extend p (e.val+1))) : Closed k s := by
  intro N m H h
  exact split H h hp (hd.trans (forcedPart_dvd h H.perfect)) children

theorem root_split {N p : ℕ} (H : Hyp N p) (hp : p.Prime) (hd : p∣N)
    (children : ∀ e : Fin 5, Closed p (root.extend p (e.val+1))) : False :=
  split H (root_realizes N) hp hd children

end OddPerfect.SixthPowerChain
