module

public import OddPerfect.SpoofBelowFive.Part4
public import OddPerfect.SpoofOrdering
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

public section

namespace OddPerfect

/-- Positive odd formally perfect factorizations with bases exceeding one
require at least five slots, even with repeated or composite bases. -/
theorem five_le_positive_odd_spoof_length {X : List (ℕ × ℕ)}
    (hx : ∀ z ∈ X, 1 < z.1 ∧ Odd z.1 ∧ 0 < z.2)
    (hb : listFormalSigma X = 2*listValue X) : 5 ≤ X.length := by
  obtain ⟨Y,hy,hm,hx',hb'⟩ := sorted_spoof_representative X hx hb
  obtain ⟨i,hfits⟩ := SpoofBox.realizing_initial Y.get hx' hb'
  by_contra! hshort
  have h : Y.length < 5 := hy.length_eq ▸ hshort
  have classify (k : ℕ) (hk : k<5) (j : Fin k) :
      SpoofBox.Covered (· ∈ ([] : List (Fin k → ℕ × ℕ))) (SpoofBox.initial j) := by
    interval_cases k
    · exact j.elim0
    · fin_cases j
      exact SpoofBox.covered_1_0
    · fin_cases j
      · exact SpoofBox.covered_2_0
      · exact SpoofBox.covered_2_1
    · fin_cases j
      · exact SpoofBox.covered_3_0
      · exact SpoofBox.covered_3_1
      · exact SpoofBox.covered_3_2
    · fin_cases j
      · exact SpoofBox.covered_4_0
      · exact SpoofBox.covered_4_1
      · exact SpoofBox.covered_4_2
      · exact SpoofBox.covered_4_3
  exact List.not_mem_nil (classify _ h i Y.get hm hfits hb')

/-- The five components in Descartes's historical representation, in base order. -/
@[expose] def descartesFive : List (ℕ × ℕ) := [(3,2),(7,2),(11,2),(13,2),(22021,1)]

/-- With positive exponents and odd bases exceeding one, five is the
smallest possible number of slots of a formally perfect factorization. -/
theorem least_positive_odd_spoof_length :
    IsLeast {k : ℕ | ∃ X : List (ℕ × ℕ), X.length=k ∧
      (∀ z ∈ X, 1 < z.1 ∧ Odd z.1 ∧ 0 < z.2) ∧ listFormalSigma X=2*listValue X} 5 := by
  constructor
  · refine ⟨descartesFive,rfl,?_,by decide +kernel⟩
    intro z hz
    simp [descartesFive] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl <;> decide
  · rintro k ⟨X,rfl,hx,hb⟩
    exact five_le_positive_odd_spoof_length hx hb

end OddPerfect
