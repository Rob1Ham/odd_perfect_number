module

public import OddPerfect.QuasiFactors
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Sort

public section

namespace OddPerfect

/-- Sort any positive odd formally perfect list of slots by base. This
preserves repeated entries, the represented integer and the formal balance. -/
theorem sorted_spoof_representative (X : List (ℕ × ℕ))
    (hx : ∀ z ∈ X, 1 < z.1 ∧ Odd z.1 ∧ 0 < z.2)
    (hb : listFormalSigma X = 2*listValue X) :
    ∃ Y : List (ℕ × ℕ), Y.Perm X ∧ Monotone (fun i : Fin Y.length => (Y.get i).1) ∧
      (∀ i : Fin Y.length, 1 < (Y.get i).1 ∧ Odd (Y.get i).1 ∧ 0 < (Y.get i).2) ∧
      formalSigma Finset.univ (fun i : Fin Y.length => (Y.get i).1) (fun i => (Y.get i).2) =
        2 * ∏ i : Fin Y.length, (Y.get i).1^(Y.get i).2 := by
  let leB := fun z w : ℕ × ℕ => decide (z.1 ≤ w.1)
  let Y := X.mergeSort leB
  have hperm : Y.Perm X := List.mergeSort_perm _ _
  have hpair : List.Pairwise (fun z w : ℕ × ℕ => z.1 ≤ w.1) Y := by
    have ht (a b c : ℕ × ℕ) (h1 : leB a b) (h2 : leB b c) : leB a c := by
      exact decide_eq_true (le_trans (of_decide_eq_true h1) (of_decide_eq_true h2))
    have hc (a b : ℕ × ℕ) : leB a b || leB b a := by
      rcases le_total a.1 b.1 with h|h <;> simp [leB,h]
    simpa [Y,leB] using List.pairwise_mergeSort ht hc X
  have hprod (f : ℕ × ℕ → ℕ) : (∏ i : Fin Y.length, f (Y.get i)) = (X.map f).prod := by
    calc _ = (List.ofFn (f ∘ Y.get)).prod := (Fin.prod_ofFn _).symm
         _ = (Y.map f).prod := by rw [← List.map_ofFn,List.ofFn_get]
         _ = _ := (hperm.map _).prod_eq
  refine ⟨Y,hperm,?_,fun i => hx _ (hperm.mem_iff.mp (List.get_mem Y i)),?_⟩
  · intro i j hij
    rcases lt_or_eq_of_le hij with hlt | rfl
    · exact (List.pairwise_iff_getElem.mp hpair) i.val j.val i.isLt j.isLt hlt
    · rfl
  · rw [formalSigma,hprod (fun z => ∑ j ∈ Finset.range (z.2+1),z.1^j),hprod (fun z => z.1^z.2)]
    exact hb

end OddPerfect
