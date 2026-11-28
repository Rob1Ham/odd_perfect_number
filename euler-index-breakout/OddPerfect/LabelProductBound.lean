module

public import OddPerfect.ProductGap
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Ring

public section

namespace OddPerfect
open Finset

/-- A bound on the product of all labels in a balance of adjacent integers.
At each step all newly admitted labels are at most twice the number of labels
times the product already admitted. The exponent doubles per label, including
when more than one label enters at the same cutoff. -/
theorem product_bound_above_prefix {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (label a b : ι → ℕ) {k : ℕ} (hk : s.card≤k) (hkpos : 0<k)
    (hfull : s.prod a=2*s.prod b)
    (hp : ∀ i ∈ s, 1<label i ∧
      (a i=label i ∧ b i=label i-1 ∨ a i=label i-1 ∧ b i=label i))
    (gap : ∀ t : ℕ, (∃ i ∈ s, t<label i) →
      (s.filter (fun i => label i≤t)).prod a ≠ 2*(s.filter (fun i => label i≤t)).prod b) :
    ∀ t : ℕ, (2*k)*s.prod label ≤
      ((2*k)*(s.filter (fun i => label i≤t)).prod label)^(2^(s.filter (fun i => t<label i)).card) := by
  let C := 2*k
  have cpos : 0<C := by dsimp [C]; omega
  let left (t : ℕ) := s.filter (fun i => label i≤t)
  let rest (t : ℕ) := s.filter (fun i => t<label i)
  have split (t : ℕ) (f : ι→ℕ) : (left t).prod f*(rest t).prod f=s.prod f := by
    simpa only [left,rest,not_le] using s.prod_filter_mul_prod_filter_not (fun i => label i≤t) f
  have card_parts (t : ℕ) : (left t).card+(rest t).card=s.card := by
    simpa only [left,rest,not_le] using s.card_filter_add_card_filter_not (fun i => label i≤t)
  have main (n t : ℕ) (hn : (rest t).card=n) :
      C*s.prod label≤(C*(left t).prod label)^(2^n) := by
    induction n using Nat.strong_induction_on generalizing t with
    | ind n ih =>
      by_cases hem : (rest t).Nonempty
      · obtain ⟨j,hj⟩ := hem
        have ne := gap t ⟨j,(mem_filter.mp hj).1,(mem_filter.mp hj).2⟩
        have eq : (left t).prod a*(rest t).prod a=(2*(left t).prod b)*(rest t).prod b := by
          rw [split,mul_assoc,split,hfull]
        obtain ⟨i,hi,hsmall⟩ := exists_small_label_of_balance (rest t) label a b ne eq
          (fun i hi => hp i (mem_filter.mp hi).1)
        have htt := (mem_filter.mp hi).2
        let t' := label i
        let P := (left t).prod label
        have hab (f : ι→ℕ) (hf : ∀ j ∈ s, f j≤label j) : (left t).prod f≤P :=
          Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _)
            (fun j hj => hf j (mem_filter.mp hj).1)
        have ha := hab a (fun j hj => by rcases hp j hj with ⟨_,h|h⟩ <;> omega)
        have hb := hab b (fun j hj => by rcases hp j hj with ⟨_,h|h⟩ <;> omega)
        have hm : max ((left t).prod a) (2*(left t).prod b)≤2*P := max_le (by omega) (by omega)
        have hcard : (rest t).card≤k := (card_le_card (filter_subset _ _)).trans hk
        have hcap : t'≤C*P := hsmall.trans ((Nat.mul_le_mul hcard hm).trans_eq (by dsimp [C]; ring))
        have sub : left t ⊆ left t' := fun j hj => mem_filter.mpr
          ⟨(mem_filter.mp hj).1,(mem_filter.mp hj).2.trans htt.le⟩
        let G := left t' \ left t
        have hprod : G.prod label*P=(left t').prod label := prod_sdiff sub
        have hcards : G.card+(left t).card=(left t').card := card_sdiff_add_card_eq_card sub
        have hadded : G.prod label≤(C*P)^G.card := by
          simpa only [prod_const] using Finset.prod_le_prod₀ (s:=G) (g:=fun _ => C*P)
            (fun j _ => Nat.zero_le (label j))
            (fun j hj => ((mem_filter.mp (mem_sdiff.mp hj).1).2.trans hcap))
        have ppos : 0<P := prod_pos (fun j hj => zero_lt_one.trans (hp j (mem_filter.mp hj).1).1)
        have doubled : G.card+1≤2^G.card := Nat.lt_two_pow_self
        have hI' : C*(left t').prod label ≤ (C*P)^(2^G.card) := by
          calc C*(left t').prod label = (C*P)*G.prod label := by rw [←hprod]; ring
               _ ≤ (C*P)*(C*P)^G.card := Nat.mul_le_mul_left _ hadded
               _ = (C*P)^(G.card+1) := by rw [pow_succ,mul_comm]
               _ ≤ (C*P)^(2^G.card) := Nat.pow_le_pow_right (Nat.mul_pos cpos ppos) doubled
        have hsub : rest t' ⊆ rest t := fun j hj => mem_filter.mpr
          ⟨(mem_filter.mp hj).1,htt.trans (mem_filter.mp hj).2⟩
        have hdec := card_lt_card ((ssubset_iff_of_subset hsub).mpr
          ⟨i,hi,fun hij => (lt_irrefl (label i)) (mem_filter.mp hij).2⟩)
        have hcount : G.card+(rest t').card=n := by
          have c1 := card_parts t
          have c2 := card_parts t'
          omega
        calc C*s.prod label ≤ (C*(left t').prod label)^(2^(rest t').card) := ih _ (hn ▸ hdec) t' rfl
             _ ≤ ((C*P)^(2^G.card))^(2^(rest t').card) := Nat.pow_le_pow_left hI' _
             _ = (C*P)^(2^n) := by rw [←pow_mul,←pow_add,hcount]
      · have all : left t=s := by
          apply filter_eq_self.mpr
          intro i hi
          exact le_of_not_gt (fun hg => hem ⟨i,mem_filter.mpr ⟨hi,hg⟩⟩)
        have rempty : rest t=∅ := not_nonempty_iff_eq_empty.mp hem
        have nz : n=0 := by simpa only [rempty,card_empty] using hn.symm
        simp [all,nz]
  exact fun t => main _ t rfl

/-- Starting with the empty numerical prefix gives a bound in the
cardinality alone. -/
theorem product_bound_of_no_balanced_prefix {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (label a b : ι → ℕ) {k : ℕ} (hk : s.card≤k) (hkpos : 0<k)
    (hfull : s.prod a=2*s.prod b)
    (hp : ∀ i ∈ s, 1<label i ∧
      (a i=label i ∧ b i=label i-1 ∨ a i=label i-1 ∧ b i=label i))
    (gap : ∀ t : ℕ, (∃ i ∈ s, t<label i) →
      (s.filter (fun i => label i≤t)).prod a ≠ 2*(s.filter (fun i => label i≤t)).prod b) :
    (2*k)*s.prod label ≤ (2*k)^(2^s.card) := by
  have empty : s.filter (fun i => label i≤0)=∅ :=
    filter_eq_empty_iff.mpr (fun i hi => by have := (hp i hi).1; omega)
  have rest : s.filter (fun i => 0<label i)=s :=
    filter_eq_self.mpr (fun i hi => zero_lt_one.trans (hp i hi).1)
  simpa only [empty,prod_empty,mul_one,rest] using
    product_bound_above_prefix s label a b hk hkpos hfull hp gap 0

end OddPerfect
