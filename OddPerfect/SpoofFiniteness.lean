module

public import OddPerfect.SpoofFactors
public import OddPerfect.PartialAbundancy
public import OddPerfect.ProductGap
import Mathlib.Data.Fintype.Pi
import Mathlib.Basic.Finite.Prod

public section

namespace OddPerfect

open Finset

private def closingLabel {ι : Type*} (b e : ι → ℕ) (i : ι) := b i ^ (e i + 1)

private theorem base_le_label {ι : Type*} (b e : ι → ℕ) (i : ι) (hb : 1 < b i) :
    b i ≤ closingLabel b e i := by
  rw [closingLabel, pow_succ]
  exact Nat.le_mul_of_pos_left _ (pow_pos hb.le _)

private theorem geom_gt_last (b : ℕ) {e : ℕ} (he : 0 < e) :
    b ^ e < ∑ j ∈ range (e + 1), b ^ j := by
  rw [sum_range_succ]
  have hle := single_le_sum (f := fun j => b ^ j) (fun j _ => Nat.zero_le _) (mem_range.mpr he)
  simp only [pow_zero] at hle
  omega

/-- Cancel the common factors in the two-factor representation of abundancy.
Here l contains the prime bases already encountered, and c the components
whose closing factor has also been encountered. -/
private theorem prefix_balance_iff {ι : Type*} [DecidableEq ι] (b e : ι → ℕ) (l c : Finset ι)
    (hcl : c ⊆ l) (hc : ∀ i ∈ c, 1 < b i) :
    (l.prod b) * (∏ p ∈ c, (closingLabel b e p - 1)) =
      2 * ((∏ p ∈ l, (b p - 1)) * ∏ p ∈ c, closingLabel b e p) ↔
    (∏ p ∈ c, (∑ j ∈ range (e p + 1), b p ^ j)) * ((l \ c).prod b) =
      2 * (∏ p ∈ c, b p ^ e p) * ∏ p ∈ l \ c, (b p - 1) := by
  let f := fun p => b p ^ e p
  let g := fun p => ∑ j ∈ range (e p + 1), b p ^ j
  let pred := fun p => b p - 1
  let o := l \ c
  have hg : (∏ p ∈ c, (closingLabel b e p - 1)) = c.prod g * c.prod pred := by
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro p hp
    have hb := hc p hp
    have h := geom_sum_mul_add (b p - 1) (e p + 1)
    rw [Nat.sub_add_cancel hb.le] at h
    change b p ^ (e p + 1) - 1 = (∑ j ∈ range (e p + 1), b p ^ j) * (b p - 1)
    omega
  have hf : c.prod (closingLabel b e) = c.prod f * c.prod b := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl (fun p _ => pow_succ (b p) (e p))
  let common := c.prod b * c.prod pred
  have hpos : 0 < common := mul_pos
    (prod_pos fun p hp => (hc p hp).le)
    (prod_pos fun p hp => Nat.sub_pos_of_lt (hc p hp))
  change l.prod b * _ = 2 * (l.prod pred * _) ↔ c.prod g * o.prod b = 2 * c.prod f * o.prod pred
  rw [hg, hf, ← prod_sdiff (f := b) hcl, ← prod_sdiff (f := pred) hcl]
  have ha : o.prod b * c.prod b * (c.prod g * c.prod pred) = (c.prod g * o.prod b) * common := by
    dsimp [common]; ring
  have hb : 2 * (o.prod pred * c.prod pred * (c.prod f * c.prod b)) =
      (2 * c.prod f * o.prod pred) * common := by dsimp [common]; ring
  rw [ha, hb]
  exact Nat.mul_left_inj hpos.ne'

/-- Every positive odd spoof with at most k indexed bases has uniformly
bounded closing labels. Distinctness and coprimality of the bases are unnecessary. -/
theorem formal_component_le_of_bounded_factor_count {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (base exp : ι → ℕ) {k : ℕ} (hk : P.card ≤ k)
    (hb : ∀ i ∈ P, 1 < base i ∧ Odd (base i)) (he : ∀ i ∈ P, 0 < exp i)
    (hbalance : formalSigma P base exp = 2 * ∏ i ∈ P, base i ^ exp i) :
    ∀ i ∈ P, base i ^ (exp i + 1) ≤ productLabelBound (2*k) (2*k) 1 := by
  let s := P.disjSum P
  let label : ι ⊕ ι → ℕ := Sum.elim base (closingLabel base exp)
  let a : ι ⊕ ι → ℕ := Sum.elim base (fun p => closingLabel base exp p - 1)
  let b : ι ⊕ ι → ℕ := Sum.elim (fun p => base p - 1) (closingLabel base exp)
  have hcard : s.card ≤ 2*k := by dsimp [s]; rw [card_disjSum]; omega
  have hfull : s.prod a = 2 * s.prod b := by
    simp only [s, a, b, prod_disjSum, Sum.elim_inl, Sum.elim_inr]
    apply (prefix_balance_iff base exp P P (by rfl) (fun i hi => (hb i hi).1)).mpr
    simp only [sdiff_self, Finset.bot_eq_empty, prod_empty, mul_one]
    exact hbalance
  have hpairs (i : ι ⊕ ι) (hi : i ∈ s) : 1 < label i ∧
      (a i = label i ∧ b i = label i - 1 ∨ a i = label i - 1 ∧ b i = label i) := by
    cases i with
    | inl p => exact ⟨(hb p (inl_mem_disjSum.mp hi)).1, Or.inl ⟨rfl,rfl⟩⟩
    | inr p =>
      have hpm := inr_mem_disjSum.mp hi
      exact ⟨(hb p hpm).1.trans_le (base_le_label base exp p (hb p hpm).1), Or.inr ⟨rfl,rfl⟩⟩
  have gap (t : ℕ) (hstill : ∃ i ∈ s, t < label i) :
      (s.filter (fun i => label i ≤ t)).prod a ≠ 2 * (s.filter (fun i => label i ≤ t)).prod b := by
    let l := P.filter (fun p => base p ≤ t)
    let c := P.filter (fun p => closingLabel base exp p ≤ t)
    have hcl : c ⊆ l := by
      intro p hp
      exact mem_filter.mpr ⟨(mem_filter.mp hp).1, (base_le_label base exp p (hb p (mem_filter.mp hp).1).1).trans (mem_filter.mp hp).2⟩
    have hsub : c ⊆ P := filter_subset _ _
    have hc : c ⊂ P := by
      apply (ssubset_iff_of_subset hsub).mpr
      obtain ⟨i, hi, hgt⟩ := hstill
      cases i with
      | inl p =>
        have hp := inl_mem_disjSum.mp hi
        exact ⟨p, hp, fun hm => hgt.not_ge ((base_le_label base exp p (hb p hp).1).trans (mem_filter.mp hm).2)⟩
      | inr p => exact ⟨p, inr_mem_disjSum.mp hi, fun hm => hgt.not_ge (mem_filter.mp hm).2⟩
    have hfilter : s.filter (fun i => label i ≤ t) = l.disjSum c := by
      ext i
      cases i <;> simp [s, l, c, label]
    rw [hfilter]
    simp only [a, b, prod_disjSum, Sum.elim_inl, Sum.elim_inr]
    have hne := partial_product_ne_two P c (l \ c) base (fun p => base p ^ exp p)
      (fun p => ∑ j ∈ range (exp p + 1), base p ^ j) hc (sdiff_subset.trans (filter_subset _ _))
      (prod_induction _ Odd (fun _ _ => Odd.mul) odd_one (fun p hp => (hb p hp).2.pow))
      (fun p hp => (hb p hp).2) (fun p hp => ⟨pow_pos (hb p hp).1.le _, geom_gt_last (base p) (he p hp)⟩)
      hbalance
    exact fun h => hne ((prefix_balance_iff base exp l c hcl (fun p hp => (hb p (hsub hp)).1)).mp h)
  have h := labels_bounded_of_no_balanced_prefix s label a b hcard hfull hpairs gap
  intro p hp
  exact h (.inr p) (inr_mem_disjSum.mpr hp)

/-- For fixed k there are only finitely many ordered k-term positive odd
spoof-perfect factorizations. Indexing also permits identical pairs. -/
theorem finite_positive_odd_spoof_factorizations (k : ℕ) :
    Set.Finite {x : Fin k → ℕ × ℕ |
      (∀ i, 1 < (x i).1 ∧ Odd (x i).1 ∧ 0 < (x i).2) ∧
      formalSigma univ (fun i => (x i).1) (fun i => (x i).2) = 2 * ∏ i, (x i).1 ^ (x i).2} := by
  let B := productLabelBound (2*k) (2*k) 1
  let possible := {v : ℕ | v ≤ B}
  have hfin := Set.finite_le_nat B
  apply (Set.Finite.pi' (t := fun _ : Fin k => possible ×ˢ possible)
    (fun _ => hfin.prod hfin)).subset
  rintro x ⟨hb, hbal⟩ i
  have h := formal_component_le_of_bounded_factor_count univ (fun i => (x i).1) (fun i => (x i).2)
    (k := k) (by simp) (fun i _ => ⟨(hb i).1, (hb i).2.1⟩) (fun i _ => (hb i).2.2) hbal i (mem_univ _)
  constructor
  · exact (base_le_label (fun i => (x i).1) (fun i => (x i).2) i (hb i).1).trans h
  · exact (Nat.le_succ _).trans ((Nat.lt_pow_self (hb i).1).le.trans h)

/-- In the convention allowing the base one, the only positive balanced
factorization containing it consists of the single entry one to the first power. -/
theorem singleton_of_formal_balance_with_one {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (b e : ι → ℕ) (hb : ∀ j ∈ s, 0 < b j) (he : ∀ j ∈ s, 0 < e j)
    (hbal : formalSigma s b e = 2 * ∏ j ∈ s, b j ^ e j)
    {i : ι} (hi : i ∈ s) (hi1 : b i = 1) : s = {i} ∧ e i = 1 := by
  let f := fun j => b j ^ e j
  let g := fun j => ∑ n ∈ range (e j + 1), b j ^ n
  have hf : f i = 1 := by simp [f, hi1]
  have hg : g i = e i + 1 := by simp [g, hi1]
  change s.prod g = 2 * s.prod f at hbal
  rw [← mul_prod_erase s g hi, ← mul_prod_erase s f hi, hf, hg, one_mul] at hbal
  change (e i + 1) * (s.erase i).prod g = 2 * (s.erase i).prod f at hbal
  have hsize : 2 ≤ e i + 1 := by have := he i hi; omega
  have herase : s.erase i = ∅ := by
    by_contra hne
    have hlt : (s.erase i).prod f < (s.erase i).prod g := prod_lt_prod_of_nonempty₀
      (fun j hj => pow_pos (hb j (mem_of_mem_erase hj)) _)
      (fun j hj => geom_gt_last (b j) (he j (mem_of_mem_erase hj)))
      (Finset.nonempty_iff_ne_empty.mpr hne)
    have hle := Nat.mul_le_mul_right ((s.erase i).prod g) hsize
    exact (Nat.mul_lt_mul_of_pos_left hlt (by decide : 0 < 2)).not_ge (hle.trans_eq hbal)
  simp only [herase, prod_empty, mul_one] at hbal
  exact ⟨by simpa [herase] using (insert_erase hi).symm, by omega⟩

/-- BYU Computational Number Theory Group, Corollary 4.3, including the
exceptional factorization with base one and permitting repeated bases. -/
theorem finite_odd_spoofs_allowing_one (k : ℕ) :
    Set.Finite {x : Fin k → ℕ × ℕ |
      (∀ i, Odd (x i).1 ∧ 0 < (x i).2) ∧
      formalSigma univ (fun i => (x i).1) (fun i => (x i).2) = 2 * ∏ i, (x i).1 ^ (x i).2} := by
  apply ((finite_positive_odd_spoof_factorizations k).union
    (Set.finite_singleton (fun _ : Fin k => ((1,1) : ℕ × ℕ)))).subset
  rintro x ⟨hb, hbal⟩
  by_cases h : ∃ i, (x i).1 = 1
  · obtain ⟨i, hi⟩ := h
    obtain ⟨hs, he⟩ := singleton_of_formal_balance_with_one univ (fun i => (x i).1)
      (fun i => (x i).2) (fun j _ => (hb j).1.pos) (fun j _ => (hb j).2)
      hbal (mem_univ i) hi
    right
    apply Set.mem_singleton_iff.mpr
    funext j
    have hj : j ∈ ({i} : Finset (Fin k)) := hs ▸ mem_univ j
    have := mem_singleton.mp hj
    subst j
    exact Prod.ext hi he
  · left
    refine ⟨fun i => ⟨?_, hb i⟩, hbal⟩
    have := (hb i).1.pos
    have hn : (x i).1 ≠ 1 := fun heq => h ⟨i, heq⟩
    omega

end OddPerfect
