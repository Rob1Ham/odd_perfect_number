module

public import OddPerfect.PartialAbundancy
public import OddPerfect.ProductGap

public section

namespace OddPerfect

open Finset ArithmeticFunction

private def componentLabel (N p : ℕ) := p ^ (N.factorization p + 1)

private theorem base_le_label {N p : ℕ} (hp : p ∈ N.primeFactors) : p ≤ componentLabel N p := by
  rw [componentLabel, pow_succ]
  exact Nat.le_mul_of_pos_left _ (pow_pos (Nat.prime_of_mem_primeFactors hp).pos _)

/-- Cancel the common factors in the two-factor representation of abundancy.
Here l contains the prime bases already encountered, and c the components
whose closing factor has also been encountered. -/
private theorem prefix_balance_iff {N : ℕ} (l c : Finset ℕ) (hcl : c ⊆ l)
    (hc : c ⊆ N.primeFactors) :
    (∏ p ∈ l, p) * (∏ p ∈ c, (componentLabel N p - 1)) =
      2 * ((∏ p ∈ l, (p - 1)) * ∏ p ∈ c, componentLabel N p) ↔
    (∏ p ∈ c, sigma 1 (p ^ N.factorization p)) * (∏ p ∈ l \ c, p) =
      2 * (∏ p ∈ c, p ^ N.factorization p) * ∏ p ∈ l \ c, (p - 1) := by
  let f := fun p => p ^ N.factorization p
  let g := fun p => sigma 1 (f p)
  let pred := fun p : ℕ => p - 1
  let o := l \ c
  have hg : (∏ p ∈ c, (componentLabel N p - 1)) = c.prod g * c.prod pred := by
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors (hc hp)
    have h := geom_sum_mul_add (p - 1) (N.factorization p + 1)
    rw [Nat.sub_add_cancel hprime.one_lt.le, ← sigma_one_apply_prime_pow hprime] at h
    change p ^ (N.factorization p + 1) - 1 = sigma 1 (p ^ N.factorization p) * (p - 1)
    omega
  have hf : c.prod (componentLabel N) = c.prod f * c.prod id := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl (fun p _ => pow_succ p (N.factorization p))
  let common := c.prod id * c.prod pred
  have hpos : 0 < common := mul_pos
    (prod_pos fun p hp => (Nat.prime_of_mem_primeFactors (hc hp)).pos)
    (prod_pos fun p hp => Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors (hc hp)).one_lt)
  change l.prod id * _ = 2 * (l.prod pred * _) ↔ c.prod g * o.prod id = 2 * c.prod f * o.prod pred
  rw [hg, hf, ← prod_sdiff (f := id) hcl, ← prod_sdiff (f := pred) hcl]
  have ha : o.prod id * c.prod id * (c.prod g * c.prod pred) = (c.prod g * o.prod id) * common := by
    dsimp [common]; ring
  have hb : 2 * (o.prod pred * c.prod pred * (c.prod f * c.prod id)) =
      (2 * c.prod f * o.prod pred) * common := by dsimp [common]; ring
  rw [ha, hb]
  exact Nat.mul_left_inj hpos.ne'

/-- A uniform (coarse) bound on all prime powers when their number is
bounded. Each prime contributes two adjacent-factor ratios to sigma(N)/N. -/
theorem component_le_of_bounded_prime_count {N k : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hk : N.primeFactors.card ≤ k) :
    ∀ p ∈ N.primeFactors, p ^ (N.factorization p + 1) ≤ productLabelBound (2*k) (2*k) 1 := by
  let P := N.primeFactors
  let s := P.disjSum P
  let label : ℕ ⊕ ℕ → ℕ := Sum.elim id (componentLabel N)
  let a : ℕ ⊕ ℕ → ℕ := Sum.elim id (fun p => componentLabel N p - 1)
  let b : ℕ ⊕ ℕ → ℕ := Sum.elim (fun p => p - 1) (componentLabel N)
  have hcard : s.card ≤ 2*k := by dsimp [s, P]; rw [card_disjSum]; omega
  have hfull : s.prod a = 2 * s.prod b := by
    simp only [s, a, b, prod_disjSum, Sum.elim_inl, Sum.elim_inr, id_eq]
    apply (prefix_balance_iff P P (by rfl) (by rfl)).mpr
    simp only [sdiff_self, Finset.bot_eq_empty, prod_empty, mul_one]
    rw [show (∏ p ∈ P, sigma 1 (p ^ N.factorization p)) = sigma 1 N from
      (isMultiplicative_sigma.multiplicative_factorization _ hN.2.ne').symm,
      ← Nat.prod_primeFactors_pow_factorization hN.2.ne', sigma_one_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN
  have hpairs (i : ℕ ⊕ ℕ) (hi : i ∈ s) : 1 < label i ∧
      (a i = label i ∧ b i = label i - 1 ∨ a i = label i - 1 ∧ b i = label i) := by
    cases i with
    | inl p => exact ⟨(Nat.prime_of_mem_primeFactors (inl_mem_disjSum.mp hi)).one_lt, Or.inl ⟨rfl,rfl⟩⟩
    | inr p =>
      have hpm := inr_mem_disjSum.mp hi
      exact ⟨(Nat.prime_of_mem_primeFactors hpm).one_lt.trans_le (base_le_label hpm), Or.inr ⟨rfl,rfl⟩⟩
  have gap (t : ℕ) (hstill : ∃ i ∈ s, t < label i) :
      (s.filter (fun i => label i ≤ t)).prod a ≠ 2 * (s.filter (fun i => label i ≤ t)).prod b := by
    let l := P.filter (fun p => p ≤ t)
    let c := P.filter (fun p => componentLabel N p ≤ t)
    have hcl : c ⊆ l := by
      intro p hp
      exact mem_filter.mpr ⟨(mem_filter.mp hp).1, (base_le_label (mem_filter.mp hp).1).trans (mem_filter.mp hp).2⟩
    have hsub : c ⊆ P := filter_subset _ _
    have hc : c ⊂ P := by
      apply (ssubset_iff_of_subset hsub).mpr
      obtain ⟨i, hi, hgt⟩ := hstill
      cases i with
      | inl p =>
        have hp := inl_mem_disjSum.mp hi
        exact ⟨p, hp, fun hm => hgt.not_ge ((base_le_label hp).trans (mem_filter.mp hm).2)⟩
      | inr p => exact ⟨p, inr_mem_disjSum.mp hi, fun hm => hgt.not_ge (mem_filter.mp hm).2⟩
    have hfilter : s.filter (fun i => label i ≤ t) = l.disjSum c := by
      ext i
      cases i <;> simp [s, l, c, label]
    rw [hfilter]
    simp only [a, b, prod_disjSum, Sum.elim_inl, Sum.elim_inr, id_eq]
    exact fun he => partial_abundancy_ne_two ho hN c (l \ c) hc
      (sdiff_subset.trans (filter_subset _ _)) ((prefix_balance_iff l c hcl hsub).mp he)
  have h := labels_bounded_of_no_balanced_prefix s label a b hcard hfull hpairs gap
  intro p hp
  exact h (.inr p) (inr_mem_disjSum.mpr hp)

/-- An explicit uniform upper bound for fixed support cardinality. -/
theorem le_of_bounded_prime_count {N k : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hk : N.primeFactors.card ≤ k) :
    N ≤ (max 1 (productLabelBound (2*k) (2*k) 1)) ^ k := by
  let B := max 1 (productLabelBound (2*k) (2*k) 1)
  have hcap (p : ℕ) (hp : p ∈ N.primeFactors) : p ^ N.factorization p ≤ B :=
    (Nat.pow_le_pow_right (Nat.prime_of_mem_primeFactors hp).pos (Nat.le_succ _)).trans
      ((component_le_of_bounded_prime_count ho hN hk p hp).trans (le_max_right _ _))
  rw [Nat.prod_primeFactors_pow_factorization hN.2.ne']
  have h := Finset.prod_le_prod₀ (fun p (_ : p ∈ N.primeFactors) => Nat.zero_le (p ^ N.factorization p)) hcap
  rw [prod_const] at h
  exact h.trans (Nat.pow_le_pow_right (le_max_left 1 _) hk)

/-- Dickson's 1913 finiteness theorem for odd perfect numbers. -/
theorem dickson_finite (k : ℕ) :
    Set.Finite {N : ℕ | Odd N ∧ N.Perfect ∧ N.primeFactors.card ≤ k} := by
  apply (Set.finite_le_nat ((max 1 (productLabelBound (2*k) (2*k) 1)) ^ k)).subset
  rintro N ⟨ho, hN, hk⟩
  exact le_of_bounded_prime_count ho hN hk

end OddPerfect
