module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

namespace OddPerfect

open Finset

/-- An integer gap cannot be closed by a short product of fractions
whose denominators and numerators differ by at most a prescribed proportion. -/
private theorem gap_le_card_mul {ι : Type*} (s : Finset ι) (a b : ι → ℕ)
    {U V D : ℕ} (hD : 0 < D) (hUV : U < V)
    (ha : ∀ i ∈ s, 0 < a i)
    (hnear : ∀ i ∈ s, (D - 1) * a i ≤ D * b i)
    (hfull : U * s.prod a = V * s.prod b) : D ≤ s.card * V := by
  let z : ℚ := 1 - 1 / D
  have hD' : (0 : ℚ) < D := by exact_mod_cast hD
  have hz : 0 ≤ z := by
    dsimp [z]
    have : (1 : ℚ) ≤ D := by exact_mod_cast hD
    exact sub_nonneg.mpr ((div_le_one₀ hD').mpr this)
  have hlocal (i : ι) (hi : i ∈ s) : z * (a i : ℚ) ≤ b i := by
    have hn : ((D : ℚ) - 1) * a i ≤ D * b i := by
      rw [← Nat.cast_one (R := ℚ), ← Nat.cast_sub (show 1 ≤ D by omega)]
      exact_mod_cast hnear i hi
    dsimp [z]
    field_simp [hD'.ne']
    linarith
  have hprod := Finset.prod_le_prod₀ (fun i (_ : i ∈ s) => mul_nonneg hz (Nat.cast_nonneg (a i))) hlocal
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← Nat.cast_prod, ← Nat.cast_prod] at hprod
  have hpos : (0 : ℚ) < s.prod a := by exact_mod_cast Finset.prod_pos ha
  have heq : (U : ℚ) * (s.prod a : ℕ) = V * (s.prod b : ℕ) := by exact_mod_cast hfull
  have hscale := mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg V)
  rw [← heq, ← mul_assoc] at hscale
  have hpow := (mul_le_mul_iff_left₀ hpos).mp hscale
  have hbern := one_add_mul_sub_le_pow (a := z) (by linarith : -1 ≤ z) s.card
  have hbound := (mul_le_mul_of_nonneg_left hbern (Nat.cast_nonneg V)).trans hpow
  have hgap : (U : ℚ) + 1 ≤ V := by exact_mod_cast hUV
  dsimp [z] at hbound
  field_simp [hD'.ne'] at hbound
  exact_mod_cast (show (D : ℚ) ≤ s.card * V by nlinarith [mul_le_mul_of_nonneg_right hgap hD'.le])

/-- If a product of adjacent positive integers balances two distinct
integers, at least one of the adjacent pairs has a bounded larger entry. -/
theorem exists_small_label_of_balance {ι : Type*} (s : Finset ι) (label a b : ι → ℕ)
    {U V : ℕ} (hne : U ≠ V) (hfull : U * s.prod a = V * s.prod b)
    (hpair : ∀ i ∈ s, 1 < label i ∧
      (a i = label i ∧ b i = label i - 1 ∨ a i = label i - 1 ∧ b i = label i)) :
    ∃ i ∈ s, label i ≤ s.card * max U V := by
  by_contra! hall
  let D := s.card * max U V + 1
  have hD : 0 < D := Nat.succ_pos _
  have hclose {i : ι} (hi : i ∈ s) :
      (D - 1) * label i ≤ D * (label i - 1) := by
    have hiD : D ≤ label i := hall i hi
    have h1 := (hpair i hi).1
    have hA := Nat.sub_add_cancel (show 1 ≤ D by omega)
    have hB := Nat.sub_add_cancel (show 1 ≤ label i by omega)
    nlinarith [congrArg (fun t => t * (label i - 1)) hA,
      congrArg (fun t => (D - 1) * t) hB]
  have heasy (i : ι) : (D - 1) * (label i - 1) ≤ D * label i :=
    Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  rcases lt_or_gt_of_ne hne with huv | hvu
  · have h := gap_le_card_mul s a b hD huv
      (fun i hi => by rcases hpair i hi with ⟨hl, h | h⟩ <;> omega)
      (fun i hi => by rcases (hpair i hi).2 with h | h <;> rw [h.1, h.2]; exact hclose hi; exact heasy i)
      hfull
    dsimp [D] at h
    rw [max_eq_right huv.le] at h
    omega
  · have h := gap_le_card_mul s b a hD hvu
      (fun i hi => by rcases hpair i hi with ⟨hl, h | h⟩ <;> omega)
      (fun i hi => by rcases (hpair i hi).2 with h | h <;> rw [h.1, h.2]; exact heasy i; exact hclose hi)
      hfull.symm
    dsimp [D] at h
    rw [max_eq_left hvu.le] at h
    omega

/-- After at most k rounds this elementary recurrence bounds every label.
The bound is intended for finiteness, without numerical optimization. -/
def productLabelBound (k : ℕ) : ℕ → ℕ → ℕ
  | 0, t => t
  | n + 1, t => productLabelBound k n (max t (2 * k * t ^ k))

/-- In a balanced product with no balanced proper numerical prefix, the
largest label is bounded in terms of the number of factors alone. -/
theorem labels_bounded_of_no_balanced_prefix {ι : Type*}
    (s : Finset ι) (label a b : ι → ℕ) {k : ℕ} (hk : s.card ≤ k)
    (hfull : s.prod a = 2 * s.prod b)
    (hpair : ∀ i ∈ s, 1 < label i ∧
      (a i = label i ∧ b i = label i - 1 ∨ a i = label i - 1 ∧ b i = label i))
    (hgap : ∀ t : ℕ, (∃ i ∈ s, t < label i) →
      (s.filter (fun i => label i ≤ t)).prod a ≠ 2 * (s.filter (fun i => label i ≤ t)).prod b) :
    ∀ i ∈ s, label i ≤ productLabelBound k k 1 := by
  let left (t : ℕ) := s.filter (fun i => label i ≤ t)
  let rest (t : ℕ) := s.filter (fun i => t < label i)
  have split (t : ℕ) (f : ι → ℕ) : (left t).prod f * (rest t).prod f = s.prod f := by
    simpa only [left, rest, not_le] using s.prod_filter_mul_prod_filter_not (fun i => label i ≤ t) f
  have main (n t : ℕ) (ht : 1 ≤ t) (hn : (rest t).card ≤ n) :
      ∀ i ∈ s, label i ≤ productLabelBound k n t := by
    induction n generalizing t with
    | zero =>
      have hem : rest t = ∅ := card_eq_zero.mp (by omega)
      intro i hi
      by_contra! h
      have hm : i ∈ rest t := mem_filter.mpr ⟨hi, h⟩
      simp [hem] at hm
    | succ n ih =>
      let t' := max t (2 * k * t ^ k)
      have htt : t ≤ t' := le_max_left _ _
      apply ih t' (ht.trans htt)
      by_cases hem : (rest t).Nonempty
      · obtain ⟨j, hj⟩ := hem
        have hne := hgap t ⟨j, (mem_filter.mp hj).1, (mem_filter.mp hj).2⟩
        have heq : (left t).prod a * (rest t).prod a =
            (2 * (left t).prod b) * (rest t).prod b := by rw [split, mul_assoc, split, hfull]
        obtain ⟨i, hi, hl⟩ := exists_small_label_of_balance (rest t) label a b hne heq
          (fun i hi => hpair i (mem_filter.mp hi).1)
        have hpbound (f : ι → ℕ) (hf : ∀ i ∈ s, f i ≤ label i) : (left t).prod f ≤ t ^ k := by
          have hprod := Finset.prod_le_prod₀ (s := left t) (f := f) (g := fun _ => t)
            (fun j _ => Nat.zero_le (f j))
            (fun j hj => (hf j (mem_filter.mp hj).1).trans (mem_filter.mp hj).2)
          rw [prod_const] at hprod
          exact hprod.trans (Nat.pow_le_pow_right ht ((card_le_card (filter_subset _ _)).trans hk))
        have ha := hpbound a (fun j hj => by rcases hpair j hj with ⟨_, h | h⟩ <;> omega)
        have hb := hpbound b (fun j hj => by rcases hpair j hj with ⟨_, h | h⟩ <;> omega)
        have hcard : (rest t).card ≤ k := (card_le_card (filter_subset _ _)).trans hk
        have hmax : max ((left t).prod a) (2 * (left t).prod b) ≤ 2 * t ^ k :=
          max_le (by omega) (by omega)
        have hle : label i ≤ t' := hl.trans ((Nat.mul_le_mul hcard hmax).trans (by
          dsimp [t']; rw [show k * (2 * t ^ k) = 2 * k * t ^ k by ring]; exact le_max_right _ _))
        have hsub : rest t' ⊆ rest t := by
          intro x hx
          exact mem_filter.mpr ⟨(mem_filter.mp hx).1, htt.trans_lt (mem_filter.mp hx).2⟩
        have hlt := card_lt_card ((ssubset_iff_of_subset hsub).mpr
          ⟨i, hi, fun hx => hle.not_gt (mem_filter.mp hx).2⟩)
        omega
      · have hsub : rest t' = ∅ := eq_empty_iff_forall_notMem.mpr (fun i hi => hem
          ⟨i, mem_filter.mpr ⟨(mem_filter.mp hi).1, htt.trans_lt (mem_filter.mp hi).2⟩⟩)
        simp [hsub]
  exact main k 1 le_rfl ((card_le_card (filter_subset _ _)).trans hk)

end OddPerfect
