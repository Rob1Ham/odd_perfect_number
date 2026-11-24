module

public import OddPerfect.QuasiFactors
public import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

public section

namespace OddPerfect

open Finset

/-- Formal abundancy, obtained by summing the reciprocals of the powers of the base. -/
@[expose] def componentAbundancy (b e : ℕ) : ℚ :=
  ∑ j ∈ range (e+1), ((b : ℚ)⁻¹)^j

theorem componentAbundancy_eq {b : ℕ} (hb : 0 < b) (e : ℕ) :
    componentAbundancy b e = ((∑ j ∈ range (e+1), b^j : ℕ) : ℚ) / (b : ℚ)^e := by
  have hb' : (0:ℚ) < b := by exact_mod_cast hb
  apply (eq_div_iff (pow_ne_zero _ hb'.ne')).mpr
  induction e with
  | zero => simp [componentAbundancy]
  | succ e ih =>
    have hrec : (∑ j ∈ range (e+1+1), b^j) = (∑ j ∈ range (e+1), b^j)*b+1 := by
      rw [sum_range_succ']
      simp [pow_succ, sum_mul]
    have hnew : componentAbundancy b (e+1) = componentAbundancy b e + ((b:ℚ)⁻¹)^(e+1) :=
      sum_range_succ _ _
    rw [hnew, add_mul, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hb'.ne'), pow_succ, ← mul_assoc, ih, hrec]
    push_cast
    rfl

theorem one_le_componentAbundancy (b e : ℕ) : 1 ≤ componentAbundancy b e := by
  simpa [componentAbundancy] using (single_le_sum (s := range (e+1)) (f := fun j => ((b:ℚ)⁻¹)^j)
    (fun _ _ => by positivity) (mem_range.mpr (Nat.zero_lt_succ e)))

/-- Increasing the exponent strictly increases formal abundancy when the base is positive. -/
theorem componentAbundancy_strictMono {b : ℕ} (hb : 0 < b) : StrictMono (componentAbundancy b) := by
  apply strictMono_nat_of_lt_succ
  intro e
  unfold componentAbundancy
  rw [sum_range_succ (n := e+1)]
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  exact lt_add_of_pos_right _ (pow_pos (inv_pos.mpr hb') _)

/-- Increasing a positive base weakly decreases formal abundancy, for every fixed exponent. -/
theorem componentAbundancy_antitone {b c : ℕ} (hb : 0 < b) (hbc : b ≤ c) (e : ℕ) :
    componentAbundancy c e ≤ componentAbundancy b e := by
  apply sum_le_sum
  intro j _
  have hb' : (0:ℚ) < b := by exact_mod_cast hb
  apply pow_le_pow_left₀ (by positivity)
  exact inv_anti₀ hb' (by exact_mod_cast hbc)

/-- Geometric upper bound for a slot whose exponent has not yet been fixed. -/
theorem componentAbundancy_lt_limit {b : ℕ} (hb : 1 < b) (e : ℕ) :
    componentAbundancy b e < (b:ℚ)/(b-1) := by
  rw [componentAbundancy_eq (by omega : 0<b)]
  have hrat : (1:ℚ)<b := by exact_mod_cast hb
  apply (div_lt_div_iff₀ (pow_pos (zero_lt_one.trans hrat) _) (sub_pos.mpr hrat)).mpr
  have h := geom_sum_mul_add (b-1) (e+1)
  rw [Nat.sub_add_cancel hb.le, pow_succ] at h
  have hlt : (∑ j ∈ range (e+1), b^j) * (b-1) < b*b^e := by nlinarith
  have hc : (((∑ j ∈ range (e+1), b^j) * (b-1) : ℕ) : ℚ) < ((b*b^e:ℕ):ℚ) := by
    exact_mod_cast hlt
  simpa only [Nat.cast_mul, Nat.cast_sub hb.le, Nat.cast_one, Nat.cast_pow] using hc

/-- Multiplying exact factors recovers the formal ratio of the whole list. -/
theorem list_componentAbundancy {X : List (ℕ × ℕ)} (hb : ∀ z ∈ X, 0 < z.1) :
    (X.map (fun z => componentAbundancy z.1 z.2)).prod =
      (listFormalSigma X:ℚ)/(listValue X:ℚ) := by
  induction X with
  | nil => simp [listFormalSigma, listValue]
  | cons z zs ih =>
    change componentAbundancy z.1 z.2 * (zs.map (fun w => componentAbundancy w.1 w.2)).prod =
      (((∑ j ∈ range (z.2+1), z.1^j) * listFormalSigma zs:ℕ):ℚ) /
      ((z.1^z.2 * listValue zs:ℕ):ℚ)
    rw [componentAbundancy_eq (hb z (.head _)), ih (fun w hw => hb w (.tail _ hw)), div_mul_div_comm]
    push_cast
    rfl

/-- Multiplicative form of the formal balance equation for indexed slots. -/
theorem prod_componentAbundancy_eq_two {ι : Type*} (P : Finset ι) (b e : ι → ℕ)
    (hb : ∀ i ∈ P, 0 < b i)
    (hbal : formalSigma P b e = 2 * ∏ i ∈ P, b i ^ e i) :
    (∏ i ∈ P, componentAbundancy (b i) (e i)) = 2 := by
  have hden : 0 < ∏ i ∈ P, b i ^ e i := prod_pos (fun i hi => pow_pos (hb i hi) _)
  have hprod := prod_congr rfl (fun i hi => componentAbundancy_eq (hb i hi) (e i))
  rw [hprod, prod_div_distrib]
  simp only [← Nat.cast_pow, ← Nat.cast_prod]
  change ((formalSigma P b e : ℕ) : ℚ) / ((∏ i ∈ P, b i ^ e i : ℕ) : ℚ) = 2
  rw [hbal, Nat.cast_mul, Nat.cast_ofNat, mul_div_cancel_right₀]
  exact_mod_cast hden.ne'

/-- Dittmer's inequality (1). Complete the slots in C exactly, and bound
each remaining slot between its exponent-one and limiting abundancies. -/
theorem formal_partial_abundancy_bounds {ι : Type*} [DecidableEq ι] (P C : Finset ι)
    (hC : C ⊂ P) (b e : ι → ℕ) (hb : ∀ i ∈ P, 1 < b i) (he : ∀ i ∈ P, 0 < e i)
    (hbal : formalSigma P b e = 2 * ∏ i ∈ P, b i ^ e i) :
    (∏ i ∈ C, componentAbundancy (b i) (e i)) * (∏ i ∈ P \ C, componentAbundancy (b i) 1) ≤ 2 ∧
    2 < (∏ i ∈ C, componentAbundancy (b i) (e i)) * ∏ i ∈ P \ C, (b i : ℚ)/(b i-1) := by
  let f := fun i => componentAbundancy (b i) (e i)
  have hpos (i : ι) : 0 < f i := zero_lt_one.trans_le (one_le_componentAbundancy _ _)
  have hfull := prod_componentAbundancy_eq_two P b e (fun i hi => (hb i hi).le) hbal
  have heq : C.prod f * (P \ C).prod f = 2 := by
    rw [mul_comm, prod_sdiff hC.subset]
    exact hfull
  have hleft : 0 < C.prod f := prod_pos fun i _ => hpos i
  rw [← heq]
  constructor
  · apply mul_le_mul_of_nonneg_left _ hleft.le
    apply prod_le_prod₀ (fun i _ => zero_le_one.trans (one_le_componentAbundancy _ _))
    intro i hi
    exact (componentAbundancy_strictMono (hb i (mem_sdiff.mp hi).1).le).monotone (he i (mem_sdiff.mp hi).1)
  · apply mul_lt_mul_of_pos_left _ hleft
    apply prod_lt_prod_of_nonempty₀ (fun i _ => hpos i)
      (fun i hi => componentAbundancy_lt_limit (hb i (mem_sdiff.mp hi).1) _)
    exact sdiff_nonempty.mpr hC.not_superset

end OddPerfect
