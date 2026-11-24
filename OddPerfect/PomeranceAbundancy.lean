module

public import OddPerfect.SpoofAbundancy
public import OddPerfect.AbundancyLimit
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

public section

namespace OddPerfect

open Finset

/-- Multiplying finite factors at least one minus their individual errors
costs at most the sum of those errors. -/
theorem product_one_sub_errors {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1-f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs (i) (hi : i∈s) := hf i (mem_insert_of_mem hi)
    have h := hf a (mem_insert_self a s)
    have he := mul_le_mul_of_nonneg_left (ih hs) (sub_nonneg.mpr h.2)
    rw [sum_insert ha,prod_insert ha]
    nlinarith [mul_nonneg h.1 (sum_nonneg (fun i hi => (hs i hi).1))]

theorem componentAbundancy_mul_limit_inverse (p e : ℕ) :
    componentAbundancy p e * (1-(p:ℚ)⁻¹) = 1-((p:ℚ)⁻¹)^(e+1) :=
  geom_sum_mul_neg _ _

private theorem limit_mul_inverse {p : ℕ} (hp : 1<p) :
    primeAbundancyLimit p * (1-(p:ℚ)⁻¹) = 1 := by
  have hpq : (1:ℚ)<p := by exact_mod_cast hp
  rw [primeAbundancyLimit,Nat.cast_sub hp.le,Nat.cast_one]
  field_simp

private theorem inverse_mem_unit {p : ℕ} (hp : 1<p) : 0 ≤ (p:ℚ)⁻¹ ∧ (p:ℚ)⁻¹ ≤ 1 := by
  have hpq : (1:ℚ)<p := by exact_mod_cast hp
  exact ⟨inv_nonneg.mpr (Nat.cast_nonneg p),(inv_le_one₀ (zero_lt_one.trans hpq)).mpr hpq.le⟩

/-- Pomerance §1.5. If specified finite exponents replace infinite ones,
the relative loss in abundancy is at most the sum of the reciprocal next
powers. H is any nonnegative shared prefix, including a mixed finite or
limiting prefix. Repeated and composite bases are allowed in the product. -/
theorem pomerance_abundancy_error {ι : Type*} (s : Finset ι) (q b : ι → ℕ)
    (hq : ∀ i ∈ s, 1<q i) {H : ℚ} (hH : 0≤H) :
    H * (∏ i ∈ s, primeAbundancyLimit (q i)) * (1 - ∑ i ∈ s, ((q i:ℚ)⁻¹)^(b i+1)) ≤
      H * ∏ i ∈ s, componentAbundancy (q i) (b i) := by
  have hc (i) (hi : i∈s) :
      componentAbundancy (q i) (b i) =
        primeAbundancyLimit (q i) * (1-((q i:ℚ)⁻¹)^(b i+1)) := by
    rw [← componentAbundancy_mul_limit_inverse]
    calc _ = componentAbundancy (q i) (b i) * (primeAbundancyLimit (q i) * (1-(q i:ℚ)⁻¹)) := by
               rw [limit_mul_inverse (hq i hi),mul_one]
         _ = _ := by ring
  have h := product_one_sub_errors s (fun i => ((q i:ℚ)⁻¹)^(b i+1)) (by
    intro i hi
    obtain ⟨hl,hu⟩ := inverse_mem_unit (hq i hi)
    exact ⟨pow_nonneg hl _,pow_le_one₀ hl hu⟩)
  rw [prod_congr rfl hc,prod_mul_distrib,← mul_assoc]
  apply mul_le_mul_of_nonneg_left h
  exact mul_nonneg hH (prod_nonneg fun i _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- Pomerance §1.4, first bound. A deficient prefix H followed by m
finite factors reaches two only if its remaining least base is strictly
below 2m/(2-H). The prefix may contain limiting factors. -/
theorem pomerance_least_remaining_base {ι : Type*} (s : Finset ι) (q b : ι → ℕ)
    {H : ℚ} (hpos : 0<H) (hH : H<2) {p : ℕ} (hp : 1<p) (hlo : ∀ i ∈ s, p≤q i)
    (hfull : 2 ≤ H * ∏ i ∈ s, componentAbundancy (q i) (b i)) :
    (p:ℚ) < 2*s.card/(2-H) := by
  have hne : s.Nonempty := by
    by_contra! he
    simp [he] at hfull
    linarith
  let u : ℚ := 1-(p:ℚ)⁻¹
  have hpp : (0:ℚ)<p := by exact_mod_cast (show 0<p by omega)
  have hu : 0<u := sub_pos.mpr ((inv_lt_one₀ hpp).mpr (by exact_mod_cast hp))
  have localLt (i) (hi : i∈s) : componentAbundancy (q i) (b i)*u < 1 := by
    have hiq : (0:ℚ)<q i := by exact_mod_cast (show 0<q i from (show 0<p by omega).trans_le (hlo i hi))
    have huu : u ≤ 1-(q i:ℚ)⁻¹ := sub_le_sub_left (inv_anti₀ hpp (by exact_mod_cast hlo i hi)) _
    have hle := mul_le_mul_of_nonneg_left huu (zero_le_one.trans (one_le_componentAbundancy (q i) (b i)))
    rw [componentAbundancy_mul_limit_inverse] at hle
    exact hle.trans_lt (sub_lt_self _ (pow_pos (inv_pos.mpr hiq) _))
  have prodLt : (∏ i ∈ s, componentAbundancy (q i) (b i)*u) < 1 := by
    simpa only [prod_const_one] using
      (prod_lt_prod_of_nonempty₀ (g:=fun _ => (1:ℚ))
        (fun i _ => mul_pos (zero_lt_one.trans_le (one_le_componentAbundancy (q i) (b i))) hu) localLt hne)
  rw [prod_mul_distrib,prod_const] at prodLt
  have hs := mul_lt_mul_of_pos_left prodLt hpos
  rw [←mul_assoc,mul_one] at hs
  have hstrict := (mul_le_mul_of_nonneg_right hfull (pow_nonneg hu.le s.card)).trans_lt hs
  have herr := product_one_sub_errors s (fun _ => (p:ℚ)⁻¹) (fun _ _ => inverse_mem_unit hp)
  simp only [sum_const,nsmul_eq_mul,prod_const] at herr
  have hquot : 2-H < 2*(s.card:ℚ)/(p:ℚ) := by
    change 1 - (s.card:ℚ)*(p:ℚ)⁻¹ ≤ u^s.card at herr
    rw [div_eq_mul_inv]
    linarith
  apply (lt_div_iff₀ (sub_pos.mpr hH)).mpr
  simpa only [mul_comm (p:ℚ) (2-H)] using (lt_div_iff₀ hpp).mp hquot

/-- Pomerance §1.4, second bound. Adding the exponent-one factor at a
sufficiently small unused prime sends a deficient prefix above two. -/
theorem pomerance_abundant_extension {H : ℚ} (hH : H<2) {p : ℕ} (hp : 0<p)
    (h : (p:ℚ) < 2/(2-H)-1) : 2 < H * componentAbundancy p 1 := by
  have hpq : (0:ℚ)<p := by exact_mod_cast hp
  have h' := (lt_div_iff₀ (sub_pos.mpr hH)).mp (show (p:ℚ)+1 < 2/(2-H) by linarith)
  have hcomp : componentAbundancy p 1 = ((p:ℚ)+1)/p := by
    unfold componentAbundancy
    simp [sum_range_succ]
    field_simp
  rw [hcomp,←mul_div_assoc,lt_div_iff₀ hpq]
  nlinarith

end OddPerfect
