module

public import OddPerfect.EvenIndexRadical
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.FieldSimp

public section
namespace OddPerfect
open ArithmeticFunction Finset

private def telescopingFactor (r : ℕ) : ℚ :=
  if 2≤r then (r:ℚ)^2/((r:ℚ)^2-1) else 1

private theorem one_le_telescopingFactor (r : ℕ) : 1≤telescopingFactor r := by
  unfold telescopingFactor
  split_ifs with h
  · have hr : (2:ℚ)≤r := by exact_mod_cast h
    have hpos : 0<(r:ℚ)^2-1 := by nlinarith
    rw [le_div_iff₀ hpos]; linarith
  · rfl

private theorem prod_telescopingFactor (n : ℕ) :
    (∏ r ∈ range (n+2),telescopingFactor r)=2*((n:ℚ)+1)/((n:ℚ)+2) := by
  induction n with
  | zero => norm_num [telescopingFactor, Finset.prod_range_succ]
  | succ n ih =>
    rw [show n+1+2=n+2+1 by omega,Finset.prod_range_succ,ih]
    simp only [telescopingFactor,show 2≤n+2 by omega,ite_true,Nat.cast_succ]
    have nn := Nat.cast_nonneg (α:=ℚ) n
    have h1 : (n:ℚ)+2≠0 := by linarith
    have h2 : ((n:ℚ)+1+1)^2-1≠0 := by nlinarith
    have h3 : (n:ℚ)+1+2≠0 := by linarith
    rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero h1 h2) h3]
    ring

private theorem prod_telescopingFactor_le_two (S : Finset ℕ) : (S.prod telescopingFactor)≤2 := by
  let n := S.sup id
  have hsub : S ⊆ range (n+2) := by
    intro r hr
    have H : r≤n := Finset.le_sup (f:=id) hr
    exact Finset.mem_range.mpr (by omega)
  have H := Finset.prod_le_prod_of_subset_of_one_le₀ hsub
    (fun r _ => zero_le_one.trans (one_le_telescopingFactor r)) (fun r _ _ => one_le_telescopingFactor r)
  rw [prod_telescopingFactor] at H
  apply H.trans
  rw [div_le_iff₀ (by positivity : 0<(n:ℚ)+2)]
  linarith

/-- Outside the divisors of u+1 the return determinant bounds every
source prime separately in terms of its multiplicity. -/
theorem even_index_source_le_four_pow {q p s u r : ℕ} (hp : p.Prime) (hs : Odd s)
    (hr : r ∈ s.primeFactors) (hn : ¬r ∣ u+1) (hσq : sigma 1 (p^(2*u))=q)
    (hplus : q+1=2*s^2) (hσs : sigma 1 (s^2)=p^(2*u)) : r≤4^(sourceMultiplicity s p r-1) := by
  obtain ⟨hb,hout⟩ := (even_index_source_valuation_budget hp hs hσq hplus hσs).2 r hr
  have hrs := Nat.dvd_of_mem_primeFactors hr
  have hpr := Nat.prime_of_mem_primeFactors hr
  obtain ⟨hpow,hrel,hone⟩ := even_index_source_root_equations hp hpr hrs hσq hplus hout
  have hx : (p:ZMod r)≠1 := by
    intro h
    apply hn
    apply (Nat.coprime_two_right.mpr (hs.of_dvd_nat hrs)).dvd_of_dvd_mul_left
    simpa only [Nat.mul_add,Nat.mul_one] using hone h
  have hd := prime_dvd_returnDeterminant hpr hb.pos hx hpow hrel
  exact (Nat.le_of_dvd (returnDeterminant_pos _ _) hd).trans (returnDeterminant_le_four_pow_pred _ _)

/-- The return polynomial at 1/64 is controlled by the exceptional
primes dividing u+1. This bounds all its coefficients simultaneously. -/
theorem even_index_weighted_return_product {q p s u : ℕ} (hp : p.Prime) (hs : Odd s)
    (hσq : sigma 1 (p^(2*u))=q) (hplus : q+1=2*s^2) (hσs : sigma 1 (s^2)=p^(2*u)) :
    (∏ r ∈ s.primeFactors,(1+((r-1:ℕ):ℚ)/(64:ℚ)^sourceMultiplicity s p r))≤2*(u+1:ℕ) := by
  let W (r : ℕ) : ℚ := 1+((r-1:ℕ):ℚ)/(64:ℚ)^sourceMultiplicity s p r
  let S := s.primeFactors
  let E := S.filter (fun r => r ∣ u+1)
  let G := S.filter (fun r => ¬r ∣ u+1)
  have non (r : ℕ) : 0≤W r := by dsimp [W]; positivity
  have hE (r : ℕ) (hr : r∈E) : W r≤(r:ℚ) := by
    have hpr := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hr).1
    have hden : (1:ℚ)≤64^sourceMultiplicity s p r := one_le_pow₀ (by decide)
    have hval := div_le_self (a:=((r-1:ℕ):ℚ)) (Nat.cast_nonneg _) hden
    have hcast : ((r-1:ℕ):ℚ)+1=r := by exact_mod_cast Nat.sub_add_cancel hpr.one_le
    dsimp [W]; linarith
  have hsub : E ⊆ (u+1).primeFactors := by
    intro r hr
    obtain ⟨hm,hd⟩ := Finset.mem_filter.mp hr
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hm,hd,by omega⟩
  have hpE : E.prod W≤(u+1:ℕ) := by
    have hle := Finset.prod_le_prod₀ (fun r _ => non r) hE
    apply hle.trans
    have hdiv := (Finset.prod_dvd_prod_of_subset E (u+1).primeFactors id hsub).trans (Nat.prod_primeFactors_dvd _)
    simpa using Nat.cast_le (α := ℚ).mpr (Nat.le_of_dvd (by omega : 0<u+1) hdiv)
  have hG (r : ℕ) (hr : r∈G) : W r≤telescopingFactor r := by
    obtain ⟨hm,hn⟩ := Finset.mem_filter.mp hr
    let v := sourceMultiplicity s p r
    have hpr := Nat.prime_of_mem_primeFactors hm
    have hle := even_index_source_le_four_pow hp hs hm hn hσq hplus hσs
    have hcube : r^3≤64^v := by
      calc r^3 ≤ (4^v)^3 := Nat.pow_le_pow_left (hle.trans (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))) _
           _ = _ := by rw [←pow_mul,pow_mul']; norm_num
    have hc : (r:ℚ)^3≤64^v := by exact_mod_cast hcube
    have hh : (2:ℚ)≤r := by exact_mod_cast hpr.two_le
    have hcast : ((r-1:ℕ):ℚ)=(r:ℚ)-1 := Nat.cast_sub hpr.one_le
    have hden : 0<(r:ℚ)^2-1 := by nlinarith
    have hv : 0<(64:ℚ)^v := by positivity
    have hl : ((r-1:ℕ):ℚ)/(64:ℚ)^v ≤ 1/((r:ℚ)^2-1) := by
      rw [div_le_div_iff₀ hv hden,hcast]
      nlinarith [sq_nonneg (r:ℚ)]
    have heq : (r:ℚ)^2/((r:ℚ)^2-1)=1+1/((r:ℚ)^2-1) := by field_simp; ring
    dsimp only [W,telescopingFactor]
    rw [ite_eq_left hpr.two_le,heq]
    linarith
  have hpG := (Finset.prod_le_prod₀ (fun r _ => non r) hG).trans (prod_telescopingFactor_le_two G)
  have htotal := mul_le_mul hpE hpG (Finset.prod_nonneg (fun r _ => non r)) (Nat.cast_nonneg _)
  rw [show E.prod W*G.prod W=S.prod W from S.prod_filter_mul_prod_filter_not (fun r => r∣u+1) W] at htotal
  simpa only [Nat.cast_add,Nat.cast_one,mul_comm] using htotal

end OddPerfect
