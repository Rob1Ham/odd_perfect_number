module

public import OddPerfect.EvenIndexRadical
public import OddPerfect.EvenIndexSingleCopy
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.LinearCombination

public section
namespace OddPerfect
open ArithmeticFunction Finset

/-- The total of r−1 over cofactor primes sending one copy. -/
@[expose] def singleCopyWeight (s p : ℕ) : ℕ :=
  ∑ r ∈ s.primeFactors, if sourceMultiplicity s p r=1 then r-1 else 0

private theorem sum_predecessors_lt_product (S : Finset ℕ) (h : ∀r ∈ S, 0<r) :
    1+(∑r ∈ S,(r-1))≤S.prod id := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hsum := ih (fun r hr => h r (Finset.mem_insert_of_mem hr))
    have hpos := h a (Finset.mem_insert_self ..)
    rw [Finset.prod_insert ha,Finset.sum_insert ha,id_eq]
    have hsub := Nat.sub_add_cancel (show 1≤a by omega)
    nlinarith [Nat.mul_le_mul_left a hsum,Nat.le_mul_of_pos_left (∑r ∈ S,(r-1)) hpos]

/-- Distinct single-copy sources divide u+1, so the combined weight
at the linear coefficient of the return polynomial is at most u. -/
theorem singleCopyWeight_le {q p s u : ℕ} (hp : p.Prime) (hs : Odd s)
    (hσq : sigma 1 (p^(2*u))=q) (hplus : q+1=2*s^2) (hσs : sigma 1 (s^2)=p^(2*u)) :
    singleCopyWeight s p≤u := by
  let S := s.primeFactors.filter (fun r => sourceMultiplicity s p r=1)
  have hsub : S ⊆ (u+1).primeFactors := by
    intro r hr
    obtain ⟨hmem,hβ⟩ := Finset.mem_filter.mp hr
    have hout := ((even_index_source_valuation_budget hp hs hσq hplus hσs).2 r hmem).2
    change sigma 1 (r^(2*s.factorization r))=p^sourceMultiplicity s p r at hout
    rw [hβ,pow_one] at hout
    have hrp := Nat.prime_of_mem_primeFactors hmem
    exact Nat.mem_primeFactors.mpr ⟨hrp,single_copy_source_dvd hp hrp hs (Nat.dvd_of_mem_primeFactors hmem) hσq hplus hout,by omega⟩
  have H := sum_predecessors_lt_product S (fun r hr => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hr).1).pos)
  have hdiv := (Finset.prod_dvd_prod_of_subset S (u+1).primeFactors id hsub).trans (Nat.prod_primeFactors_dvd _)
  have hprod := Nat.le_of_dvd (by omega : 0<u+1) hdiv
  have hw : singleCopyWeight s p=∑ r ∈ S,(r-1) := by rw [singleCopyWeight,Finset.sum_ite]; simp [S]
  change S.prod id≤u+1 at hprod
  omega

private theorem prod_one_add_square_zero {R α : Type*} [CommRing R] {x : R} (hx : x^2=0)
    (S : Finset α) (f : α→R) : (∏r ∈ S,(1+x*f r)) = 1+x*(∑r ∈ S,f r) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi,Finset.sum_insert hi,ih]
    linear_combination (f i*(∑r ∈ S,f r))*hx

/-- The radical divided difference h=(rad(s)−1)/p obeys a first lift
that counts only the single-copy sources. -/
theorem even_index_radical_first_lift {q p s u : ℕ} (hp : p.Prime) (hpo : Odd p)
    (hs : Odd s) (hu : 0<u) (hσq : sigma 1 (p^(2*u))=q) (hplus : q+1=2*s^2)
    (hσs : sigma 1 (s^2)=p^(2*u)) :
    2*((s.primeFactors.prod id-1)/p)+1 ≡ 2*singleCopyWeight s p [MOD p] := by
  let P := s.primeFactors.prod id
  let h := (P-1)/p
  let R := ZMod (p^2)
  let x : R := p
  have hP := twice_even_index_base_lt_radical hp hpo hs hu hσq hplus hσs
  change 2*p+1≤P at hP
  have hd := (Nat.modEq_iff_dvd' (by omega : 1≤P)).mp
    (even_index_radical_mod_index_prime hp hpo hs hσq hplus hσs).symm
  have hPh : P=1+p*h := by
    have hh := Nat.mul_div_cancel' hd
    dsimp [h]
    omega
  have hx : x^2=0 := by
    change (p:ZMod (p^2))^2=0
    rw [←Nat.cast_pow,ZMod.natCast_self]
  have hq : (q:R)=1+x := by
    rw [←hσq,sigma_one_apply_prime_pow hp,Nat.cast_sum]
    simp only [Nat.cast_pow]
    rw [show 2*u+1=(2*u-1)+1+1 by omega,Finset.sum_range_succ']
    simp only [pow_succ',←Finset.mul_sum,pow_zero]
    rw [Finset.sum_range_succ']
    simp only [pow_succ',←Finset.mul_sum,pow_zero]
    change x*(x*_+1)+1=1+x
    linear_combination (∑ k ∈ range (2*u-1),x^k)*hx
  have hR := congrArg (fun n:ℕ => (n:R)) (even_index_cofactor_radical_identity hp hs hσq hplus hσs)
  change ((s^2*P:ℕ):R)=_ at hR
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_prod,Nat.cast_add,Nat.cast_one] at hR
  let f (r : ℕ) : ℕ := if sourceMultiplicity s p r=1 then r-1 else 0
  have hreplace (r : ℕ) (hr : r ∈ s.primeFactors) :
      1+((r-1:ℕ):R)*x^sourceMultiplicity s p r=1+x*(f r:R) := by
    by_cases ht : sourceMultiplicity s p r=1
    · simp [ht,f,mul_comm]
    · have hh := ((even_index_source_valuation_budget hp hs hσq hplus hσs).2 r hr).1.pos
      change 0<sourceMultiplicity s p r at hh
      rw [show sourceMultiplicity s p r=2+(sourceMultiplicity s p r-2) by omega,pow_add,hx,zero_mul,mul_zero,add_zero]
      simp [f,ht]
  have hret : (s:R)^2*(P:R)=1+x*(singleCopyWeight s p:R) := by
    calc _ = ∏ r ∈ s.primeFactors,(1+((r-1:ℕ):R)*x^sourceMultiplicity s p r) := hR
         _ = ∏ r ∈ s.primeFactors,(1+x*(f r:R)) := Finset.prod_congr rfl hreplace
         _ = 1+x*(singleCopyWeight s p:R) := by rw [prod_one_add_square_zero hx]; simp [singleCopyWeight,f,Nat.cast_ite]
  have hsq := congrArg (fun n:ℕ => (n:R)) hplus
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one,Nat.cast_ofNat] at hsq
  rw [hq] at hsq
  have hcast := congrArg (fun n:ℕ => (n:R)) hPh
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_mul] at hcast
  change (P:R)=1+x*(h:R) at hcast
  rw [hcast] at hret
  have hlin : x*(2*(h:R)+1)=x*(2*(singleCopyWeight s p:R)) := by
    linear_combination 2*hret+(1+x*(h:R))*hsq-(h:R)*hx
  have hmod : p*(2*h+1) ≡ p*(2*singleCopyWeight s p) [MOD p*p] := by
    rw [←pow_two]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa [x,R] using hlin
  exact Nat.ModEq.mul_left_cancel' hp.ne_zero hmod

/-- The first lift and parity imply a quadratic bound as soon as
p is larger than twice u. -/
theorem even_index_base_le_or_square_le_radical {q p s u : ℕ} (hp : p.Prime) (hpo : Odd p)
    (hs : Odd s) (hu : 0<u) (hσq : sigma 1 (p^(2*u))=q) (hplus : q+1=2*s^2)
    (hσs : sigma 1 (s^2)=p^(2*u)) : p≤2*u ∨ p^2≤2*(s.primeFactors.prod id-1)+p := by
  by_cases hsmall : p≤2*u
  · exact .inl hsmall
  right
  let P := s.primeFactors.prod id
  let h := (P-1)/p
  have hc := even_index_radical_first_lift hp hpo hs hu hσq hplus hσs
  change 2*h+1 ≡ 2*singleCopyWeight s p [MOD p] at hc
  have hT := singleCopyWeight_le hp hs hσq hplus hσs
  have H : p≤2*h+1 := by
    by_contra! hh
    have hh' := hc.eq_of_lt_of_lt hh (by omega)
    omega
  have hP := twice_even_index_base_lt_radical hp hpo hs hu hσq hplus hσs
  change 2*p+1≤P at hP
  have hd := (Nat.modEq_iff_dvd' (by omega : 1≤P)).mp
    (even_index_radical_mod_index_prime hp hpo hs hσq hplus hσs).symm
  have hPh : p*h=P-1 := Nat.mul_div_cancel' hd
  change p^2≤2*(P-1)+p
  calc p^2 ≤ p*(2*h+1) := by simpa [pow_two] using Nat.mul_le_mul_left p H
       _ = _ := by rw [←hPh]; ring

end OddPerfect
