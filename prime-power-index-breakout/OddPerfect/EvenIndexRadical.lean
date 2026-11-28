module

public import OddPerfect.EvenIndexEffective
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.BigOperators.ModEq

public section
namespace OddPerfect
open ArithmeticFunction Finset

/-- The return multiplicity at each cofactor prime. -/
@[expose] def sourceMultiplicity (s p r : ℕ) : ℕ :=
  (sigma 1 (r^(2*s.factorization r))).factorization p

/-- Multiplying the geometric identities across the cofactor yields
an exact polynomial identity at the index prime. -/
theorem even_index_cofactor_radical_identity {q p s u : ℕ}
    (hp : p.Prime) (hs : Odd s) (hσq : sigma 1 (p^(2*u))=q)
    (hplus : q+1=2*s^2) (hσs : sigma 1 (s^2)=p^(2*u)) :
    s^2*s.primeFactors.prod id =
      ∏ r ∈ s.primeFactors,(1+(r-1)*p^(sourceMultiplicity s p r)) := by
  obtain ⟨_,hparts⟩ := even_index_source_valuation_budget hp hs hσq hplus hσs
  have hfac := (Nat.prod_primeFactors_pow_factorization hs.pos.ne').symm
  calc s^2*s.primeFactors.prod id = ∏ r ∈ s.primeFactors,(r^s.factorization r)^2*r := by
         rw [Finset.prod_mul_distrib,Finset.prod_pow,hfac]; rfl
       _ = _ := by
         apply Finset.prod_congr rfl
         intro r hr
         have hrp := Nat.prime_of_mem_primeFactors hr
         have hgeo := geom_sum_mul_add (r-1) (2*s.factorization r+1)
         rw [Nat.sub_add_cancel hrp.one_le] at hgeo
         have hout := (hparts r hr).2
         change sigma 1 (r^(2*s.factorization r))=p^sourceMultiplicity s p r at hout
         rw [sigma_one_apply_prime_pow hrp] at hout
         rw [hout,pow_succ,pow_mul'] at hgeo
         simpa only [Nat.add_comm,Nat.mul_comm] using hgeo.symm

private theorem cofactor_square_mod_index_prime {p q s u : ℕ} (hp : p.Prime) (hpo : Odd p)
    (hσq : sigma 1 (p^(2*u))=q) (hplus : q+1=2*s^2) : s^2 ≡ 1 [MOD p] := by
  let : Fact p.Prime := ⟨hp⟩
  have hq1 : q ≡ 1 [MOD p] := by
    rw [←hσq]
    simpa [Nat.ModEq,Nat.mod_eq_of_lt hp.one_lt] using sigma_prime_pow_mod_self hp (2*u)
  have h := hq1.add_right 1
  rw [hplus] at h
  have hcop := (Nat.coprime_two_right.mpr hpo)
  exact Nat.ModEq.cancel_left_of_coprime hcop (show 2*s^2 ≡ 2*1 [MOD p] from h)

/-- The cofactor radical is one modulo the index prime. The source
orders give s² rad(s)=1 in the residue field and s²=1 there. -/
theorem even_index_radical_mod_index_prime {q p s u : ℕ} (hp : p.Prime) (hpo : Odd p)
    (hs : Odd s) (hσq : sigma 1 (p^(2*u))=q) (hplus : q+1=2*s^2)
    (hσs : sigma 1 (s^2)=p^(2*u)) : s.primeFactors.prod id ≡ 1 [MOD p] := by
  have hparts := (even_index_source_valuation_budget hp hs hσq hplus hσs).2
  have heq := even_index_cofactor_radical_identity hp hs hσq hplus hσs
  have hprod : s^2*s.primeFactors.prod id ≡ 1 [MOD p] := by
    rw [heq]
    have hh (r : ℕ) (hr : r∈s.primeFactors) : 1+(r-1)*p^sourceMultiplicity s p r ≡ 1 [MOD p] := by
      have hv := (hparts r hr).1.pos
      have hdiv := (dvd_pow_self p hv.ne').trans (dvd_mul_left (p^sourceMultiplicity s p r) (r-1))
      simpa using (Nat.modEq_zero_iff_dvd.mpr hdiv).add_left 1
    simpa using Nat.ModEq.prod hh
  have hs2 := cofactor_square_mod_index_prime hp hpo hσq hplus
  simpa using ((hs2.mul_right (s.primeFactors.prod id)).symm.trans hprod)

/-- An odd nontrivial cofactor radical congruent to one modulo an odd
prime is at least twice that prime plus one. -/
theorem twice_even_index_base_lt_radical {q p s u : ℕ} (hp : p.Prime) (hpo : Odd p)
    (hs : Odd s) (hu : 0<u) (hσq : sigma 1 (p^(2*u))=q) (hplus : q+1=2*s^2)
    (hσs : sigma 1 (s^2)=p^(2*u)) : 2*p+1≤s.primeFactors.prod id := by
  let P := s.primeFactors.prod id
  have hmod := even_index_radical_mod_index_prime hp hpo hs hσq hplus hσs
  change P ≡ 1 [MOD p] at hmod
  have hs1 : s≠1 := by
    rintro rfl
    have hbig := one_lt_pow₀ hp.one_lt (by omega : 2*u≠0)
    simp at hσs
    omega
  obtain ⟨r,hr,hrs⟩ := Nat.exists_prime_and_dvd hs1
  have hrS := Nat.mem_primeFactors.mpr ⟨hr,hrs,hs.pos.ne'⟩
  have hP0 : 0<P := Finset.prod_pos (fun r hr => (Nat.prime_of_mem_primeFactors hr).pos)
  have hP1 : 1<P := hr.one_lt.trans_le (Nat.le_of_dvd hP0 (Finset.dvd_prod_of_mem id hrS))
  have hodd : Odd P := Finset.prod_induction id Odd (fun _ _ => Odd.mul) odd_one
    (fun r hr => hs.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr))
  have hd : p∣P-1 := (Nat.modEq_iff_dvd' (by omega : 1≤P)).mp hmod.symm
  obtain ⟨k,hk⟩ := hd
  have hk0 : k≠0 := by rintro rfl; simp at hk; omega
  have hk1 : k≠1 := by
    rintro rfl
    rw [mul_one] at hk
    have := Nat.odd_iff.mp hodd
    have := Nat.odd_iff.mp hpo
    omega
  have H := Nat.mul_le_mul_left p (by omega : 2≤k)
  change 2*p+1≤P
  omega

end OddPerfect
