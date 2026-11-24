module

public import OddPerfect.DeficientThirdSource
public import OddPerfect.ReciprocalValuation
import Mathlib.FieldTheory.Finite.Basic

public section
namespace OddPerfect
open ArithmeticFunction Finset

private theorem three_source_one {r e : ℕ} (hr : r.Prime) (he : Even e)
    (hd : 3∣sigma 1 (r^e)) : r%3=1 := by
  have h3 : Nat.Prime 3 := by decide
  let : Fact (Nat.Prime 3) := ⟨h3⟩
  rw [sigma_one_apply,dvd_sum_divisors_prime_pow_iff hr h3] at hd
  by_cases h : (r:ZMod 3)=1
  · exact (ZMod.natCast_eq_natCast_iff r 1 3).mp (by simpa only [Nat.cast_one] using h)
  simp only [h,ite_false] at hd
  have h0 : (r:ZMod 3)≠0 := by intro hh; rw [hh,orderOf_zero,zero_dvd_iff] at hd; omega
  have hgrp : orderOf (r:ZMod 3)∣2 := ZMod.orderOf_dvd_card_sub_one h0
  rcases (Nat.dvd_prime Nat.prime_two).mp hgrp with hord|hord
  · exact (h (orderOf_eq_one_iff.mp hord)).elim
  · rw [hord] at hd
    have := Nat.even_iff.mp he
    omega

private theorem third_power_order_target {n r k : ℕ} (hn : n≠0) (hrm : r∈n.primeFactors)
    (hbal : 3*sigma 1 n=5*n) (hlen : 3^(k+1)∣n.factorization r+1) :
    ∃ s∈n.primeFactors.filter (fun s => s%3=1), s≠r ∧ orderOf (r:ZMod s)=3^(k+1) := by
  have hr := Nat.prime_of_mem_primeFactors hrm
  obtain ⟨s,hs,hor,hs1⟩ := exists_prime_order_prime_pow hr.one_lt (by decide : Nat.Prime 3) (by decide) k
  let : Fact s.Prime := ⟨hs⟩
  have h3 : 3∣s-1 := (dvd_pow_self 3 (Nat.succ_ne_zero k)).trans hs1
  have hres : s%3=1 := by have := hs.one_lt; omega
  have hL : 1<3^(k+1) := one_lt_pow₀ (by decide : 1<3) (Nat.succ_ne_zero k)
  have hne : s≠r := by rintro rfl; rw [ZMod.natCast_self,orderOf_zero] at hor; omega
  have hn1 : (r:ZMod s)≠1 := by intro h; rw [h,orderOf_one] at hor; omega
  have hdiv : s∣sigma 1 (r^(n.factorization r)) := by
    rw [sigma_one_apply,dvd_sum_divisors_prime_pow_iff hr hs]
    simpa [hn1,hor] using hlen
  have hsn : s∣sigma 1 n := hdiv.trans (by
    rw [(isMultiplicative_sigma (k:=1)).multiplicative_factorization _ hn]
    exact dvd_prod_of_mem _ hrm)
  have hN : s∣n := (hs.dvd_mul.mp (show s∣5*n from hbal ▸ dvd_mul_of_dvd_right hsn 3)).resolve_left
    (fun h => by have := (Nat.prime_dvd_prime_iff_eq hs (by decide : Nat.Prime 5)).mp h; omega)
  exact ⟨s,mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hs,hN,hn⟩,hres⟩,hne,hor⟩

/-- With at most two residue-one primes a square source cannot supply a
second factor of three. Such a source would require distinct primitive
targets of orders three and nine, both different from the source. -/
theorem three_valuation_le_one_at_deficient_source {n r : ℕ} (hn : n≠0) (hsq : IsSquare n)
    (hbal : 3*sigma 1 n=5*n) (hc : (n.primeFactors.filter (fun p => p%3=1)).card≤2)
    (hrm : r∈n.primeFactors) :
    (sigma 1 (r^(n.factorization r))).factorization 3 ≤ (if r%3=1 then 1 else 0) := by
  have hr := Nat.prime_of_mem_primeFactors hrm
  have h3 : Nat.Prime 3 := by decide
  let C := n.primeFactors.filter (fun p => p%3=1)
  by_cases h : 3∣sigma 1 (r^(n.factorization r))
  · have hmod := three_source_one hr (Nat.isSquare_iff_even_factorization.mp hsq r hr) h
    rw [ite_eq_left hmod,sigma_factorization_of_dvd_pred h3 (by decide) hr
      ((Nat.modEq_iff_dvd' hr.one_le).mp (show r ≡ 1 [MOD 3] from hmod).symm)]
    by_contra! hlo
    have h9 : 3^2∣n.factorization r+1 := (h3.pow_dvd_iff_le_factorization (Nat.succ_ne_zero _)).mpr hlo
    obtain ⟨s,hsm,hsr,hs⟩ := third_power_order_target (k:=0) hn hrm hbal ((show 3^(0+1)∣3^2 by decide).trans h9)
    obtain ⟨t,htm,htr,ht⟩ := third_power_order_target (k:=1) hn hrm hbal h9
    have hst : s≠t := by rintro rfl; rw [hs] at ht; norm_num at ht
    have hmem : ({r,s,t}:Finset ℕ)⊆C := by
      intro x hx
      rcases (show x=r ∨ x=s ∨ x=t by simpa using hx) with rfl|rfl|rfl
      · exact mem_filter.mpr ⟨hrm,hmod⟩
      · exact hsm
      · exact htm
    have hsize := card_le_card hmem
    have hcard : ({r,s,t}:Finset ℕ).card=3 := by simp [Ne.symm hsr,Ne.symm htr,hst]
    rw [hcard] at hsize
    change C.card≤2 at hc
    omega
  · rw [Nat.factorization_eq_zero_of_not_dvd h]
    exact Nat.zero_le _

/-- For a deficient-perfect square satisfying 3σ(n)=5n, at most two
prime divisors one modulo three force the exact 3-component and its
companion prime thirteen. -/
theorem deficient_thirds_three_exponent_and_thirteen {n : ℕ} (ho : Odd n) (hsq : IsSquare n)
    (h3 : 3∣n) (hbal : 3*sigma 1 n=5*n) (hc : (n.primeFactors.filter (fun p => p%3=1)).card≤2) :
    n.factorization 3=2 ∧ 13∣n := by
  have hp : Nat.Prime 3 := by decide
  have hsig : (sigma 1 n).factorization 3≤2 := by
    rw [(isMultiplicative_sigma (k:=1)).multiplicative_factorization _ ho.pos.ne']
    change (∏ r∈n.primeFactors,sigma 1 (r^(n.factorization r))).factorization 3≤2
    rw [Nat.factorization_prod_apply (fun r hr =>
      (sigma_pos 1 _ (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hr).ne_zero)).ne')]
    calc ∑ r∈n.primeFactors,(sigma 1 (r^(n.factorization r))).factorization 3 ≤
            ∑ r∈n.primeFactors,if r%3=1 then 1 else 0 :=
          sum_le_sum (fun r hr => three_valuation_le_one_at_deficient_source ho.pos.ne' hsq hbal hc hr)
         _ = (n.primeFactors.filter (fun r => r%3=1)).card := by simp
         _ ≤ 2 := hc
  have hv := congrArg (fun z : ℕ => z.factorization 3) hbal
  change (3*sigma 1 n).factorization 3=(5*n).factorization 3 at hv
  rw [Nat.factorization_mul (by decide) (sigma_pos 1 _ ho.pos.ne').ne',Finsupp.add_apply,
    hp.factorization_self,Nat.factorization_mul (by decide) ho.pos.ne',Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬3∣5),zero_add] at hv
  have he := Nat.even_iff.mp (Nat.isSquare_iff_even_factorization.mp hsq 3 hp)
  have hpos := hp.factorization_pos_of_dvd ho.pos.ne' h3
  have hval : n.factorization 3=2 := by omega
  have h13 : 13∣sigma 1 n := by
    rw [(isMultiplicative_sigma (k:=1)).multiplicative_factorization _ ho.pos.ne']
    have hh := dvd_prod_of_mem (fun r => sigma 1 (r^(n.factorization r)))
      (Nat.mem_primeFactors.mpr ⟨hp,h3,ho.pos.ne'⟩)
    rw [hval,sigma_one_apply_prime_pow hp,show ∑ j∈range (2+1),(3:ℕ)^j=13 by decide] at hh
    exact hh
  exact ⟨hval,((by decide : Nat.Prime 13).dvd_mul.mp (show 13∣5*n from hbal ▸ dvd_mul_of_dvd_right h13 3)).resolve_left (by decide)⟩

end OddPerfect
