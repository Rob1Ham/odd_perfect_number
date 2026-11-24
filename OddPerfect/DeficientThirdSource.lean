module

public import OddPerfect.Primitive
import Mathlib.FieldTheory.Finite.Basic

public section
namespace OddPerfect
open ArithmeticFunction Finset

/-- A prime with power-of-two predecessor dividing the divisor sum of a
square requires a source congruent to one and a distinct prime target
of that source, both congruent to one modulo the original prime. -/
theorem fermat_divisor_of_square_sigma_companion {n l k : ℕ} (hn : n≠0) (hsq : IsSquare n)
    (hl : l.Prime) (hlo : Odd l) (hk : l-1=2^k) (hd : l∣sigma 1 n) :
    ∃ r∈n.primeFactors, l∣r-1 ∧ l∣n.factorization r+1 ∧
      ∃ s, s.Prime ∧ s≠r ∧ orderOf (r:ZMod s)=l ∧ l∣s-1 ∧ s∣sigma 1 (r^(n.factorization r)) := by
  let : Fact l.Prime := ⟨hl⟩
  rw [(isMultiplicative_sigma (k:=1)).multiplicative_factorization _ hn] at hd
  obtain ⟨r,hrm,hs⟩ := (hl.prime.dvd_finsetProd_iff _).mp hd
  have hr := Nat.prime_of_mem_primeFactors hrm
  have he := Nat.isSquare_iff_even_factorization.mp hsq r hr
  let e := n.factorization r
  change l∣sigma 1 (r^e) at hs
  have hodd : Odd (e+1) := Nat.odd_iff.mpr (by have H := Nat.even_iff.mp he; dsimp [e]; omega)
  rw [sigma_one_apply,dvd_sum_divisors_prime_pow_iff hr hl] at hs
  have hr1 : (r:ZMod l)=1 := by
    by_contra hne
    simp only [hne,ite_false] at hs
    have hr0 : (r:ZMod l)≠0 := by intro h; rw [h,orderOf_zero,zero_dvd_iff] at hs; omega
    have hgrp := ZMod.orderOf_dvd_card_sub_one hr0
    rw [hk] at hgrp
    obtain ⟨v,_,hv⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hgrp
    by_cases h : v=0
    · exact hne (orderOf_eq_one_iff.mp (by simpa [h] using hv))
    · exact (hodd.of_dvd_nat hs).not_two_dvd_nat (hv ▸ dvd_pow_self 2 h)
  have hlen : l∣e+1 := by simpa [hr1] using hs
  have hcon := (ZMod.natCast_eq_natCast_iff r 1 l).mp (by simpa only [Nat.cast_one] using hr1)
  have hpred := (Nat.modEq_iff_dvd' hr.one_le).mp hcon.symm
  obtain ⟨s,hsp,hord,hs1⟩ := exists_prime_order_prime_pow hr.one_lt hl hlo 0
  let : Fact s.Prime := ⟨hsp⟩
  simp only [zero_add,pow_one] at hord hs1
  have hsr : s≠r := by rintro rfl; rw [ZMod.natCast_self,orderOf_zero] at hord; exact hl.ne_zero hord.symm
  have hn1 : (r:ZMod s)≠1 := by intro h; rw [h,orderOf_one] at hord; exact hl.ne_one hord.symm
  refine ⟨r,hrm,hpred,hlen,s,hsp,hsr,hord,hs1,?_⟩
  rw [sigma_one_apply,dvd_sum_divisors_prime_pow_iff hr hsp]
  simpa [hn1,hord] using hlen

/-- When 3σ(n)=5n both the source and companion at every odd Fermat
prime divisor of σ(n) belong to n. In particular this applies to 3,
5, and every Fermat prime other than 3 dividing n. -/
theorem fermat_order_pair_of_deficient_thirds {n l k : ℕ} (ho : Odd n) (hsq : IsSquare n)
    (hl : l.Prime) (hlo : Odd l) (hk : l-1=2^k) (hd : l∣sigma 1 n) (hbal : 3*sigma 1 n=5*n) :
    ∃ r∈n.primeFactors, ∃ s∈n.primeFactors, r≠s ∧ l∣r-1 ∧ l∣s-1 ∧ l∣n.factorization r+1 ∧ orderOf (r:ZMod s)=l := by
  obtain ⟨r,hrm,hr1,hlen,s,hsp,hsr,hord,hs1,hs⟩ := fermat_divisor_of_square_sigma_companion ho.pos.ne' hsq hl hlo hk hd
  have hsN : s∣sigma 1 n := hs.trans (by
    rw [(isMultiplicative_sigma (k:=1)).multiplicative_factorization _ ho.pos.ne']
    exact Finset.dvd_prod_of_mem _ hrm)
  have hs5 : ¬s∣5 := by
    intro h
    have he := (Nat.prime_dvd_prime_iff_eq hsp (by decide : Nat.Prime 5)).mp h
    have h4 : l∣2^2 := by rw [he] at hs1; exact hs1
    have hl2 := (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow h4)
    exact hlo.not_two_dvd_nat (hl2 ▸ dvd_rfl)
  have hsn : s∣n := (hsp.dvd_mul.mp (show s∣5*n from hbal ▸ dvd_mul_of_dvd_right hsN 3)).resolve_left hs5
  exact ⟨r,hrm,s,Nat.mem_primeFactors.mpr ⟨hsp,hsn,ho.pos.ne'⟩,hsr.symm,hr1,hs1,hlen,hord⟩

/-- The two ends of the order edge are distinct prime divisors of n
that are individually one modulo the Fermat prime. -/
theorem two_fermat_residue_primes_of_deficient_thirds {n l k : ℕ} (ho : Odd n) (hsq : IsSquare n)
    (hl : l.Prime) (hlo : Odd l) (hk : l-1=2^k) (hd : l∣sigma 1 n) (hbal : 3*sigma 1 n=5*n) :
    ∃ r∈n.primeFactors, ∃ s∈n.primeFactors, r≠s ∧ l∣r-1 ∧ l∣s-1 := by
  obtain ⟨r,hr,s,hs,hrs,hr1,hs1,_,_⟩ := fermat_order_pair_of_deficient_thirds ho hsq hl hlo hk hd hbal
  exact ⟨r,hr,s,hs,hrs,hr1,hs1⟩

/-- With 3σ(n)=5n every pair forced at the Fermat divisor 3 occurs
inside n. This is the deficient-perfect case n/d=3. -/
theorem two_one_mod_three_of_deficient_thirds {n : ℕ} (ho : Odd n) (hsq : IsSquare n)
    (h3 : 3∣sigma 1 n) (hbal : 3*sigma 1 n=5*n) :
    ∃ r∈n.primeFactors, ∃ s∈n.primeFactors, r≠s ∧ r%3=1 ∧ s%3=1 := by
  obtain ⟨r,hr,s,hs,hrs,hr1,hs1⟩ := two_fermat_residue_primes_of_deficient_thirds ho hsq
    (by decide : Nat.Prime 3) (by decide) (by decide : 3-1=2^1) h3 hbal
  have hpr := (Nat.prime_of_mem_primeFactors hr).one_lt
  have hps := (Nat.prime_of_mem_primeFactors hs).one_lt
  exact ⟨r,hr,s,hs,hrs,by omega,by omega⟩

/-- The same two primes occur if 5n is perfect, including an opening
factor five that already divides the square n. -/
theorem two_one_mod_three_of_five_mul_perfect {n : ℕ} (ho : Odd n) (hsq : IsSquare n)
    (h3 : 3∣sigma 1 n) (hN : (5*n).Perfect) :
    ∃ r∈n.primeFactors, ∃ s∈n.primeFactors, r≠s ∧ r%3=1 ∧ s%3=1 := by
  obtain ⟨r,hrm,hr1,hlen,s,hsp,hsr,hord,hs1,_⟩ := fermat_divisor_of_square_sigma_companion
    ho.pos.ne' hsq (by decide : Nat.Prime 3) (by decide) (by decide : 3-1=2^1) h3
  have hrp := Nat.prime_of_mem_primeFactors hrm
  have hrmod : r%3=1 := by have := hrp.one_lt; omega
  have hsmod : s%3=1 := by have := hsp.one_lt; omega
  have hr5 : ¬r∣5 := fun h => by have := (Nat.prime_dvd_prime_iff_eq hrp (by decide : Nat.Prime 5)).mp h; omega
  have he : (5*n).factorization r=n.factorization r := by
    rw [Nat.factorization_mul (by decide) ho.pos.ne',Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd hr5,zero_add]
  have hsN := Nat.dvd_of_mem_primeFactors (Finset.mem_erase.mp (forced_mem_erase_of_order hN hrp he hsp
    (by decide : 1<3) hord hs1 hlen)).2
  have hsn := (hsp.dvd_mul.mp hsN).resolve_left (fun h => by
    have := (Nat.prime_dvd_prime_iff_eq hsp (by decide : Nat.Prime 5)).mp h
    omega)
  exact ⟨r,hrm,s,Nat.mem_primeFactors.mpr ⟨hsp,hsn,ho.pos.ne'⟩,hsr.symm,hrmod,hsmod⟩

end OddPerfect
