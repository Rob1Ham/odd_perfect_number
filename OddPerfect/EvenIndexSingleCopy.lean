module

public import OddPerfect.EvenIndexRoots
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.LinearCombination
import Mathlib.FieldTheory.Finite.Basic

public section
namespace OddPerfect
open ArithmeticFunction Finset

/-- A source sending a single copy of the index prime divides half the
index exponent plus one. -/
theorem single_copy_source_dvd {q p r s u : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hs : Odd s) (hrs : r ∣ s) (hσq : sigma 1 (p^(2*u))=q) (hplus : q+1=2*s^2)
    (hsource : sigma 1 (r^(2*s.factorization r))=p) : r ∣ u+1 := by
  have h1 : p ≡ 1 [MOD r] := by
    rw [←hsource]
    simpa [Nat.ModEq,Nat.mod_eq_of_lt hr.one_lt] using sigma_prime_pow_mod_self hr (2*s.factorization r)
  have hσ := sigma_modEq_of_one hp h1 (2*u)
  rw [hσq] at hσ
  have hqp : r ∣ q+1 := hplus ▸ dvd_mul_of_dvd_right (dvd_pow hrs (by decide : 2≠0)) _
  have hfull : r ∣ 2*(u+1) := (by omega : 2*u+1+1=2*(u+1)) ▸ ((hσ.add_right 1).dvd_iff dvd_rfl).mp hqp
  exact (Nat.coprime_two_right.mpr (hs.of_dvd_nat hrs)).dvd_of_dvd_mul_left hfull

/-- Apart from the prime divisors of u+1 every cofactor prime uses at
least three copies of the index prime. -/
theorem even_index_three_copy_bound {q p s u : ℕ} (hp : p.Prime) (hs : Odd s)
    (hσq : sigma 1 (p^(2*u))=q) (hplus : q+1=2*s^2) (hσs : sigma 1 (s^2)=p^(2*u)) :
    3*s.primeFactors.card ≤ 2*u+2*(u+1).primeFactors.card := by
  let f (r : ℕ) := sigma 1 (r^(2*s.factorization r))
  let v (r : ℕ) := (f r).factorization p
  let F := (u+1).primeFactors
  obtain ⟨hsum,hparts⟩ := even_index_source_valuation_budget hp hs hσq hplus hσs
  change ∑ r ∈ s.primeFactors,v r=2*u at hsum
  have hlow (r : ℕ) (hr : r ∈ s.primeFactors) : 3≤v r+(if r ∈ F then 2 else 0) := by
    obtain ⟨hodd,hout⟩ := hparts r hr
    change Odd (v r) at hodd
    change f r=p^(v r) at hout
    have := Nat.odd_iff.mp hodd
    split_ifs with hin
    · omega
    · by_contra! h
      rw [show v r=1 by omega,pow_one] at hout
      exact hin (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hr,
        single_copy_source_dvd hp (Nat.prime_of_mem_primeFactors hr) hs (Nat.dvd_of_mem_primeFactors hr) hσq hplus hout,by omega⟩)
  have h := Finset.sum_le_sum hlow
  simp only [Finset.sum_const,smul_eq_mul,Finset.sum_add_distrib,hsum,Finset.sum_ite] at h
  have hsub : s.primeFactors.filter (· ∈ F) ⊆ F := fun r hr => (Finset.mem_filter.mp hr).2
  have := Finset.card_le_card hsub
  dsimp [F] at *
  omega

/-- At a prime whose prime predecessor has odd part at most three, the
root-of-unity condition makes every source act like a single-copy source. -/
theorem low_order_source_dvd {q p s u r β : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hro : Odd r) (hr3 : r≠3) (hsm : r-1 ∣ 48) (hrs : r ∣ s) (hβ : Odd β)
    (hσq : sigma 1 (p^(2*u))=q) (hplus : q+1=2*s^2)
    (hout : sigma 1 (r^(2*s.factorization r))=p^β) : r ∣ u+1 := by
  let : Fact r.Prime := ⟨hr⟩
  let x : ZMod r := p
  obtain ⟨hpow,hrel,hone⟩ := even_index_source_root_equations hp hr hrs hσq hplus hout
  change x^β=1 at hpow
  change x^(2*u+1)+x=2 at hrel
  change x=1 → r ∣ 2*u+2 at hone
  have hx0 : x≠0 := by intro h; rw [h,zero_pow hβ.pos.ne'] at hpow; exact zero_ne_one hpow
  have hoβ := orderOf_dvd_of_pow_eq_one hpow
  have hoo := hβ.of_dvd_nat hoβ
  have h48 := (ZMod.orderOf_dvd_card_sub_one hx0).trans hsm
  have hcop := (Nat.coprime_two_right.mpr hoo).pow_right 4
  have h3 : x^3=1 := orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_left (show orderOf x ∣ 2^4*3 from h48))
  have hx : x=1 := by
    by_contra hn
    have hphi : x^2+x+1=0 := by
      have h : (x-1)*(x^2+x+1)=0 := by linear_combination h3
      exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hn)
    have hperiod : x^(2*u+1)=x^((2*u+1)%3) := by
      conv_lhs => rw [←Nat.div_add_mod (2*u+1) 3,pow_add,pow_mul,h3,one_pow,one_mul]
    rw [hperiod] at hrel
    have hcases : (2*u+1)%3=0 ∨ (2*u+1)%3=1 ∨ (2*u+1)%3=2 := by omega
    rcases hcases with h|h|h
    · rw [h,pow_zero] at hrel
      exact hn (by linear_combination hrel)
    · rw [h,pow_one] at hrel
      have hmul : (2:ZMod r)*(x-1)=0 := by linear_combination hrel
      have htwo : (2:ZMod r)≠0 := by
        intro hz
        have hd : r ∣ 2 := (ZMod.natCast_eq_zero_iff 2 r).mp (by simpa using hz)
        exact hro.not_two_dvd_nat (((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp hd) ▸ dvd_rfl)
      exact hn (sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left htwo))
    · rw [h] at hrel
      have hz : ((3:ℕ):ZMod r)=0 := by push_cast; linear_combination hphi-hrel
      exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp ((ZMod.natCast_eq_zero_iff 3 r).mp hz))
  apply (Nat.coprime_two_right.mpr hro).dvd_of_dvd_mul_left
  simpa only [Nat.mul_add,Nat.mul_one] using hone hx

end OddPerfect
