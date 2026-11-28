module

public import OddPerfect.EvenPrimePowerBounds
public import OddPerfect.EvenIndexRoots
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.LinearCombination

public section
namespace OddPerfect
open ArithmeticFunction Finset

/-- At index exponent sixteen, a small return exponent is confined to
the two primes 3 and 11. -/
theorem exponent_sixteen_small_returns {q p s r β : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hro : Odd r) (hrs : r ∣ s)
    (hσ : sigma 1 (p^(2*8))=q) (hplus : q+1=2*s^2)
    (hout : sigma 1 (r^(2*s.factorization r))=p^β) :
    (β=1 ∨ β=3 → r=3) ∧ (β=5 → r=3 ∨ r=11) := by
  let : Fact r.Prime := ⟨hr⟩
  let x : ZMod r := p
  obtain ⟨hpow,hrel,hone⟩ := even_index_source_root_equations hp hr hrs hσ hplus hout
  change x^β=1 at hpow
  change x^17+x=2 at hrel
  change x=1 → r ∣ 18 at hone
  have R3 (hx : x=1) : r=3 := by
    have hd := hone hx
    have h := hr.dvd_mul.mp (show r ∣ 2*3^2 from hd)
    rcases h with h|h
    · exact (hro.not_two_dvd_nat (((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h) ▸ dvd_rfl)).elim
    · exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hr.dvd_of_dvd_pow h)
  have root (h : x^17=x^2) : x=1 ∨ x=(-2:ZMod r) := by
    rw [h] at hrel
    have hz : (x-1)*(x+2)=0 := by linear_combination hrel
    rcases mul_eq_zero.mp hz with h|h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  constructor
  · rintro (hb|hb)
    · rw [hb,pow_one] at hpow
      exact R3 hpow
    · rw [hb] at hpow
      have red : x^17=x^2 := by rw [show 17=3*5+2 by decide,pow_add,pow_mul,hpow,one_pow,one_mul]
      rcases root red with h|h
      · exact R3 h
      · rw [h] at hpow
        have hz : ((9:ℕ):ZMod r)=0 := by push_cast; linear_combination -hpow
        exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp
          (hr.dvd_of_dvd_pow (show r ∣ 3^2 from (ZMod.natCast_eq_zero_iff 9 r).mp hz))
  · intro hb
    rw [hb] at hpow
    have red : x^17=x^2 := by rw [show 17=5*3+2 by decide,pow_add,pow_mul,hpow,one_pow,one_mul]
    rcases root red with h|h
    · exact Or.inl (R3 h)
    · rw [h] at hpow
      have hz : ((33:ℕ):ZMod r)=0 := by push_cast; linear_combination -hpow
      rcases hr.dvd_mul.mp (show r ∣ 3*11 from (ZMod.natCast_eq_zero_iff 33 r).mp hz) with h|h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h)
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by decide : Nat.Prime 11)).mp h)

/-- Sixteen copies of the index prime cannot pay for four distinct
cofactor sources. At all sources except 3 and 11 at least seven copies
are required. -/
theorem component_index_ne_prime_sixteenth_power {N q a b i p : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0<a)
    (hform : N=q^a*b) (hqb : ¬q ∣ b) (hl : sigma 1 b=q^a*i)
    (hr : sigma 1 (q^a)*i=2*b) (hp : p.Prime) : i≠p^16 := by
  intro hi
  obtain ⟨ha1,hσ⟩ := even_prime_power_index_eq_selected_sigma hN ho hq ha hform hqb hl hr hp
    (by decide : 0<8) hi
  have hbo := ho.of_dvd_nat (hform ▸ dvd_mul_left b _)
  have hp2 : p≠2 := by
    rintro rfl
    have h4 : 4 ∣ 2*b := hr ▸ hi ▸ (by decide : 4 ∣ 2^16).trans (dvd_mul_left _ _)
    have := hbo.not_two_dvd_nat
    omega
  have hpo := hp.odd_of_ne_two hp2
  obtain ⟨m,_,_,hqm,rfl⟩ := euler_form_of_odd_component_index hN ho hq ha hform hqb hl hr (hi ▸ hpo.pow)
  have hmo := ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2≠0)) _)
  rw [ha1,pow_one] at hform hl hr
  rw [hi] at hl hr
  obtain ⟨s,hso,hcop,hms,_,hplus,hσs⟩ := even_prime_power_cofactor_split hq hp hmo hpo (by decide : 0<8) hl hr
  have hn := prime_count_of_even_index_split hq hp hmo hso (by decide : 0<8) hqm hcop hform hms
  have hmin := five_le_distinct_prime_factor_count ho hN
  have hpar := (even_index_cofactor_prime_count hp hso hσ hplus hσs).1
  have h4 : 4≤s.primeFactors.card := by have := Nat.even_iff.mp hpar; omega
  let f (r : ℕ) := sigma 1 (r^(2*s.factorization r))
  let v (r : ℕ) := (f r).factorization p
  obtain ⟨hsum,hparts⟩ := even_index_source_valuation_budget hp hso hσ hplus hσs
  change ∑ r ∈ s.primeFactors,v r=16 at hsum
  have hlocal (r : ℕ) (h : r ∈ s.primeFactors) : 7≤v r+(if r=3 then 6 else 0)+(if r=11 then 2 else 0) := by
    obtain ⟨hodd,hout⟩ := hparts r h
    change Odd (v r) at hodd
    change f r=p^(v r) at hout
    have hdiv := Nat.dvd_of_mem_primeFactors h
    obtain ⟨h13,h5⟩ := exponent_sixteen_small_returns hp (Nat.prime_of_mem_primeFactors h) (hso.of_dvd_nat hdiv)
      hdiv hσ hplus hout
    have := Nat.odd_iff.mp hodd
    split_ifs <;> omega
  have htotal := Finset.sum_le_sum hlocal
  simp only [Finset.sum_const,smul_eq_mul,Finset.sum_add_distrib,hsum,Finset.sum_ite_eq'] at htotal
  split_ifs at htotal <;> omega

/-- Every prime-power index of an exact component has exponent at least
66, with no restrictions on the index prime. -/
theorem component_prime_power_index_exponent_ge_sixty_six {N q a b i p j : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0<a)
    (hform : N=q^a*b) (hqb : ¬q ∣ b) (hl : sigma 1 b=q^a*i)
    (hr : sigma 1 (q^a)*i=2*b) (hp : p.Prime) (hj : 0<j) (hi : i=p^j) :
    66≤j := by
  rcases component_prime_power_index_exponent hN ho hq ha hform hqb hl hr hp hj hi with ⟨h,_⟩|h
  · exact (component_index_ne_prime_sixteenth_power hN ho hq ha hform hqb hl hr hp (h ▸ hi)).elim
  · exact h

end OddPerfect
