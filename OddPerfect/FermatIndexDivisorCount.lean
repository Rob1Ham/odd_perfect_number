module

public import OddPerfect.FermatIndexSources
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- In a Fermat-supported index, a `1 mod 4` index valuation at a base
`p≡1 mod 4` and an odd valuation at another base force sixteen divisors
of the Euler length. -/
theorem sixteen_le_euler_length_divisors_of_fermat_valuations {N q a m i p r : ℕ}
    (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1) (ha : Odd a) (hform : N=q^a*m^2)
    (hi : Odd i) (hs : ∀ s ∈ i.primeFactors, ∃ k : ℕ, s-1=2^k)
    (hl : sigma 1 (m^2)=q^a*i) (hret : sigma 1 (q^a)*i=2*m^2)
    (hpI : p ∈ i.primeFactors) (hrI : r ∈ i.primeFactors) (hpr : p ≠ r) (hp4 : p%4=1)
    (hpv : i.factorization p%4=1) (hrv : Odd (i.factorization r)) : 16 ≤ (a+1).divisors.card := by
  have hp := Nat.prime_of_mem_primeFactors hpI
  have hr := Nat.prime_of_mem_primeFactors hrI
  have hpo := hi.of_dvd_nat (Nat.dvd_of_mem_primeFactors hpI)
  have hro := hi.of_dvd_nat (Nat.dvd_of_mem_primeFactors hrI)
  have hm := (ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left _ _))).pos
  have hvp := (fermat_supported_index_valuation hq hm hi hpI hs hl hret).2
  have hvr := (fermat_supported_index_valuation hq hm hi hrI hs hl hret).2
  obtain ⟨k,hk⟩ := hs p hpI
  have he := cofactor_component_sum_dvd_index_product hm hp rfl (by omega : 0<2*m.factorization p) hl
  have h4 := fermat_supported_component_four_dvd_exponent hp hk hp4 ⟨m.factorization p,by omega⟩ hi hq hq4 hs he
  have hpd := (hp.pow_dvd_iff_le_factorization (by omega : a+1 ≠ 0)).mpr (by omega : 3 ≤ (a+1).factorization p)
  have hrd := (hr.dvd_iff_one_le_factorization (by omega : a+1 ≠ 0)).mpr
    (by have := Nat.odd_iff.mp hrv; omega : 1 ≤ (a+1).factorization r)
  have hcop := (hp.coprime_iff_not_dvd.mpr (fun h => hpr ((Nat.prime_dvd_prime_iff_eq hp hr).mp h))).pow_left 3
  have hc2 := (Nat.coprime_two_right.mpr ((hpo.pow (n:=3)).mul hro)).symm
  have hd := hc2.mul_dvd_of_dvd_of_dvd (by have := Nat.odd_iff.mp ha; omega : 2 ∣ a+1) (hcop.mul_dvd_of_dvd_of_dvd hpd hrd)
  have hc := Finset.card_le_card (Nat.divisors_subset_of_dvd (by omega : a+1 ≠ 0) hd)
  rw [Nat.Coprime.card_divisors_mul hc2, Nat.Coprime.card_divisors_mul hcop, Nat.card_divisors (pow_ne_zero 3 hp.ne_zero),
    Nat.primeFactors_pow _ (by decide : 3 ≠ 0),hp.primeFactors,Finset.prod_singleton,hp.factorization_pow,
    Finsupp.single_eq_same,Nat.card_divisors hr.ne_zero,hr.primeFactors,Finset.prod_singleton,hr.factorization_self,
    show (2:ℕ).divisors.card=2 by decide] at hc
  exact hc

end OddPerfect
