module

public import OddPerfect.IndexPrimeReturn
public import OddPerfect.CyclotomicOrders
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.FieldTheory.Finite.Basic

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- The divisor sum at any shorter length dividing a component length divides
the full component sum. -/
theorem sigma_dvd_of_length_dvd {p e d : ℕ} (hp : p.Prime) (hd : 0<d) (hdiv : d ∣ e+1) :
    sigma 1 (p^(d-1)) ∣ sigma 1 (p^e) := by
  have hg (u : ℕ) : sigma 1 (p^u)*(p-1) = p^(u+1)-1 := by
    rw [sigma_one_apply_prime_pow hp]; exact geom_sum_mul_of_one_le hp.one_lt.le _
  have h := (Nat.pow_sub_one_dvd_pow_sub_one_iff hp.one_lt).mpr hdiv
  rw [show d=d-1+1 by omega, ← hg, ← hg] at h
  exact Nat.dvd_of_mul_dvd_mul_right (by have := hp.one_lt; omega) h

/-- A pure even component cannot exceed its index valuation by more than
half the Euler length divisor count. -/
theorem twice_pure_exponent_excess_le_length_divisors {p q a m i β : ℕ} (hp : p.Prime)
    (hpo : Odd p) (hq : q.Prime) (ha : Odd a) (hm : 0<m) (hi : 0 < i)
    (hepos : 0<2*m.factorization p) (hout : sigma 1 (p^(2*m.factorization p))=q^β)
    (hr : sigma 1 (q^a)*i=2*m^2) : 2*(2*m.factorization p-i.factorization p) ≤ (a+1).divisors.card := by
  let t := 2*m.factorization p-i.factorization p-1
  have hd : p^t ∣ a+1 := pure_component_index_return_length hp hpo hq hm hi hepos hout hr
  have hcop := (Nat.coprime_two_right.mpr (hpo.pow (n:=t))).symm
  have hprod := hcop.mul_dvd_of_dvd_of_dvd (by have := Nat.odd_iff.mp ha; omega : 2∣a+1) hd
  have hc := Finset.card_le_card (Nat.divisors_subset_of_dvd (by omega : a+1 ≠ 0) hprod)
  have hcard : (p^t).divisors.card=t+1 := by
    by_cases ht : t=0
    · simp [ht]
    · rw [Nat.card_divisors (pow_ne_zero t hp.ne_zero),Nat.primeFactors_pow _ ht,hp.primeFactors,
        Finset.prod_singleton,hp.factorization_pow,Finsupp.single_eq_same]
  rw [Nat.Coprime.card_divisors_mul hcop,show (2:ℕ).divisors.card=2 by decide,hcard] at hc
  dsimp [t] at hc
  omega

/-- The full odd length of every even-exponent cofactor component occurs
as a multiplicative order at the Euler prime or an index prime. -/
theorem component_length_is_order_at_index_or_euler {p q e a i : ℕ} (hp : p.Prime)
    (hpo : Odd p) (hq : q.Prime) (he : Even e) (hepos : 0<e) (hi : i≠0)
    (hout : sigma 1 (p^e) ∣ q^a*i) :
    ∃ r ∈ insert q i.primeFactors, r.Prime ∧ orderOf (p : ZMod r)=e+1 ∧ e+1 ∣ r-1 := by
  have hex : ∃ r : ℕ, r.Prime ∧ orderOf (p : ZMod r)=e+1 ∧ e+1 ∣ r-1 := by
    by_cases hpow : IsPrimePow (e+1)
    · obtain ⟨l,k,hl,hlen⟩ := (isPrimePow_iff_pow_succ (e+1)).mp hpow
      have hlp := Nat.prime_iff.mpr hl
      have hlo := (show Odd (e+1) from Nat.odd_iff.mpr (by have := Nat.even_iff.mp he; omega)).of_dvd_nat
        ((dvd_pow_self l (by omega : k+1≠0)).trans (hlen ▸ dvd_rfl))
      simpa [hlen] using exists_prime_order_prime_pow hp.one_lt hlp hlo k
    · exact exists_prime_order_mixed (by have := hp.two_le; have := Nat.odd_iff.mp hpo; omega) (by omega) hpow
  obtain ⟨r,hr,ho,hd⟩ := hex
  have hne : (p : ZMod r) ≠ 1 := by intro h; rw [h,orderOf_one] at ho; omega
  have hdiv : r ∣ sigma 1 (p^e) := by
    rw [sigma_one_apply,dvd_sum_divisors_prime_pow_iff hp hr]; simp [hne,ho]
  refine ⟨r,?_,hr,ho,hd⟩
  rcases hr.dvd_mul.mp (hdiv.trans hout) with h|h
  · exact Finset.mem_insert.mpr (.inl ((Nat.prime_dvd_prime_iff_eq hr hq).mp (hr.dvd_of_dvd_pow h)))
  · exact Finset.mem_insert_of_mem (Nat.mem_primeFactors.mpr ⟨hr,h,hi⟩)

end OddPerfect
