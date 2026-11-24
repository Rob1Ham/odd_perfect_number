module

public import OddPerfect.IndexPrimeReturn
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- For index `p²r` the component at `r` has exponent two, four, or `p−1`
whenever `p−1` is a power of two. An exponent larger than four must come
from an outgoing factor `p`. -/
theorem square_times_prime_index_source_exponent {N q a m p r k : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : Odd a) (hqm : ¬ q ∣ m)
    (hform : N=q^a*m^2) (hp : p.Prime) (hr : r.Prime) (hro : Odd r) (hpr : p ≠ r)
    (hk : p-1=2^k) (hl : sigma 1 (m^2)=q^a*(p^2*r)) (hret : sigma 1 (q^a)*(p^2*r)=2*m^2) :
    let e := 2*m.factorization r
    0 < e ∧ sigma 1 (r^e) ∣ p^2*q^a ∧
      ((p ∣ sigma 1 (r^e) ∧ e+1=p) ∨ ((e=2 ∨ e=4) ∧ ∃ β : ℕ, sigma 1 (r^e)=q^β)) := by
  let e := 2*m.factorization r
  change 0 < e ∧ _
  have hm := (ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left _ _))).pos
  have hi := Nat.mul_pos (Nat.pow_pos (n:=2) hp.pos) hr.pos
  have hnrp : ¬r ∣ p^2 := fun h => hpr ((Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow h)).symm
  have hvr : (p^2*r).factorization r = 1 := by
    rw [Nat.factorization_mul (pow_ne_zero 2 hp.ne_zero) hr.ne_zero,Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnrp,hr.factorization_self,zero_add]
  have hv := index_prime_return_valuation hr hro hq hm hi hret
  rw [hvr] at hv
  have hepos : 0 < e := by dsimp [e]; omega
  have heven : Even e := ⟨m.factorization r,by simp [e,two_mul]⟩
  have heout := cofactor_component_sum_dvd_index_product hm hr (e:=e) rfl hepos hl
  have hself : ¬r ∣ sigma 1 (r^e) := by rw [Nat.dvd_iff_mod_eq_zero, sigma_prime_pow_mod_self hr]; decide
  have hred : sigma 1 (r^e) ∣ p^2*q^a := ((hr.coprime_iff_not_dvd.mpr hself).symm.dvd_of_dvd_mul_right
    (show sigma 1 (r^e) ∣ (p^2*q^a)*r by rwa [show (p^2*q^a)*r=q^a*(p^2*r) by ac_rfl]))
  refine ⟨hepos,hred,?_⟩
  by_cases hpd : p ∣ sigma 1 (r^e)
  · exact Or.inl ⟨hpd,(exceptional_prime_power_index_component hr heven hepos hp hk hq hred hpd).1⟩
  · have hcop := (hp.coprime_iff_not_dvd.mpr hpd).symm.pow_right 2
    obtain ⟨β,_,hβ⟩ := (Nat.dvd_prime_pow hq).mp (hcop.dvd_of_dvd_mul_left hred)
    refine Or.inr ⟨?_,β,hβ⟩
    have hlen := pure_component_index_return_length hr hro hq hm hi hepos hβ hret
    rw [hvr] at hlen
    change r^(e-1-1) ∣ a+1 at hlen
    have hF : (p^2*r).primeFactors = {p,r} := by rw [Nat.primeFactors_mul (pow_ne_zero 2 hp.ne_zero) hr.ne_zero,
      Nat.primeFactors_pow _ (by decide : 2 ≠ 0),hp.primeFactors,hr.primeFactors]; simp
    have hB : (p^2*r).primeFactors.card+cardFactors (p^2*r) ≤ 5 := by
      rw [hF,cardFactors_mul (pow_ne_zero 2 hp.ne_zero) hr.ne_zero,cardFactors_apply_prime_pow hp,cardFactors_apply_prime hr]
      simp [hpr]
    have hw := euler_index_weight_bounds (B:=5) (T:=4) hN ho hq ha hqm hform hl hret hB (by decide)
    have h6 : ¬6 ≤ e := by
      intro h
      have h4 := (pow_dvd_pow r (by omega : 4 ≤ e-1-1)).trans hlen
      have hcop2 := (Nat.coprime_two_right.mpr (hro.pow (n:=4))).symm
      have hdiv := hcop2.mul_dvd_of_dvd_of_dvd (by have := Nat.odd_iff.mp ha; omega : 2 ∣ a+1) h4
      have hc := Finset.card_le_card (Nat.divisors_subset_of_dvd (by omega : a+1 ≠ 0) hdiv)
      rw [Nat.Coprime.card_divisors_mul hcop2, Nat.card_divisors (pow_ne_zero 4 hr.ne_zero),
        Nat.primeFactors_pow _ (by decide : 4 ≠ 0),hr.primeFactors,Finset.prod_singleton,hr.factorization_pow,
        Finsupp.single_eq_same,show (2:ℕ).divisors.card=2 by decide] at hc
      omega
    have := Nat.even_iff.mp heven
    omega

end OddPerfect
