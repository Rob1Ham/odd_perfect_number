module

public import OddPerfect.FermatIndexSources
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

open ArithmeticFunction Finset

private theorem twelve_le_length_divisor_count {L p r : ℕ} (hL : L ≠ 0)
    (hp : p.Prime) (hr : r.Prime) (hpo : Odd p) (hro : Odd r) (hpr : p ≠ r)
    (h2 : 2 ∣ L) (hp2 : p^2 ∣ L) (hrL : r ∣ L) : 12 ≤ L.divisors.card := by
  have hcop := (hp.coprime_iff_not_dvd.mpr (fun h => hpr ((Nat.prime_dvd_prime_iff_eq hp hr).mp h))).pow_left 2
  have hc2 := (Nat.coprime_two_right.mpr ((hpo.pow (n:=2)).mul hro)).symm
  have hd := hc2.mul_dvd_of_dvd_of_dvd h2 (hcop.mul_dvd_of_dvd_of_dvd hp2 hrL)
  have hc := Finset.card_le_card (Nat.divisors_subset_of_dvd hL hd)
  rw [Nat.Coprime.card_divisors_mul hc2, Nat.Coprime.card_divisors_mul hcop, Nat.card_divisors (pow_ne_zero 2 hp.ne_zero),
    Nat.primeFactors_pow _ (by decide : 2 ≠ 0), hp.primeFactors, Finset.prod_singleton, hp.factorization_pow,
    Finsupp.single_eq_same, Nat.card_divisors hr.ne_zero, hr.primeFactors, Finset.prod_singleton, hr.factorization_self,
    show (2:ℕ).divisors.card=2 by decide] at hc
  exact hc

/-- No Euler index has the form `p² r` for distinct odd primes `p,r` whose
predecessors are powers of two. -/
theorem euler_component_index_ne_fermat_square_times_prime {N q a m i p r k j : ℕ}
    (hN : Nat.Perfect N) (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1)
    (hqm : ¬ q ∣ m) (hform : N=q^a*m^2) (hp : p.Prime) (hr : r.Prime)
    (hpo : Odd p) (hro : Odd r) (hpr : p ≠ r) (hk : p-1=2^k) (hj : r-1=2^j)
    (hleft : sigma 1 (m^2)=q^a*i) (hright : sigma 1 (q^a)*i=2*m^2) : i ≠ p^2*r := by
  rintro rfl
  have ha : Odd a := Nat.odd_iff.mpr (by omega)
  have hm := (ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left _ _))).pos
  have hi := (hpo.pow (n:=2)).mul hro
  have hF : (p^2*r).primeFactors = {p,r} := by rw [Nat.primeFactors_mul (pow_ne_zero 2 hp.ne_zero) hr.ne_zero,
    Nat.primeFactors_pow _ (by decide : 2 ≠ 0), hp.primeFactors, hr.primeFactors]; simp
  have hs : ∀ u ∈ (p^2*r).primeFactors, ∃ d : ℕ, u-1=2^d := by
    intro u hu
    rw [hF, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact ⟨k,hk⟩
    · exact ⟨j,hj⟩
  have ⟨_,hpv⟩ := fermat_supported_index_valuation hq hm hi (by simp [hF] : p ∈ (p^2*r).primeFactors) hs hleft hright
  have ⟨hrq,hrv⟩ := fermat_supported_index_valuation hq hm hi (by simp [hF] : r ∈ (p^2*r).primeFactors) hs hleft hright
  have hnpr : ¬p ∣ r := fun h => hpr ((Nat.prime_dvd_prime_iff_eq hp hr).mp h)
  have hnrp : ¬r ∣ p^2 := fun h => hpr ((Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow h)).symm
  rw [Nat.factorization_mul (pow_ne_zero 2 hp.ne_zero) hr.ne_zero,Finsupp.add_apply,hp.factorization_pow,
    Finsupp.single_eq_same,Nat.factorization_eq_zero_of_not_dvd hnpr] at hpv
  rw [Nat.factorization_mul (pow_ne_zero 2 hp.ne_zero) hr.ne_zero,Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hnrp,hr.factorization_self] at hrv
  have hB : (p^2*r).primeFactors.card+cardFactors (p^2*r) ≤ 5 := by
    rw [hF, cardFactors_mul (pow_ne_zero 2 hp.ne_zero) hr.ne_zero, cardFactors_apply_prime_pow hp,
      cardFactors_apply_prime hr]; simp [hpr]
  have hw := euler_index_weight_bounds (B:=5) (T:=4) hN ho hq ha hqm hform hleft hright hB (by decide)
  have hrL := (hr.dvd_iff_one_le_factorization (by omega : a+1 ≠ 0)).mpr
    (by omega : 1 ≤ (a+1).factorization r)
  have hp2 : 2*m.factorization p=2 := by
    by_contra h
    have hpL := (hp.pow_dvd_iff_le_factorization (by omega : a+1 ≠ 0)).mpr
      (by omega : 2 ≤ (a+1).factorization p)
    have := twelve_le_length_divisor_count (by omega : a+1 ≠ 0) hp hr hpo hro hpr (by omega) hpL hrL
    omega
  have hout := cofactor_component_sum_dvd_index_product hm hp hp2 (by decide) hleft
  have hp4 : p%4 ≠ 1 := fun h => (by decide : ¬ 4 ∣ 2)
    (fermat_supported_component_four_dvd_exponent hp hk h (by decide) hi hq hq4 hs hout)
  have hp3 : p=3 := by
    have := hp.two_le
    have := Nat.odd_iff.mp hpo
    cases k with
    | zero => simp only [pow_zero] at hk; omega
    | succ k => cases k with
                | zero => norm_num at hk; omega
                | succ k => rw [pow_succ, pow_succ] at hk; omega
  subst p
  have hcop := coprime_fermat_supported_component hp hk (by decide : Even 2) hi hs
  have h13 : 13 ∣ q^a := (show 13 ∣ sigma 1 (3^2) by rw [sigma_one_apply_prime_pow hp]; decide).trans
    (hcop.dvd_of_dvd_mul_right hout)
  have hq13 := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 13) hq).mp ((by decide : Nat.Prime 13).dvd_of_dvd_pow h13)
  subst q
  change r ∣ 12 at hrq
  have hcases : ∀ n : Fin 13, Nat.Prime (n:ℕ) → Odd (n:ℕ) → (n:ℕ) ∣ 12 → (n:ℕ)=3 := by decide +kernel
  exact hpr (hcases ⟨r,by have := Nat.le_of_dvd (by decide : 0<12) hrq; omega⟩ hr hro hrq).symm

end OddPerfect
