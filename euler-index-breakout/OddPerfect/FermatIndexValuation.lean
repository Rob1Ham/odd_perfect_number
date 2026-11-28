module

public import OddPerfect.FermatIndexSupport
public import OddPerfect.ReciprocalValuation
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- When every prime in an odd index has predecessor a power of two, each
prime `p` of the index divides `q−1`. Its exponent in the cofactor is the
sum of its exponents in the Euler length and in the index. -/
theorem fermat_supported_index_valuation {q a m i p : ℕ} (hq : q.Prime)
    (hm : 0 < m) (hi : Odd i) (hpI : p ∈ i.primeFactors)
    (hsupp : ∀ u ∈ i.primeFactors, ∃ k : ℕ, u-1=2^k)
    (hleft : sigma 1 (m^2)=q^a*i) (hright : sigma 1 (q^a)*i=2*m^2) :
    p ∣ q-1 ∧ 2*m.factorization p = (a+1).factorization p + i.factorization p := by
  obtain ⟨hp, hpi, _⟩ := Nat.mem_primeFactors.mp hpI
  have hpo := hi.of_dvd_nat hpi
  have hm2 := pow_ne_zero 2 hm.ne'
  have hpout : p ∣ sigma 1 (m^2) := hleft ▸ hpi.trans (dvd_mul_left _ _)
  have hprod := (isMultiplicative_sigma (k := 1)).multiplicative_factorization _ hm2
  rw [hprod] at hpout
  obtain ⟨r, hrmem, hd⟩ := (hp.prime.dvd_finsetProd_iff _).mp hpout
  let e := (m^2).factorization r
  have he : Even e := ⟨m.factorization r, by simp [e, Nat.factorization_pow, two_mul]⟩
  have hrσ : sigma 1 (r^e) ∣ i*q^a := by
    rw [Nat.mul_comm i, ← hleft, hprod]
    exact Finset.dvd_prod_of_mem _ hrmem
  have hpred := index_prime_dvd_selected_pred (Nat.prime_of_mem_primeFactors hrmem) he hp hpo hq
    hpi hi.pos.ne' hsupp hrσ hd
  refine ⟨hpred, ?_⟩
  have hp2 : ¬ p ∣ 2 := fun h => hpo.not_two_dvd_nat ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h ▸ dvd_rfl)
  have hv := congrArg (fun n : ℕ => n.factorization p) hright
  change (sigma 1 (q^a)*i).factorization p = (2*m^2).factorization p at hv
  rw [Nat.factorization_mul (sigma_pos 1 _ (pow_ne_zero _ hq.ne_zero)).ne' hi.pos.ne',
    Nat.factorization_mul (by decide : 2 ≠ 0) hm2, Finsupp.add_apply, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hp2, sigma_factorization_of_dvd_pred hp hpo hq hpred] at hv
  simpa [Nat.factorization_pow] using hv.symm

/-- A numerical bound for `ω(i)+Ω(i)` bounds the Euler length divisor count
whenever `2^t > t + B` at and beyond the threshold `T`. -/
theorem euler_index_weight_bounds {N q a m i B T : ℕ}
    (hN : Nat.Perfect N) (ho : Odd N) (hq : q.Prime) (ha : Odd a)
    (hqm : ¬ q ∣ m) (hform : N=q^a*m^2) (hleft : sigma 1 (m^2)=q^a*i)
    (hright : sigma 1 (q^a)*i=2*m^2) (hB : i.primeFactors.card+cardFactors i ≤ B)
    (hT : T+B < 2^T) :
    (a+1).divisors.card ≤ N.primeFactors.card ∧ N.primeFactors.card < T+B := by
  have hqb : ¬ q ∣ m^2 := fun h => hqm (hq.dvd_of_dvd_pow h)
  have hw := euler_prime_count_le_length_and_index_factors hN ho hq ha hform hqb hleft hright
  have hp := two_pow_component_length_support_le_prime_count hN ho hq ha.pos hform hqb
  have hexp (t : ℕ) (ht : T ≤ t) : t+B < 2^t := by
    induction t, ht using Nat.le_induction with
    | base => exact hT
    | succ t _ ih => rw [pow_succ]; have : 0 < 2^t := Nat.pow_pos (by decide); omega
  have ht : (a+1).primeFactors.card < T := by
    by_contra! h
    have := hexp _ h
    omega
  have hm2 := (ho.of_dvd_nat (hform ▸ dvd_mul_left (m^2) (q^a))).pos
  have hqN := Nat.mem_primeFactors.mpr ⟨hq, hform ▸ (dvd_pow_self q ha.pos.ne').trans
    (dvd_mul_right _ _), hN.2.ne'⟩
  have hval : N.factorization q = a := by
    rw [hform, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) hm2.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hqb, hq.factorization_pow, Finsupp.single_eq_same, add_zero]
  have hτ := component_length_divisor_count hN ho hqN
  rw [hval] at hτ
  exact ⟨hτ, by omega⟩

/-- An exact cofactor exponent forces its component sum into the Euler
prime power times the index. -/
theorem cofactor_component_sum_dvd_index_product {p q a m i e : ℕ} (hm : 0 < m)
    (hp : p.Prime) (he : 2*m.factorization p = e) (hepos : 0 < e)
    (hleft : sigma 1 (m^2)=q^a*i) : sigma 1 (p^e) ∣ q^a*i := by
  have hval : (m^2).factorization p = e := by simpa [Nat.factorization_pow] using he
  have hmem := Nat.mem_primeFactors.mpr ⟨hp, (hp.dvd_iff_one_le_factorization (pow_ne_zero 2 hm.ne')).mpr
    (by omega), pow_ne_zero 2 hm.ne'⟩
  rw [← hleft, (isMultiplicative_sigma (k := 1)).multiplicative_factorization _ (pow_ne_zero 2 hm.ne'), ← hval]
  exact Finset.dvd_prod_of_mem _ hmem

end OddPerfect
