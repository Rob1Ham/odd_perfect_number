module

public import OddPerfect.IndexSieveResiduals
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect.IndexSieve

open ArithmeticFunction Finset

/-- Half of the divisor-count bound obtained using the threshold four in
`2^t > t+ω(i)+Ω(i)`. -/
@[expose] def halfBound (i : ℕ) : ℕ := (3+i.primeFactors.card+cardFactors i)/2

/-- A pair of index primes whose candidate residuals violate a necessary
Euler-index condition. -/
structure Row where
  index : ℕ
  firstPrime : ℕ
  secondPrime : ℕ
  deriving DecidableEq

/-- The complete numerical predicate checked for one row of the sieve. -/
@[expose] def Row.valid (w : Row) : Prop :=
  w.firstPrime ∈ w.index.primeFactors ∧ w.secondPrime ∈ w.index.primeFactors ∧
    4+(w.index.primeFactors.card+cardFactors w.index) < 2^4 ∧
    ¬Compatible w.index w.firstPrime w.secondPrime (halfBound w.index) (residueModulus w.index)

instance (w : Row) : Decidable w.valid :=
  inferInstanceAs (Decidable (w.firstPrime ∈ w.index.primeFactors ∧ w.secondPrime ∈ w.index.primeFactors ∧
    4+(w.index.primeFactors.card+cardFactors w.index) < 2^4 ∧
    ¬Compatible w.index w.firstPrime w.secondPrime (halfBound w.index) (residueModulus w.index)))

/-- A checked incompatible row excludes its index in every odd perfect
number in Euler form with exponent greater than one. -/
theorem excludes_of_valid_row {N q a m i : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (ha : 1<a) (hqm : ¬q ∣ m) (hform : N=q^a*m^2)
    (hl : sigma 1 (m^2)=q^a*i) (hr : sigma 1 (q^a)*i=2*m^2) (hio : Odd i)
    (w : Row) (hw : w.valid) : i ≠ w.index := by
  intro heq
  obtain ⟨hpI,hrI,hweight,hbad⟩ := hw
  rw [← heq] at hpI hrI hweight hbad
  have hao : Odd a := Nat.odd_iff.mpr (by omega)
  have hm := (ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left _ _))).pos
  have hqo := ho.of_dvd_nat (hform ▸ (dvd_pow_self q hao.pos.ne').trans (dvd_mul_right _ _))
  have hqi : q.Coprime i := hq.coprime_iff_not_dvd.mpr (fun h => hqm (hq.dvd_of_dvd_pow
    ((Nat.coprime_two_right.mpr hqo).dvd_of_dvd_mul_left (hr ▸ h.trans (dvd_mul_left _ _)))))
  have hcount := euler_index_weight_bounds (T:=4) hN ho hq hao hqm hform hl hr (Nat.le_refl _) hweight
  have hH : (a+1).divisors.card/2 ≤ halfBound i := by unfold halfBound; omega
  obtain ⟨hM,hqM⟩ := euler_modulus hN ho hq hq4 ha4 ha hqm hform hl
  exact hbad (compatible_of_euler_index hq hao hm hio hqi hM hqM hpI hrI hH hl hr)

end OddPerfect.IndexSieve
