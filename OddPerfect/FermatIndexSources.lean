module

public import OddPerfect.FermatIndexValuation
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- An even-exponent component based at a prime with power-of-two predecessor
sends no divisor to any odd prime with power-of-two predecessor. -/
theorem coprime_fermat_supported_component {p e k i : ℕ} (hp : p.Prime) (hk : p-1=2^k)
    (he : Even e) (hi : Odd i) (hs : ∀ u ∈ i.primeFactors, ∃ j : ℕ, u-1=2^j) :
    (sigma 1 (p^e)).Coprime i := by
  apply Nat.coprime_of_dvd
  intro u hu hd hI
  let : Fact u.Prime := ⟨hu⟩
  have huo := hi.of_dvd_nat hI
  obtain ⟨j,hj⟩ := hs u (Nat.mem_primeFactors.mpr ⟨hu,hI,hi.pos.ne'⟩)
  rw [sigma_one_apply, dvd_sum_divisors_prime_pow_iff hp hu] at hd
  have hnot : (p : ZMod u) ≠ 1 := by
    intro h
    have hcon := (ZMod.natCast_eq_natCast_iff p 1 u).mp (by simpa using h)
    have hpred := (Nat.modEq_iff_dvd' hp.one_lt.le).mp hcon.symm
    rw [hk] at hpred
    exact huo.not_two_dvd_nat ((Nat.prime_dvd_prime_iff_eq hu Nat.prime_two).mp (hu.dvd_of_dvd_pow hpred) ▸ dvd_rfl)
  simp only [hnot, ite_false] at hd
  have hodd := (show Odd (e+1) from Nat.odd_iff.mpr (by have := Nat.even_iff.mp he; omega)).of_dvd_nat hd
  have hzero : (p : ZMod u) ≠ 0 := by intro h; rw [h, orderOf_zero, zero_dvd_iff] at hd; omega
  have hg := ZMod.orderOf_dvd_card_sub_one hzero
  rw [hj] at hg
  obtain ⟨d, _, heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hg
  by_cases hz : d = 0
  · exact hnot (orderOf_eq_one_iff.mp (by simpa [hz] using heq))
  · exact hodd.not_two_dvd_nat (heq ▸ dvd_pow_self 2 hz)

/-- With a Fermat-supported Euler index, a component at a Fermat-prime
base congruent to one modulo four has exponent divisible by four. -/
theorem fermat_supported_component_four_dvd_exponent {p e k i q a : ℕ} (hp : p.Prime)
    (hk : p-1=2^k) (hp4 : p%4=1) (he : Even e) (hi : Odd i) (hq : q.Prime)
    (hq4 : q%4=1) (hs : ∀ u ∈ i.primeFactors, ∃ j : ℕ, u-1=2^j)
    (hd : sigma 1 (p^e) ∣ q^a*i) : 4 ∣ e := by
  have hcop := coprime_fermat_supported_component hp hk he hi hs
  obtain ⟨β,_,hβ⟩ := (Nat.dvd_prime_pow hq).mp (hcop.dvd_of_dvd_mul_right hd)
  have hpcon := sigma_modEq_of_one hp (show p ≡ 1 [MOD 4] from hp4) e
  have hqcon := (show q ≡ 1 [MOD 4] from hq4).pow β
  rw [hβ] at hpcon
  simp only [one_pow] at hqcon
  change q^β % 4 = 1 at hqcon
  change q^β % 4 = (e+1)%4 at hpcon
  omega

end OddPerfect
