module

public import OddPerfect.Reciprocal
public import OddPerfect.Order
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Linarith

public section

namespace OddPerfect

open ArithmeticFunction

/-- At an odd prime dividing `q−1`, the valuation of a prime-power divisor
sum equals the valuation of its length. -/
theorem sigma_factorization_of_dvd_pred {p q a : ℕ} (hp : Nat.Prime p) (hpo : Odd p)
    (hq : Nat.Prime q) (hd : p ∣ q-1) :
    (sigma 1 (q^a)).factorization p = (a+1).factorization p := by
  let : Fact p.Prime := ⟨hp⟩
  have hnd : ¬ p ∣ q := by
    intro h
    have hs := Nat.dvd_sub h hd
    rw [show q-(q-1) = 1 by have := hq.one_lt; omega] at hs
    exact hp.not_dvd_one hs
  have hval := Nat.multiplicity_pow_sub_pow hpo hq.one_lt hd hnd (n := a+1) (by omega)
  simp only [one_pow, Nat.multiplicity_eq_factorization hp] at hval
  have hgeo : sigma 1 (q^a) * (q-1) = q^(a+1)-1 := by
    rw [sigma_one_apply_prime_pow hq]
    exact geom_sum_mul_of_one_le hq.one_lt.le _
  rw [← hgeo, Nat.factorization_mul (sigma_pos _ _ (pow_ne_zero _ hq.ne_zero)).ne'
    (by have := hq.one_lt; omega), Finsupp.add_apply] at hval
  omega

/-- The full return to an even exponent cannot occur at Euler length twice
the very same odd source prime. -/
theorem not_pure_return_at_twice_source_length {p q e a β : ℕ} (hp : p.Prime) (hpo : Odd p)
    (hq : q.Prime) (he : Even e) (hepos : 0 < e) (hout : sigma 1 (p^e) = q^β)
    (hback : p^e ∣ sigma 1 (q^a)) (hlen : a+1 = 2*p) : False := by
  have hn2 : ¬ p^2 ∣ a+1 := by
    intro h
    rw [hlen, pow_two, Nat.mul_comm 2] at h
    have hp2 := Nat.dvd_of_mul_dvd_mul_left hp.pos h
    have := Nat.le_of_dvd (by decide : 0 < 2) hp2
    have := hp.two_le
    have := Nat.odd_iff.mp hpo
    omega
  have hret := reciprocal_component_length hp hpo hq hepos hout hback
  have he2 : e = 2 := by
    by_contra h
    have hE := Nat.even_iff.mp he
    exact hn2 ((pow_dvd_pow p (by omega : 2 ≤ e-1)).trans hret)
  subst e
  have hs : sigma 1 (p^2) = p^2+p+1 := by
    rw [sigma_one_apply_prime_pow hp]
    simp [Finset.sum_range_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hβo : Odd β := by
    rcases Nat.even_or_odd β with ⟨j,hj⟩ | h
    · have heq : p^2+p+1 = (q^j)^2 := by rw [← hs, hout, hj, pow_add, pow_two]
      by_cases hle : q^j ≤ p
      · have hh := Nat.pow_le_pow_left hle 2
        nlinarith
      · have hh := Nat.pow_le_pow_left (by omega : p+1 ≤ q^j) 2
        have := hp.one_lt
        nlinarith
    · exact h
  let : Fact p.Prime := ⟨hp⟩
  have hqx : (q : ZMod p)^β = 1 := by
    rw [← Nat.cast_pow, ← hout, hs]
    simp
  let o := orderOf (q : ZMod p)
  have hoβ : o ∣ β := orderOf_dvd_of_pow_eq_one hqx
  have hoo := hβo.of_dvd_nat hoβ
  have hne : (q : ZMod p) ≠ 0 := by
    intro hz
    rw [hz, zero_pow hβo.pos.ne'] at hqx
    exact zero_ne_one hqx
  have hoc : o ∣ p-1 := ZMod.orderOf_dvd_card_sub_one hne
  have hop : o.Coprime p := by
    apply (hp.coprime_iff_not_dvd.mpr ?_).symm
    intro h
    have := Nat.le_of_dvd (by have := hp.one_lt; omega : 0 < p-1) (h.trans hoc)
    omega
  have hqone : (q : ZMod p) = 1 := by
    by_contra h
    have hpd : p ∣ sigma 1 (q^a) := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hback
    rw [sigma_one_apply, dvd_sum_divisors_prime_pow_iff hq hp] at hpd
    simp only [h, ite_false, hlen] at hpd
    have ho2 := hop.dvd_of_dvd_mul_right hpd
    have hone : o = 1 := by
      have := Nat.le_of_dvd (by decide : 0 < 2) ho2
      have := Nat.odd_iff.mp hoo
      omega
    exact h (orderOf_eq_one_iff.mp hone)
  have hcon : q ≡ 1 [MOD p] := (ZMod.natCast_eq_natCast_iff q 1 p).mp (by simpa using hqone)
  have hdiv : p ∣ q-1 := (Nat.modEq_iff_dvd' hq.one_lt.le).mp hcon.symm
  have hval := sigma_factorization_of_dvd_pred (a := a) hp hpo hq hdiv
  apply hn2
  apply (hp.pow_dvd_iff_le_factorization (by omega : a+1 ≠ 0)).mpr
  rw [← hval]
  exact (hp.pow_dvd_iff_le_factorization (sigma_pos _ _ (pow_ne_zero _ hq.ne_zero)).ne').mp hback

end OddPerfect
