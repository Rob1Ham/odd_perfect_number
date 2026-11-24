module

public import OddPerfect.IndexTwo
public import OddPerfect.Primitive
import Mathlib.FieldTheory.Finite.Basic

public section

namespace OddPerfect

open ArithmeticFunction

private theorem eq_one_of_odd_dvd_two_pow {d k : ℕ} (ho : Odd d) (hd : d ∣ 2 ^ k) :
    d = 1 := by
  obtain ⟨t, _, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  by_cases ht : t = 0
  · simp [ht]
  · exact (ho.not_two_dvd_nat (dvd_pow_self _ ht)).elim

/-- If an even-exponent component can feed only primes `i,q`, and `i−1` is a
power of two, its length is prime and is the order at `q`. -/
theorem prime_length_of_two_target_component {p e i q a k : ℕ} (hp : Nat.Prime p)
    (he : Even e) (hepos : 0 < e) (hi : Nat.Prime i) (hik : i - 1 = 2 ^ k)
    (hq : Nat.Prime q) (hσ : sigma 1 (p ^ e) ∣ i * q ^ a) :
    (e + 1).Prime ∧ orderOf (p : ZMod q) = e + 1 ∧ e + 1 ∣ q - 1 := by
  have ho : Odd (e + 1) := Nat.odd_iff.mpr (by have := Nat.even_iff.mp he; omega)
  have force (l : ℕ) (hl : Nat.Prime l) (j : ℕ) (hd : l ^ (j+1) ∣ e+1) :
      orderOf (p : ZMod q) = l ^ (j+1) ∧ l ^ (j+1) ∣ q-1 := by
    have hlo := ho.of_dvd_nat ((dvd_pow_self l (by omega : j+1 ≠ 0)).trans hd)
    have hbig : 1 < l ^ (j+1) := one_lt_pow₀ hl.one_lt (by omega)
    obtain ⟨r, hr, hor, hcon⟩ := exists_prime_order_prime_pow hp.one_lt hl hlo j
    have hne : (p : ZMod r) ≠ 1 := by intro h; simp [h] at hor; omega
    have hdiv : r ∣ sigma 1 (p ^ e) := by
      rw [sigma_one_apply, dvd_sum_divisors_prime_pow_iff hp hr]
      simpa [hne, hor] using hd
    rcases hr.dvd_mul.mp (hdiv.trans hσ) with hri | hrq
    · have hri := (Nat.prime_dvd_prime_iff_eq hr hi).mp hri
      subst r
      rw [hik] at hcon
      have := eq_one_of_odd_dvd_two_pow hlo.pow hcon
      omega
    · have hrq := (Nat.prime_dvd_prime_iff_eq hr hq).mp (hr.dvd_of_dvd_pow hrq)
      subst r
      exact ⟨hor, hcon⟩
  have force_prime (l : ℕ) (hl : Nat.Prime l) (hd : l ∣ e+1) :
      orderOf (p : ZMod q) = l ∧ l ∣ q - 1 := by
    simpa using force l hl 0 (by simpa using hd)
  obtain ⟨l, hl, hd⟩ := Nat.exists_prime_and_dvd (by omega : e+1 ≠ 1)
  obtain ⟨hor, hcon⟩ := force_prime l hl hd
  suffices h : e+1 = l by simpa [h] using And.intro hl (And.intro hor hcon)
  obtain ⟨b, hb⟩ := hd
  by_contra h
  have hb1 : b ≠ 1 := by rintro rfl; simp at hb; omega
  obtain ⟨r, hr, hrb⟩ := Nat.exists_prime_and_dvd hb1
  have hlr := (force_prime r hr (hrb.trans (hb ▸ dvd_mul_left _ _))).1
  have hrl : r = l := hlr.symm.trans hor
  have hlb : l ∣ b := hrl ▸ hrb
  have hsquare : l ^ (1+1) ∣ e+1 := by rw [hb, pow_two]; exact Nat.mul_dvd_mul_left _ hlb
  have hdiff := (force l hl 1 hsquare).1
  rw [hor, pow_two] at hdiff
  have := Nat.mul_lt_mul_of_pos_left hl.one_lt hl.pos
  omega

/-- If the small prime contributes to this outgoing sum, it is the exact
length, and the base is one modulo that prime. -/
theorem exceptional_small_index_component {p e i q a k : ℕ} (hp : Nat.Prime p)
    (he : Even e) (hepos : 0 < e) (hi : Nat.Prime i) (hik : i - 1 = 2 ^ k)
    (hq : Nat.Prime q) (hσ : sigma 1 (p ^ e) ∣ i * q ^ a) (hd : i ∣ sigma 1 (p ^ e)) :
    e + 1 = i ∧ (p : ZMod i) = 1 ∧ i ∣ q - 1 := by
  obtain ⟨hl, _, hcon⟩ := prime_length_of_two_target_component hp he hepos hi hik hq hσ
  have ho : Odd (e+1) := Nat.odd_iff.mpr (by have := Nat.even_iff.mp he; omega)
  let : Fact i.Prime := ⟨hi⟩
  rw [sigma_one_apply, dvd_sum_divisors_prime_pow_iff hp hi] at hd
  by_cases hone : (p : ZMod i) = 1
  · simp only [hone, ite_true] at hd
    have heq := ((Nat.prime_dvd_prime_iff_eq hi hl).mp hd).symm
    exact ⟨heq, hone, heq ▸ hcon⟩
  · simp only [hone, ite_false] at hd
    have hz : (p : ZMod i) ≠ 0 := by
      rintro h
      rw [h, orderOf_zero, zero_dvd_iff] at hd
      omega
    have hcard := ZMod.orderOf_dvd_card_sub_one hz
    rw [hik] at hcard
    exact (hone (orderOf_eq_one_iff.mp (eq_one_of_odd_dvd_two_pow (ho.of_dvd_nat hd) hcard))).elim

end OddPerfect
