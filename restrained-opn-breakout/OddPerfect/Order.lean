module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.OrderOfElement
public import OddPerfect.Forcing
import Mathlib.Algebra.Ring.GeomSum

public section

namespace OddPerfect

/-- The prime divisors of the divisor sum of a prime power are determined by the
length of a geometric sum, including when the two primes coincide. -/
theorem dvd_sum_divisors_prime_pow_iff {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (e : ℕ) :
    (r ∣ ∑ d ∈ (p ^ e).divisors, d) ↔
      (if (p : ZMod r) = 1 then r ∣ e + 1 else orderOf (p : ZMod r) ∣ e + 1) := by
  let : Fact r.Prime := ⟨hr⟩
  rw [Nat.sum_divisors_prime_pow (f := fun x => x) hp, ← ZMod.natCast_eq_zero_iff]
  simp only [Nat.cast_sum, Nat.cast_pow]
  split_ifs with h
  · simp only [h, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact ZMod.natCast_eq_zero_iff _ _
  · rw [orderOf_dvd_iff_pow_eq_one]
    calc
      _ ↔ (∑ i ∈ Finset.range (e + 1), (p : ZMod r) ^ i) * ((p : ZMod r) - 1) = 0 := by
        rw [mul_eq_zero, or_iff_left (sub_ne_zero.mpr h)]
      _ ↔ _ := by rw [geom_sum_mul, sub_eq_zero]

/-- An odd prime meeting the residue or order test at the exact exponent of a
prime in a perfect number divides that number. -/
theorem dvd_perfect_of_order_test {N p r e : ℕ} (hN : Nat.Perfect N)
    (hp : p.Prime) (hr : r.Prime) (hodd : Odd r)
    (he : p ^ e ∣ N) (hex : ¬ p ^ (e + 1) ∣ N)
    (ht : if (p : ZMod r) = 1 then r ∣ e + 1 else orderOf (p : ZMod r) ∣ e + 1) :
    r ∣ N :=
  dvd_perfect_of_exact_prime_pow hN hp he hex hr hodd
    ((dvd_sum_divisors_prime_pow_iff hp hr e).2 ht)

end OddPerfect
