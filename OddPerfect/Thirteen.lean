module

public import OddPerfect.Forcing
import Mathlib.Tactic.NormNum

/-! Factor-chain steps at the exact power of 13 in a perfect number. -/

public section

namespace OddPerfect

/-- Complete blocks of geometric terms can be discarded when testing divisibility. -/
private theorem dvd_geom_sum_iff_remainder {p r t : ℕ}
    (ht : r ∣ ∑ i ∈ Finset.range t, p ^ i) (n : ℕ) :
    (r ∣ ∑ i ∈ Finset.range n, p ^ i) ↔
      r ∣ ∑ i ∈ Finset.range (n % t), p ^ i := by
  have block (s : ℕ) : (r ∣ ∑ i ∈ Finset.range (s + t), p ^ i) ↔
      r ∣ ∑ i ∈ Finset.range s, p ^ i := by
    rw [Finset.sum_range_add]
    simp_rw [pow_add]
    rw [← Finset.mul_sum]
    exact Nat.dvd_add_left (dvd_mul_of_dvd_right ht _)
  have blocks (s q : ℕ) : (r ∣ ∑ i ∈ Finset.range (s + t * q), p ^ i) ↔
      r ∣ ∑ i ∈ Finset.range s, p ^ i := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc]
      exact (block _).trans ih
  simpa only [Nat.mod_add_div] using blocks (n % t) (n / t)

/-- The 13-component supplies a factor 61 exactly in one exponent class modulo 3. -/
theorem sixtyOne_dvd_sigma_thirteen_pow_iff (e : ℕ) :
    (61 ∣ ∑ d ∈ ((13 : ℕ) ^ e).divisors, d) ↔ e % 3 = 2 := by
  rw [Nat.sum_divisors_prime_pow (f := fun x => x) (by decide : Nat.Prime 13),
    dvd_geom_sum_iff_remainder (t := 3) (by decide)]
  have cases : (e + 1) % 3 = 0 ∨ (e + 1) % 3 = 1 ∨ (e + 1) % 3 = 2 := by omega
  rcases cases with h | h | h <;> rw [h] <;> norm_num [Finset.sum_range_succ] <;> omega

/-- The 13-component supplies a factor 7 exactly in the odd exponent classes. -/
theorem seven_dvd_sigma_thirteen_pow_iff (e : ℕ) :
    (7 ∣ ∑ d ∈ ((13 : ℕ) ^ e).divisors, d) ↔ e % 2 = 1 := by
  rw [Nat.sum_divisors_prime_pow (f := fun x => x) (by decide : Nat.Prime 13),
    dvd_geom_sum_iff_remainder (t := 2) (by decide)]
  have cases : (e + 1) % 2 = 0 ∨ (e + 1) % 2 = 1 := by omega
  rcases cases with h | h <;> rw [h] <;> norm_num [Finset.sum_range_succ] <;> omega

theorem sixtyOne_dvd_of_exact_thirteen_pow {N e : ℕ} (hN : Nat.Perfect N)
    (hpow : 13 ^ e ∣ N) (hnext : ¬ 13 ^ (e + 1) ∣ N) (he : e % 3 = 2) :
    61 ∣ N :=
  dvd_perfect_of_exact_prime_pow hN (by decide) hpow hnext (by decide)
    ⟨30, rfl⟩ ((sixtyOne_dvd_sigma_thirteen_pow_iff e).2 he)

theorem seven_dvd_of_exact_thirteen_pow {N e : ℕ} (hN : Nat.Perfect N)
    (hpow : 13 ^ e ∣ N) (hnext : ¬ 13 ^ (e + 1) ∣ N) (he : e % 2 = 1) :
    7 ∣ N :=
  dvd_perfect_of_exact_prime_pow hN (by decide) hpow hnext (by decide)
    ⟨3, rfl⟩ ((seven_dvd_sigma_thirteen_pow_iff e).2 he)

/-- The exact-square milestone. -/
theorem sixtyOne_dvd_of_exact_thirteen_sq {N : ℕ} (hN : Nat.Perfect N)
    (h169 : 169 ∣ N) (h2197 : ¬ 2197 ∣ N) : 61 ∣ N :=
  sixtyOne_dvd_of_exact_thirteen_pow (e := 2) hN h169 h2197 (by decide)

end OddPerfect
