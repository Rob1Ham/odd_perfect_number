module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc

public section

namespace OddPerfect

open ArithmeticFunction

/-- The divisor sum of a full coprime component divides twice the perfect number. -/
theorem sum_divisors_dvd_two_mul {N a b : ℕ} (hN : Nat.Perfect N)
    (hprod : N = a * b) (hab : a.Coprime b) : (∑ d ∈ a.divisors, d) ∣ 2 * N := by
  rw [← (Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN, hprod, hab.sum_divisors_mul]
  exact Nat.dvd_mul_right _ _

/-- Every odd divisor of the component's divisor sum divides the perfect number.
This includes odd composite divisors and odd prime powers. -/
theorem odd_dvd_perfect_of_dvd_sum_divisors {N a b r : ℕ} (hN : Nat.Perfect N)
    (hprod : N = a * b) (hab : a.Coprime b) (hr : Odd r)
    (hs : r ∣ ∑ d ∈ a.divisors, d) : r ∣ N :=
  hr.coprime_two_right.dvd_of_dvd_mul_left (hs.trans (sum_divisors_dvd_two_mul hN hprod hab))

/-- Extract the coprime component from an exact prime power, including exponent zero. -/
theorem exists_coprime_cofactor_of_exact_prime_pow {N p k : ℕ} (hp : Nat.Prime p)
    (hk : p ^ k ∣ N) (hnext : ¬ p ^ (k + 1) ∣ N) :
    ∃ b, N = p ^ k * b ∧ (p ^ k).Coprime b := by
  obtain ⟨b, hb⟩ := hk
  refine ⟨b, hb, (hp.coprime_pow_of_not_dvd ?_).symm⟩
  intro hpb
  apply hnext
  rw [hb, pow_succ]
  exact Nat.mul_dvd_mul_left _ hpb

/-- An odd prime in the divisor sum of the exact prime-power part is forced into `N`. -/
theorem dvd_perfect_of_exact_prime_pow {N p k r : ℕ} (hN : Nat.Perfect N) (hp : Nat.Prime p)
    (hk : p ^ k ∣ N) (hnext : ¬ p ^ (k + 1) ∣ N) (_hr : Nat.Prime r) (ho : Odd r)
    (hs : r ∣ ∑ d ∈ (p ^ k).divisors, d) : r ∣ N := by
  obtain ⟨b, hb, hcop⟩ := exists_coprime_cofactor_of_exact_prime_pow hp hk hnext
  exact odd_dvd_perfect_of_dvd_sum_divisors hN hb hcop ho hs

/-- For a perfect number with exact 3-adic exponent two, the divisor sum of nine forces 13. -/
theorem thirteen_dvd_of_exact_nine {N : ℕ} (hN : Nat.Perfect N)
    (h9 : 9 ∣ N) (h27 : ¬ 27 ∣ N) : 13 ∣ N := by
  apply dvd_perfect_of_exact_prime_pow (p := 3) (k := 2) hN (by decide) h9 h27
      (by decide) (by decide)
  rw [← sigma_one_apply, sigma_one_apply_prime_pow (by decide : Nat.Prime 3)]
  decide

end OddPerfect
