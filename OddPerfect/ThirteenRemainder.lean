module

public import OddPerfect.Thirteen

public section

namespace OddPerfect

/-- In the even exponent classes missed by 61, the least possible prime factor
of the 13-component's divisor sum is 23. -/
theorem prime_dvd_sigma_thirteen_pow_ge_twentyThree {e r : ℕ}
    (heven : e % 2 = 0) (hres : e % 3 ≠ 2) (hr : r.Prime)
    (hd : r ∣ ∑ d ∈ ((13 : ℕ) ^ e).divisors, d) : 23 ≤ r := by
  by_contra! hsmall
  rw [Nat.sum_divisors_prime_pow (f := fun x => x) (by decide : Nat.Prime 13)] at hd
  have criterion (t : ℕ) (ht : 0 < t)
      (block : r ∣ ∑ i ∈ Finset.range t, (13 : ℕ) ^ i)
      (prefixes : ∀ j : Fin t, (r ∣ ∑ i ∈ Finset.range j.val, (13 : ℕ) ^ i) → j.val = 0) :
      t ∣ e + 1 :=
    Nat.dvd_of_mod_eq_zero (prefixes ⟨(e + 1) % t, Nat.mod_lt _ ht⟩
      ((dvd_geom_sum_iff_remainder block _).1 hd))
  have primes : ∀ q : Fin 23, q.val.Prime →
      q.val = 2 ∨ q.val = 3 ∨ q.val = 5 ∨ q.val = 7 ∨
      q.val = 11 ∨ q.val = 13 ∨ q.val = 17 ∨ q.val = 19 := by decide
  rcases primes ⟨r, hsmall⟩ hr with h | h | h | h | h | h | h | h <;> change r = _ at h <;> subst r
  · have := criterion 2 (by decide) (by decide) (by decide)
    omega
  · have := criterion 3 (by decide) (by decide) (by decide)
    omega
  · have := criterion 4 (by decide) (by decide) (by decide)
    omega
  · have := criterion 2 (by decide) (by decide) (by decide)
    omega
  · have := criterion 10 (by decide) (by decide) (by decide)
    omega
  · rw [Finset.sum_range_succ'] at hd
    simp only [pow_succ', ← Finset.mul_sum, pow_zero] at hd
    omega
  · have := criterion 4 (by decide) (by decide) (by decide)
    omega
  · have := criterion 18 (by decide) (by decide) (by decide)
    omega

/-- Exponent ten attains the lower bound in the local divisor-sum test. -/
theorem twentyThree_dvd_sigma_thirteen_pow_ten :
    23 ∣ ∑ d ∈ ((13 : ℕ) ^ 10).divisors, d := by
  rw [Nat.sum_divisors_prime_pow (f := fun x => x) (by decide : Nat.Prime 13)]
  decide

/-- Every perfect number containing 13 falls into one of these factor-chain branches.
The final alternative supplies a prime from the 13-component itself. -/
theorem thirteen_factor_alternatives {N : ℕ} (hN : Nat.Perfect N) (h13 : 13 ∣ N) :
    7 ∣ N ∨ 61 ∣ N ∨ ∃ r : ℕ, r.Prime ∧ 23 ≤ r ∧ r ≠ 61 ∧
      r ∣ ∑ d ∈ ((13 : ℕ) ^ (N.factorization 13)).divisors, d ∧ r ∣ N := by
  let e := N.factorization 13
  have prime13 : Nat.Prime 13 := by decide
  have hn := hN.2.ne'
  have hpow : 13 ^ e ∣ N := (prime13.pow_dvd_iff_le_factorization hn).2 le_rfl
  have hnext : ¬ 13 ^ (e + 1) ∣ N := by
    rw [prime13.pow_dvd_iff_le_factorization hn]
    exact Nat.not_succ_le_self _
  by_cases hodd : e % 2 = 1
  · exact Or.inl (seven_dvd_of_exact_thirteen_pow hN hpow hnext hodd)
  by_cases hthree : e % 3 = 2
  · exact Or.inr (Or.inl (sixtyOne_dvd_of_exact_thirteen_pow hN hpow hnext hthree))
  have hpos : 1 ≤ e := (prime13.dvd_iff_one_le_factorization hn).1 h13
  have hsum : 1 < ∑ d ∈ ((13 : ℕ) ^ e).divisors, d := by
    rw [Nat.sum_divisors_prime_pow (f := fun x => x) prime13, Finset.sum_range_succ]
    have hp : 1 < (13 : ℕ) ^ e := one_lt_pow₀ (by decide) (by omega)
    omega
  obtain ⟨r, hr, hd⟩ := Nat.exists_prime_and_dvd hsum.ne'
  have hlarge := prime_dvd_sigma_thirteen_pow_ge_twentyThree (by omega) hthree hr hd
  have hdiff : r ≠ 61 := by
    rintro rfl
    exact hthree ((sixtyOne_dvd_sigma_thirteen_pow_iff e).1 hd)
  exact Or.inr (Or.inr ⟨r, hr, hlarge, hdiff, hd,
    dvd_perfect_of_exact_prime_pow hN prime13 hpow hnext hr (hr.odd_of_ne_two (by omega)) hd⟩)

end OddPerfect
