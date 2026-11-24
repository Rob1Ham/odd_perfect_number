module

public import OddPerfect.AbundancyLimit
public import OddPerfect.OchemRao
public import OddPerfect.Counts

/-! Ochem and Rao's terminal sieve branch with no prime factor below 23. -/

public section

namespace OddPerfect

/-- Lean enumerates every prime in the closed interval and compares the two
integer products exactly. -/
theorem prime_interval_23_673_certificate :
    let t := (Finset.Icc 23 673).filter Nat.Prime
    t.card = 114 ∧ (∏ p ∈ t, p) < 2 * ∏ p ∈ t, (p - 1) := by decide +kernel

/-- Terminal support case for the count sieve. Every odd perfect number
avoiding all seven odd primes below 23 has at least 115 distinct prime factors. -/
theorem prime_factor_count_avoiding_primes_below_23 {N : ℕ} (ho : Odd N)
    (hN : N.Perfect) (hcop : N.Coprime (3 * 5 * 7 * 11 * 13 * 17 * 19)) :
    115 ≤ N.primeFactors.card := by
  let t := (Finset.Icc 23 673).filter Nat.Prime
  have hsmall : ∀ p : Fin 23, p.val.Prime →
      p.val = 2 ∨ p.val ∣ 3 * 5 * 7 * 11 * 13 * 17 * 19 := by decide
  have hs (p : ℕ) (hp : p ∈ N.primeFactors) : p.Prime ∧ 23 ≤ p := by
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hd := Nat.dvd_of_mem_primeFactors hp
    refine ⟨hprime, ?_⟩
    by_contra! h
    rcases hsmall ⟨p, h⟩ hprime with h2 | hprod
    · exact ho.not_two_dvd_nat (h2 ▸ hd)
    · have hdg := Nat.dvd_gcd hd hprod
      rw [hcop] at hdg
      exact hprime.not_dvd_one hdg
  obtain ⟨hn, hprod⟩ := prime_interval_23_673_certificate
  change t.card = 114 at hn
  change (∏ p ∈ t, p) < 2 * ∏ p ∈ t, (p - 1) at hprod
  have hnum : (∏ p ∈ t, primeAbundancyLimit p) < 2 := by
    simp only [primeAbundancyLimit, Finset.prod_div_distrib, ← Nat.cast_prod]
    have hden : 0 < ∏ p ∈ t, (p - 1) := Finset.prod_pos fun _ hp =>
      Nat.sub_pos_of_lt (Finset.mem_filter.mp hp).2.one_lt
    rw [div_lt_iff₀ (by exact_mod_cast hden)]
    simpa only [Nat.cast_prod, Nat.cast_mul, Nat.cast_ofNat] using
      (Nat.cast_lt (α := ℚ)).mpr hprod
  by_contra! h
  have hc : N.primeFactors.card ≤ t.card := by omega
  exact (not_lt_of_ge (two_lt_prod_primeAbundancyLimit hN).le)
    ((prod_primeAbundancyLimit_le_interval (a := 23) (b := 673) (by decide) N.primeFactors hs hc).trans_lt hnum)

/-- On the terminal branch, the absence of 3 and the odd total factor count
improve the bound obtained from the unconditional Ochem–Rao inequality. -/
theorem total_prime_factor_count_avoiding_primes_below_23 {N : ℕ} (ho : Odd N)
    (hN : N.Perfect) (hcop : N.Coprime (3 * 5 * 7 * 11 * 13 * 17 * 19)) :
    2 * N.primeFactors.card + 65 ≤ N.primeFactorsList.length := by
  have h3 : ¬ 3 ∣ N := by
    intro hd
    have hc := Nat.dvd_gcd hd (by decide : 3 ∣ (3 * 5 * 7 * 11 * 13 * 17 * 19 : ℕ))
    rw [hcop] at hc
    exact (by decide : ¬ 3 ∣ (1 : ℕ)) hc
  have hω := prime_factor_count_avoiding_primes_below_23 ho hN hcop
  have hΩ := (ochem_rao_count_cases ho hN).2 h3
  have hpar := Nat.odd_iff.mp (odd_total_prime_factor_count ho hN)
  omega

end OddPerfect
