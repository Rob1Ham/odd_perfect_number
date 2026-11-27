module

public import OddPerfect.ChainAbundancy
public import OddPerfect.Spoof

/-! # Divisibility by three in Descartes factorizations of small support

The limiting abundancy of the six smallest primes greater than three is below
two. This forces three into the support of any Descartes number with at most
six distinct prime divisors.
-/

public section

namespace OddPerfect.Submissions

open ArithmeticFunction

/-- An odd Descartes number with at most six distinct prime divisors is divisible by
three. If three were absent, the limiting abundancy of its support could be no
larger than that of the six primes from five through nineteen. -/
theorem three_dvd_of_spoof_card_le_six {m w : ℕ} (h : SingleCompositeSpoof m w)
    (hc : (m * w).primeFactors.card ≤ 6) : 3 ∣ m * w := by
  by_contra h3
  have hn : 1 < m * w := h.one_lt.trans_le (Nat.le_mul_of_pos_left w h.odd_left.pos)
  have hs (p : ℕ) (hp : p ∈ (m * w).primeFactors) : p.Prime ∧ 5 ≤ p := by
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hodd := Nat.odd_iff.mp ((h.odd_left.mul h.odd_right).of_dvd_nat hpd)
    have hne : p ≠ 3 := fun heq => h3 (heq ▸ hpd)
    exact ⟨hprime, by have := hprime.two_le; omega⟩
  have hcap := prod_primeAbundancyLimit_le_interval (a := 5) (b := 19)
    (by decide) (m * w).primeFactors hs
    (hc.trans (by decide +kernel : 6 ≤ ((Finset.Icc 5 19).filter Nat.Prime).card))
  have hsum : (2 : ℚ) < (sigma 1 (m * w) : ℚ) / (m * w : ℕ) := by
    rw [lt_div_iff₀ (by exact_mod_cast (show 0 < m * w by omega))]
    exact_mod_cast h.true_sigma_gt
  exact (hsum.trans ((FactorBudget.abundancy_lt_prod_limits hn).trans_le hcap)).not_ge
    (by decide +kernel)

end OddPerfect.Submissions
