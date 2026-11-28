module

public import OddPerfect.CountSeeds
public import OddPerfect.OchemRao

/-! Exhaustive small-prime seeds for larger total-factor budgets. -/

public section

namespace OddPerfect

/-- A certified product of limiting abundancies bounds the size of a support
whose prime divisors are all at least the lower endpoint. -/
theorem support_exceeds_prime_interval {N a b : ℕ} (hN : N.Perfect) (hb : 1 < b)
    (hfloor : ∀ p ∈ N.primeFactors, a ≤ p)
    (hnum : (∏ p ∈ (Finset.Icc a b).filter Nat.Prime, primeAbundancyLimit p) ≤ 2) :
    ((Finset.Icc a b).filter Nat.Prime).card < N.primeFactors.card := by
  by_contra! h
  have hbound := prod_primeAbundancyLimit_le_interval hb N.primeFactors
    (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp, hfloor p hp⟩) h
  exact (two_lt_prod_primeAbundancyLimit hN).not_ge (hbound.trans hnum)

/-- The 3-free Ochem–Rao inequality improves the two-seed cutoff to 36. -/
theorem total_count_of_three_five_free {N : ℕ} (ho : Odd N) (hN : N.Perfect)
    (h3 : ¬ 3 ∣ N) (h5 : ¬ 5 ∣ N) : 37 ≤ N.primeFactorsList.length := by
  have := fifteen_distinct_of_three_five_free ho hN h3 h5
  have := (ochem_rao_count_cases ho hN).2 h3
  omega

/-- Completing the three divisibility cases at 3, 5 and 7 suffices for
any exclusion budget below 69. -/
theorem counts_of_three_five_seven_free {N : ℕ} (ho : Odd N) (hN : N.Perfect)
    (h3 : ¬ 3 ∣ N) (h5 : ¬ 5 ∣ N) (h7 : ¬ 7 ∣ N) :
    27 ≤ N.primeFactors.card ∧ 69 ≤ N.primeFactorsList.length := by
  have hfloor : ∀ p ∈ N.primeFactors, 11 ≤ p := by
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hd := Nat.dvd_of_mem_primeFactors hp
    have hodd := (ho.of_dvd_nat hd).not_two_dvd_nat
    have hcase : ∀ i : Fin 11, i.val.Prime → ¬ 2 ∣ i.val → i.val = 3 ∨ i.val = 5 ∨ i.val = 7 := by decide
    by_contra! h
    rcases hcase ⟨p, h⟩ hp' hodd with h | h | h
    · exact h3 (h ▸ hd)
    · exact h5 (h ▸ hd)
    · exact h7 (h ▸ hd)
  have hnum : (∏ p ∈ (Finset.Icc 11 113).filter Nat.Prime, primeAbundancyLimit p) ≤ 2 := by decide +kernel
  have hc : ((Finset.Icc 11 113).filter Nat.Prime).card = 26 := by decide +kernel
  have hbound := support_exceeds_prime_interval hN (by decide : 1 < 113) hfloor hnum
  have := (ochem_rao_count_cases ho hN).2 h3
  have := Nat.odd_iff.mp (odd_total_prime_factor_count ho hN)
  omega

/-- The four seeds used in Ochem–Rao's 2012 total-count theorem suffice
for budgets below 105 using their later analytic count inequality. -/
theorem counts_of_three_five_seven_eleven_free {N : ℕ} (ho : Odd N) (hN : N.Perfect)
    (h3 : ¬ 3 ∣ N) (h5 : ¬ 5 ∣ N) (h7 : ¬ 7 ∣ N) (h11 : ¬ 11 ∣ N) :
    41 ≤ N.primeFactors.card ∧ 105 ≤ N.primeFactorsList.length := by
  have hfloor : ∀ p ∈ N.primeFactors, 13 ≤ p := by
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hd := Nat.dvd_of_mem_primeFactors hp
    have hodd := (ho.of_dvd_nat hd).not_two_dvd_nat
    have hcase : ∀ i : Fin 13, i.val.Prime → ¬ 2 ∣ i.val →
        i.val = 3 ∨ i.val = 5 ∨ i.val = 7 ∨ i.val = 11 := by decide
    by_contra! h
    rcases hcase ⟨p, h⟩ hp' hodd with h | h | h | h
    · exact h3 (h ▸ hd)
    · exact h5 (h ▸ hd)
    · exact h7 (h ▸ hd)
    · exact h11 (h ▸ hd)
  have hnum : (∏ p ∈ (Finset.Icc 13 197).filter Nat.Prime, primeAbundancyLimit p) ≤ 2 := by decide +kernel
  have hc : ((Finset.Icc 13 197).filter Nat.Prime).card = 40 := by decide +kernel
  have hbound := support_exceeds_prime_interval hN (by decide : 1 < 197) hfloor hnum
  have := (ochem_rao_count_cases ho hN).2 h3
  have := Nat.odd_iff.mp (odd_total_prime_factor_count ho hN)
  omega

end OddPerfect
