module

public import OddPerfect.ZelinskyFullSlope
public import OddPerfect.SixthPowerBounds

public section

namespace OddPerfect

/-- A sixth-power-free candidate has at least 1179 prime factors, counted with multiplicity. -/
theorem sixthPowerFree_total_prime_factor_count {N : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) : 1179 ≤ N.primeFactorsList.length := by
  have hno : ¬ ∃ p : ℕ, p.Prime ∧ p ^ 6 ∣ N := fun ⟨p, hp, hd⟩ => hfree p hp hd
  have h3 : ¬ 3 ∣ N := fun hd =>
    hno (prime_sixth_power_dvd_of_small_factor ho hN (by decide : 2 ≤ 3) hd (by decide))
  obtain ⟨h443, _, _⟩ := (sixth_power_or_large_support ho hN).resolve_left hno
  have hslope := cyclotomic_slope_three_free ho hN h3
  omega

/-- The three-free Clayton–Hansen slope when the counted large sources are sufficiently numerous. -/
theorem clayton_hansen_three_free_of_large_sources {N q : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r, r ≠ q → Even (N.factorization r)) (h3 : ¬ 3 ∣ N)
    (hcount : N.primeFactors.card ≤ 76 * (twoModThreeLargeSources N q).card + 5) :
    51 * N.primeFactors.card ≤ 19 * N.primeFactorsList.length + 46 := by
  have h := (sharpened_cyclotomic_slope_three_free ho hN hq hq4 he hev h3).2
  omega

/-- Up to one sixth of the support may be exceptional for Zelinsky's three-free slope. -/
theorem zelinsky_three_five_free_of_square_source_count {N : ℕ} (ho : Odd N) (hN : N.Perfect)
    (h3 : ¬ 3 ∣ N) (h5 : ¬ 5 ∣ N)
    (hcount : 6 * ((squareSources N).filter (· % 5 = 1)).card ≤ N.primeFactors.card) :
    302 * N.primeFactors.card ≤ 113 * N.primeFactorsList.length + 286 := by
  obtain ⟨q, hq, hq4, he, hev⟩ := euler_exponents ho hN
  have hmulti := multi_block_coupled_three_five_free ho hN hq hq4 he hev h3 h5
  have hbase := cyclotomic_slope_three_free ho hN h3
  omega

/-- At rank at least 97, the same one-sixth allowance gives the stronger Clayton–Hansen slope. -/
theorem clayton_hansen_three_five_free_of_square_source_count {N : ℕ} (ho : Odd N)
    (hN : N.Perfect) (h3 : ¬ 3 ∣ N) (h5 : ¬ 5 ∣ N) (hrank : 97 ≤ N.primeFactors.card)
    (hcount : 6 * ((squareSources N).filter (· % 5 = 1)).card ≤ N.primeFactors.card) :
    51 * N.primeFactors.card ≤ 19 * N.primeFactorsList.length + 46 := by
  obtain ⟨q, hq, hq4, he, hev⟩ := euler_exponents ho hN
  have hmulti := multi_block_coupled_three_five_free ho hN hq hq4 he hev h3 h5
  omega

end OddPerfect
