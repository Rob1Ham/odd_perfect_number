module

public import OddPerfect.TothTrillion
public import OddPerfect.DeficientFourClassification
public import OddPerfect.DeficientThirdSource
public import OddPerfect.ParityDichotomy
public import OddPerfect.SixthPowerBounds
public import OddPerfect.QuasiperfectSupport
public import OddPerfect.HarmonicFinite

/-! Consequences for restricted cases of the catalog targets, checked against the
    odd_perfect_number project. The statements use the underlying divisor-sum
    equations so their hypotheses can be compared directly with the upstream definitions. -/

public section

namespace OddPerfect.CatalogCases

open ArithmeticFunction

/-- An odd nontrivial witness to the almost-perfect equation must avoid both
the size and prime-count regions of the deficient-perfect classifications. -/
theorem odd_almostPerfect_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (h : 1 + sigma 1 n = 2 * n) : 10 ^ 12 < n ∧ 5 ≤ n.primeFactors.card := by
  have hd : DeficientPerfectWith n 1 :=
    ⟨Nat.one_mem_properDivisors_iff_one_lt.mpr hn, by omega⟩
  constructor
  · by_contra! hsmall
    have hi := ((deficientPerfect_below_trillion_iff ho hsmall).mp hd).2
    omega
  · by_contra! hfew
    have hfour := four_le_distinct_primes_of_odd_deficientPerfect ho hd
    have hi := ((odd_deficientPerfect_four_iff ho (by omega)).mp hd).2
    omega

/-- OEIS A388012. At the boundary σ(n)/n = 5/3 the residue class 1 modulo 5
contains at least two distinct prime divisors of the witness. -/
theorem five_thirds_residue_primes {n : ℕ} (hn : 0 < n) (h : 3 * sigma 1 n = 5 * n) :
    ∃ r ∈ n.primeFactors, ∃ s ∈ n.primeFactors, r ≠ s ∧ r % 5 = 1 ∧ s % 5 = 1 := by
  have hthree : 3 ∣ n := by omega
  obtain ⟨d, hd⟩ := hthree
  have hdef : DeficientPerfectWith n d :=
    ⟨Nat.mem_properDivisors.mpr ⟨⟨3, by omega⟩, by omega⟩, by omega⟩
  have ho : Odd n := by
    apply Nat.odd_iff.mpr
    by_contra! heven
    have h6 : 6 ∣ n := by omega
    exact not_deficientPerfectWith_of_perfect_dvd (P := 6) (by decide) h6 hdef
  have hσ : Odd (sigma 1 n) := Nat.odd_iff.mpr (by have := Nat.odd_iff.mp ho; omega)
  obtain ⟨r, hr, s, hs, hrs, hr5, hs5⟩ := two_fermat_residue_primes_of_deficient_thirds ho
    ((odd_sigma_iff_square_of_odd ho).mp hσ) (by decide : Nat.Prime 5) (by decide)
    (by decide : 5 - 1 = 2 ^ 2) (by omega) h
  have hrpos := (Nat.prime_of_mem_primeFactors hr).one_lt
  have hspos := (Nat.prime_of_mem_primeFactors hs).one_lt
  exact ⟨r, hr, s, hs, hrs, by omega, by omega⟩

set_option exponentiation.threshold 3200 in
/-- Both conclusions in Ochem–Rao's catalog statement on the sixth-power-free branch. -/
theorem ochem_rao_of_sixth_power_free {n : ℕ} (ho : Odd n) (hp : n.Perfect)
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ n) :
    n > 10 ^ 1500 ∧ n.primeFactorsList.length ≥ 101 := by
  obtain ⟨_, hcount, hsize⟩ := (sixth_power_or_large_support ho hp).resolve_left
    (fun ⟨p, hprime, hd⟩ => hfree p hprime hd)
  exact ⟨lt_of_le_of_lt (Nat.pow_le_pow_right (by decide : 0 < 10) (by decide : 1500 ≤ 3136)) hsize,
    le_trans (by decide : 101 ≤ 1137) hcount⟩

/-- Necessary conditions on any witness to the catalog's quasiperfect existence question. -/
theorem quasiperfect_witness {n : ℕ} (h : sigma 1 n = 2 * n + 1) :
    Odd n ∧ IsSquare n ∧ 4 ≤ n.primeFactors.card ∧ (¬ 3 ∣ n → 7 ≤ n.primeFactors.card) := by
  have hq : Quasiperfect n := h
  obtain ⟨ho, hs⟩ := quasiperfect_odd_square hq
  exact ⟨ho, hs, four_le_primeFactors_of_quasiperfect hq,
    seven_le_primeFactors_of_quasiperfect_three_free hq⟩

/-- Any counterexample to Ore's conjecture avoids all positive prime powers. -/
theorem ore_no_prime_power {p e : ℕ} (hp : p.Prime) (he : 0 < e) :
    ¬ sigma 1 (p ^ e) ∣ (p ^ e) * sigma 0 (p ^ e) := by
  intro hh
  apply prime_pow_not_oreHarmonic hp he
  exact ⟨Nat.one_lt_pow (by omega) hp.one_lt, by simpa only [sigma_zero_apply] using hh⟩

/-- Ore's conclusion for odd harmonic integers with at most two distinct prime divisors. -/
theorem ore_odd_of_at_most_two_primes {n : ℕ} (hn : 0 < n) (ho : Odd n)
    (hh : sigma 1 n ∣ n * sigma 0 n) (hfew : n.primeFactors.card ≤ 2) : n = 1 := by
  by_contra h1
  have hH : OreHarmonic n := ⟨by omega, by simpa only [sigma_zero_apply] using hh⟩
  have := odd_oreHarmonic_three_le_primeFactors ho hH
  omega

#print axioms ore_odd_of_at_most_two_primes
#print axioms odd_almostPerfect_witness
#print axioms five_thirds_residue_primes
#print axioms ochem_rao_of_sixth_power_free
#print axioms quasiperfect_witness
#print axioms ore_no_prime_power

end OddPerfect.CatalogCases
