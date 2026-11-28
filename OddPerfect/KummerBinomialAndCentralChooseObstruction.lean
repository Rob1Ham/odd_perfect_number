module

public import OddPerfect.PadicValuationConservationAndLegendreFactorial
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Digits.Defs

/-!
# Kummer's Theorem for Dyadic Binomial Valuations and Central Choose Obstructions

Establishes two unconditional theorems using Kummer's theorem in base `2` via
`sub_one_mul_multiplicity_choose_eq_sub_sum_digits'` (without deprecated `padicValNat_*` aliases):

1. `OddPerfect.kummer_dyadic_choose_and_central_binomial_laws`:
   Evaluates `multiplicity 2 (Nat.choose (a + b) a)` as
   `(Nat.digits 2 a).sum + (Nat.digits 2 b).sum - (Nat.digits 2 (a + b)).sum`, and specializes to
   central binomial coefficients `Nat.choose (2 * n) n` for `1 ≤ n`, proving
   `multiplicity 2 (Nat.choose (2 * n) n) = (Nat.digits 2 n).sum`, parity (`Even`), exact
   divisibility `2 ^ (Nat.digits 2 n).sum ∣ Nat.choose (2 * n) n`, and `Nat.choose (2 * n) n < 4 ^ n`.
2. `OddPerfect.odd_perfect_central_choose_and_double_factorial_profile`:
   Specializes the Kummer central binomial laws to `ω = N.primeFactors.card` for any odd perfect
   number `N` and combines them with `odd_perfect_legendre_factorial_dyadic_radical_bound` to relate
   `multiplicity 2 ((2 * ω)!)`, `multiplicity 2 (2 ^ ω * ω!)`, `Nat.choose (2 * ω) ω`, `4 ^ ω`,
   and the radical lower bound `3 * 2 ^ (2 * ω - (Nat.digits 2 ω).sum) < rad`.
-/

public section

namespace OddPerfect

private theorem sum_digits_two_mul_two {n : ℕ} (hn : 1 ≤ n) :
    (Nat.digits 2 (2 * n)).sum = (Nat.digits 2 n).sum := by
  have hmod : (2 * n) % 2 = 0 := by omega
  have hdiv : (2 * n) / 2 = n := by omega
  rw [Nat.digits_def' (by decide : 1 < 2) (by omega : 0 < 2 * n), hmod, hdiv, List.sum_cons,
    zero_add]

/-- Kummer's dyadic valuation formula for binomial coefficients and its specialization to
central binomial coefficients `Nat.choose (2 * n) n` for `n ≥ 1`. -/
theorem kummer_dyadic_choose_and_central_binomial_laws :
    (∀ a b : ℕ,
      multiplicity 2 (Nat.choose (a + b) a) =
        (Nat.digits 2 a).sum + (Nat.digits 2 b).sum - (Nat.digits 2 (a + b)).sum) ∧
    (∀ n : ℕ, 1 ≤ n →
      multiplicity 2 (Nat.choose (2 * n) n) = (Nat.digits 2 n).sum ∧
      1 ≤ multiplicity 2 (Nat.choose (2 * n) n) ∧
      Even (Nat.choose (2 * n) n) ∧
      2 ^ (Nat.digits 2 n).sum ∣ Nat.choose (2 * n) n ∧
      2 ^ (Nat.digits 2 n).sum ≤ Nat.choose (2 * n) n ∧
      Nat.choose (2 * n) n < 4 ^ n) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkummer : ∀ a b : ℕ,
      multiplicity 2 (Nat.choose (a + b) a) =
        (Nat.digits 2 a).sum + (Nat.digits 2 b).sum - (Nat.digits 2 (a + b)).sum := by
    intro a b
    have h := sub_one_mul_multiplicity_choose_eq_sub_sum_digits' (p := 2) (k := a) (n := b)
    simpa [add_comm b a] using h
  refine ⟨hkummer, fun n hn => ?_⟩
  have h2n_digits : (Nat.digits 2 (2 * n)).sum = (Nat.digits 2 n).sum :=
    sum_digits_two_mul_two hn
  have hmult : multiplicity 2 (Nat.choose (2 * n) n) = (Nat.digits 2 n).sum := by
    have h := hkummer n n
    rw [show n + n = 2 * n by omega, h2n_digits] at h
    omega
  have hleg : multiplicity 2 n.factorial = n - (Nat.digits 2 n).sum := by
    simpa using Nat.Prime.sub_one_mul_multiplicity_factorial (n := n) Nat.prime_two
  have hdig_le : (Nat.digits 2 n).sum ≤ n := Nat.digit_sum_le 2 n
  have hlt : multiplicity 2 n.factorial < n := by
    simpa using sub_one_mul_multiplicity_factorial_lt_of_ne_zero 2 (by omega : n ≠ 0)
  have hdig_ge1 : 1 ≤ (Nat.digits 2 n).sum := by omega
  have hmult_ge1 : 1 ≤ multiplicity 2 (Nat.choose (2 * n) n) := by omega
  have hchoose_pos : 0 < Nat.choose (2 * n) n := Nat.choose_pos (by omega)
  have hdvd : 2 ^ (Nat.digits 2 n).sum ∣ Nat.choose (2 * n) n := by
    rw [Nat.pow_dvd_iff_le_multiplicity (by decide : (2 : ℕ) ≠ 1) hchoose_pos.ne', hmult]
  have heven : Even (Nat.choose (2 * n) n) := by
    have h2dvd : 2 ∣ Nat.choose (2 * n) n :=
      dvd_trans (pow_dvd_pow 2 hdig_ge1) (by simpa using hdvd)
    exact even_iff_two_dvd.mpr h2dvd
  have hle : 2 ^ (Nat.digits 2 n).sum ≤ Nat.choose (2 * n) n :=
    Nat.le_of_dvd hchoose_pos hdvd
  have hlt4 : Nat.choose (2 * n) n < 4 ^ n := by
    have hsum : (∑ k ∈ Finset.range (2 * n + 1), Nat.choose (2 * n) k) = 2 ^ (2 * n) :=
      Nat.sum_range_choose (2 * n)
    have h0_mem : 0 ∈ Finset.range (2 * n + 1) := Finset.mem_range.mpr (by omega)
    have hn_mem : n ∈ Finset.range (2 * n + 1) := Finset.mem_range.mpr (by omega)
    have h0_ne_n : (0 : ℕ) ≠ n := by omega
    have hsub : ({0, n} : Finset ℕ) ⊆ Finset.range (2 * n + 1) := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl <;> assumption
    have hpair_le : Nat.choose (2 * n) 0 + Nat.choose (2 * n) n ≤ 2 ^ (2 * n) := by
      rw [← hsum]
      calc Nat.choose (2 * n) 0 + Nat.choose (2 * n) n
          = ∑ k ∈ ({0, n} : Finset ℕ), Nat.choose (2 * n) k := by
              rw [Finset.sum_pair h0_ne_n]
        _ ≤ ∑ k ∈ Finset.range (2 * n + 1), Nat.choose (2 * n) k :=
              Finset.sum_le_sum_of_subset hsub
    have h4pow : (4 : ℕ) ^ n = 2 ^ (2 * n) := by
      rw [show (4 : ℕ) = 2 ^ 2 by decide, ← pow_mul]
    rw [Nat.choose_zero_right] at hpair_le
    omega
  exact ⟨hmult, hmult_ge1, heven, hdvd, hle, hlt4⟩

/-- Kummer central-binomial and double-factorial dyadic profile for the distinct prime factor
count `ω = N.primeFactors.card` of an odd perfect number `N`. -/
theorem odd_perfect_central_choose_and_double_factorial_profile
    {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    let ω := N.primeFactors.card
    let rad := ∏ p ∈ N.primeFactors, p
    multiplicity 2 (Nat.choose (2 * ω) ω) = (Nat.digits 2 ω).sum ∧
    multiplicity 2 (Nat.factorial (2 * ω)) = 2 * ω - (Nat.digits 2 ω).sum ∧
    multiplicity 2 (Nat.factorial (2 * ω)) = multiplicity 2 (2 ^ ω * Nat.factorial ω) ∧
    2 ^ (Nat.digits 2 ω).sum ∣ Nat.choose (2 * ω) ω ∧
    Even (Nat.choose (2 * ω) ω) ∧
    Nat.choose (2 * ω) ω < 4 ^ ω ∧
    2 ^ (Nat.digits 2 ω).sum * 2 ^ (2 * ω - (Nat.digits 2 ω).sum) = 4 ^ ω ∧
    3 * 2 ^ (2 * ω - (Nat.digits 2 ω).sum) < rad := by
  intro ω rad
  have h5 : 5 ≤ ω := five_le_distinct_prime_factor_count ho hN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨_, hcentral⟩ := kummer_dyadic_choose_and_central_binomial_laws
  obtain ⟨hchoose_mult, _, hchoose_even, hchoose_dvd, _, hchoose_lt⟩ := hcentral ω (by omega)
  obtain ⟨_, _, _, hprod_mult, _, _, hrad_lt, _⟩ :=
    odd_perfect_legendre_factorial_dyadic_radical_bound ho hN
  have hfact2ω : multiplicity 2 (Nat.factorial (2 * ω)) = 2 * ω - (Nat.digits 2 ω).sum := by
    have hleg2ω :
        multiplicity 2 (Nat.factorial (2 * ω)) = 2 * ω - (Nat.digits 2 (2 * ω)).sum := by
      simpa using Nat.Prime.sub_one_mul_multiplicity_factorial (n := 2 * ω) Nat.prime_two
    rw [hleg2ω, sum_digits_two_mul_two (by omega)]
  have hfact_eq :
      multiplicity 2 (Nat.factorial (2 * ω)) = multiplicity 2 (2 ^ ω * Nat.factorial ω) :=
    hfact2ω.trans hprod_mult.symm
  have hdig_le : (Nat.digits 2 ω).sum ≤ ω := Nat.digit_sum_le 2 ω
  have hpow_eq : 2 ^ (Nat.digits 2 ω).sum * 2 ^ (2 * ω - (Nat.digits 2 ω).sum) = 4 ^ ω := by
    rw [← pow_add, Nat.add_sub_of_le (by omega), show (4 : ℕ) = 2 ^ 2 by decide, ← pow_mul]
  exact ⟨hchoose_mult, hfact2ω, hfact_eq, hchoose_dvd, hchoose_even, hchoose_lt, hpow_eq, hrad_lt⟩

end OddPerfect
