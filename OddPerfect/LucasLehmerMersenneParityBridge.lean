module

public import Mathlib.NumberTheory.LucasLehmer
public import OddPerfect.Even
public import OddPerfect.ParityDichotomy
public import OddPerfect.Euler

/-!
# Lucas–Lehmer, Mersenne Primes, Near-Perfect Families, and Odd-Perfect Parity Bridge

This module bridges Mathlib's Lucas–Lehmer primality test (`Mathlib.NumberTheory.LucasLehmer`)
with the project's Euclid–Euler classification (`OddPerfect.Even`), even near-perfect families
(`OddPerfect.ParityDichotomy`), and Euler special-prime constraints (`OddPerfect.Euler`).
-/

public section

namespace OddPerfect

/-- Bridge between the Lucas–Lehmer test, Mersenne primes, even perfect and near-perfect
families, and the conditional classification of all perfect numbers under `¬ existsOddPerfect`. -/
theorem lucasLehmer_mersenne_prime_and_nearPerfect_families :
    (∀ p : ℕ, 3 ≤ p → (LucasLehmerTest p ↔ (mersenne p).Prime)) ∧
    (∀ p : ℕ, 2 ≤ p → LucasLehmerTest p →
      (mersenne p).Prime ∧
      Even (2 ^ (p - 1) * mersenne p) ∧
      Nat.Perfect (2 ^ (p - 1) * mersenne p) ∧
      NearPerfectWith (2 ^ p * mersenne p) (2 ^ p) ∧
      NearPerfectWith (2 ^ (p - 1) * (mersenne p) ^ 2) (mersenne p)) ∧
    (¬ existsOddPerfect →
      ∀ n : ℕ,
        Nat.Perfect n ↔
          n = 6 ∨ ∃ p : ℕ, 3 ≤ p ∧ p.Prime ∧ LucasLehmerTest p ∧ n = 2 ^ (p - 1) * mersenne p) := by
  refine ⟨fun p hp3 => ⟨lucas_lehmer_sufficiency p (by omega), lucas_lehmer_necessity p hp3⟩,
    fun p hp2 hll => ?_, fun hno n => ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = k + 1 := ⟨p - 1, by omega⟩
    have hprime : (mersenne (k + 1)).Prime := lucas_lehmer_sufficiency (k + 1) (by omega) hll
    have heven_perf : Even (2 ^ k * mersenne (k + 1)) ∧ Nat.Perfect (2 ^ k * mersenne (k + 1)) :=
      Theorems100.Nat.even_and_perfect_iff.mpr ⟨k, hprime, rfl⟩
    refine ⟨hprime, heven_perf.1, heven_perf.2,
      mersenne_nearPerfect_two_pow_mul (k := k) (by omega) hprime,
      mersenne_nearPerfect_mul_sq hprime⟩
  · rw [perfect_iff_mersenne_of_not_existsOddPerfect hno n]
    constructor
    · rintro ⟨k, hprime, rfl⟩
      match k with
      | 0 =>
        exfalso
        exact Nat.not_prime_one hprime
      | 1 =>
        exact Or.inl (by decide)
      | k + 2 =>
        refine Or.inr ⟨k + 3, by omega, Nat.Prime.of_mersenne hprime,
          lucas_lehmer_necessity (k + 3) (by omega) hprime, rfl⟩
    · rintro (rfl | ⟨p, hp3, _, hll, rfl⟩)
      · exact ⟨1, by decide, by decide⟩
      · obtain ⟨k, hk⟩ : ∃ k : ℕ, p = k + 1 := ⟨p - 1, by omega⟩
        have hprime : (mersenne (k + 1)).Prime := by
          rw [← hk]
          exact lucas_lehmer_sufficiency p (by omega) hll
        exact ⟨k, hprime, by rw [hk]; rfl⟩

/-- Every Mersenne number `mersenne p` with `p ≥ 2` satisfies `mersenne p ≡ 3 [MOD 4]`,
so it can never equal Euler's special prime (`q % 4 = 1`) of an odd perfect number `N`.
Consequently, any Mersenne prime dividing `N` has positive even valuation in `N`,
and its square divides `N`. -/
theorem odd_perfect_mersenne_not_euler_and_even_valuation {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) :
    ∀ p : ℕ, 2 ≤ p →
      mersenne p % 4 = 3 ∧
      ((mersenne p).Prime → mersenne p ∣ N →
        Even (N.factorization (mersenne p)) ∧
        2 ≤ N.factorization (mersenne p) ∧
        (mersenne p) ^ 2 ∣ N) := by
  intro p hp2
  have hmod : mersenne p % 4 = 3 := mersenne_mod_four hp2
  refine ⟨hmod, fun hm_prime hm_dvd => ?_⟩
  obtain ⟨q, _, hq4, _, hEven⟩ := euler_exponents ho hN
  have hne : mersenne p ≠ q := by omega
  have heven : Even (N.factorization (mersenne p)) := hEven (mersenne p) hne
  have hpos : 0 < N.factorization (mersenne p) :=
    hm_prime.factorization_pos_of_dvd ho.pos.ne' hm_dvd
  have ⟨t, ht⟩ := heven
  have h2le : 2 ≤ N.factorization (mersenne p) := by omega
  have hdvd_sq : (mersenne p) ^ 2 ∣ N :=
    dvd_trans (Nat.pow_dvd_pow (mersenne p) h2le) (Nat.ordProj_dvd N (mersenne p))
  exact ⟨heven, h2le, hdvd_sq⟩

end OddPerfect
