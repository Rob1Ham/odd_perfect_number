module

public import OddPerfect.ParityDichotomy
public import OddPerfect.DeficientFiniteness
public import OddPerfect.NearPerfectFinite
public import OddPerfect.Dickson

/-!
# Parity Dichotomy and Fixed-Rank Finiteness for Deficient-Perfect & Near-Perfect Numbers

Standalone public entry point for `parity-finiteness-breakout`, packaging:
1. Infinite and conditional even families at unbounded `2`-adic valuation
   (`pow_two_deficientPerfect`, `thabit_deficientPerfect`,
   `mersenne_nearPerfect_two_pow_mul`, `mersenne_nearPerfect_mul_sq`,
   `not_deficientPerfectWith_of_perfect_dvd`).
2. Weighted prefix product-gap engine (`labels_bounded_of_weighted_no_balanced_prefix`).
3. Unrestricted-parity `(k, A)`-finiteness and explicit upper bounds for both
   deficient-perfect and near-perfect pairs (`ω(n) ≤ k`, `v₂(n) ≤ A`), answering
   Yang and Togbé (2023, §6).
4. Explicit odd fixed-rank bounds and finiteness (`A = 0`), resolving Dutta and
   Saikia's Conjecture 3.2 (2020) with effective bound `(4(k + 1))^(4^(k + 1))`,
   alongside odd near-perfect finiteness and Dickson's odd perfect finiteness.
-/

public section

namespace ParityFiniteness

open OddPerfect ArithmeticFunction

/-- Infinite even `k = 1` deficient-perfect family `(2 ^ a, 1)` (`a ≥ 1`). -/
theorem even_pow_two_deficientPerfect {a : ℕ} (ha : 1 ≤ a) :
    DeficientPerfectWith (2 ^ a) 1 :=
  OddPerfect.pow_two_deficientPerfect ha

/-- Conditional even `k = 2` Thabit-prime deficient-perfect family. -/
theorem even_thabit_deficientPerfect {a : ℕ} (ha : 1 ≤ a) (hq : (3 * 2 ^ a - 1).Prime) :
    DeficientPerfectWith (2 ^ a * (3 * 2 ^ a - 1)) (2 ^ a) :=
  OddPerfect.thabit_deficientPerfect ha hq

/-- Conditional even `k = 2` Mersenne-prime near-perfect families. -/
theorem even_mersenne_nearPerfect_families {k : ℕ} (hk : 1 ≤ k)
    (hq : (mersenne (k + 1)).Prime) :
    NearPerfectWith (2 ^ (k + 1) * mersenne (k + 1)) (2 ^ (k + 1)) ∧
    NearPerfectWith (2 ^ k * mersenne (k + 1) ^ 2) (mersenne (k + 1)) :=
  ⟨OddPerfect.mersenne_nearPerfect_two_pow_mul hk hq,
   OddPerfect.mersenne_nearPerfect_mul_sq hq⟩

/-- No multiple of a perfect number is deficient-perfect. -/
theorem not_deficientPerfect_of_perfect_dvd {P n d : ℕ} (hP : P.Perfect) (hdvd : P ∣ n) :
    ¬ DeficientPerfectWith n d :=
  OddPerfect.not_deficientPerfectWith_of_perfect_dvd hP hdvd

/-- Explicit size bound for any deficient-perfect pair `(n, d)` with `ω(n) ≤ k` and `v₂(n) ≤ A`. -/
theorem deficientPerfect_le_of_bounded_rank_two_val {n d k A : ℕ}
    (h : DeficientPerfectWith n d) (hk : n.primeFactors.card ≤ k) (hA : n.factorization 2 ≤ A) :
    n ≤ 2 ^ A * (max 1 (weightedLabelBound (2 * k + 1) (2 ^ (A + 1)) (2 * k + 1) 1)) ^ k :=
  h.le_of_bounded_prime_count_two_val hk hA

/-- Explicit size bound for any near-perfect pair `(n, d)` with `ω(n) ≤ k` and `v₂(n) ≤ A`. -/
theorem nearPerfect_le_of_bounded_rank_two_val {n d k A : ℕ}
    (h : NearPerfectWith n d) (hk : n.primeFactors.card ≤ k) (hA : n.factorization 2 ≤ A) :
    n ≤ 2 ^ A * (max 1 (weightedLabelBound (2 * k + 1) (2 ^ (A + 1)) (2 * k + 1) 1)) ^ k :=
  h.le_of_bounded_prime_count_two_val hk hA

/-- **Unrestricted-Parity `(k, v₂)`-Finiteness Dichotomy (Main Theorem)**:
For every `(k, A)`, both the set of deficient-perfect pairs and the set of near-perfect pairs
with `ω(n) ≤ k` and `v₂(n) ≤ A` are finite. -/
theorem finite_deficient_and_nearPerfect_of_bounded_rank_two_val (k A : ℕ) :
    Set.Finite {v : ℕ × ℕ | v.1.primeFactors.card ≤ k ∧ v.1.factorization 2 ≤ A ∧
      DeficientPerfectWith v.1 v.2} ∧
    Set.Finite {v : ℕ × ℕ | v.1.primeFactors.card ≤ k ∧ v.1.factorization 2 ≤ A ∧
      NearPerfectWith v.1 v.2} :=
  ⟨OddPerfect.finite_deficientPerfect_pairs_of_bounded_prime_count_two_val k A,
   OddPerfect.finite_nearPerfect_pairs_of_bounded_prime_count_two_val k A⟩

/-- **Dutta–Saikia Conjecture 3.2 (2020) & Explicit Odd Bound**:
Every odd deficient-perfect pair `(n, d)` with `ω(n) ≤ k` satisfies
`n ≤ (4 * (k + 1)) ^ (4 ^ (k + 1))`, and for every `k` (allowing `d = n` as well)
the set of odd solutions with `ω(n) = k` is finite. -/
theorem odd_deficientPerfect_explicit_bound_and_finiteness (k : ℕ) :
    (∀ n d : ℕ, DeficientPerfectWith n d → Odd n → n.primeFactors.card ≤ k →
      n ≤ (4 * (k + 1)) ^ (4 ^ (k + 1))) ∧
    Set.Finite {v : ℕ × ℕ | Odd v.1 ∧ v.1.primeFactors.card ≤ k ∧ DeficientPerfectWith v.1 v.2} ∧
    Set.Finite {n : ℕ | Odd n ∧ n.primeFactors.card = k ∧
      ∃ d : ℕ, 0 < d ∧ d ∣ n ∧ sigma 1 n + d = 2 * n} :=
  ⟨fun _ _ h ho hk => h.le_of_bounded_prime_count ho hk,
   OddPerfect.finite_odd_deficientPerfect_pairs_of_bounded_prime_count k,
   OddPerfect.finite_odd_deficientPerfect_of_prime_count k⟩

/-- Fixed-rank finiteness for odd near-perfect numbers (`ω(n) ≤ k`). -/
theorem odd_nearPerfect_finiteness (k : ℕ) :
    Set.Finite {n : ℕ | Odd n ∧ n.primeFactors.card ≤ k ∧ ∃ d, NearPerfectWith n d} :=
  OddPerfect.finite_odd_nearPerfect_of_bounded_prime_count k

end ParityFiniteness
