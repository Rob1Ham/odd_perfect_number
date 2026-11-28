module

public import OddPerfect.RestrainedExponents
public import OddPerfect.RestrainedThreeFreeObstruction
public import OddPerfect.RestrainedLinearElimination
public import OddPerfect.ThreeFreeRestrainedClosure
public import OddPerfect.ThreeFreeTwoLargeSources
public import OddPerfect.RestrainedThreeSquareObstruction
public import OddPerfect.RestrainedSquareSourcesOneObstruction

/-!
# Analytical Exclusion of Three-Free Restrained Odd Perfect Numbers & Two-Large-Sources Extensions

Standalone public entry point for `restrained-opn-breakout`, packaging purely
analytical (zero branch-search tree) obstructions for restrained odd perfect
candidates (`(largeSources N q).card ≤ 1`) and two-large-exponent candidates
(`(largeSources N q).card ≤ 2`):

1. `three_free_restrained_excluded`:
   Unconditionally proves `¬ 3 ∣ N → 2 ≤ (largeSources N q).card` and its
   contrapositive `(largeSources N q).card ≤ 1 → 3 ∣ N` via the 3-element
   pigeonhole median step `5 * u₀ + 3 ≤ 2 * u₂` on `{q, r₀}`-smooth quadratic
   divisor sums `u ^ 2 + u + 1`.
2. `three_free_two_large_sources_congruence`:
   Extends the smooth-quadratic growth engine to `(largeSources N q).card = 2`:
   when `¬ 3 ∣ N`, either at least two large non-Euler primes satisfy `r ≡ 1 [MOD 3]`
   or `3 ≤ (largeSources N q).card` (and if no large prime is `1 [MOD 3]`, then
   `7 ≤ (largeSources N q).card`).
3. `restrained_three_divisibility_and_exponent_profile`:
   When `(largeSources N q).card = 0`, `8 ≤ v₃(N)`; when `(largeSources N q).card ≤ 1`
   and `q ≡ 2 [MOD 3]` (including `q = 5`), `4 ≤ v₃(N)` (`81 ∣ N`); and on the
   sole remaining `v₃(N) = 2` subbranch, `q % 12 = 1`, `13 ≤ q`, and
   `1 ≤ (squareSourcesOne N).card ≤ 2`.
4. `finite_of_bounded_nonSquare_exponents`:
   Finiteness of odd perfect numbers when the sum of non-square exponents is bounded.
-/

public section

namespace RestrainedOPN

open OddPerfect ArithmeticFunction

/-- Core 3-element `{q, r₀}`-smooth quadratic growth inequality `5 * u₀ + 3 ≤ 2 * u₂`
driving the purely analytical exclusion of three-free restrained candidates. -/
theorem smooth_quadratic_three_step_growth {q r₀ u₀ u₁ u₂ α₀ α₁ α₂ β₀ β₁ β₂ : ℕ}
    (hq : q.Prime) (hq_odd : Odd q) (hq3 : q % 3 = 1)
    (hr₀ : r₀.Prime) (hr₀_odd : Odd r₀) (hr₀3 : r₀ % 3 = 1)
    (h01 : u₀ < u₁) (h12 : u₁ < u₂)
    (hu₀_odd : Odd u₀) (hu₁_odd : Odd u₁) (hu₂_odd : Odd u₂)
    (hu₀5 : 5 ≤ u₀) (hu₀3 : u₀ % 3 = 2) (hu₁3 : u₁ % 3 = 2) (hu₂3 : u₂ % 3 = 2)
    (heq₀ : u₀ ^ 2 + u₀ + 1 = q ^ α₀ * r₀ ^ β₀)
    (heq₁ : u₁ ^ 2 + u₁ + 1 = q ^ α₁ * r₀ ^ β₁)
    (heq₂ : u₂ ^ 2 + u₂ + 1 = q ^ α₂ * r₀ ^ β₂) :
    25 * (u₀ ^ 2 + u₀ + 1) ≤ (u₁ + u₂ + 1) ^ 2 ∧ 5 * u₀ + 3 ≤ 2 * u₂ :=
  OddPerfect.two_prime_smooth_sq_add_self_add_one_step
    hq hq_odd hq3 hr₀ hr₀_odd hr₀3 h01 h12
    hu₀_odd hu₁_odd hu₂_odd hu₀5 hu₀3 hu₁3 hu₂3 heq₀ heq₁ heq₂

/-- **Unconditional Analytical Exclusion of Three-Free Restrained Odd Perfect Numbers**:
Every `3`-free odd perfect number has at least two non-Euler primes with exponent `≥ 4`;
equivalently, `(largeSources N q).card ≤ 1` forces `3 ∣ N`. -/
theorem three_free_restrained_excluded {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) :
    (¬ 3 ∣ N → 2 ≤ (largeSources N q).card) ∧
    ((largeSources N q).card ≤ 1 → 3 ∣ N) :=
  ⟨OddPerfect.two_le_largeSources_of_three_free ho hN hq hq4 he hev,
   OddPerfect.three_dvd_of_largeSources_le_one ho hN hq hq4 he hev⟩

/-- **Two-Large-Sources Congruence & Seven-Source Jump for `3 ∤ N`**:
On any `3`-free odd perfect number, either `2 ≤ |oneModThreeLargeSources|` or
`3 ≤ |largeSources|`; if `oneModThreeLargeSources = ∅`, then `7 ≤ |largeSources|`;
and if `|largeSources| = 2`, both large non-Euler primes are `≡ 1 [MOD 3]`. -/
theorem three_free_two_large_sources_congruence {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) (h3 : ¬ 3 ∣ N) :
    (2 ≤ (oneModThreeLargeSources N q).card ∨ 3 ≤ (largeSources N q).card) ∧
    ((oneModThreeLargeSources N q).Nonempty ∨ 7 ≤ (largeSources N q).card) ∧
    ((largeSources N q).card = 2 →
      (oneModThreeLargeSources N q).card = 2 ∧
      twoModThreeLargeSources N q = ∅ ∧
      ∀ r ∈ largeSources N q, r % 3 = 1) :=
  ⟨OddPerfect.two_le_oneModThreeLarge_or_three_le_largeSources_of_three_free ho hN hq hq4 he hev h3,
   OddPerfect.oneModThreeLarge_nonempty_or_seven_le_largeSources_of_three_free ho hN hq hq4 he hev h3,
   OddPerfect.three_free_card_largeSources_two_forces_all_oneModThree ho hN hq hq4 he hev h3⟩

/-- **Restrained `3`-Adic Exponent & Exact-Nine Confinement Profile**:
1. If `largeSources N q = ∅`, then `8 ≤ v₃(N)` and `Ω(componentIndex N 3) + 8 ≤ Ω(N)`.
2. If `|largeSources N q| ≤ 1` and `q % 3 = 2`, then `4 ≤ v₃(N)` (`81 ∣ N`).
3. If `|largeSources N q| ≤ 1` and `v₃(N) = 2`, then `q % 12 = 1`, `13 ≤ q`, and
   `1 ≤ (squareSourcesOne N).card ≤ 2`. -/
theorem restrained_three_divisibility_and_exponent_profile {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) :
    (largeSources N q = ∅ →
      8 ≤ N.factorization 3 ∧
      3 ∈ N.primeFactors ∧
      cardFactors (componentIndex N 3) + 8 ≤ cardFactors N) ∧
    ((largeSources N q).card ≤ 1 → q % 3 = 2 → 4 ≤ N.factorization 3 ∧ 81 ∣ N) ∧
    ((largeSources N q).card ≤ 1 → N.factorization 3 = 2 →
      q % 12 = 1 ∧ 13 ≤ q ∧
      (squareSourcesOne N).Nonempty ∧
      1 ≤ (squareSourcesOne N).card ∧ (squareSourcesOne N).card ≤ 2) :=
  ⟨fun hempty =>
    ⟨OddPerfect.eight_le_three_exponent_of_largeSources_empty ho hN hq hq4 he hev hempty,
     OddPerfect.exists_eight_drop_at_three_of_largeSources_empty ho hN hq hq4 he hev hempty⟩,
   fun hle hq3 =>
    OddPerfect.four_le_three_exponent_of_restrained_euler_two_mod_three ho hN hq hq4 he hev hle hq3,
   fun hle h3 =>
    OddPerfect.restrained_exact_nine_profile ho hN hq hq4 he hev hle h3⟩

/-- Finiteness of odd perfect numbers under any uniform bound `E` on total non-square
prime-factor multiplicity. -/
theorem finite_of_bounded_nonSquare_exponents (E : ℕ) :
    Set.Finite {N : ℕ | Odd N ∧ N.Perfect ∧ ∃ q ∈ N.primeFactors,
      q % 4 = 1 ∧ N.factorization q % 4 = 1 ∧
      (∀ r, r ≠ q → Even (N.factorization r)) ∧
      N.factorization q + N.factorization 3 +
        ∑ r ∈ largeSources N q, N.factorization r ≤ E} :=
  OddPerfect.finite_of_bounded_nonSquare_exponents E

end RestrainedOPN
