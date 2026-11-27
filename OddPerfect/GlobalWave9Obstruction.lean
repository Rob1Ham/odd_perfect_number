module

public import OddPerfect.GlobalWave8Obstruction
public import OddPerfect.SixthPowerFreeQuarterDensity
public import OddPerfect.RestrainedCommonDivisorObstruction
public import OddPerfect.ExceptionalValuationProfile
public import OddPerfect.EightFactorDropObstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Wave 9 Global Obstruction Synthesis (`OddPerfect.GlobalWave9Obstruction`)

Tier 2 global synthesis unifying and cross-coupling the four Wave 9 structural pillars:
1. `OddPerfect.RestrainedCommonDivisorObstruction` + `OddPerfect.EightFactorDropObstruction`:
   - Lifts the Euler component-index factor drop on three-free restrained candidates
     (`¬ 3 ∣ N`, `(largeSources N q).card ≤ 1`) from `+ 7` to
     `cardFactors (componentIndex N q) + 24 ≤ cardFactors N`, proves the exact square-source
     odd-valuation pairing (`oddSigmaSources N u = ∅` or `{q, r₀}` with both valuations `1`),
     reduces all forced `oddSigmaEdge` cycles to either the direct 2-cycle `q ↔ r₀` or a
     common-divisor witness `u ∈ squareSources N` dividing `gcd(σ(q^a), σ(r₀^{e₀}))`, and forces
     `u % 12 = 11` across `squareSources N` whenever `r₀ % 4 = 1`.
2. `OddPerfect.SixthPowerFreeQuarterDensity` + `OddPerfect.SixthPowerFreeBipartiteParity`:
   - Upgrades the `S₅₁` lower bound on sixth-power-free odd perfect numbers from `92` (`20.8%`)
     to `110 ≤ |S₅₁|` and the quarter-density support cap `ω(N) ≤ 4 * |S₅₁| + 5`, alongside
     `438 + |Q₂₃| ≤ 4 * |S₅₁|` and `|S| ≤ 2 * |Q₁₃| + 1`.
3. `OddPerfect.ExceptionalValuationProfile`:
   - Identifies `oddSigmaTargets N q = {l}` on the exceptional prime-times-square Euler-index
     branch `sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`1 < a`, `l.Prime`) and establishes an
     unconditional `+ 36` Euler factor drop and a `+ 148` drop when `¬ 3 ∣ N`.
4. `OddPerfect.EightFactorDropObstruction`:
   - Upgrades the global component-index multiplicity drop dichotomy from `+ 7` to `+ 8`,
     bounding sextic divisor sums (`cardFactors (sigma 1 (r ^ 6)) ≤ 2`) and forcing `a = 1`,
     eighth-power-freeness, and `2 * Ω(N) + 1 ≤ 8 * ω(N)` whenever no `+ 8` drop occurs.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- **Wave 9 Restrained Three-Free Common-Divisor & 24-Factor Drop Profile**:
Every three-free restrained odd perfect number (`¬ 3 ∣ N`, `(largeSources N q).card ≤ 1`)
satisfies `21 ≤ N.factorization q`, `cardFactors (componentIndex N q) + 24 ≤ cardFactors N`,
and has a unique `r₀` (`largeSources N q = {r₀}`) for which either `q ↔ r₀` is a direct
`oddSigmaEdge` 2-cycle or some `u ∈ squareSources N` divides
`Nat.gcd (sigma 1 (q ^ N.factorization q)) (sigma 1 (r₀ ^ N.factorization r₀))` with
`oddSigmaSources N u = {q, r₀}` and `oddSigmaEdge N u q ∨ oddSigmaEdge N u r₀`. -/
theorem restrained_three_free_wave9_common_divisor_profile {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (h3 : ¬ 3 ∣ N) (hle : (largeSources N q).card ≤ 1) :
    21 ≤ N.factorization q ∧
    cardFactors (componentIndex N q) + 24 ≤ cardFactors N ∧
    ∃ r₀, largeSources N q = {r₀} ∧ q % 12 = 1 ∧ 13 ≤ q ∧ r₀ % 3 = 1 ∧ 7 ≤ r₀ ∧
      N.factorization r₀ % 3 ≠ 2 ∧
      ((oddSigmaEdge N q r₀ ∧ oddSigmaEdge N r₀ q) ∨
        (∃ u ∈ squareSources N,
          oddSigmaSources N u = {q, r₀} ∧
          u ∣ Nat.gcd (sigma 1 (q ^ N.factorization q)) (sigma 1 (r₀ ^ N.factorization r₀)) ∧
          (oddSigmaEdge N u q ∨ oddSigmaEdge N u r₀))) ∧
      (r₀ % 4 = 1 → ∀ u ∈ squareSources N, u % 12 = 11) := by
  obtain ⟨h21, _, _, _, _, _, _, _, _⟩ :=
    restrained_three_free_forces_oddSigma_cycle ho hN hq hq4 he hev h3 hle
  have h24 := restrained_three_free_twenty_four_factor_drop ho hN hq hq4 he hev h3 hle
  obtain ⟨r₀, hr₀, hq12, hr₀3, _, hq13, hr₀7, hmod3⟩ :=
    restrained_three_free_euler_exp_ge_17 ho hN hq hq4 he hev h3 hle
  have hcyc_or_gcd :=
    restrained_three_free_cycle_two_or_gcd_witness ho hN hq hq4 he hev h3 hr₀
  have hmod12 :=
    restrained_three_free_mod_four_square_sources ho hN hq hq4 he hev h3 hr₀
  exact ⟨h21, h24, ⟨r₀, hr₀, hq12, hq13, hr₀3, hr₀7, hmod3, hcyc_or_gcd, hmod12⟩⟩

/-- **Wave 9 Sixth-Power-Free Quarter-Density & Cycle Confinement Profile**:
Unifies the quarter-density `S₅₁` bounds (`110 ≤ |S₅₁|`, `ω(N) ≤ 4 * |S₅₁| + 5`,
`438 + |Q₂₃| ≤ 4 * |S₅₁|`, `|S| ≤ 2 * |Q₁₃| + 1`) with bipartite capacity and
`oddSigmaEdge` cycle confinement on sixth-power-free odd perfect numbers. -/
theorem sixth_power_free_wave9_quarter_density_profile {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    let S₅₀ := (squareSources N).filter (· % 5 ≠ 1)
    let S₅₁ := (squareSources N).filter (· % 5 = 1)
    let Q₁₃ := oneModThreeLargeSources N q
    let Q₂₃ := twoModThreeLargeSources N q
    110 ≤ S₅₁.card ∧
    438 + Q₂₃.card ≤ 4 * S₅₁.card ∧
    291 + Q₁₃.card ≤ 4 * S₅₁.card ∧
    (squareSources N).card ≤ 2 * Q₁₃.card + 1 ∧
    N.primeFactors.card ≤ 4 * S₅₁.card + 5 ∧
    3 * Q₁₃.card + 2 * Q₂₃.card ≤ 4 * S₅₁.card + 3 ∧
    (∀ r ∈ S₅₀ ∪ Q₂₃, oddSigmaSources N r = ∅ ∧ ¬ Relation.TransGen (oddSigmaEdge N) r r) ∧
    ((∃ p ∈ insert q (S₅₁ ∪ Q₁₃), Relation.TransGen (oddSigmaEdge N) p p) ∨
      (N.factorization q = 1 ∧ q % 48 = 1 ∧ 5617 ≤ q ∧ IsSquare ((q + 1) / 2))) := by
  intro S₅₀ S₅₁ Q₁₃ Q₂₃
  obtain ⟨h110, h438, hS_le, hquarter⟩ :=
    sixth_power_free_square_sources_quarter_density ho hN hq hq4 he hev hfree
  obtain ⟨hcap, h291, hvac, hcyc⟩ :=
    sixth_power_free_wave8_bipartite_and_cycle_profile ho hN hq hq4 he hev hfree
  exact ⟨h110, h438, h291, hS_le, hquarter, hcap, hvac, hcyc⟩

/-- Unified Wave 9 global obstruction profile across every odd perfect number `N`. -/
theorem odd_perfect_wave9_master_profile {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    (∃ p ∈ N.primeFactors,
      cardFactors (componentIndex N p) + 6 ≤ cardFactors N ∧
      7 ≤ N.factorization p + cardFactors (sigma 1 (ordProj[p] N))) ∧
    ((∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 8 ≤ cardFactors N) ∨
      ((∀ p : ℕ, p.Prime → ¬ p ^ 8 ∣ N) ∧
        (∀ r ∈ N.primeFactors, N.factorization r = 6 →
          cardFactors (sigma 1 (r ^ 6)) ≤ 2 ∧ (r % 7 ≠ 1 → sigma 1 (r ^ 6) % 7 = 1)) ∧
        2 * cardFactors N + 1 ≤ 8 * N.primeFactors.card)) ∧
    (((squareSources N).filter (· % 5 = 1)).card < 110 ∨
      4 * ((squareSources N).filter (· % 5 = 1)).card + 6 ≤ N.primeFactors.card →
      ∃ p : ℕ, p.Prime ∧ p ^ 6 ∣ N) ∧
    ∃ q a m, q.Prime ∧ q % 4 = 1 ∧ a % 4 = 1 ∧ ¬ q ∣ m ∧ N = q ^ a * m ^ 2 ∧
      q ∈ N.primeFactors ∧ N.factorization q = a ∧
      (∀ r, r ≠ q → Even (N.factorization r)) ∧
      (1 < a → ∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 8 ≤ cardFactors N) ∧
      (1 < a → ∀ l t : ℕ, l.Prime → sigma 1 (m ^ 2) / q ^ a = l * t ^ 2 →
        componentIndex N q = l * t ^ 2 ∧
        oddSigmaTargets N q = {l} ∧
        cardFactors (componentIndex N q) + 36 ≤ cardFactors N ∧
        (¬ 3 ∣ N → cardFactors (componentIndex N q) + 148 ≤ cardFactors N)) ∧
      (¬ 3 ∣ N →
        (∃ p ∈ N.primeFactors, Relation.TransGen (oddSigmaEdge N) p p) ∨
          (a = 1 ∧ q % 48 = 1 ∧ 97 ≤ q ∧ IsSquare ((q + 1) / 2))) ∧
      (¬ 3 ∣ N → (largeSources N q).card ≤ 1 →
        21 ≤ a ∧
        cardFactors (componentIndex N q) + 24 ≤ cardFactors N ∧
        ∃ r₀, largeSources N q = {r₀} ∧ q % 12 = 1 ∧ 13 ≤ q ∧ r₀ % 3 = 1 ∧ 7 ≤ r₀ ∧
          N.factorization r₀ % 3 ≠ 2 ∧
          ((oddSigmaEdge N q r₀ ∧ oddSigmaEdge N r₀ q) ∨
            (∃ u ∈ squareSources N,
              oddSigmaSources N u = {q, r₀} ∧
              u ∣ Nat.gcd (sigma 1 (q ^ a)) (sigma 1 (r₀ ^ N.factorization r₀)) ∧
              (oddSigmaEdge N u q ∨ oddSigmaEdge N u r₀))) ∧
          (r₀ % 4 = 1 → ∀ u ∈ squareSources N, u % 12 = 11)) ∧
      (∀ r ∈ N.primeFactors, ∀ p j, p.Prime → 0 < j → componentIndex N r = p ^ j →
        r = q ∧ Odd p ∧ p ≠ q ∧ 36207 ≤ j ∧
        10 ^ 17240 < componentIndex N q ∧ 10 ^ 17240 < N ∧
        (Odd j → ¬ ExcludedFermatResidue q) ∧
        (Even j → a = 1 ∧ HasNineOddPrimeRepunits p ∧ 12 ≤ N.primeFactors.card ∧
          6469693228 ≤ j ∧ 10 ^ 122924171332 < componentIndex N q ∧ 10 ^ 122924171332 < N)) := by
  obtain ⟨h6, _, q, a, m, hq, hq4, ha4, hqm, hform, hqN, hval, hev, h3_cyc, _, hpp⟩ :=
    odd_perfect_wave8_master_profile ho hN
  have he4 : N.factorization q % 4 = 1 := by simpa [hval] using ha4
  have h8_or :
      (∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 8 ≤ cardFactors N) ∨
        ((∀ p : ℕ, p.Prime → ¬ p ^ 8 ∣ N) ∧
          (∀ r ∈ N.primeFactors, N.factorization r = 6 →
            cardFactors (sigma 1 (r ^ 6)) ≤ 2 ∧ (r % 7 ≠ 1 → sigma 1 (r ^ 6) % 7 = 1)) ∧
          2 * cardFactors N + 1 ≤ 8 * N.primeFactors.card) := by
    by_cases h8 : ∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 8 ≤ cardFactors N
    · exact Or.inl h8
    · right
      have hno : ∀ p ∈ N.primeFactors, cardFactors N < cardFactors (componentIndex N p) + 8 :=
        fun p hp => Nat.lt_of_not_ge fun hge => h8 ⟨p, hp, hge⟩
      obtain ⟨_, _, hfree8, hsextic, hdens8⟩ :=
        no_eight_factor_drop_profile ho hN hqN hq4 he4 hev hno
      exact ⟨hfree8, hsextic, hdens8⟩
  refine ⟨h6, h8_or, sixth_power_dichotomy_on_S51_quarter_density ho hN,
    q, a, m, hq, hq4, ha4, hqm, hform, hqN, hval, hev, ?_, ?_, h3_cyc, ?_, hpp⟩
  · intro ha1
    exact exists_componentIndex_cardFactors_add_eight_le_of_euler_exp_gt_one
      ho hN hqN hq4 he4 hev (hval ▸ ha1)
  · intro ha1 l t hl hI
    obtain ⟨_, _, _, hci, _, _, _, _, _⟩ :=
      exceptional_euler_componentIndex_eq ho hN hq hq4 ha4 ha1 hqm hform hl hI
    obtain ⟨_, _, htargets, _⟩ :=
      exceptional_euler_valuation_matrix_profile ho hN hq hq4 ha4 ha1 hqm hform hl hI
    obtain ⟨h36, h148⟩ :=
      exceptional_euler_thirty_six_and_148_factor_drop ho hN hq hq4 ha4 ha1 hqm hform hl hI
    exact ⟨hci, htargets, h36, h148⟩
  · intro h3 hle
    obtain ⟨h21, h24, ⟨r₀, hr₀, hq12, hq13, hr₀3, hr₀7, hmod3, hcyc_or_gcd, hmod12⟩⟩ :=
      restrained_three_free_wave9_common_divisor_profile ho hN hqN hq4 he4 hev h3 hle
    have hcyc_or_gcd' :
        (oddSigmaEdge N q r₀ ∧ oddSigmaEdge N r₀ q) ∨
          (∃ u ∈ squareSources N,
            oddSigmaSources N u = {q, r₀} ∧
            u ∣ Nat.gcd (sigma 1 (q ^ a)) (sigma 1 (r₀ ^ N.factorization r₀)) ∧
            (oddSigmaEdge N u q ∨ oddSigmaEdge N u r₀)) := by
      rwa [hval] at hcyc_or_gcd
    exact ⟨h21.trans_eq hval, h24, ⟨r₀, hr₀, hq12, hq13, hr₀3, hr₀7, hmod3, hcyc_or_gcd', hmod12⟩⟩

end OddPerfect
