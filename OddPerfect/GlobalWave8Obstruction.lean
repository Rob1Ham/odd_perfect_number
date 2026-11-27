module

public import OddPerfect.GlobalWave7Obstruction
public import OddPerfect.SixthPowerFreeBipartiteParity
public import OddPerfect.EvenIndexQuadraticCongruence
public import OddPerfect.RestrainedCyclotomicObstruction
public import OddPerfect.OddValuationCycleObstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Wave 8 Global Obstruction Synthesis (`OddPerfect.GlobalWave8Obstruction`)

Tier 2 global synthesis unifying and cross-coupling the four Wave 8 structural pillars:
1. `OddPerfect.RestrainedCyclotomicObstruction` + `OddPerfect.OddValuationCycleObstruction`:
   - Lifts the Euler exponent floor on three-free restrained candidates (`¬ 3 ∣ N`,
     `(largeSources N q).card ≤ 1`) to `21 ≤ N.factorization q`, forces a coprime cyclotomic pair
     `geometricBlock q l` and `(q ^ l + 1) / (q + 1)` (`l := ((a + 1) / 2).minFac ≥ 5`) supplying
     at least one `u ∈ squareSources N` with `u ∣ σ(q^a)` and `u = l ∨ 2 * l ∣ u - 1`, and
     **eliminates the square-sink branch** of `three_free_odd_sigma_cycle_or_euler_forty_eight`
     to prove `restrained_three_free_forces_oddSigma_cycle` (`∃ p ∈ N.primeFactors,
     Relation.TransGen (oddSigmaEdge N) p p`).
2. `OddPerfect.SixthPowerFreeBipartiteParity` + `OddPerfect.OddValuationCycleObstruction`:
   - Combines the mod-3 parity dichotomy on `Ω(σ(u^4))` (`Odd` on `Q₁₃ \ Q₁₃_q`, `Even` and `≥ 2`
     on `Q₂₃`) and exact bipartite multiplicity conservation (`3 * |Q₁₃| + 2 * |Q₂₃| ≤ 4 * |S₅₁| + 3`,
     hence `291 + |Q₁₃| ≤ 4 * |S₅₁|`) with odd-valuation vacuum (`oddSigmaSources N r = ∅` on
     `S₅₀ ∪ Q₂₃`) and cycle confinement to `insert q (S₅₁ ∪ Q₁₃)` (or `q % 48 = 1 ∧ 5617 ≤ q ∧
     IsSquare ((q + 1) / 2)`).
3. `OddPerfect.EvenIndexQuadraticCongruence`:
   - Extracts the exact `T`-independent second-order mod-`p` quotient identity
     `(QuadCoef + 3 * P_L) % p = (4 * m) % p` (`SumCoef = P_L + m * p`, `1 ≤ m`) and the
     `e(r_max) = 1` specialization (`m * r₀ < 2 * P_L`, `(r₀ - 1)^2 ≡ -3 * r₀ [ZMOD p]`).
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- **Cross-Pillar Odd-Valuation Cycle Forcing on Restrained Three-Free Candidates**:
Every three-free restrained odd perfect number (`¬ 3 ∣ N`, `(largeSources N q).card ≤ 1`)
satisfies `21 ≤ N.factorization q`, admits a seven-factor component-index drop, forces a
cyclotomic square-source prime `u ∈ squareSources N` dividing `σ(q ^ N.factorization q)` with
`u = l ∨ 2 * l ∣ u - 1` (`l := ((N.factorization q + 1) / 2).minFac ≥ 5`), and **unconditionally
contains a directed `oddSigmaEdge` cycle**. -/
theorem restrained_three_free_forces_oddSigma_cycle {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (h3 : ¬ 3 ∣ N) (hle : (largeSources N q).card ≤ 1) :
    let d := (N.factorization q + 1) / 2
    let l := d.minFac
    21 ≤ N.factorization q ∧
    11 ≤ d ∧ ¬ 3 ∣ d ∧ l.Prime ∧ 5 ≤ l ∧ l ∣ d ∧
    (∃ u ∈ squareSources N, u ∣ sigma 1 (q ^ N.factorization q) ∧ (u = l ∨ 2 * l ∣ u - 1)) ∧
    (∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 7 ≤ cardFactors N) ∧
    (∃ p ∈ N.primeFactors, Relation.TransGen (oddSigmaEdge N) p p) := by
  intro d l
  obtain ⟨h21, hndvd3, hd11⟩ :=
    restrained_three_free_euler_exp_ge_21 ho hN hq hq4 he hev h3 hle
  obtain ⟨_, _, hl_prime, hl5, hl_dvd, _, hu_ex⟩ :=
    restrained_three_free_cyclotomic_square_source_witness ho hN hq hq4 he hev h3 hle
  have hdrop7 :=
    (exists_componentIndex_cardFactors_add_seven_le_of_three_free_restrained
      ho hN hq hq4 he hev h3 hle).2
  have hcyc : ∃ p ∈ N.primeFactors, Relation.TransGen (oddSigmaEdge N) p p := by
    rcases three_free_odd_sigma_cycle_or_euler_forty_eight ho hN h3 with
      hcyc | ⟨q', _, hq'1, _, _, _⟩
    · exact hcyc
    · exfalso
      by_cases hqq : q' = q
      · subst hqq
        omega
      · obtain ⟨k, hk⟩ := hev q' hqq
        omega
  exact ⟨h21, hd11, hndvd3, hl_prime, hl5, hl_dvd, hu_ex, hdrop7, hcyc⟩

/-- **Unified Sixth-Power-Free Bipartite Capacity & Cycle Confinement Profile**:
On any sixth-power-free odd perfect number `N`, `3 * |Q₁₃| + 2 * |Q₂₃| ≤ 4 * |S₅₁| + 3`,
`291 + |Q₁₃| ≤ 4 * |S₅₁|`, every prime in `S₅₀ ∪ Q₂₃` has `oddSigmaSources N r = ∅`, and either
an `oddSigmaEdge` cycle exists inside `insert q (S₅₁ ∪ Q₁₃)` or `q % 48 = 1 ∧ 5617 ≤ q ∧
IsSquare ((q + 1) / 2)`. -/
theorem sixth_power_free_wave8_bipartite_and_cycle_profile {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    let S₅₀ := (squareSources N).filter (· % 5 ≠ 1)
    let S₅₁ := (squareSources N).filter (· % 5 = 1)
    let Q₁₃ := oneModThreeLargeSources N q
    let Q₂₃ := twoModThreeLargeSources N q
    3 * Q₁₃.card + 2 * Q₂₃.card ≤ 4 * S₅₁.card + 3 ∧
    291 + Q₁₃.card ≤ 4 * S₅₁.card ∧
    (∀ r ∈ S₅₀ ∪ Q₂₃, oddSigmaSources N r = ∅ ∧ ¬ Relation.TransGen (oddSigmaEdge N) r r) ∧
    ((∃ p ∈ insert q (S₅₁ ∪ Q₁₃), Relation.TransGen (oddSigmaEdge N) p p) ∨
      (N.factorization q = 1 ∧ q % 48 = 1 ∧ 5617 ≤ q ∧ IsSquare ((q + 1) / 2))) := by
  intro S₅₀ S₅₁ Q₁₃ Q₂₃
  have h3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  have h147 : 147 ≤ (largeSources N q).card :=
    (three_free_sixthPowerFree_forces_147_largeSources ho hN hq hq4 he hev h3 hfree).2.1
  have hQ_parts : largeSources N q = Q₁₃ ∪ Q₂₃ := by
    ext r
    simp only [Q₁₃, Q₂₃, oneModThreeLargeSources, twoModThreeLargeSources,
      Finset.mem_union, Finset.mem_filter]
    by_cases h : r % 3 = 1 <;> tauto
  have hQ_disj : Disjoint Q₁₃ Q₂₃ := by
    apply Finset.disjoint_left.mpr
    intro r h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hQ_card : (largeSources N q).card = Q₁₃.card + Q₂₃.card := by
    rw [hQ_parts, Finset.card_union_of_disjoint hQ_disj]
  have hcap := sixth_power_free_sharpened_quartic_to_S51_bound ho hN hq hq4 he hev hfree
  change 3 * Q₁₃.card + 2 * Q₂₃.card ≤ 4 * S₅₁.card + 3 at hcap
  have h291 : 291 + Q₁₃.card ≤ 4 * S₅₁.card := by omega
  have hvac := (sixth_power_free_oddSigma_vacuum_and_routing ho hN hq hq4 he hev hfree).1
  have hcyc := sixth_power_free_cycle_confinement_or_large_square_sink ho hN hq hq4 he hev hfree
  exact ⟨hcap, h291, hvac, hcyc⟩

/-- Unified Wave 8 global obstruction profile across every odd perfect number `N`. -/
theorem odd_perfect_wave8_master_profile {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    (∃ p ∈ N.primeFactors,
      cardFactors (componentIndex N p) + 6 ≤ cardFactors N ∧
      7 ≤ N.factorization p + cardFactors (sigma 1 (ordProj[p] N))) ∧
    ((∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 7 ≤ cardFactors N) ∨
      ((∀ p : ℕ, p.Prime → ¬ p ^ 8 ∣ N) ∧
        (∀ r ∈ N.primeFactors, N.factorization r = 6 → (sigma 1 (r ^ 6)).Prime ∧ r % 7 ≠ 1) ∧
        2 * cardFactors N + 1 ≤ 7 * N.primeFactors.card)) ∧
    ∃ q a m, q.Prime ∧ q % 4 = 1 ∧ a % 4 = 1 ∧ ¬ q ∣ m ∧ N = q ^ a * m ^ 2 ∧
      q ∈ N.primeFactors ∧ N.factorization q = a ∧
      (∀ r, r ≠ q → Even (N.factorization r)) ∧
      (¬ 3 ∣ N →
        (∃ p ∈ N.primeFactors, Relation.TransGen (oddSigmaEdge N) p p) ∨
          (a = 1 ∧ q % 48 = 1 ∧ 97 ≤ q ∧ IsSquare ((q + 1) / 2))) ∧
      (¬ 3 ∣ N → (largeSources N q).card ≤ 1 →
        21 ≤ a ∧
        (∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 7 ≤ cardFactors N) ∧
        (∃ p ∈ N.primeFactors, Relation.TransGen (oddSigmaEdge N) p p) ∧
        ∃ u ∈ squareSources N, u ∣ sigma 1 (q ^ a) ∧
          (u = ((a + 1) / 2).minFac ∨ 2 * ((a + 1) / 2).minFac ∣ u - 1)) ∧
      (∀ r ∈ N.primeFactors, ∀ p j, p.Prime → 0 < j → componentIndex N r = p ^ j →
        r = q ∧ Odd p ∧ p ≠ q ∧ 36207 ≤ j ∧
        10 ^ 17240 < componentIndex N q ∧ 10 ^ 17240 < N ∧
        (Odd j → ¬ ExcludedFermatResidue q) ∧
        (Even j → a = 1 ∧ HasNineOddPrimeRepunits p ∧ 12 ≤ N.primeFactors.card ∧
          6469693228 ≤ j ∧ 10 ^ 122924171332 < componentIndex N q ∧ 10 ^ 122924171332 < N)) := by
  obtain ⟨h6, h7_or, q, a, m, hq, hq4, ha4, hqm, hform, hqN, hval, hev, _, _, _, hpp⟩ :=
    odd_perfect_wave7_master_profile ho hN
  have he4 : N.factorization q % 4 = 1 := by simpa [hval] using ha4
  refine ⟨h6, h7_or, q, a, m, hq, hq4, ha4, hqm, hform, hqN, hval, hev, ?_, ?_, hpp⟩
  · intro h3
    rcases three_free_odd_sigma_cycle_or_euler_forty_eight ho hN h3 with
      hcyc | ⟨q', _, hq'1, hq'48, hq'97, hsq⟩
    · exact Or.inl hcyc
    · right
      have hqq : q' = q := by
        by_contra hne
        obtain ⟨k, hk⟩ := hev q' hne
        omega
      subst hqq
      exact ⟨hval.symm.trans hq'1, hq'48, hq'97, hsq⟩
  · intro h3 hle
    obtain ⟨h21, _, _, _, _, _, hu_ex, hdrop7, hcyc⟩ :=
      restrained_three_free_forces_oddSigma_cycle ho hN hqN hq4 he4 hev h3 hle
    have hu_ex' : ∃ u ∈ squareSources N, u ∣ sigma 1 (q ^ a) ∧
        (u = ((a + 1) / 2).minFac ∨ 2 * ((a + 1) / 2).minFac ∣ u - 1) := by
      rwa [hval] at hu_ex
    exact ⟨h21.trans_eq hval, hdrop7, hcyc, hu_ex'⟩

end OddPerfect
