module

public import OddPerfect.GlobalWave9Obstruction
public import OddPerfect.ThreeFreeRestrainedClosure
public import OddPerfect.LinearEulerOrderObstruction
public import OddPerfect.SixthPowerFreePrimeCompositeSplit
public import OddPerfect.UndecupleRepunitObstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Wave 10 Global Obstruction Synthesis (`OddPerfect.GlobalWave10Obstruction`)

Tier 2 global synthesis unifying and cross-coupling the four Wave 10 structural pillars:
1. `OddPerfect.ThreeFreeRestrainedClosure`:
   - **Unconditionally closes the entire three-free restrained branch**: proves
     `two_le_largeSources_of_three_free` (`¬ 3 ∣ N → 2 ≤ (largeSources N q).card`) and
     `three_dvd_of_largeSources_le_one` (`(largeSources N q).card ≤ 1 → 3 ∣ N`) via `{q, r₀}`-smooth
     quadratic sums, the prime-power Zelinsky common-divisor inequality
     `5 * P ^ c ≤ a + b + 1`, and a 3-element pigeonhole median growth bound
     `5 * u₀ + 3 ≤ 2 * u₂`, alongside `exists_eight_drop_at_three_of_largeSources_empty`
     (`largeSources N q = ∅ → cardFactors (componentIndex N 3) + 8 ≤ cardFactors N`).
2. `OddPerfect.LinearEulerOrderObstruction`:
   - Establishes the congruent-1 vs. cyclotomic-order dichotomy for the unique `q`-source `r₀ ∣ m`
     on every linear Euler candidate `N = q * m ^ 2`, eliminating the cyclotomic-order branch for
     all Fermat primes `q - 1 = 2 ^ k` (`linear_euler_fermat_prime_obstruction`), specializing
     `q = 5` (`linear_euler_five_profile`), and proving `r₀ ^ 16 ∣ N` plus an unconditional
     eight-factor drop for every Fermat prime `q > 5`.
3. `OddPerfect.SixthPowerFreePrimeCompositeSplit`:
   - Refines sixth-power-free bipartite capacity via prime/composite splittings
     (`|Q₁₃_prime| ≤ 1 + |S₅₁_comp|`, `|S₅₁_prime| ≤ 1 + |Q₁₃|`,
     `|Q₁₃_prime| + 3 * |Q₁₃_comp| + 2 * |Q₂₃| ≤ 2 * |S₅₁| + 2`,
     `3 * |Q₁₃| + 2 * |Q₂₃| + 2 * |S₅₁_prime| ≤ 4 * |S₅₁| + 4`) and proves the no-eight-drop pinch
     (`|Q₂₃| ≤ 1`, `|S₅₀| ≤ 3`, `147 ≤ |Q₁₃|`, `439 ≤ |S₅₁| + |Q₁₃|`).
4. `OddPerfect.UndecupleRepunitObstruction`:
   - Eliminates both `|S₁| = 9` and `|S₁| = 10` symbolically on even prime-power component indices
     `i_q = p ^ (2 * u)`, forcing `HasElevenOddPrimeRepunits p ∧ 14 ≤ ω(N)`,
     `7420738134808 ≤ j`, and `10 ^ 185518453370200 < i_q < N`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- **Complete Structural Dichotomy on Restrained vs. Three-Free Candidates**:
Every three-free odd perfect number has `q % 12 = 1`, `13 ≤ q`, and `2 ≤ (largeSources N q).card`;
every restrained odd perfect number (`(largeSources N q).card ≤ 1`) is divisible by `3`, and
`largeSources N q = ∅` forces an explicit eight-factor drop at `p = 3`. -/
theorem restrained_and_three_free_wave10_dichotomy {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) :
    (¬ 3 ∣ N → q % 12 = 1 ∧ 13 ≤ q ∧ 2 ≤ (largeSources N q).card) ∧
    ((largeSources N q).card ≤ 1 → 3 ∣ N) ∧
    (largeSources N q = ∅ →
      3 ∈ N.primeFactors ∧ 8 ≤ N.factorization 3 ∧
      cardFactors (componentIndex N 3) + 8 ≤ cardFactors N) := by
  refine ⟨?_, three_dvd_of_largeSources_le_one ho hN hq hq4 he hev, ?_⟩
  · intro h3
    obtain ⟨hq12, hq13⟩ := three_free_euler_prime_mod_twelve ho hN hq hq4 he h3
    exact ⟨hq12, hq13, two_le_largeSources_of_three_free ho hN hq hq4 he hev h3⟩
  · intro hempty
    have h8 := eight_le_three_exponent_of_largeSources_empty ho hN hq hq4 he hev hempty
    obtain ⟨h3_mem, hdrop8⟩ :=
      exists_eight_drop_at_three_of_largeSources_empty ho hN hq hq4 he hev hempty
    exact ⟨h3_mem, h8, hdrop8⟩

/-- **Euler-Only Undecuple-Repunit Prime-Power Component-Index Obstruction**:
Every prime-power component index `componentIndex N r = p ^ j` (`j ≥ 1`) occurs exclusively at the
Euler prime `r = q`, satisfies `36207 ≤ j` and `10 ^ 17240 < componentIndex N q < N`, and when `j`
is even forces `N.factorization q = 1`, `HasElevenOddPrimeRepunits p`, `14 ≤ ω(N)`,
`7420738134808 ≤ j`, and `10 ^ 185518453370200 < componentIndex N q < N`. -/
theorem component_prime_power_index_euler_only_and_undecuple_lift {N q r p j : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ s : ℕ, s ≠ q → Even (N.factorization s))
    (hr : r ∈ N.primeFactors) (hp : p.Prime) (hj : 0 < j)
    (hci_eq : componentIndex N r = p ^ j) :
    r = q ∧ Odd p ∧ p ≠ q ∧
    36207 ≤ j ∧ 10 ^ 17240 < componentIndex N q ∧ 10 ^ 17240 < N ∧
    (Odd j → ¬ ExcludedFermatResidue q) ∧
    (Even j → N.factorization q = 1 ∧ HasElevenOddPrimeRepunits p ∧ 14 ≤ N.primeFactors.card ∧
      7420738134808 ≤ j ∧ 10 ^ 185518453370200 < componentIndex N q ∧ 10 ^ 185518453370200 < N) := by
  obtain ⟨hr_eq_q, hp_odd, hp_neq_q, hj36207, hi17240, hN17240, hodd_j, heven_w6⟩ :=
    component_prime_power_index_euler_only_and_septuple_lift
      ho hN hq hq4 he hev hr hp hj hci_eq
  subst r
  refine ⟨rfl, hp_odd, hp_neq_q, hj36207, hi17240, hN17240, hodd_j, fun hj_even => ?_⟩
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have ha_pos : 0 < N.factorization q := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hq)
  have hNb : N = q ^ N.factorization q * ordCompl[q] N :=
    (Nat.ordProj_mul_ordCompl_eq_self N q).symm
  have hqb : ¬ q ∣ ordCompl[q] N := Nat.not_dvd_ordCompl hq_prime hN.2.ne'
  obtain ⟨i, _, hleft, hright, _⟩ := exists_component_index hN hq_prime hNb hqb
  have hci : componentIndex N q = i := by
    rw [componentIndex, hleft]
    exact Nat.mul_div_cancel_left i (pow_pos hq_prime.pos _)
  have hi_eq : i = p ^ j := hci.symm.trans hci_eq
  obtain ⟨hq1, _, _, _, _, _⟩ := heven_w6 hj_even
  have hj_even' : Even j := hj_even
  obtain ⟨u, rfl⟩ := hj_even
  have hu : 0 < u := by omega
  have hi2 : i = p ^ (2 * u) := by
    rw [hi_eq, show u + u = 2 * u by ring]
  obtain ⟨heleven, h14⟩ :=
    even_prime_power_component_forces_eleven_repunits_and_fourteen_primes
      hN ho hq_prime ha_pos hNb hqb hleft hright hp hu hi2
  obtain ⟨hj74, hi185, hN185⟩ :=
    even_prime_power_component_size_gt_ten_pow_185518453370200
      hN ho hq_prime ha_pos hNb hqb hleft hright hp hj hj_even' hi_eq
  exact ⟨hq1, heleven, h14, hj74, lt_of_lt_of_eq hi185 hci.symm, hN185⟩

/-- **Wave 10 Sixth-Power-Free Prime–Composite Bipartite & Eight-Drop Dichotomy Profile**:
Unifies quarter-density bounds, `Q₁₃_prime` / `S₅₁_prime` injections, prime-composite bipartite
capacity, and the eight-factor component-index drop dichotomy on sixth-power-free candidates. -/
theorem sixth_power_free_wave10_bipartite_and_drop_profile {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    let S := squareSources N
    let S₅₁ := S.filter (· % 5 = 1)
    let S₅₀ := S.filter (· % 5 ≠ 1)
    let Q₁₃ := oneModThreeLargeSources N q
    let Q₂₃ := twoModThreeLargeSources N q
    let Q₁₃_prime := Q₁₃.filter (fun u => (sigma 1 (u ^ 4)).Prime)
    let Q₁₃_comp := Q₁₃.filter (fun u => ¬ (sigma 1 (u ^ 4)).Prime)
    let S₅₁_prime := S₅₁.filter (fun s => (sigma 1 (s ^ 2)).Prime)
    let S₅₁_comp := S₅₁.filter (fun s => ¬ (sigma 1 (s ^ 2)).Prime)
    110 ≤ S₅₁.card ∧
    N.primeFactors.card ≤ 4 * S₅₁.card + 5 ∧
    Q₁₃_prime.card ≤ 1 + S₅₁_comp.card ∧
    S₅₁_prime.card ≤ 1 + Q₁₃.card ∧
    Q₁₃_prime.card + 3 * Q₁₃_comp.card + 2 * Q₂₃.card ≤ 2 * S₅₁.card + 2 ∧
    3 * Q₁₃.card + 2 * Q₂₃.card + 2 * S₅₁_prime.card ≤ 4 * S₅₁.card + 4 ∧
    ((∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 8 ≤ cardFactors N) ∨
      ((Q₂₃.card ≤ 1 ∧ S₅₀.card ≤ 3 ∧ 2 * S₅₀.card + 4 * Q₂₃.card ≤ 6) ∧
        (147 ≤ Q₁₃.card ∧ 439 ≤ S₅₁.card + Q₁₃.card) ∧
        (∀ u ∈ Q₁₃, ¬ q ∣ sigma 1 (u ^ 4) →
          cardFactors (sigma 1 (u ^ 4)) = 1 ∨ cardFactors (sigma 1 (u ^ 4)) = 3))) := by
  intro S S₅₁ S₅₀ Q₁₃ Q₂₃ Q₁₃_prime Q₁₃_comp S₅₁_prime S₅₁_comp
  obtain ⟨h110, _, _, hquarter⟩ :=
    sixth_power_free_square_sources_quarter_density ho hN hq hq4 he hev hfree
  obtain ⟨hinj1, hinj2⟩ :=
    sixth_power_free_Q13_prime_and_S51_prime_injections ho hN hq hq4 he hev hfree
  obtain ⟨hbip1, hbip2⟩ :=
    sixth_power_free_prime_composite_bipartite_bound ho hN hq hq4 he hev hfree
  have hdrop_or :
      (∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 8 ≤ cardFactors N) ∨
        ((Q₂₃.card ≤ 1 ∧ S₅₀.card ≤ 3 ∧ 2 * S₅₀.card + 4 * Q₂₃.card ≤ 6) ∧
          (147 ≤ Q₁₃.card ∧ 439 ≤ S₅₁.card + Q₁₃.card) ∧
          (∀ u ∈ Q₁₃, ¬ q ∣ sigma 1 (u ^ 4) →
            cardFactors (sigma 1 (u ^ 4)) = 1 ∨ cardFactors (sigma 1 (u ^ 4)) = 3)) := by
    by_cases h8 : ∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 8 ≤ cardFactors N
    · exact Or.inl h8
    · right
      have hno8 : ∀ p ∈ N.primeFactors, cardFactors N < cardFactors (componentIndex N p) + 8 :=
        fun p hp => Nat.lt_of_not_ge fun hge => h8 ⟨p, hp, hge⟩
      exact sixth_power_free_no_eight_drop_pinch ho hN hq hq4 he hev hfree hno8
  exact ⟨h110, hquarter, hinj1, hinj2, hbip1, hbip2, hdrop_or⟩

/-- Unified Wave 10 global obstruction profile across every odd perfect number `N`. -/
theorem odd_perfect_wave10_master_profile {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
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
      (a = 1 →
        (∃ r₀ ∈ m.primeFactors,
          let e₀ := m.factorization r₀
          N.factorization r₀ = 2 * e₀ ∧
          q ∣ sigma 1 (r₀ ^ (2 * e₀)) ∧
          (sigma 1 (r₀ ^ (2 * e₀))).factorization q = 1 ∧
          ((r₀ % q = 1 ∧ 2 * q + 1 ≤ r₀ ∧ q ∣ 2 * e₀ + 1 ∧ ¬ q ^ 2 ∣ 2 * e₀ + 1 ∧
              q - 1 ≤ N.factorization r₀) ∨
            (∃ l : ℕ, l.Prime ∧ Odd l ∧ l ∣ 2 * e₀ + 1 ∧ 4 * l ∣ q - 1 ∧ 13 ≤ q))) ∧
        (q = 5 → ∃ r₀ ∈ N.primeFactors,
          11 ≤ r₀ ∧ r₀ % 10 = 1 ∧ 5 ∣ N.factorization r₀ + 1 ∧
          ¬ 25 ∣ N.factorization r₀ + 1 ∧ 4 ≤ N.factorization r₀ ∧ r₀ ∈ largeSources N 5) ∧
        ((∃ k : ℕ, q - 1 = 2 ^ k) → 5 < q →
          (∃ r₀ : ℕ, r₀.Prime ∧ r₀ ^ 16 ∣ N) ∧
          (∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 8 ≤ cardFactors N))) ∧
      (1 < a → ∀ l t : ℕ, l.Prime → sigma 1 (m ^ 2) / q ^ a = l * t ^ 2 →
        componentIndex N q = l * t ^ 2 ∧
        oddSigmaTargets N q = {l} ∧
        cardFactors (componentIndex N q) + 36 ≤ cardFactors N ∧
        (¬ 3 ∣ N → cardFactors (componentIndex N q) + 148 ≤ cardFactors N)) ∧
      (¬ 3 ∣ N → q % 12 = 1 ∧ 13 ≤ q ∧ 2 ≤ (largeSources N q).card) ∧
      ((largeSources N q).card ≤ 1 → 3 ∣ N) ∧
      (largeSources N q = ∅ →
        3 ∈ N.primeFactors ∧ 8 ≤ N.factorization 3 ∧
        cardFactors (componentIndex N 3) + 8 ≤ cardFactors N) ∧
      (¬ 3 ∣ N →
        (∃ p ∈ N.primeFactors, Relation.TransGen (oddSigmaEdge N) p p) ∨
          (a = 1 ∧ q % 48 = 1 ∧ 97 ≤ q ∧ IsSquare ((q + 1) / 2))) ∧
      (∀ r ∈ N.primeFactors, ∀ p j, p.Prime → 0 < j → componentIndex N r = p ^ j →
        r = q ∧ Odd p ∧ p ≠ q ∧ 36207 ≤ j ∧
        10 ^ 17240 < componentIndex N q ∧ 10 ^ 17240 < N ∧
        (Odd j → ¬ ExcludedFermatResidue q) ∧
        (Even j → a = 1 ∧ HasElevenOddPrimeRepunits p ∧ 14 ≤ N.primeFactors.card ∧
          7420738134808 ≤ j ∧
          10 ^ 185518453370200 < componentIndex N q ∧ 10 ^ 185518453370200 < N)) := by
  obtain ⟨h6, h8_or, hquarter, q, a, m, hq, hq4, ha4, hqm, hform, hqN, hval, hev,
    ha1_drop8, ha1_exc, h3_cyc, _, _⟩ :=
    odd_perfect_wave9_master_profile ho hN
  have he4 : N.factorization q % 4 = 1 := by simpa [hval] using ha4
  obtain ⟨h3_free_two, hrest_3dvd, hempty_3⟩ :=
    restrained_and_three_free_wave10_dichotomy ho hN hqN hq4 he4 hev
  refine ⟨h6, h8_or, hquarter, q, a, m, hq, hq4, ha4, hqm, hform, hqN, hval, hev,
    ha1_drop8, ?_, ha1_exc, h3_free_two, hrest_3dvd, hempty_3, h3_cyc, ?_⟩
  · intro ha_eq1
    have hform1 : N = q * m ^ 2 := by simpa [ha_eq1] using hform
    refine ⟨linear_euler_unique_source_order_dichotomy ho hN hq hq4 hqm hform1, ?_, ?_⟩
    · intro hq5
      subst hq5
      exact linear_euler_five_profile ho hN hqm hform1
    · intro hfermat hq_gt5
      exact linear_euler_fermat_gt_five_forces_eight_drop ho hN hq hqm hform1 hfermat hq_gt5
  · intro r hr p j hp hj hci_eq
    obtain ⟨hrq, hpo, hpq, hj36, hi17, hN17, hodd, heven⟩ :=
      component_prime_power_index_euler_only_and_undecuple_lift
        ho hN hqN hq4 he4 hev hr hp hj hci_eq
    refine ⟨hrq, hpo, hpq, hj36, hi17, hN17, hodd, fun hje => ?_⟩
    obtain ⟨hq1, heleven, h14, hj74, hi185, hN185⟩ := heven hje
    exact ⟨hval.symm.trans hq1, heleven, h14, hj74, hi185, hN185⟩

end OddPerfect
