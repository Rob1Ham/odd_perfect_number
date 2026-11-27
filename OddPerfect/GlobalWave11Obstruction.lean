module

public import OddPerfect.GlobalWave10Obstruction
public import OddPerfect.ThreeFreeTwoLargeSources
public import OddPerfect.RestrainedThreeSquareObstruction
public import OddPerfect.NineFactorDropObstruction
public import OddPerfect.TridecupleRepunitObstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Wave 11 Global Obstruction Synthesis (`OddPerfect.GlobalWave11Obstruction`)

Tier 2 global synthesis unifying and cross-coupling the four Wave 11 structural pillars:
1. `OddPerfect.ThreeFreeTwoLargeSources`:
   - Proves `two_le_oneModThreeLarge_or_three_le_largeSources_of_three_free`
     (`¬ 3 ∣ N → 2 ≤ (oneModThreeLargeSources N q).card ∨ 3 ≤ (largeSources N q).card`),
     forcing both large sources to be `≡ 1 [MOD 3]` whenever `(largeSources N q).card = 2`,
     and `oneModThreeLarge_nonempty_or_seven_le_largeSources_of_three_free`
     (`(oneModThreeLargeSources N q).Nonempty ∨ 7 ≤ (largeSources N q).card`).
2. `OddPerfect.RestrainedThreeSquareObstruction`:
   - Eliminates `N.factorization 3 = 2` across all restrained candidates with `q % 3 = 2`
     (`four_le_three_exponent_of_restrained_euler_two_mod_three`:
     `(largeSources N q).card ≤ 1 → q % 3 = 2 → 4 ≤ N.factorization 3 ∧ 81 ∣ N`, including `q = 5`).
3. `OddPerfect.NineFactorDropObstruction`:
   - Proves `five_le_cardFactors_sigma_fifth_pow` (`5 ≤ Ω(σ(q^5))` for all primes `q ≡ 1 [MOD 4]`)
     and `two_le_cardFactors_sigma_eighth_pow` (`2 ≤ Ω(σ(r^8))`), upgrading the global drop
     dichotomy from `+ 8` to `+ 9` while **preserving `v_q(N) = 1` and eighth-power-freeness** on
     the complement, and lifting `largeSources N q = ∅` (and Fermat linear Euler `q > 5`) to `+ 9`.
4. `OddPerfect.TridecupleRepunitObstruction`:
   - Eliminates `|S₁| ∈ {11, 12}` symbolically on even prime-power component indices
     `i_q = p ^ (2 * u)`, forcing `HasThirteenOddPrimeRepunits p ∧ 16 ≤ ω(N)`,
     `13082761331670028 ≤ j`, and `10 ^ 353234555955090756 < i_q < N`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- **Wave 11 Three-Free & Restrained Support Dichotomy**:
Unifies three-free large-source residue structure (`2 ≤ |Q₁₃| ∨ 3 ≤ |largeSources|`,
`Q₁₃.Nonempty ∨ 7 ≤ |largeSources|`), restrained `3`-divisibility with `4 ≤ v₃(N)` whenever
`q % 3 = 2`, and the explicit `+ 9` drop at `p = 3` when `largeSources N q = ∅`. -/
theorem restrained_and_three_free_wave11_dichotomy {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) :
    (¬ 3 ∣ N →
      q % 12 = 1 ∧ 13 ≤ q ∧ 2 ≤ (largeSources N q).card ∧
      (2 ≤ (oneModThreeLargeSources N q).card ∨ 3 ≤ (largeSources N q).card) ∧
      ((oneModThreeLargeSources N q).Nonempty ∨ 7 ≤ (largeSources N q).card)) ∧
    ((largeSources N q).card ≤ 1 →
      3 ∣ N ∧ (q % 3 = 2 → 4 ≤ N.factorization 3 ∧ 81 ∣ N)) ∧
    (largeSources N q = ∅ →
      3 ∈ N.primeFactors ∧ 8 ≤ N.factorization 3 ∧
      cardFactors (componentIndex N 3) + 9 ≤ cardFactors N) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h3
    obtain ⟨hq12, hq13⟩ := three_free_euler_prime_mod_twelve ho hN hq hq4 he h3
    exact ⟨hq12, hq13,
      two_le_largeSources_of_three_free ho hN hq hq4 he hev h3,
      two_le_oneModThreeLarge_or_three_le_largeSources_of_three_free ho hN hq hq4 he hev h3,
      oneModThreeLarge_nonempty_or_seven_le_largeSources_of_three_free ho hN hq hq4 he hev h3⟩
  · intro hle
    exact ⟨three_dvd_of_largeSources_le_one ho hN hq hq4 he hev hle,
      four_le_three_exponent_of_restrained_euler_two_mod_three ho hN hq hq4 he hev hle⟩
  · intro hempty
    have h8 := eight_le_three_exponent_of_largeSources_empty ho hN hq hq4 he hev hempty
    obtain ⟨h3_mem, hdrop9⟩ :=
      exists_nine_drop_at_three_of_largeSources_empty ho hN hq hq4 he hev hempty
    exact ⟨h3_mem, h8, hdrop9⟩

/-- **Cross-Pillar Fermat Linear Euler Nine-Factor Drop**:
Every linear Euler odd perfect number `N = q * m ^ 2` with Fermat prime `q > 5` (`q - 1 = 2 ^ k`)
has a prime sixteenth power `r₀ ^ 16 ∣ N` and hence admits a nine-factor component-index drop. -/
theorem linear_euler_fermat_gt_five_forces_nine_drop {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m)
    (hform : N = q * m ^ 2) (hfermat : ∃ k : ℕ, q - 1 = 2 ^ k) (hq5 : 5 < q) :
    (∃ r₀ : ℕ, r₀.Prime ∧ r₀ ^ 16 ∣ N) ∧
    (∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 9 ≤ cardFactors N) := by
  obtain ⟨⟨r₀, hr₀_prime, hr₀_16⟩, _⟩ :=
    linear_euler_fermat_gt_five_forces_eight_drop ho hN hq hqm hform hfermat hq5
  have hr₀_8 : r₀ ^ 8 ∣ N := (pow_dvd_pow r₀ (by decide : 8 ≤ 16)).trans hr₀_16
  exact ⟨⟨r₀, hr₀_prime, hr₀_16⟩,
    exists_componentIndex_cardFactors_add_nine_le_of_eighth_power ho hN ⟨r₀, hr₀_prime, hr₀_8⟩⟩

/-- **Euler-Only Tridecuple-Repunit Prime-Power Component-Index Obstruction**:
Every prime-power component index `componentIndex N r = p ^ j` (`j ≥ 1`) occurs exclusively at the
Euler prime `r = q`, satisfies `36207 ≤ j` and `10 ^ 17240 < componentIndex N q < N`, and when `j`
is even forces `N.factorization q = 1`, `HasThirteenOddPrimeRepunits p`, `16 ≤ ω(N)`,
`13082761331670028 ≤ j`, and `10 ^ 353234555955090756 < componentIndex N q < N`. -/
theorem component_prime_power_index_euler_only_and_tridecuple_lift {N q r p j : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ s : ℕ, s ≠ q → Even (N.factorization s))
    (hr : r ∈ N.primeFactors) (hp : p.Prime) (hj : 0 < j)
    (hci_eq : componentIndex N r = p ^ j) :
    r = q ∧ Odd p ∧ p ≠ q ∧
    36207 ≤ j ∧ 10 ^ 17240 < componentIndex N q ∧ 10 ^ 17240 < N ∧
    (Odd j → ¬ ExcludedFermatResidue q) ∧
    (Even j → N.factorization q = 1 ∧ HasThirteenOddPrimeRepunits p ∧ 16 ≤ N.primeFactors.card ∧
      13082761331670028 ≤ j ∧
      10 ^ 353234555955090756 < componentIndex N q ∧ 10 ^ 353234555955090756 < N) := by
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
  obtain ⟨hthirteen, h16⟩ :=
    even_prime_power_component_forces_thirteen_repunits_and_sixteen_primes
      hN ho hq_prime ha_pos hNb hqb hleft hright hp hu hi2
  obtain ⟨hj130, hi353, hN353⟩ :=
    even_prime_power_component_size_gt_ten_pow_353234555955090756
      hN ho hq_prime ha_pos hNb hqb hleft hright hp hj hj_even' hi_eq
  exact ⟨hq1, hthirteen, h16, hj130, lt_of_lt_of_eq hi353 hci.symm, hN353⟩

/-- Unified Wave 11 global obstruction profile across every odd perfect number `N`. -/
theorem odd_perfect_wave11_master_profile {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    (∃ p ∈ N.primeFactors,
      cardFactors (componentIndex N p) + 6 ≤ cardFactors N ∧
      7 ≤ N.factorization p + cardFactors (sigma 1 (ordProj[p] N))) ∧
    ((∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 9 ≤ cardFactors N) ∨
      ((∀ p : ℕ, p.Prime → ¬ p ^ 8 ∣ N) ∧
        (∀ r ∈ N.primeFactors, N.factorization r = 6 →
          cardFactors (sigma 1 (r ^ 6)) ≤ 3 ∧ (r % 7 ≠ 1 → sigma 1 (r ^ 6) % 7 = 1)) ∧
        2 * cardFactors N + 1 ≤ 9 * N.primeFactors.card)) ∧
    (((squareSources N).filter (· % 5 = 1)).card < 110 ∨
      4 * ((squareSources N).filter (· % 5 = 1)).card + 6 ≤ N.primeFactors.card →
      ∃ p : ℕ, p.Prime ∧ p ^ 6 ∣ N) ∧
    ∃ q a m, q.Prime ∧ q % 4 = 1 ∧ a % 4 = 1 ∧ ¬ q ∣ m ∧ N = q ^ a * m ^ 2 ∧
      q ∈ N.primeFactors ∧ N.factorization q = a ∧
      (∀ r, r ≠ q → Even (N.factorization r)) ∧
      (1 < a → ∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 9 ≤ cardFactors N) ∧
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
          (∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 9 ≤ cardFactors N))) ∧
      (1 < a → ∀ l t : ℕ, l.Prime → sigma 1 (m ^ 2) / q ^ a = l * t ^ 2 →
        componentIndex N q = l * t ^ 2 ∧
        oddSigmaTargets N q = {l} ∧
        cardFactors (componentIndex N q) + 36 ≤ cardFactors N ∧
        (¬ 3 ∣ N → cardFactors (componentIndex N q) + 148 ≤ cardFactors N)) ∧
      (¬ 3 ∣ N →
        q % 12 = 1 ∧ 13 ≤ q ∧ 2 ≤ (largeSources N q).card ∧
        (2 ≤ (oneModThreeLargeSources N q).card ∨ 3 ≤ (largeSources N q).card) ∧
        ((oneModThreeLargeSources N q).Nonempty ∨ 7 ≤ (largeSources N q).card)) ∧
      ((largeSources N q).card ≤ 1 →
        3 ∣ N ∧ (q % 3 = 2 → 4 ≤ N.factorization 3 ∧ 81 ∣ N)) ∧
      (largeSources N q = ∅ →
        3 ∈ N.primeFactors ∧ 8 ≤ N.factorization 3 ∧
        cardFactors (componentIndex N 3) + 9 ≤ cardFactors N) ∧
      (¬ 3 ∣ N →
        (∃ p ∈ N.primeFactors, Relation.TransGen (oddSigmaEdge N) p p) ∨
          (a = 1 ∧ q % 48 = 1 ∧ 97 ≤ q ∧ IsSquare ((q + 1) / 2))) ∧
      (∀ r ∈ N.primeFactors, ∀ p j, p.Prime → 0 < j → componentIndex N r = p ^ j →
        r = q ∧ Odd p ∧ p ≠ q ∧ 36207 ≤ j ∧
        10 ^ 17240 < componentIndex N q ∧ 10 ^ 17240 < N ∧
        (Odd j → ¬ ExcludedFermatResidue q) ∧
        (Even j → a = 1 ∧ HasThirteenOddPrimeRepunits p ∧ 16 ≤ N.primeFactors.card ∧
          13082761331670028 ≤ j ∧
          10 ^ 353234555955090756 < componentIndex N q ∧ 10 ^ 353234555955090756 < N)) := by
  obtain ⟨h6, _, hquarter, q, a, m, hq, hq4, ha4, hqm, hform, hqN, hval, hev,
    _, ha_eq1_w10, ha1_exc, _, _, _, h3_cyc, _⟩ :=
    odd_perfect_wave10_master_profile ho hN
  have he4 : N.factorization q % 4 = 1 := by simpa [hval] using ha4
  have h9_or :
      (∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 9 ≤ cardFactors N) ∨
        ((∀ p : ℕ, p.Prime → ¬ p ^ 8 ∣ N) ∧
          (∀ r ∈ N.primeFactors, N.factorization r = 6 →
            cardFactors (sigma 1 (r ^ 6)) ≤ 3 ∧ (r % 7 ≠ 1 → sigma 1 (r ^ 6) % 7 = 1)) ∧
          2 * cardFactors N + 1 ≤ 9 * N.primeFactors.card) := by
    by_cases h9 : ∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 9 ≤ cardFactors N
    · exact Or.inl h9
    · right
      have hno : ∀ p ∈ N.primeFactors, cardFactors N < cardFactors (componentIndex N p) + 9 :=
        fun p hp => Nat.lt_of_not_ge fun hge => h9 ⟨p, hp, hge⟩
      obtain ⟨_, _, hfree8, hsextic, hdens9⟩ :=
        no_nine_factor_drop_profile ho hN hqN hq4 he4 hev hno
      exact ⟨hfree8, hsextic, hdens9⟩
  obtain ⟨h3_free_w11, hrest_w11, hempty_3⟩ :=
    restrained_and_three_free_wave11_dichotomy ho hN hqN hq4 he4 hev
  refine ⟨h6, h9_or, hquarter, q, a, m, hq, hq4, ha4, hqm, hform, hqN, hval, hev,
    ?_, ?_, ha1_exc, h3_free_w11, hrest_w11, hempty_3, h3_cyc, ?_⟩
  · intro ha1
    exact exists_componentIndex_cardFactors_add_nine_le_of_euler_exp_gt_one
      ho hN hqN hq4 he4 hev (hval ▸ ha1)
  · intro ha_eq1
    obtain ⟨hord_dich, hq5_prof, _⟩ := ha_eq1_w10 ha_eq1
    have hform1 : N = q * m ^ 2 := by simpa [ha_eq1] using hform
    refine ⟨hord_dich, hq5_prof, fun hfermat hq_gt5 => ?_⟩
    exact linear_euler_fermat_gt_five_forces_nine_drop ho hN hq hqm hform1 hfermat hq_gt5
  · intro r hr p j hp hj hci_eq
    obtain ⟨hrq, hpo, hpq, hj36, hi17, hN17, hodd, heven⟩ :=
      component_prime_power_index_euler_only_and_tridecuple_lift
        ho hN hqN hq4 he4 hev hr hp hj hci_eq
    refine ⟨hrq, hpo, hpq, hj36, hi17, hN17, hodd, fun hje => ?_⟩
    obtain ⟨hq1, hthirteen, h16, hj130, hi353, hN353⟩ := heven hje
    exact ⟨hval.symm.trans hq1, hthirteen, h16, hj130, hi353, hN353⟩

end OddPerfect
