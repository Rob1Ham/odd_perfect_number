module

public import OddPerfect.LinearEulerSixthPowerFreeRightSourcePeeling
public import OddPerfect.KummerBinomialAndCentralChooseObstruction
public import OddPerfect.SixthPowerFreeMirrorDichotomy74Pinch
public import OddPerfect.ExceptionalEuler42And486FactorDrop
public import OddPerfect.GlobalTier2WaveRObstruction
import Mathlib.Tactic.Ring

/-!
# Global Tier 2 Wave S Synthesis (`OddPerfect.GlobalTier2WaveSObstruction`)

Unifies all four Priority Wave S structural modules (`925 → 930` public modules) into cross-module
global theorems with 100% preservation of every component invariant:
1. **Kummer Dyadic Central Binomial, Double-Factorial, & Unconditional `74 ≤ |S₅₁_col|` Envelope**
   (`odd_perfect_kummer_central_choose_and_74_collision_envelope`):
   unifies Kummer's dyadic binomial valuation formula, central binomial & `(2 * ω)!` dyadic laws,
   and the unconditional elimination of the `|S₅₁_col| = 73` sixth-power-free extremal boundary
   (`74 ≤ |S₅₁_col|`, `148 ≤ 2 * |S₅₁_col|`).
2. **Tier 2 Wave S Master Profile** (`odd_perfect_tier2_waveS_master_profile`):
   couples the global Kummer & `74 ≤ |S₅₁_col|` envelope with:
   - sixth-power-free `Squarefree g_R`, `g_R ∣ u₀`, `g_R ^ 3 ∣ R`, exact valuations
     `(1, 1, 1, 3, 2, 4)` across `g_R.primeFactors`, and right-source `ordCompl[r₀]` peeling,
   - pure-`S₅₁_col` total-multiplicity (`Ω(N) ≤ 16 * |S₅₁_col| + 11`), excess (`M + E ≤ 10 * |S₅₁_col| + 6`),
     and component-drop (`∑ drop ≤ 26 * |S₅₁_col| + 18`) caps, and
   - exact `Ω(σ(q ^ a)) = 4 + 2 * (Ω(w) + Ω(z) + Ω(v))` (`10 ≤ Ω(σ(q ^ a))` at `d = 17`) and
     `42` / `86` / `150` / `486` component-index factor drops on `I = l * t ^ 2` (`a > 1`).
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- **1. Kummer Dyadic Central Binomial & Unconditional `74 ≤ |S₅₁_col|` Envelope**:
Preserves every conjunct from `KummerBinomialAndCentralChooseObstruction` and
`sixth_power_free_unconditional_74_S51_col_and_dichotomy`. -/
theorem odd_perfect_kummer_central_choose_and_74_collision_envelope {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) :
    let ω := N.primeFactors.card
    let rad := ∏ p ∈ N.primeFactors, p
    (∀ a b : ℕ,
      multiplicity 2 (Nat.choose (a + b) a) =
        (Nat.digits 2 a).sum + (Nat.digits 2 b).sum - (Nat.digits 2 (a + b)).sum) ∧
    (∀ n : ℕ, 1 ≤ n →
      multiplicity 2 (Nat.choose (2 * n) n) = (Nat.digits 2 n).sum ∧
      1 ≤ multiplicity 2 (Nat.choose (2 * n) n) ∧
      Even (Nat.choose (2 * n) n) ∧
      2 ^ (Nat.digits 2 n).sum ∣ Nat.choose (2 * n) n ∧
      2 ^ (Nat.digits 2 n).sum ≤ Nat.choose (2 * n) n ∧
      Nat.choose (2 * n) n < 4 ^ n) ∧
    multiplicity 2 (Nat.choose (2 * ω) ω) = (Nat.digits 2 ω).sum ∧
    multiplicity 2 (Nat.factorial (2 * ω)) = 2 * ω - (Nat.digits 2 ω).sum ∧
    multiplicity 2 (Nat.factorial (2 * ω)) = multiplicity 2 (2 ^ ω * Nat.factorial ω) ∧
    2 ^ (Nat.digits 2 ω).sum ∣ Nat.choose (2 * ω) ω ∧
    Even (Nat.choose (2 * ω) ω) ∧
    Nat.choose (2 * ω) ω < 4 ^ ω ∧
    2 ^ (Nat.digits 2 ω).sum * 2 ^ (2 * ω - (Nat.digits 2 ω).sum) = 4 ^ ω ∧
    3 * 2 ^ (2 * ω - (Nat.digits 2 ω).sum) < rad ∧
    (∃ q ∈ N.primeFactors,
      q % 4 = 1 ∧ N.factorization q % 4 = 1 ∧
      (let S₅₁ := (squareSources N).filter (· % 5 = 1)
       let S₅₁_col := S₅₁.filter (fun r => indegAt N q r = 2)
       ((∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) →
         74 ≤ S₅₁_col.card ∧ 148 ≤ 2 * S₅₁_col.card) ∧
       ((S₅₁_col.card < 74 ∨
         6 * S₅₁_col.card + 6 ≤ N.primeFactors.card ∨
         16 * S₅₁_col.card + 12 ≤ cardFactors N) →
         ∃ p : ℕ, p.Prime ∧ p ^ 6 ∣ N))) := by
  intro ω rad
  obtain ⟨hk1, hk2⟩ := kummer_dyadic_choose_and_central_binomial_laws
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8⟩ :=
    odd_perfect_central_choose_and_double_factorial_profile ho hN
  exact ⟨hk1, hk2, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8,
    sixth_power_free_unconditional_74_S51_col_and_dichotomy ho hN⟩

/-- **2. Tier 2 Wave S Master Profile**:
Unconditionally synthesizes all four Wave S component modules with 100% invariant preservation. -/
theorem odd_perfect_tier2_waveS_master_profile {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) :
    let ω := N.primeFactors.card
    let rad := ∏ p ∈ N.primeFactors, p
    (∀ a b : ℕ,
      multiplicity 2 (Nat.choose (a + b) a) =
        (Nat.digits 2 a).sum + (Nat.digits 2 b).sum - (Nat.digits 2 (a + b)).sum) ∧
    (∀ n : ℕ, 1 ≤ n →
      multiplicity 2 (Nat.choose (2 * n) n) = (Nat.digits 2 n).sum ∧
      1 ≤ multiplicity 2 (Nat.choose (2 * n) n) ∧
      Even (Nat.choose (2 * n) n) ∧
      2 ^ (Nat.digits 2 n).sum ∣ Nat.choose (2 * n) n ∧
      2 ^ (Nat.digits 2 n).sum ≤ Nat.choose (2 * n) n ∧
      Nat.choose (2 * n) n < 4 ^ n) ∧
    multiplicity 2 (Nat.choose (2 * ω) ω) = (Nat.digits 2 ω).sum ∧
    multiplicity 2 (Nat.factorial (2 * ω)) = 2 * ω - (Nat.digits 2 ω).sum ∧
    multiplicity 2 (Nat.factorial (2 * ω)) = multiplicity 2 (2 ^ ω * Nat.factorial ω) ∧
    2 ^ (Nat.digits 2 ω).sum ∣ Nat.choose (2 * ω) ω ∧
    Even (Nat.choose (2 * ω) ω) ∧
    Nat.choose (2 * ω) ω < 4 ^ ω ∧
    2 ^ (Nat.digits 2 ω).sum * 2 ^ (2 * ω - (Nat.digits 2 ω).sum) = 4 ^ ω ∧
    3 * 2 ^ (2 * ω - (Nat.digits 2 ω).sum) < rad ∧
    (∃ q ∈ N.primeFactors,
      q % 4 = 1 ∧ N.factorization q % 4 = 1 ∧
      (let S₅₁ := (squareSources N).filter (· % 5 = 1)
       let S₅₁_col := S₅₁.filter (fun r => indegAt N q r = 2)
       ((∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) →
         74 ≤ S₅₁_col.card ∧ 148 ≤ 2 * S₅₁_col.card) ∧
       ((S₅₁_col.card < 74 ∨
         6 * S₅₁_col.card + 6 ≤ N.primeFactors.card ∨
         16 * S₅₁_col.card + 12 ≤ cardFactors N) →
         ∃ p : ℕ, p.Prime ∧ p ^ 6 ∣ N))) ∧
    ∃ q a m : ℕ,
      q.Prime ∧ q ∈ N.primeFactors ∧ q % 4 = 1 ∧ a % 4 = 1 ∧ 0 < a ∧ ¬ q ∣ m ∧
      N = q ^ a * m ^ 2 ∧
      ((∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) →
        (∃ m₀ h₀ u₀ g_L g_R : ℕ,
          let A := (q + 1) / 2
          let I := componentIndex N q
          let R := Nat.factorizationLCMRight A I
          Odd m₀ ∧ ¬ q ∣ m₀ ∧ N = q * m₀ ^ 2 ∧
          Nat.gcd A I = g_L * g_R ∧
          Nat.Coprime g_L g_R ∧ Nat.Coprime g_L u₀ ∧ Nat.Coprime g_R h₀ ∧ Nat.Coprime h₀ u₀ ∧
          A = g_L * g_R * h₀ ^ 2 ∧ I = g_L * g_R * u₀ ^ 2 ∧ R = g_R * u₀ ^ 2 ∧
          Squarefree g_R ∧
          g_R ∣ u₀ ∧
          g_R ^ 3 ∣ R ∧
          (∀ p ∈ g_R.primeFactors,
            g_R.factorization p = 1 ∧
            u₀.factorization p = 1 ∧
            A.factorization p = 1 ∧
            I.factorization p = 3 ∧
            m₀.factorization p = 2 ∧
            N.factorization p = 4 ∧
            p ∈ largeSources N q ∧
            61 ≤ p) ∧
          (∀ p ∈ g_L.primeFactors,
            1 ≤ g_L.factorization p ∧
            g_L.factorization p ≤ 2 ∧
            61 ≤ p)) ∧
        (∃ m₀ h₀ u₀ g_L g_R r₀ : ℕ,
          let A := (q + 1) / 2
          let I := componentIndex N q
          let L := Nat.factorizationLCMLeft A I
          let R := Nat.factorizationLCMRight A I
          let m_L := Nat.gcd m₀ L
          let m_R := Nat.gcd m₀ R
          Odd m₀ ∧ ¬ q ∣ m₀ ∧ N = q * m₀ ^ 2 ∧
          A = g_L * g_R * h₀ ^ 2 ∧
          I = g_L * g_R * u₀ ^ 2 ∧
          Squarefree g_R ∧
          g_R ∣ u₀ ∧
          m_L = g_L * h₀ ∧
          m_R = g_R * u₀ ∧
          r₀ ∈ m₀.primeFactors ∧
          q ∣ sigma 1 (r₀ ^ (2 * m₀.factorization r₀)) ∧
          (r₀ ∣ m_R →
            let e₀ := m₀.factorization r₀
            let M_R := ordCompl[r₀] m_R
            let c₀ := sigma 1 (r₀ ^ (2 * e₀)) / q
            let W_R := sigma 1 (m_R ^ 2) / q
            m_R.factorization r₀ = e₀ ∧
            m_R = r₀ ^ e₀ * M_R ∧
            Nat.Coprime r₀ M_R ∧
            W_R = c₀ * sigma 1 (M_R ^ 2) ∧
            c₀ * sigma 1 (M_R ^ 2) * sigma 1 (m_L ^ 2) = g_L * g_R * u₀ ^ 2 ∧
            ((r₀ ∣ g_R ∧
                e₀ = 2 ∧
                N.factorization r₀ = 4 ∧
                A.factorization r₀ = 1 ∧
                I.factorization r₀ = 3 ∧
                r₀ ∈ largeSources N q ∧
                61 ≤ r₀) ∨
             (¬ r₀ ∣ g_R ∧
                (e₀ = 1 ∨ e₀ = 2) ∧
                r₀ ^ e₀ ∣ u₀ ∧
                Nat.Coprime r₀ A ∧
                M_R = g_R * (u₀ / r₀ ^ e₀) ∧
                r₀ ^ (2 * e₀) ∣ sigma 1 (M_R ^ 2) * sigma 1 (m_L ^ 2) ∧
                c₀ ∣ g_L * g_R * (u₀ / r₀ ^ e₀) ^ 2)))) ∧
        (let S₅₁ := (squareSources N).filter (· % 5 = 1)
         let S₅₁_col := S₅₁.filter (fun r => indegAt N q r = 2)
         let S₅₁_rep := S₅₁.filter (fun r => indegAt N q r = 1)
         let S₅₁_rep_src := S₅₁_rep.filter (fun r => ¬ r ∣ (q + 1) / 2)
         let Q₁₃ := oneModThreeLargeSources N q
         let Q₂₃ := twoModThreeLargeSources N q
         let repFib := fun u => S₅₁_rep_src.filter (fun r => r ∣ sigma 1 (u ^ 4))
         let Q₁₃_comp := Q₁₃.filter (fun u => ¬ q ∣ sigma 1 (u ^ 4) ∧ ¬ (sigma 1 (u ^ 4)).Prime)
         let Q₁₃_comp_free := Q₁₃_comp.filter (fun u => repFib u = ∅)
         cardFactors N + 16 * Q₁₃_comp_free.card + 12 * Q₂₃.card ≤ 16 * S₅₁_col.card + 11 ∧
         cardFactors N ≤ 16 * S₅₁_col.card + 11 ∧
         localRepeatExcess N q + collisionExcess N q + 10 * Q₁₃_comp_free.card + 7 * Q₂₃.card ≤
           10 * S₅₁_col.card + 6 ∧
         localRepeatExcess N q + collisionExcess N q ≤ 10 * S₅₁_col.card + 6 ∧
         (∑ p ∈ N.primeFactors, (cardFactors N - cardFactors (componentIndex N p))) +
           26 * Q₁₃_comp_free.card + 19 * Q₂₃.card ≤ 26 * S₅₁_col.card + 18 ∧
         (∑ p ∈ N.primeFactors, (cardFactors N - cardFactors (componentIndex N p))) ≤
           26 * S₅₁_col.card + 18)) ∧
      (1 < a → ∀ l t : ℕ, l.Prime → sigma 1 (m ^ 2) / q ^ a = l * t ^ 2 →
        let d := (a + 1) / 2
        (∃ w z v : ℕ,
          0 < w ∧ 3 ≤ z ∧ 0 < v ∧
          q + 1 = 2 * d * w ^ 2 ∧
          (q ^ d + 1) / (q + 1) = d * z ^ 2 ∧
          geometricBlock q d = l * v ^ 2 ∧
          sigma 1 (q ^ a) = 2 * d ^ 2 * l * (w * z * v) ^ 2 ∧
          cardFactors (sigma 1 (q ^ a)) =
            4 + 2 * (cardFactors w + cardFactors z + cardFactors v) ∧
          6 ≤ cardFactors (sigma 1 (q ^ a)) ∧
          (d = 17 → 2 ≤ cardFactors w ∧ 10 ≤ cardFactors (sigma 1 (q ^ a)))) ∧
        cardFactors (componentIndex N q) + 42 ≤ cardFactors N ∧
        (d ≠ 17 → cardFactors (componentIndex N q) + 86 ≤ cardFactors N) ∧
        (¬ 3 ∣ N → cardFactors (componentIndex N q) + 150 ≤ cardFactors N) ∧
        (¬ 3 ∣ N → ¬ 5 ∣ N → cardFactors (componentIndex N q) + 486 ≤ cardFactors N)) := by
  intro ω rad
  obtain ⟨hk1, hk2, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, h74⟩ :=
    odd_perfect_kummer_central_choose_and_74_collision_envelope ho hN
  obtain ⟨_, _, _, _, q, a, m, hq, hq_mem, hq4, ha4, ha_pos, hqm, hform, _, _, _⟩ :=
    odd_perfect_tier2_waveR_master_profile ho hN
  have hm0 : m ≠ 0 := by
    intro hm
    rw [hm] at hform
    simp at hform
    exact hN.2.ne' hform
  have hfact_q : N.factorization q = a := by
    rw [hform, Nat.factorization_mul (pow_ne_zero a hq.ne_zero) (pow_ne_zero 2 hm0),
      Finsupp.add_apply, hq.factorization_pow, Finsupp.single_eq_same]
    have hqm2 : ¬ q ∣ m ^ 2 := fun hd => hqm (hq.dvd_of_dvd_pow hd)
    rw [Nat.factorization_eq_zero_of_not_dvd hqm2]
    omega
  have he_q : N.factorization q % 4 = 1 := by omega
  have hev_N : ∀ r : ℕ, r ≠ q → Even (N.factorization r) := by
    intro r hr_ne
    by_cases hr_prime : r.Prime
    · rw [hform, Nat.factorization_mul (pow_ne_zero a hq.ne_zero) (pow_ne_zero 2 hm0),
        Finsupp.add_apply, hq.factorization_pow, Finsupp.single_eq_of_ne hr_ne, zero_add,
        Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
      exact ⟨m.factorization r, by ring⟩
    · rw [Nat.factorization_eq_zero_of_not_prime N hr_prime]
      exact ⟨0, rfl⟩
  refine ⟨hk1, hk2, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, h74,
    q, a, m, hq, hq_mem, hq4, ha4, ha_pos, hqm, hform, ?_, ?_⟩
  · intro hfree
    exact ⟨sixth_power_free_gR_squarefree_and_valuation_pinch ho hN hq_mem hq4 he_q hev_N hfree,
      sixth_power_free_right_source_peeling_profile ho hN hq_mem hq4 he_q hev_N hfree,
      sixth_power_free_pure_collision_total_and_drop_caps ho hN hq_mem hq4 he_q hev_N hfree⟩
  · intro ha_gt1 l t hl hi
    obtain ⟨hd1, hd2, hd3, hd4⟩ :=
      exceptional_euler_42_86_150_486_factor_drop hN ho hq hq4 ha4 ha_gt1 hqm hform hl hi
    exact ⟨exceptional_euler_exact_sigma_q_cardFactors hN ho hq hq4 ha4 ha_gt1 hqm hform hl hi,
      hd1, hd2, hd3, hd4⟩

end OddPerfect
