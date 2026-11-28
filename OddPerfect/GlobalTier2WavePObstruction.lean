module

public import OddPerfect.LinearEulerLCMGcdTothObstruction
public import OddPerfect.LucasLehmerMersenneParityBridge
public import OddPerfect.MoebiusInversionAndCyclotomicExpandLaws
public import OddPerfect.SixthPowerFreeQ13CompCollisionPinch
public import OddPerfect.GlobalTier2WaveOObstruction
import Mathlib.Tactic.Ring

/-!
# Global Tier 2 Wave P Synthesis (`OddPerfect.GlobalTier2WavePObstruction`)

Unifies all four Priority Wave P structural modules (`910 → 915` public modules) into cross-module
global theorems with 100% preservation of every component invariant:
1. **Lucas–Lehmer / Mersenne Parity, Möbius Inversion, & Cyclotomic `expand` Envelope**
   (`odd_perfect_lucasLehmer_moebius_and_cyclotomic_expand_envelope`):
   bridges `Mathlib.NumberTheory.LucasLehmer` (completing `100%` nonzero coverage of all curated
   7-domain Mathlib modules in `research/MATHLIB_KB.md`), `ArithmeticFunction.Moebius`, and
   `Polynomial.Cyclotomic.Expand`.
2. **Tier 2 Wave P Master Profile** (`odd_perfect_tier2_waveP_master_profile`):
   couples the global Lucas–Lehmer / Möbius / cyclotomic-`expand` envelope with:
   - the `m_L = 1 ↔ L = 1` equivalence and unique `q`-source `r₀` split dichotomy across
     `m = gcd(m, L) * gcd(m, R)` (`r₀ ∣ m_L → 2 ≤ e₀ ∧ r₀ ^ 4 ∣ N ∧ σ(m_R ^ 2) ∣ I` vs.
     `r₀ ∣ m_R → σ(m_L ^ 2) ∣ I`), plus its sixth-power-free `53 ≤ m_R`, `2863 ≤ σ(m_R ^ 2)`,
     and `61 ≤ r₀` specialization, and
   - the sixth-power-free `Q₁₃_comp = Q₁₃_comp_free ∪ Q₁₃_comp_rep` refinement proving
     `|Q₁₃| + 2 * |Q₁₃_comp_free| + 2 * |Q₂₃| ≤ 2 * |S₅₁_col| + 1`,
     `219 ≤ 2 * |S₅₁_col| + |S₅₁_rep_src|`, and `S₅₁_rep_src = ∅ → 110 ≤ |S₅₁_col|`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- **1. Global Lucas–Lehmer, Möbius Inversion, & Cyclotomic `expand` Envelope**:
Preserves every conjunct from `LucasLehmerMersenneParityBridge` and
`MoebiusInversionAndCyclotomicExpandLaws`. -/
theorem odd_perfect_lucasLehmer_moebius_and_cyclotomic_expand_envelope {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) :
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
          n = 6 ∨ ∃ p : ℕ, 3 ≤ p ∧ p.Prime ∧ LucasLehmerTest p ∧ n = 2 ^ (p - 1) * mersenne p) ∧
    (∀ p : ℕ, 2 ≤ p →
      mersenne p % 4 = 3 ∧
      ((mersenne p).Prime → mersenne p ∣ N →
        Even (N.factorization (mersenne p)) ∧
        2 ≤ N.factorization (mersenne p) ∧
        (mersenne p) ^ 2 ∣ N)) ∧
    ¬ Squarefree N ∧
    ArithmeticFunction.moebius N = 0 ∧
    (∑ d ∈ N.divisors, ArithmeticFunction.moebius d) = 0 ∧
    (∑ d ∈ N.divisors, (ArithmeticFunction.moebius d) ^ 2) =
      (2 : ℤ) ^ N.primeFactors.card ∧
    (N.divisors.filter Squarefree).card = 2 ^ N.primeFactors.card ∧
    (∑ d ∈ N.divisors, ArithmeticFunction.moebius d * (sigma 1 (N / d) : ℤ)) = (N : ℤ) ∧
    (∀ (p n : ℕ) (x : ℤ), p.Prime → p ∣ n →
      (Polynomial.cyclotomic (n * p) ℤ).eval x =
        (Polynomial.cyclotomic n ℤ).eval (x ^ p)) ∧
    (∀ (p n : ℕ) (x : ℤ), p.Prime → ¬ p ∣ n →
      (Polynomial.cyclotomic (n * p) ℤ).eval x * (Polynomial.cyclotomic n ℤ).eval x =
        (Polynomial.cyclotomic n ℤ).eval (x ^ p)) ∧
    (∀ (p n : ℕ), [Fact p.Prime] → p ∣ n →
      Polynomial.cyclotomic (n * p) (ZMod p) = (Polynomial.cyclotomic n (ZMod p)) ^ p) ∧
    (∀ (p n : ℕ), [Fact p.Prime] → ¬ p ∣ n →
      Polynomial.cyclotomic (n * p) (ZMod p) = (Polynomial.cyclotomic n (ZMod p)) ^ (p - 1)) := by
  obtain ⟨hll1, hll2, hll3⟩ := lucasLehmer_mersenne_prime_and_nearPerfect_families
  have hmers := odd_perfect_mersenne_not_euler_and_even_valuation ho hN
  obtain ⟨hnsq, hmu0, hsum_mu, hsum_mu2, hsq_card, hinv⟩ :=
    odd_perfect_moebius_and_squarefree_divisor_laws ho hN
  obtain ⟨hcyc1, hcyc2, hcyc3, hcyc4⟩ := cyclotomic_expand_eval_and_char_p_laws
  exact ⟨hll1, hll2, hll3, hmers, hnsq, hmu0, hsum_mu, hsum_mu2, hsq_card, hinv,
    hcyc1, hcyc2, hcyc3, hcyc4⟩

/-- **2. Tier 2 Wave P Master Profile**:
Unconditionally synthesizes all four Wave P component modules with 100% invariant preservation. -/
theorem odd_perfect_tier2_waveP_master_profile {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) :
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
          n = 6 ∨ ∃ p : ℕ, 3 ≤ p ∧ p.Prime ∧ LucasLehmerTest p ∧ n = 2 ^ (p - 1) * mersenne p) ∧
    (∀ p : ℕ, 2 ≤ p →
      mersenne p % 4 = 3 ∧
      ((mersenne p).Prime → mersenne p ∣ N →
        Even (N.factorization (mersenne p)) ∧
        2 ≤ N.factorization (mersenne p) ∧
        (mersenne p) ^ 2 ∣ N)) ∧
    ¬ Squarefree N ∧
    ArithmeticFunction.moebius N = 0 ∧
    (∑ d ∈ N.divisors, ArithmeticFunction.moebius d) = 0 ∧
    (∑ d ∈ N.divisors, (ArithmeticFunction.moebius d) ^ 2) =
      (2 : ℤ) ^ N.primeFactors.card ∧
    (N.divisors.filter Squarefree).card = 2 ^ N.primeFactors.card ∧
    (∑ d ∈ N.divisors, ArithmeticFunction.moebius d * (sigma 1 (N / d) : ℤ)) = (N : ℤ) ∧
    (∀ (p n : ℕ) (x : ℤ), p.Prime → p ∣ n →
      (Polynomial.cyclotomic (n * p) ℤ).eval x =
        (Polynomial.cyclotomic n ℤ).eval (x ^ p)) ∧
    (∀ (p n : ℕ) (x : ℤ), p.Prime → ¬ p ∣ n →
      (Polynomial.cyclotomic (n * p) ℤ).eval x * (Polynomial.cyclotomic n ℤ).eval x =
        (Polynomial.cyclotomic n ℤ).eval (x ^ p)) ∧
    (∀ (p n : ℕ), [Fact p.Prime] → p ∣ n →
      Polynomial.cyclotomic (n * p) (ZMod p) = (Polynomial.cyclotomic n (ZMod p)) ^ p) ∧
    (∀ (p n : ℕ), [Fact p.Prime] → ¬ p ∣ n →
      Polynomial.cyclotomic (n * p) (ZMod p) = (Polynomial.cyclotomic n (ZMod p)) ^ (p - 1)) ∧
    ∃ q a m : ℕ,
      q.Prime ∧ q ∈ N.primeFactors ∧ q % 4 = 1 ∧ a % 4 = 1 ∧ 0 < a ∧ ¬ q ∣ m ∧
      N = q ^ a * m ^ 2 ∧
      (a = 1 →
        let A := (q + 1) / 2
        let I := componentIndex N q
        let L := Nat.factorizationLCMLeft A I
        let R := Nat.factorizationLCMRight A I
        let m_L := Nat.gcd m L
        let m_R := Nat.gcd m R
        (m_L = 1 ↔ L = 1) ∧
        (m_L ≠ 1 → 3 ≤ m_L ∧ 13 ≤ sigma 1 (m_L ^ 2)) ∧
        13 ≤ sigma 1 (m_R ^ 2) ∧
        ∃ r₀ ∈ m.primeFactors,
          let e₀ := m.factorization r₀
          (sigma 1 (m ^ 2)).factorization q = 1 ∧
          q ∣ sigma 1 (r₀ ^ (2 * e₀)) ∧
          ((r₀ ∣ m_L ∧ ¬ r₀ ∣ m_R ∧
              r₀ ∣ A ∧ 2 * r₀ ∣ q + 1 ∧ 2 ≤ e₀ ∧ r₀ ^ 4 ∣ N ∧
              q ∣ sigma 1 (m_L ^ 2) ∧ ¬ q ∣ sigma 1 (m_R ^ 2) ∧
              sigma 1 (m_R ^ 2) ∣ I ∧
              (sigma 1 (m_L ^ 2) / q) * sigma 1 (m_R ^ 2) = I) ∨
           (r₀ ∣ m_R ∧ ¬ r₀ ∣ m_L ∧
              q ∣ sigma 1 (m_R ^ 2) ∧ ¬ q ∣ sigma 1 (m_L ^ 2) ∧
              sigma 1 (m_L ^ 2) ∣ I ∧
              (sigma 1 (m_R ^ 2) / q) * sigma 1 (m_L ^ 2) = I))) ∧
      ((∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) →
        (∃ m₀ : ℕ,
          let A := (q + 1) / 2
          let I := componentIndex N q
          let L := Nat.factorizationLCMLeft A I
          let R := Nat.factorizationLCMRight A I
          let m_L := Nat.gcd m₀ L
          let m_R := Nat.gcd m₀ R
          Odd m₀ ∧ ¬ q ∣ m₀ ∧ N = q * m₀ ^ 2 ∧
          53 ≤ m_R ∧ 2863 ≤ sigma 1 (m_R ^ 2) ∧
          ∃ r₀ ∈ m₀.primeFactors,
            q ∣ sigma 1 (r₀ ^ (2 * m₀.factorization r₀)) ∧
            ((r₀ ∣ m_L ∧ ¬ r₀ ∣ m_R ∧
                m₀.factorization r₀ = 2 ∧ r₀ ∈ largeSources N q ∧
                61 ≤ r₀ ∧ 2 * r₀ ∣ q + 1 ∧
                sigma 1 (m_R ^ 2) ∣ I ∧
                (sigma 1 (m_L ^ 2) / q) * sigma 1 (m_R ^ 2) = I) ∨
             (r₀ ∣ m_R ∧ ¬ r₀ ∣ m_L ∧
                sigma 1 (m_L ^ 2) ∣ I ∧
                (sigma 1 (m_R ^ 2) / q) * sigma 1 (m_L ^ 2) = I))) ∧
        (let S₅₁ := (squareSources N).filter (· % 5 = 1)
         let S₅₁_col := S₅₁.filter (fun r => indegAt N q r = 2)
         let S₅₁_rep := S₅₁.filter (fun r => indegAt N q r = 1)
         let S₅₁_rep_src := S₅₁_rep.filter (fun r => ¬ r ∣ (q + 1) / 2)
         let Q₁₃ := oneModThreeLargeSources N q
         let Q₂₃ := twoModThreeLargeSources N q
         let repFib := fun u => S₅₁_rep_src.filter (fun r => r ∣ sigma 1 (u ^ 4))
         let Q₁₃_comp := Q₁₃.filter (fun u => ¬ q ∣ sigma 1 (u ^ 4) ∧ ¬ (sigma 1 (u ^ 4)).Prime)
         let Q₁₃_comp_free := Q₁₃_comp.filter (fun u => repFib u = ∅)
         let Q₁₃_comp_rep := Q₁₃_comp.filter (fun u => (repFib u).Nonempty)
         Q₁₃_comp = Q₁₃_comp_free ∪ Q₁₃_comp_rep ∧
         Disjoint Q₁₃_comp_free Q₁₃_comp_rep ∧
         Q₁₃_comp.card = Q₁₃_comp_free.card + Q₁₃_comp_rep.card ∧
         Q₁₃_comp_rep.card ≤ S₅₁_rep_src.card ∧
         Q₁₃.card + 2 * Q₁₃_comp_free.card + 2 * Q₂₃.card ≤ 2 * S₅₁_col.card + 1 ∧
         146 + 2 * Q₁₃_comp_free.card + Q₂₃.card ≤ 2 * S₅₁_col.card ∧
         3 * Q₁₃.card + 2 * Q₂₃.card ≤ 4 * S₅₁_col.card + 2 * S₅₁_rep_src.card + 3 ∧
         438 + Q₂₃.card ≤ 4 * S₅₁_col.card + 2 * S₅₁_rep_src.card ∧
         219 ≤ 2 * S₅₁_col.card + S₅₁_rep_src.card ∧
         N.primeFactors.card ≤ 4 * S₅₁_col.card + 2 * S₅₁_rep_src.card + 5 ∧
         (S₅₁_rep_src = ∅ → 110 ≤ S₅₁_col.card))) := by
  obtain ⟨hll1, hll2, hll3, hmers, hnsq, hmu0, hsum_mu, hsum_mu2, hsq_card, hinv,
    hcyc1, hcyc2, hcyc3, hcyc4⟩ :=
    odd_perfect_lucasLehmer_moebius_and_cyclotomic_expand_envelope ho hN
  obtain ⟨_, _, q, a, m, hq, hq_mem, hq4, ha4, ha_pos, hqm, hform, _, _, _⟩ :=
    odd_perfect_tier2_waveO_master_profile ho hN
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
  refine ⟨hll1, hll2, hll3, hmers, hnsq, hmu0, hsum_mu, hsum_mu2, hsq_card, hinv,
    hcyc1, hcyc2, hcyc3, hcyc4, q, a, m, hq, hq_mem, hq4, ha4, ha_pos, hqm, hform, ?_, ?_⟩
  · intro ha1
    have hform1 : N = q * m ^ 2 := by
      rw [hform, ha1, pow_one]
    exact linear_euler_mL_eq_one_iff_and_r0_split_dichotomy ho hN hq hqm hform1
  · intro hfree
    have hlcm :=
      sixth_power_free_lcm_gcd_coprime_split_profile ho hN hq_mem hq4 he_q hev_N hfree
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩ :=
      sixth_power_free_Q13_comp_free_and_rep_bounds ho hN hq_mem hq4 he_q hev_N hfree
    obtain ⟨hp1, hp2, hp3, hp4, hp5⟩ :=
      sixth_power_free_col_rep_src_pinch_and_110_bound ho hN hq_mem hq4 he_q hev_N hfree
    exact ⟨hlcm, hc1, hc2, hc3, hc4, hc5, hc6, hp1, hp2, hp3, hp4, hp5⟩

end OddPerfect
