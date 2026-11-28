module

public import OddPerfect.FactorizationLCMSplitObstruction
public import OddPerfect.AntitoneLogAndEvenIndexSubexpPinch
public import OddPerfect.LegendreHomAndSecondBlockReciprocity
public import OddPerfect.SixthPowerFreeBipartiteSlackPinch
public import OddPerfect.GlobalTier2WaveMObstruction

/-!
# Global Tier 2 Wave N Synthesis (`OddPerfect.GlobalTier2WaveNObstruction`)

Unifies all four Priority Wave N structural modules into cross-module global theorems with
100% preservation of every component invariant:
1. **Antitone Log-Over-Self Prime-Reciprocal & Monotone Stirling Envelope**
   (`odd_perfect_antitone_log_and_stirling_rank_envelope`):
   unconditionally bounds `log p / p ≤ log (N.minFac) / N.minFac ≤ log 3 / 3` for all `p ∣ N`,
   `∑_{p ∣ N} log p / p ^ 2 < (log (N.minFac) / N.minFac) * log 2 ≤ (log 3 / 3) * log 2`,
   `6 * K * (log (2 * K) - 1) < log 3 + 4 * log N` for `1 ≤ K ≤ ω(N)`, `6 * ω(N) < log 3 + 4 * log N`,
   and `30 * ω(N) < log 3 + 4 * log N` when sixth-power-free.
2. **Tier 2 Wave N Master Profile** (`odd_perfect_tier2_waveN_master_profile`):
   couples the global antitone-log / Stirling envelope with:
   - the universal `gcd` / `factorizationLCMLeft` / `factorizationLCMRight` square parametrization
     `A = g * h₀ ^ 2`, `I = g * u₀ ^ 2`, `m = g * h₀ * u₀`, `L * R = g * h₀ ^ 2 * u₀ ^ 2`,
     `σ((g * h₀ * u₀) ^ 2) = g * (2 * g * h₀ ^ 2 - 1) * u₀ ^ 2` and non-coprime (`3 ≤ g`) prime
     collision profile on `N = q * m ^ 2`,
   - the second-block Legendre & Jacobi reciprocity law `legendreSym q r = ZMod.χ₄ r` and
     `jacobiSym q z = jacobiSym z q = ZMod.χ₄ z` on `σ(m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`), and
   - the sixth-power-free `Q₁₃_prime ↪ S₅₁_col` injection and sharpened collision/repeat slack
     bounds (`3 * |Q₁₃| + 2 * |Q₂₃| + 2 * |S₅₁_rep_q| ≤ 4 * |S₅₁_col| + 2 * |S₅₁_rep| + 3`,
     `219 ≤ 2 * |S₅₁_col| + |S₅₁_rep|`, `ω(N) + 2 * |S₅₁_rep_q| ≤ 4 * |S₅₁_col| + 2 * |S₅₁_rep| + 5`).
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- **1. Global Antitone Log-Over-Self & Monotone Stirling Rank Envelope**:
Unconditionally preserves every global analytic invariant from
`AntitoneLogAndEvenIndexSubexpPinch`. -/
theorem odd_perfect_antitone_log_and_stirling_rank_envelope {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) :
    (∀ p ∈ N.primeFactors,
      Real.log (p : ℝ) / (p : ℝ) ≤ Real.log (N.minFac : ℝ) / (N.minFac : ℝ) ∧
      Real.log (p : ℝ) / (p : ℝ) ≤ Real.log 3 / 3) ∧
    (∑ p ∈ N.primeFactors, Real.log (p : ℝ) / (p : ℝ) ^ 2) <
      (Real.log (N.minFac : ℝ) / (N.minFac : ℝ)) * Real.log 2 ∧
    (∑ p ∈ N.primeFactors, Real.log (p : ℝ) / (p : ℝ) ^ 2) <
      (Real.log 3 / 3) * Real.log 2 ∧
    (∀ K : ℕ, 1 ≤ K → K ≤ N.primeFactors.card →
      6 * (K : ℝ) * (Real.log (2 * (K : ℝ)) - 1) < Real.log 3 + 4 * Real.log (N : ℝ)) ∧
    6 * (N.primeFactors.card : ℝ) < Real.log 3 + 4 * Real.log (N : ℝ) ∧
    ((∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) →
      30 * (N.primeFactors.card : ℝ) < Real.log 3 + 4 * Real.log (N : ℝ)) := by
  obtain ⟨hpt, hlt_min, hlt_three⟩ :=
    odd_perfect_antitone_log_div_self_prime_reciprocal_bounds ho hN
  obtain ⟨hmono, h6ω, h30ω⟩ :=
    odd_perfect_stirling_monotone_rank_and_sixth_power_free_bounds ho hN
  exact ⟨hpt, hlt_min, hlt_three, hmono, h6ω, h30ω⟩

/-- **2. Tier 2 Wave N Master Profile**:
Unconditionally synthesizes all four Wave N component modules with 100% invariant preservation. -/
theorem odd_perfect_tier2_waveN_master_profile {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) :
    (∀ p ∈ N.primeFactors,
      Real.log (p : ℝ) / (p : ℝ) ≤ Real.log (N.minFac : ℝ) / (N.minFac : ℝ) ∧
      Real.log (p : ℝ) / (p : ℝ) ≤ Real.log 3 / 3) ∧
    (∑ p ∈ N.primeFactors, Real.log (p : ℝ) / (p : ℝ) ^ 2) <
      (Real.log (N.minFac : ℝ) / (N.minFac : ℝ)) * Real.log 2 ∧
    (∑ p ∈ N.primeFactors, Real.log (p : ℝ) / (p : ℝ) ^ 2) <
      (Real.log 3 / 3) * Real.log 2 ∧
    (∀ K : ℕ, 1 ≤ K → K ≤ N.primeFactors.card →
      6 * (K : ℝ) * (Real.log (2 * (K : ℝ)) - 1) < Real.log 3 + 4 * Real.log (N : ℝ)) ∧
    6 * (N.primeFactors.card : ℝ) < Real.log 3 + 4 * Real.log (N : ℝ) ∧
    ((∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) →
      30 * (N.primeFactors.card : ℝ) < Real.log 3 + 4 * Real.log (N : ℝ)) ∧
    ∃ q a m : ℕ,
      q.Prime ∧ q ∈ N.primeFactors ∧ q % 4 = 1 ∧ a % 4 = 1 ∧ 0 < a ∧ ¬ q ∣ m ∧
      N = q ^ a * m ^ 2 ∧
      (a = 1 →
        let A := (q + 1) / 2
        let I := componentIndex N q
        let g := Nat.gcd A I
        let L := Nat.factorizationLCMLeft A I
        let R := Nat.factorizationLCMRight A I
        Odd g ∧ 1 ≤ g ∧ g ∣ m ∧
        Nat.Coprime L R ∧ L ∣ A ∧ R ∣ I ∧ L * R = Nat.lcm A I ∧
        (∃ h₀ u₀ : ℕ,
          Odd h₀ ∧ Odd u₀ ∧ 1 ≤ h₀ ∧ 1 ≤ u₀ ∧
          Nat.Coprime h₀ u₀ ∧
          A = g * h₀ ^ 2 ∧
          I = g * u₀ ^ 2 ∧
          m = g * h₀ * u₀ ∧
          q = 2 * g * h₀ ^ 2 - 1 ∧
          L * R = g * h₀ ^ 2 * u₀ ^ 2 ∧
          sigma 1 ((g * h₀ * u₀) ^ 2) = g * (2 * g * h₀ ^ 2 - 1) * u₀ ^ 2 ∧
          (g = 1 ↔ Nat.Coprime A I)) ∧
        (¬ Nat.Coprime A I →
          3 ≤ g ∧
          ∀ s ∈ g.primeFactors,
            s.Prime ∧ Odd s ∧ 2 * s ∣ q + 1 ∧ s ∣ I ∧ s ∣ m ∧
            ∃ p ∈ m.primeFactors, p ≠ s ∧ s ∣ sigma 1 (p ^ (2 * m.factorization p)))) ∧
      (1 < a → ∀ l t : ℕ, l.Prime → sigma 1 (m ^ 2) / q ^ a = l * t ^ 2 →
        let d := (a + 1) / 2
        ∃ y w z : ℕ,
          0 < y ∧ 0 < w ∧ 3 ≤ z ∧ Odd w ∧ Odd z ∧ Nat.Coprime w z ∧ ¬ d ∣ z ∧
          y = d * w * z ∧ q + 1 = 2 * d * w ^ 2 ∧ (q ^ d + 1) / (q + 1) = d * z ^ 2 ∧
          q ^ d + 1 = 2 * y ^ 2 ∧
          (z : ℤ) ^ 2 ≡ 1 + (d : ℤ) * (w : ℤ) ^ 2 [ZMOD (d : ℤ) ^ 2] ∧
          (∀ r ∈ z.primeFactors, 2 * d ∣ r - 1) ∧ 2 * d + 1 ≤ z.minFac ∧
          (∀ [Fact q.Prime],
            ∀ r ∈ z.primeFactors,
              ∀ [Fact r.Prime],
                legendreSym r (q : ℤ) = ZMod.χ₄ r ∧
                legendreSym q (r : ℤ) = ZMod.χ₄ r ∧
                (legendreSym q (r : ℤ) = 1 ↔ r % 4 = 1) ∧
                (legendreSym q (r : ℤ) = -1 ↔ r % 4 = 3)) ∧
          jacobiSym (z : ℤ) q = ZMod.χ₄ z ∧
          jacobiSym (q : ℤ) z = ZMod.χ₄ z ∧
          (z % 4 = 1 → jacobiSym (q : ℤ) z = 1) ∧
          (z % 4 = 3 → jacobiSym (q : ℤ) z = -1)) ∧
      ((∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) →
        let S₅₀ := (squareSources N).filter (· % 5 ≠ 1)
        let S₅₁ := (squareSources N).filter (· % 5 = 1)
        let S₅₁_col := S₅₁.filter (fun r => indegAt N q r = 2)
        let S₅₁_rep := S₅₁.filter (fun r => indegAt N q r = 1)
        let S₅₁_rep_q := S₅₁_rep.filter (fun r => r ∣ (q + 1) / 2)
        let Q₁₃ := oneModThreeLargeSources N q
        let Q₂₃ := twoModThreeLargeSources N q
        let Q₁₃_prime := Q₁₃.filter (fun u => ¬ q ∣ sigma 1 (u ^ 4) ∧ (sigma 1 (u ^ 4)).Prime)
        Q₁₃_prime.card ≤ S₅₁_col.card ∧
        3 * Q₁₃.card + 2 * Q₂₃.card + 2 * S₅₁_rep_q.card ≤
          4 * S₅₁_col.card + 2 * S₅₁_rep.card + 3 ∧
        438 + Q₂₃.card + 2 * S₅₁_rep_q.card ≤ 4 * S₅₁_col.card + 2 * S₅₁_rep.card ∧
        219 ≤ 2 * S₅₁_col.card + S₅₁_rep.card ∧
        N.primeFactors.card + 2 * S₅₁_rep_q.card ≤ 4 * S₅₁_col.card + 2 * S₅₁_rep.card + 5 ∧
        S₅₀.card + Q₁₃.card + Q₂₃.card + 2 * S₅₁_rep_q.card ≤
          3 * S₅₁_col.card + S₅₁_rep.card + 4) := by
  obtain ⟨hpt, hlt_min, hlt_three, hmono, h6ω, h30ω⟩ :=
    odd_perfect_antitone_log_and_stirling_rank_envelope ho hN
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _,
    q, a, m, hq, hq_mem, hq4, ha4, ha_pos, hqm, hform, _, _, _⟩ :=
    odd_perfect_tier2_waveM_master_profile ho hN
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
  refine ⟨hpt, hlt_min, hlt_three, hmono, h6ω, h30ω,
    q, a, m, hq, hq_mem, hq4, ha4, ha_pos, hqm, hform, ?_, ?_, ?_⟩
  · intro ha1
    have hform1 : N = q * m ^ 2 := by
      rw [hform, ha1, pow_one]
    obtain ⟨hg_odd, hg_ge1, hg_m, hLR_cop, hL_dvd, hR_dvd, hLR_lcm, hex⟩ :=
      universal_half_succ_index_gcd_square_parametrization ho hN hq hqm hform1
    refine ⟨hg_odd, hg_ge1, hg_m, hLR_cop, hL_dvd, hR_dvd, hLR_lcm, hex, ?_⟩
    intro hncop
    exact noncoprime_half_succ_gcd_prime_collision_profile ho hN hq hqm hform1 hncop
  · intro ha_gt1 l t hl hi
    obtain ⟨y, w, z, hy, hw, hz3, hwo, hzo, hcop, hdz, hydwz, hq1, hdiv, hpow,
      hmod, hpf, hmin, hrec, hjac1, hjac2, hz1, hz3m⟩ :=
      exceptional_euler_second_block_jacobi_and_legendre_profile
        hN ho hq hq4 ha4 ha_gt1 hqm hform hl hi
    exact ⟨y, w, z, hy, hw, hz3, hwo, hzo, hcop, hdz, hydwz, hq1, hdiv, hpow,
      hmod, hpf, hmin, @fun _ => hrec, hjac1, hjac2, hz1, hz3m⟩
  · intro hfree
    have hinj :=
      sixth_power_free_Q13_prime_inj_into_S51_col ho hN hq_mem hq4 he_q hev_N hfree
    have hcap :=
      sixth_power_free_sharpened_col_rep_bipartite_bound ho hN hq_mem hq4 he_q hev_N hfree
    obtain ⟨h438, h219, hω5, hS50⟩ :=
      sixth_power_free_omega_le_four_col_add_two_rep ho hN hq_mem hq4 he_q hev_N hfree
    exact ⟨hinj, hcap, h438, h219, hω5, hS50⟩

end OddPerfect
