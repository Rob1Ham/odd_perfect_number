module

public import OddPerfect.FactorizationLCMSplitCoprimeBalance
public import OddPerfect.PadicPade8119HigherContraction
public import OddPerfect.PellMatiyasevicAndFirstBlockReciprocity
public import OddPerfect.SixthPowerFreeRepSourceDecomposition
public import OddPerfect.GlobalTier2WaveNObstruction
import Mathlib.Tactic.Ring

/-!
# Global Tier 2 Wave O Synthesis (`OddPerfect.GlobalTier2WaveOObstruction`)

Unifies all four Priority Wave O structural modules (`905 → 910` public modules) into cross-module
global theorems with 100% preservation of every component invariant:
1. **Pell–Matiyasevic `ℤ√2` Tower & Fifth-Order `47321 / 8119` Pell–Padé Envelope**
   (`odd_perfect_pellMatiyasevic_and_47321_8119_envelope`):
   links `Pell.xn` / `Pell.yn` (`a = 3`, `d = 8`) with `silverUnit ^ (2 * n)` and establishes
   the fifth-order `47321 / 8119` Pell–Padé contraction, `(10 ^ 1000) ^ 6 * p * k_pade.natAbs < 6 ^ u`
   (`10 ^ 6000` margin), and sharpened repunit slopes across `r ∈ {5, 7, 11, 13}`.
2. **Tier 2 Wave O Master Profile** (`odd_perfect_tier2_waveO_master_profile`):
   couples the global Pell–Matiyasevic / `47321 / 8119` envelope with:
   - unconditional `(q + 1) / 2 < componentIndex N q`, `h₀ + 2 ≤ u₀` (strictly separating genuine
     `N = q * m ^ 2` from Descartes's spoof `198585576189`), and the canonical coprime
     `m = gcd(m, L) * gcd(m, R)` balance (`σ(m_L ^ 2) * σ(m_R ^ 2) = q * I`, `3 ≤ m_R < R`),
   - unconditional `¬ d ∣ geometricBlock q d`, `l ≠ d`, `legendreSym q l = 1`, `jacobiSym q v = 1`,
     and `jacobiSym q z = ZMod.χ₄ z` on `σ(m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`), and
   - the sixth-power-free `S₅₁_rep = S₅₁_rep_q ∪ S₅₁_rep_src` decomposition canceling `2 * |S₅₁_rep|`
     to prove `|Q₁₃| + 2 * |Q₂₃| ≤ 2 * |S₅₁_col| + 1`, `146 + |Q₂₃| ≤ 2 * |S₅₁_col|`, and
     `438 + 5 * |Q₂₃| ≤ 6 * |S₅₁_col|` (`Q₂₃.Nonempty → 74 ≤ |S₅₁_col|`).
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- **1. Global Pell–Matiyasevic `ℤ√2` & Fifth-Order `47321 / 8119` Pell–Padé Envelope**:
Preserves `pellMatiyasevic_three_eq_silverUnit_even_pow`, `padeSeq_sharpened_47321_8119_contraction`,
`sharpened_repunit_slopes_of_47321_8119_cap`, and `even_prime_power_47321_8119_and_ten_pow_6000_profile`. -/
theorem odd_perfect_pellMatiyasevic_and_47321_8119_envelope {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) :
    (let a1 : 1 < 3 := by decide
      StrictMono (Pell.xn a1) ∧
      StrictMono (Pell.yn a1) ∧
      ∀ n : ℕ,
        n < Pell.xn a1 n ∧
        n ≤ Pell.yn a1 n ∧
        Pell.xn a1 n * Pell.xn a1 n - 8 * Pell.yn a1 n * Pell.yn a1 n = 1 ∧
        ((silverUnit ^ (2 * n) : (ℤ√2)ˣ) : ℤ√2).re = (Pell.xn a1 n : ℤ) ∧
        ((silverUnit ^ (2 * n) : (ℤ√2)ˣ) : ℤ√2).im = 2 * (Pell.yn a1 n : ℤ)) ∧
    (∀ p u : ℕ, 3 ≤ p → 5 ≤ u →
      (8119 * padeSeqA u p ≤ 5741 * padeSeqB u p) ∧
      (8119 * padeSeqB (u + 1) p < 47321 * (p : ℤ) * padeSeqB u p) ∧
      (8119 ^ (u - 5) * padeSeqB u p < 8119 * 47321 ^ (u - 5) * (p : ℤ) ^ u)) ∧
    (∀ r l u : ℕ, 1154 ≤ u → 2 < l →
      8119 ^ (u - 5) * r ^ (l - 1) < 8119 * 47321 ^ (u - 5) →
      (r ∈ ({5, 7, 11, 13} : Finset ℕ) → 10 * l ≤ 11 * u + 10) ∧
      (r ∈ ({7, 11, 13} : Finset ℕ) → 32 * l ≤ 29 * u + 35 ∧ l + 107 ≤ u) ∧
      (r ∈ ({11, 13} : Finset ℕ) → 19 * l ≤ 14 * u + 20 ∧ l + 302 ≤ u) ∧
      (r = 13 → 13 * l ≤ 9 * u + 13 ∧ l + 354 ≤ u)) ∧
    (∀ r₀ ∈ N.primeFactors, ∀ p j : ℕ, p.Prime → 0 < j → Even j →
      componentIndex N r₀ = p ^ j →
      ∃ q s u r l : ℕ,
        let k_pade : ℤ := ((s : ℤ) * padeSeqB u p - padeSeqA u p) / (p : ℤ) ^ (2 * u + 1)
        r₀ = q ∧ q.Prime ∧ q % 4 = 1 ∧ N.factorization q = 1 ∧ Odd s ∧
        j = 2 * u ∧ 6541380665835014 ≤ u ∧
        sigma 1 (p ^ (2 * u)) = q ∧ q + 1 = 2 * s ^ 2 ∧ sigma 1 (s ^ 2) = p ^ (2 * u) ∧
        1 ≤ k_pade ∧
        8119 ^ (u - 5) * (p * k_pade.natAbs) < 8119 * 47321 ^ (u - 5) ∧
        (10 ^ 1000) ^ 6 * p * k_pade.natAbs < 6 ^ u ∧
        ((p % 4 = 3 ∨ Even u) → 2 * (10 ^ 1000) ^ 6 * p < 6 ^ u) ∧
        (p ∣ 64 ^ u - 1 → (10 ^ 1000) ^ 6 * p ^ 2 < 6 ^ u) ∧
        ((2 * u + 1) ∣ p - 2 → (10 ^ 1000) ^ 6 * u * p < 6 ^ u) ∧
        r ∈ ({3, 5, 7, 11, 13} : Finset ℕ) ∧ r.Prime ∧ 2 < l ∧ l.Prime ∧
        r ^ 2 ∣ N ∧ geometricBlock r l = p ∧
        (r ∈ ({5, 7, 11, 13} : Finset ℕ) → 10 * l ≤ 11 * u + 10) ∧
        (r ∈ ({7, 11, 13} : Finset ℕ) → 32 * l ≤ 29 * u + 35 ∧ l + 613254000000000 ≤ u) ∧
        (r ∈ ({11, 13} : Finset ℕ) → 19 * l ≤ 14 * u + 20 ∧ l + 1721415000000000 ≤ u) ∧
        (r = 13 → 13 * l ≤ 9 * u + 13 ∧ l + 2012732000000000 ≤ u)) := by
  refine ⟨pellMatiyasevic_three_eq_silverUnit_even_pow,
    fun p u hp3 hu5 => padeSeq_sharpened_47321_8119_contraction hp3 hu5,
    fun r l u hu hl hcap => sharpened_repunit_slopes_of_47321_8119_cap hu hl hcap,
    fun r₀ hr₀ p j hp hj_pos hj_even hidx =>
      even_prime_power_47321_8119_and_ten_pow_6000_profile ho hN hr₀ hp hj_pos hj_even hidx⟩

/-- **2. Tier 2 Wave O Master Profile**:
Unconditionally synthesizes all four Wave O component modules with 100% invariant preservation. -/
theorem odd_perfect_tier2_waveO_master_profile {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) :
    (let a1 : 1 < 3 := by decide
      StrictMono (Pell.xn a1) ∧
      StrictMono (Pell.yn a1) ∧
      ∀ n : ℕ,
        n < Pell.xn a1 n ∧
        n ≤ Pell.yn a1 n ∧
        Pell.xn a1 n * Pell.xn a1 n - 8 * Pell.yn a1 n * Pell.yn a1 n = 1 ∧
        ((silverUnit ^ (2 * n) : (ℤ√2)ˣ) : ℤ√2).re = (Pell.xn a1 n : ℤ) ∧
        ((silverUnit ^ (2 * n) : (ℤ√2)ˣ) : ℤ√2).im = 2 * (Pell.yn a1 n : ℤ)) ∧
    (∀ r₀ ∈ N.primeFactors, ∀ p j : ℕ, p.Prime → 0 < j → Even j →
      componentIndex N r₀ = p ^ j →
      ∃ q s u r l : ℕ,
        let k_pade : ℤ := ((s : ℤ) * padeSeqB u p - padeSeqA u p) / (p : ℤ) ^ (2 * u + 1)
        r₀ = q ∧ q.Prime ∧ q % 4 = 1 ∧ N.factorization q = 1 ∧ Odd s ∧
        j = 2 * u ∧ 6541380665835014 ≤ u ∧
        sigma 1 (p ^ (2 * u)) = q ∧ q + 1 = 2 * s ^ 2 ∧ sigma 1 (s ^ 2) = p ^ (2 * u) ∧
        1 ≤ k_pade ∧
        8119 ^ (u - 5) * (p * k_pade.natAbs) < 8119 * 47321 ^ (u - 5) ∧
        (10 ^ 1000) ^ 6 * p * k_pade.natAbs < 6 ^ u ∧
        ((p % 4 = 3 ∨ Even u) → 2 * (10 ^ 1000) ^ 6 * p < 6 ^ u) ∧
        (p ∣ 64 ^ u - 1 → (10 ^ 1000) ^ 6 * p ^ 2 < 6 ^ u) ∧
        ((2 * u + 1) ∣ p - 2 → (10 ^ 1000) ^ 6 * u * p < 6 ^ u) ∧
        r ∈ ({3, 5, 7, 11, 13} : Finset ℕ) ∧ r.Prime ∧ 2 < l ∧ l.Prime ∧
        r ^ 2 ∣ N ∧ geometricBlock r l = p ∧
        (r ∈ ({5, 7, 11, 13} : Finset ℕ) → 10 * l ≤ 11 * u + 10) ∧
        (r ∈ ({7, 11, 13} : Finset ℕ) → 32 * l ≤ 29 * u + 35 ∧ l + 613254000000000 ≤ u) ∧
        (r ∈ ({11, 13} : Finset ℕ) → 19 * l ≤ 14 * u + 20 ∧ l + 1721415000000000 ≤ u) ∧
        (r = 13 → 13 * l ≤ 9 * u + 13 ∧ l + 2012732000000000 ≤ u)) ∧
    ∃ q a m : ℕ,
      q.Prime ∧ q ∈ N.primeFactors ∧ q % 4 = 1 ∧ a % 4 = 1 ∧ 0 < a ∧ ¬ q ∣ m ∧
      N = q ^ a * m ^ 2 ∧
      (a = 1 →
        let A := (q + 1) / 2
        let I := componentIndex N q
        let g := Nat.gcd A I
        let L := Nat.factorizationLCMLeft A I
        let R := Nat.factorizationLCMRight A I
        let m_L := Nat.gcd m L
        let m_R := Nat.gcd m R
        q ^ 2 < 3 * m ^ 2 ∧
        A < I ∧
        q + 3 ≤ 2 * I ∧
        ¬ (I ∣ A) ∧
        1 < R ∧
        (∃ h₀ u₀ : ℕ,
          Odd h₀ ∧ Odd u₀ ∧ 1 ≤ h₀ ∧ 3 ≤ u₀ ∧ h₀ + 2 ≤ u₀ ∧
          Nat.Coprime h₀ u₀ ∧
          A = g * h₀ ^ 2 ∧ I = g * u₀ ^ 2 ∧ m = g * h₀ * u₀) ∧
        Odd m_L ∧ Odd m_R ∧
        Nat.Coprime m_L m_R ∧
        m = m_L * m_R ∧
        m_L ∣ L ∧ m_L ∣ A ∧ 2 * m_L ≤ q + 1 ∧ m_L < q ∧
        m_R ∣ R ∧ m_R ∣ I ∧ 3 ≤ m_R ∧ m_R < R ∧
        sigma 1 (m ^ 2) = sigma 1 (m_L ^ 2) * sigma 1 (m_R ^ 2) ∧
        sigma 1 (m_L ^ 2) * sigma 1 (m_R ^ 2) = q * I) ∧
      (1 < a → ∀ l t : ℕ, l.Prime → sigma 1 (m ^ 2) / q ^ a = l * t ^ 2 →
        let d := (a + 1) / 2
        ¬ d ∣ geometricBlock q d ∧
        l ≠ d ∧
        ∃ w z v : ℕ,
          0 < w ∧ 3 ≤ z ∧ Odd w ∧ Odd z ∧ Odd v ∧
          Nat.Coprime w z ∧ ¬ d ∣ z ∧ ¬ d ∣ v ∧
          q + 1 = 2 * d * w ^ 2 ∧
          (q ^ d + 1) / (q + 1) = d * z ^ 2 ∧
          geometricBlock q d = l * v ^ 2 ∧
          (∀ [Fact q.Prime] [Fact l.Prime],
            legendreSym l (q : ℤ) = 1 ∧
            legendreSym q (l : ℤ) = 1 ∧
            (∀ r ∈ (geometricBlock q d).primeFactors,
              ∀ [Fact r.Prime],
                legendreSym r (q : ℤ) = 1 ∧
                legendreSym q (r : ℤ) = 1)) ∧
          jacobiSym (v : ℤ) q = 1 ∧
          jacobiSym (q : ℤ) v = 1 ∧
          jacobiSym (z : ℤ) q = ZMod.χ₄ z ∧
          jacobiSym (q : ℤ) z = ZMod.χ₄ z) ∧
      ((∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) →
        let S₅₁ := (squareSources N).filter (· % 5 = 1)
        let S₅₁_col := S₅₁.filter (fun r => indegAt N q r = 2)
        let S₅₁_rep := S₅₁.filter (fun r => indegAt N q r = 1)
        let S₅₁_rep_q := S₅₁_rep.filter (fun r => r ∣ (q + 1) / 2)
        let S₅₁_rep_src := S₅₁_rep.filter (fun r => ¬ r ∣ (q + 1) / 2)
        let Q₁₃ := oneModThreeLargeSources N q
        let Q₂₃ := twoModThreeLargeSources N q
        let repFib := fun u => S₅₁_rep_src.filter (fun r => r ∣ sigma 1 (u ^ 4))
        S₅₁_rep = S₅₁_rep_q ∪ S₅₁_rep_src ∧
        Disjoint S₅₁_rep_q S₅₁_rep_src ∧
        S₅₁_rep.card = S₅₁_rep_q.card + S₅₁_rep_src.card ∧
        (∀ p ∈ squareSources N, ∀ r ∈ S₅₁, ¬ r ∣ sigma 1 (p ^ 2)) ∧
        (∀ r ∈ S₅₁_rep_src,
          ∃ u ∈ largeSources N q,
            (sigma 1 (u ^ 4)).factorization r = 2 ∧
            r ^ 2 ∣ sigma 1 (u ^ 4) ∧
            ∀ v ∈ (largeSources N q).erase u, ¬ r ∣ sigma 1 (v ^ 4)) ∧
        (∑ u ∈ largeSources N q, (repFib u).card) = S₅₁_rep_src.card ∧
        (∀ u ∈ largeSources N q, 2 * (repFib u).card + 1 ≤ cardFactors (sigma 1 (u ^ 4))) ∧
        (∀ u ∈ Q₂₃, 2 * (repFib u).card + 2 ≤ cardFactors (sigma 1 (u ^ 4))) ∧
        Q₁₃.card + 2 * Q₂₃.card ≤ 2 * S₅₁_col.card + 1 ∧
        146 + Q₂₃.card ≤ 2 * S₅₁_col.card ∧
        438 + 5 * Q₂₃.card ≤ 6 * S₅₁_col.card ∧
        (Q₂₃.Nonempty → 74 ≤ S₅₁_col.card)) := by
  obtain ⟨hpell, _, _, hpade_prof⟩ :=
    odd_perfect_pellMatiyasevic_and_47321_8119_envelope ho hN
  obtain ⟨_, _, _, _, _, _,
    q, a, m, hq, hq_mem, hq4, ha4, ha_pos, hqm, hform, _, _, _⟩ :=
    odd_perfect_tier2_waveN_master_profile ho hN
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
  refine ⟨hpell, hpade_prof, q, a, m, hq, hq_mem, hq4, ha4, ha_pos, hqm, hform, ?_, ?_, ?_⟩
  · intro ha1
    have hform1 : N = q * m ^ 2 := by
      rw [hform, ha1, pow_one]
    obtain ⟨hq2, hAI, hq3, hndiv, hR1, hex⟩ :=
      linear_euler_half_succ_lt_index_and_h0_lt_u0 ho hN hq hqm hform1
    obtain ⟨hmL_o, hmR_o, hcop_m, hm_eq, hmL_L, hmL_A, h2mL, hmLq,
      hmR_R, hmR_I, hmR3, hmR_lt, hsig1, hsig2⟩ :=
      linear_euler_lcm_gcd_canonical_coprime_split ho hN hq hqm hform1
    exact ⟨hq2, hAI, hq3, hndiv, hR1, hex, hmL_o, hmR_o, hcop_m, hm_eq,
      hmL_L, hmL_A, h2mL, hmLq, hmR_R, hmR_I, hmR3, hmR_lt, hsig1, hsig2⟩
  · intro ha_gt1 l t hl hi
    obtain ⟨hnd, hld, w, z, v, hw, hz3, hwo, hzo, hvo, hcop, hdz, hdv,
      hq1, hdiv, hgeom, hleg_lq, hleg_ql, hrec_all, hjvq, hjqv, hjzq, hjqz⟩ :=
      exceptional_euler_first_and_second_block_reciprocity_profile
        hN ho hq hq4 ha4 ha_gt1 hqm hform hl hi
    exact ⟨hnd, hld, w, z, v, hw, hz3, hwo, hzo, hvo, hcop, hdz, hdv,
      hq1, hdiv, hgeom, @fun _ _ => ⟨hleg_lq, hleg_ql, hrec_all⟩, hjvq, hjqv, hjzq, hjqz⟩
  · intro hfree
    obtain ⟨hp1, hp2, hp3, hp4, hp5⟩ :=
      sixth_power_free_S51_rep_source_partition ho hN hq_mem hq4 he_q hev_N hfree
    obtain ⟨hq1, hq2, hq3, hq4', hq5, hq6, hq7⟩ :=
      sixth_power_free_quartic_double_Q23_collision_pinch ho hN hq_mem hq4 he_q hev_N hfree
    exact ⟨hp1, hp2, hp3, hp4, hp5, hq1, hq2, hq3, hq4', hq5, hq6, hq7⟩

end OddPerfect
