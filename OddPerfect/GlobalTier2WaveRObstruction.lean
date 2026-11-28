module

public import OddPerfect.LinearEulerGcdSplitSourcePeeling
public import OddPerfect.PadicPade47321SixthOrderContraction
public import OddPerfect.SixthPowerFreePureCollisionRankCap
public import OddPerfect.ExceptionalBlockCoprimeFactorizationAndTargetRouting
public import OddPerfect.GlobalTier2WaveQObstruction
import Mathlib.Tactic.Ring

/-!
# Global Tier 2 Wave R Synthesis (`OddPerfect.GlobalTier2WaveRObstruction`)

Unifies all four Priority Wave R structural modules (`920 → 925` public modules) into cross-module
global theorems with 100% preservation of every component invariant:
1. **Sixth-Order `275807 / 47321` Pell–Padé Contraction, Million-Digit Margin, & Pure-`S₅₁_col`
   Dichotomy Envelope** (`odd_perfect_pade_275807_47321_and_pure_collision_envelope`):
   unifies the sixth-order `275807 / 47321` Pell–Padé contraction, sharpened repunit slopes across
   `r ∈ {3, 5, 7, 11, 13}`, `(10 ^ 1000) ^ 1000 * p * k_pade.natAbs < 6 ^ u` (`10 ^ 1,000,000`
   margin), and the global sixth-power dichotomy on `S₅₁_col.card < 73 ∨ 6 * S₅₁_col.card + 6 ≤ ω(N)`.
2. **Tier 2 Wave R Master Profile** (`odd_perfect_tier2_waveR_master_profile`):
   couples the global `275807 / 47321` & pure-`S₅₁_col` envelope with:
   - the `g_R` fourth-power law and `ordCompl[r₀]` right-source peeling dichotomy on `N = q * m ^ 2`,
   - the sixth-power-free pure-`S₅₁_col` repeat, square-source, and prime-support bounds
     (`N.primeFactors.card + 6 * Q₁₃_comp_free.card + 5 * Q₂₃.card ≤ 6 * S₅₁_col.card + 5`,
     `73 + Q₁₃_comp_free.card ≤ S₅₁_col.card`), and
   - the exceptional Euler-index coprime-triple factorization `m = d * l * w * z * v * t`,
     `d * l * z ∣ m`, `l`-target routing into `{q} ∪ t.primeFactors`, and three-/five-free
     `z.minFac` & `d * l * z` floors (`556631`, `37494917`, `6572805461`).
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- **1. Sixth-Order `275807 / 47321` Pell–Padé & Pure-`S₅₁_col` Dichotomy Envelope**:
Preserves every conjunct from `PadicPade47321SixthOrderContraction` and
`sixth_power_dichotomy_on_pure_S51_col_cap`. -/
theorem odd_perfect_pade_275807_47321_and_pure_collision_envelope {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) :
    (∀ p u : ℕ, 3 ≤ p → 6 ≤ u →
      padeLeadB 6 = 47321 ∧
      padeLeadB 7 = 275807 ∧
      (47321 * padeSeqA u p ≤ 33461 * padeSeqB u p) ∧
      (47321 * padeSeqB (u + 1) p < 275807 * (p : ℤ) * padeSeqB u p) ∧
      (47321 ^ (u - 6) * padeSeqB u p < 47321 * 275807 ^ (u - 6) * (p : ℤ) ^ u) ∧
      (∀ k : ℤ, 1 ≤ k → (p : ℤ) ^ (u + 1) * k < padeSeqB u p →
        47321 ^ (u - 6) * (p * k.natAbs) < 47321 * 275807 ^ (u - 6))) ∧
    (∀ r l u : ℕ, 6 ≤ u → 1 ≤ l →
      47321 ^ (u - 6) * r ^ (l - 1) < 47321 * 275807 ^ (u - 6) →
      (3 ≤ r → 43 * l ≤ 69 * u + 50) ∧
      (5 ≤ r → 31 * l ≤ 34 * u + 34) ∧
      (7 ≤ r → 32 * l ≤ 29 * u + 35) ∧
      (11 ≤ r → 34 * l ≤ 25 * u + 36) ∧
      (13 ≤ r → 16 * l ≤ 11 * u + 17)) ∧
    (∀ r₀ ∈ N.primeFactors, ∀ p j : ℕ, p.Prime → 0 < j → Even j →
      componentIndex N r₀ = p ^ j →
      ∃ q s u r l : ℕ,
        let k_pade : ℤ := ((s : ℤ) * padeSeqB u p - padeSeqA u p) / (p : ℤ) ^ (2 * u + 1)
        r₀ = q ∧ q.Prime ∧ q % 4 = 1 ∧ N.factorization q = 1 ∧ Odd s ∧
        j = 2 * u ∧ 6541380665835014 ≤ u ∧
        sigma 1 (p ^ (2 * u)) = q ∧ q + 1 = 2 * s ^ 2 ∧ sigma 1 (s ^ 2) = p ^ (2 * u) ∧
        1 ≤ k_pade ∧
        47321 ^ (u - 6) * (p * k_pade.natAbs) < 47321 * 275807 ^ (u - 6) ∧
        (10 ^ 1000) ^ 1000 * p * k_pade.natAbs < 6 ^ u ∧
        ((p % 4 = 3 ∨ Even u) → 2 * (10 ^ 1000) ^ 1000 * p < 6 ^ u) ∧
        (p ∣ 64 ^ u - 1 → (10 ^ 1000) ^ 1000 * p ^ 2 < 6 ^ u) ∧
        ((2 * u + 1) ∣ p - 2 → (10 ^ 1000) ^ 1000 * u * p < 6 ^ u) ∧
        r ∈ ({3, 5, 7, 11, 13} : Finset ℕ) ∧ r.Prime ∧ 2 < l ∧ l.Prime ∧
        r ^ 2 ∣ N ∧ geometricBlock r l = p ∧
        (3 ≤ r → 43 * l ≤ 69 * u + 50) ∧
        (5 ≤ r → 31 * l ≤ 34 * u + 34) ∧
        (7 ≤ r → 32 * l ≤ 29 * u + 35 ∧ l + 613254437422031 ≤ u) ∧
        (11 ≤ r → 34 * l ≤ 25 * u + 36 ∧ l + 1731541940956326 ≤ u) ∧
        (13 ≤ r → 16 * l ≤ 11 * u + 17 ∧ l + 2044181458073440 ≤ u) ∧
        (∀ r' ∈ s.primeFactors,
          let l' : ℕ := 2 * s.factorization r' + 1
          geometricBlock r' l' = p →
            (43 * l' ≤ 69 * u + 50) ∧
            (5 ≤ r' → 31 * l' ≤ 34 * u + 34) ∧
            (7 ≤ r' → 32 * l' ≤ 29 * u + 35 ∧ l' + 613254437422031 ≤ u) ∧
            (11 ≤ r' → 34 * l' ≤ 25 * u + 36 ∧ l' + 1731541940956326 ≤ u) ∧
            (13 ≤ r' → 16 * l' ≤ 11 * u + 17 ∧ l' + 2044181458073440 ≤ u))) ∧
    (∃ q ∈ N.primeFactors,
      q % 4 = 1 ∧ N.factorization q % 4 = 1 ∧
      (let S₅₁ := (squareSources N).filter (· % 5 = 1)
       let S₅₁_col := S₅₁.filter (fun r => indegAt N q r = 2)
       (S₅₁_col.card < 73 ∨ 6 * S₅₁_col.card + 6 ≤ N.primeFactors.card) →
         ∃ p : ℕ, p.Prime ∧ p ^ 6 ∣ N)) :=
  ⟨fun _ _ hp3 hu6 => padeSeq_sharpened_275807_47321_contraction hp3 hu6,
   fun _ _ _ hu6 hl1 hcap => sharpened_repunit_slopes_of_275807_47321_cap hu6 hl1 hcap,
   fun _ hr₀ _ _ hp hj_pos hj_even hidx =>
     even_prime_power_275807_47321_and_million_digit_profile ho hN hr₀ hp hj_pos hj_even hidx,
   sixth_power_dichotomy_on_pure_S51_col_cap ho hN⟩

/-- **2. Tier 2 Wave R Master Profile**:
Unconditionally synthesizes all four Wave R component modules with 100% invariant preservation. -/
theorem odd_perfect_tier2_waveR_master_profile {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) :
    (∀ p u : ℕ, 3 ≤ p → 6 ≤ u →
      padeLeadB 6 = 47321 ∧
      padeLeadB 7 = 275807 ∧
      (47321 * padeSeqA u p ≤ 33461 * padeSeqB u p) ∧
      (47321 * padeSeqB (u + 1) p < 275807 * (p : ℤ) * padeSeqB u p) ∧
      (47321 ^ (u - 6) * padeSeqB u p < 47321 * 275807 ^ (u - 6) * (p : ℤ) ^ u) ∧
      (∀ k : ℤ, 1 ≤ k → (p : ℤ) ^ (u + 1) * k < padeSeqB u p →
        47321 ^ (u - 6) * (p * k.natAbs) < 47321 * 275807 ^ (u - 6))) ∧
    (∀ r l u : ℕ, 6 ≤ u → 1 ≤ l →
      47321 ^ (u - 6) * r ^ (l - 1) < 47321 * 275807 ^ (u - 6) →
      (3 ≤ r → 43 * l ≤ 69 * u + 50) ∧
      (5 ≤ r → 31 * l ≤ 34 * u + 34) ∧
      (7 ≤ r → 32 * l ≤ 29 * u + 35) ∧
      (11 ≤ r → 34 * l ≤ 25 * u + 36) ∧
      (13 ≤ r → 16 * l ≤ 11 * u + 17)) ∧
    (∀ r₀ ∈ N.primeFactors, ∀ p j : ℕ, p.Prime → 0 < j → Even j →
      componentIndex N r₀ = p ^ j →
      ∃ q s u r l : ℕ,
        let k_pade : ℤ := ((s : ℤ) * padeSeqB u p - padeSeqA u p) / (p : ℤ) ^ (2 * u + 1)
        r₀ = q ∧ q.Prime ∧ q % 4 = 1 ∧ N.factorization q = 1 ∧ Odd s ∧
        j = 2 * u ∧ 6541380665835014 ≤ u ∧
        sigma 1 (p ^ (2 * u)) = q ∧ q + 1 = 2 * s ^ 2 ∧ sigma 1 (s ^ 2) = p ^ (2 * u) ∧
        1 ≤ k_pade ∧
        47321 ^ (u - 6) * (p * k_pade.natAbs) < 47321 * 275807 ^ (u - 6) ∧
        (10 ^ 1000) ^ 1000 * p * k_pade.natAbs < 6 ^ u ∧
        ((p % 4 = 3 ∨ Even u) → 2 * (10 ^ 1000) ^ 1000 * p < 6 ^ u) ∧
        (p ∣ 64 ^ u - 1 → (10 ^ 1000) ^ 1000 * p ^ 2 < 6 ^ u) ∧
        ((2 * u + 1) ∣ p - 2 → (10 ^ 1000) ^ 1000 * u * p < 6 ^ u) ∧
        r ∈ ({3, 5, 7, 11, 13} : Finset ℕ) ∧ r.Prime ∧ 2 < l ∧ l.Prime ∧
        r ^ 2 ∣ N ∧ geometricBlock r l = p ∧
        (3 ≤ r → 43 * l ≤ 69 * u + 50) ∧
        (5 ≤ r → 31 * l ≤ 34 * u + 34) ∧
        (7 ≤ r → 32 * l ≤ 29 * u + 35 ∧ l + 613254437422031 ≤ u) ∧
        (11 ≤ r → 34 * l ≤ 25 * u + 36 ∧ l + 1731541940956326 ≤ u) ∧
        (13 ≤ r → 16 * l ≤ 11 * u + 17 ∧ l + 2044181458073440 ≤ u) ∧
        (∀ r' ∈ s.primeFactors,
          let l' : ℕ := 2 * s.factorization r' + 1
          geometricBlock r' l' = p →
            (43 * l' ≤ 69 * u + 50) ∧
            (5 ≤ r' → 31 * l' ≤ 34 * u + 34) ∧
            (7 ≤ r' → 32 * l' ≤ 29 * u + 35 ∧ l' + 613254437422031 ≤ u) ∧
            (11 ≤ r' → 34 * l' ≤ 25 * u + 36 ∧ l' + 1731541940956326 ≤ u) ∧
            (13 ≤ r' → 16 * l' ≤ 11 * u + 17 ∧ l' + 2044181458073440 ≤ u))) ∧
    (∃ q ∈ N.primeFactors,
      q % 4 = 1 ∧ N.factorization q % 4 = 1 ∧
      (let S₅₁ := (squareSources N).filter (· % 5 = 1)
       let S₅₁_col := S₅₁.filter (fun r => indegAt N q r = 2)
       (S₅₁_col.card < 73 ∨ 6 * S₅₁_col.card + 6 ≤ N.primeFactors.card) →
         ∃ p : ℕ, p.Prime ∧ p ^ 6 ∣ N)) ∧
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
        (∃ h₀ u₀ g_L g_R : ℕ,
          Nat.gcd A I = g_L * g_R ∧
          Nat.Coprime g_L g_R ∧
          Nat.Coprime g_L u₀ ∧
          Nat.Coprime g_R h₀ ∧
          Nat.Coprime h₀ u₀ ∧
          A = g_L * g_R * h₀ ^ 2 ∧
          I = g_L * g_R * u₀ ^ 2 ∧
          L = g_L * h₀ ^ 2 ∧
          R = g_R * u₀ ^ 2 ∧
          m_R = g_R * u₀ ∧
          (∀ p ∈ g_R.primeFactors,
            1 ≤ A.factorization p ∧
            A.factorization p + 2 ≤ I.factorization p ∧
            3 ≤ I.factorization p ∧
            2 ≤ m.factorization p ∧
            p ^ 4 ∣ N ∧
            2 * p ∣ q + 1 ∧
            (p ≠ 3 → p ∈ largeSources N q))) ∧
        (∃ h₀ u₀ g_L g_R r₀ : ℕ,
          A = g_L * g_R * h₀ ^ 2 ∧
          I = g_L * g_R * u₀ ^ 2 ∧
          m_L = g_L * h₀ ∧
          m_R = g_R * u₀ ∧
          r₀ ∈ m.primeFactors ∧
          q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀)) ∧
          (r₀ ∣ m_R →
            let e₀ := m.factorization r₀
            let M_R := ordCompl[r₀] m_R
            let c₀ := sigma 1 (r₀ ^ (2 * e₀)) / q
            let W_R := sigma 1 (m_R ^ 2) / q
            m_R.factorization r₀ = e₀ ∧
            m_R = r₀ ^ e₀ * M_R ∧
            Nat.Coprime r₀ M_R ∧
            W_R = c₀ * sigma 1 (M_R ^ 2) ∧
            c₀ * sigma 1 (M_R ^ 2) * sigma 1 (m_L ^ 2) = g_L * g_R * u₀ ^ 2 ∧
            ((r₀ ∣ g_R ∧
                2 ≤ e₀ ∧
                3 ≤ I.factorization r₀ ∧
                r₀ ^ 4 ∣ N ∧
                2 * r₀ ∣ q + 1 ∧
                (r₀ ≠ 3 → r₀ ∈ largeSources N q)) ∨
             (¬ r₀ ∣ g_R ∧
                r₀ ^ e₀ ∣ u₀ ∧
                Nat.Coprime r₀ A ∧
                M_R = g_R * (u₀ / r₀ ^ e₀) ∧
                r₀ ^ (2 * e₀) ∣ sigma 1 (M_R ^ 2) * sigma 1 (m_L ^ 2) ∧
                c₀ ∣ g_L * g_R * (u₀ / r₀ ^ e₀) ^ 2))))) ∧
      ((∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) →
        let S := squareSources N
        let S₅₀ := S.filter (· % 5 ≠ 1)
        let S₅₁ := S.filter (· % 5 = 1)
        let S₅₁_col := S₅₁.filter (fun r => indegAt N q r = 2)
        let S₅₁_rep := S₅₁.filter (fun r => indegAt N q r = 1)
        let S₅₁_rep_q := S₅₁_rep.filter (fun r => r ∣ (q + 1) / 2)
        let S₅₁_rep_src := S₅₁_rep.filter (fun r => ¬ r ∣ (q + 1) / 2)
        let Q₁₃ := oneModThreeLargeSources N q
        let Q₂₃ := twoModThreeLargeSources N q
        let repFib := fun u => S₅₁_rep_src.filter (fun r => r ∣ sigma 1 (u ^ 4))
        let Q₁₃_comp := Q₁₃.filter (fun u => ¬ q ∣ sigma 1 (u ^ 4) ∧ ¬ (sigma 1 (u ^ 4)).Prime)
        let Q₁₃_comp_free := Q₁₃_comp.filter (fun u => repFib u = ∅)
        S₅₀.card + S₅₁_rep.card + 4 * Q₁₃_comp_free.card + 4 * Q₂₃.card ≤ 3 * S₅₁_col.card + 3 ∧
        S₅₀.card + S₅₁_rep_q.card + S₅₁_rep_src.card + 4 * Q₁₃_comp_free.card + 4 * Q₂₃.card ≤
          3 * S₅₁_col.card + 3 ∧
        S.card + 4 * Q₁₃_comp_free.card + 4 * Q₂₃.card ≤ 4 * S₅₁_col.card + 3 ∧
        N.primeFactors.card + 6 * Q₁₃_comp_free.card + 5 * Q₂₃.card ≤ 6 * S₅₁_col.card + 5 ∧
        N.primeFactors.card ≤ 6 * S₅₁_col.card + 5 ∧
        438 + 6 * Q₁₃_comp_free.card + 5 * Q₂₃.card ≤ 6 * S₅₁_col.card ∧
        73 + Q₁₃_comp_free.card ≤ S₅₁_col.card ∧
        (Q₁₃_comp_free.Nonempty ∨ Q₂₃.Nonempty → 74 ≤ S₅₁_col.card)) ∧
      (1 < a → ∀ l t : ℕ, l.Prime → sigma 1 (m ^ 2) / q ^ a = l * t ^ 2 →
        let d := (a + 1) / 2
        (∃ w z v : ℕ,
          0 < w ∧ 3 ≤ z ∧ 3 ≤ t ∧ Odd w ∧ Odd z ∧ Odd v ∧ Odd t ∧
          q + 1 = 2 * d * w ^ 2 ∧
          (q ^ d + 1) / (q + 1) = d * z ^ 2 ∧
          geometricBlock q d = l * v ^ 2 ∧
          m = d * l * w * z * v * t ∧
          Nat.Coprime d l ∧
          Nat.Coprime d z ∧
          Nat.Coprime l z ∧
          Nat.Coprime w z ∧
          Nat.Coprime l w ∧
          d * l * z ∣ m ∧
          83 ≤ z.minFac ∧
          (d = 17 → 239 ≤ z.minFac) ∧
          556631 ≤ d * l * z ∧
          (∀ p ∈ (sigma 1 (ordProj[l] N)).primeFactors, p = q ∨ p ∣ t)) ∧
        (∃ z : ℕ,
          3 ≤ z ∧
          (q ^ d + 1) / (q + 1) = d * z ^ 2 ∧
          d * l * z ∣ m ∧
          (¬ 3 ∣ N →
            293 ≤ z.minFac ∧
            37494917 ≤ d * l * z) ∧
          (¬ 3 ∣ N → ¬ 5 ∣ N →
            1637 ≤ z.minFac ∧
            (d = 241 → 2411 ≤ z.minFac) ∧
            6572805461 ≤ d * l * z))) := by
  obtain ⟨hp1, hp2, hp3, hp4⟩ := odd_perfect_pade_275807_47321_and_pure_collision_envelope ho hN
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    q, a, m, hq, hq_mem, hq4, ha4, ha_pos, hqm, hform, _, _, _⟩ :=
    odd_perfect_tier2_waveQ_master_profile ho hN
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
  refine ⟨hp1, hp2, hp3, hp4, q, a, m, hq, hq_mem, hq4, ha4, ha_pos, hqm, hform, ?_, ?_, ?_⟩
  · intro ha1
    have hform1 : N = q * m ^ 2 := by
      rw [hform, ha1, pow_one]
    exact ⟨linear_euler_gR_fourth_power_law ho hN hq hqm hform1,
      linear_euler_right_source_peeling_dichotomy ho hN hq hqm hform1⟩
  · intro hfree
    exact sixth_power_free_pure_collision_repeat_and_rank_bounds ho hN hq_mem hq4 he_q hev_N hfree
  · intro ha_gt1 l t hl hi
    exact ⟨exceptional_euler_coprime_triple_factorization_and_l_routing
        hN ho hq hq4 ha4 ha_gt1 hqm hform hl hi,
      exceptional_euler_three_and_five_free_coprime_triple_bounds
        hN ho hq hq4 ha4 ha_gt1 hqm hform hl hi⟩

end OddPerfect
