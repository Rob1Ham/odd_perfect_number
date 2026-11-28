module

public import OddPerfect.LinearEulerNoncoprimeHalfSuccQuotientDuality
public import OddPerfect.CarmichaelExponentAndTotientTwoPowObstruction
public import OddPerfect.PadicValuationConservationAndLegendreFactorial
public import OddPerfect.ZsqrtTwoCombinedFirstSecondBlockSieve
public import OddPerfect.GlobalTier2WavePObstruction
import Mathlib.Tactic.Ring

/-!
# Global Tier 2 Wave Q Synthesis (`OddPerfect.GlobalTier2WaveQObstruction`)

Unifies all four Priority Wave Q structural modules (`915 → 920` public modules) into cross-module
global theorems with 100% preservation of every component invariant:
1. **Global Carmichael–Totient, `multiplicity` Conservation, & Legendre Factorial Envelope**
   (`odd_perfect_carmichael_totient_multiplicity_and_legendre_envelope`):
   unifies exact Carmichael LCM and Euler-cofactor divisibility (`4 * q ^ (a - 1) * m ∣ carmichael N`,
   `16 * N ≤ q * (carmichael N) ^ 2`, `1 < a → 16 * N < (carmichael N) ^ 2`), totient `2 ^ (ω + 1)`
   divisibility (`2 ^ (ω + 1) * q ^ (a - 1) * m ∣ N.totient`, `2 ^ 150 ∣ N.totient` when
   sixth-power-free), `multiplicity` conservation across `p = 2` and odd primes, and Legendre's
   base-`2` factorial bound `3 * 2 ^ (2 * ω - s₂(ω)) < rad(N)`.
2. **Tier 2 Wave Q Master Profile** (`odd_perfect_tier2_waveQ_master_profile`):
   couples the global Carmichael / totient / `multiplicity` / Legendre envelope with:
   - the `g = g_L * g_R` coprime refinement on `N = q * m ^ 2` (`m_L = g_L * h₀`, `m_R = g_R * u₀`,
     `L = g_L * h₀ ^ 2`, `R = g_R * u₀ ^ 2`, `g_R * W_L < g_L`, `3 ≤ g_L` when `r₀ ∣ m_L`, and
     unconditional `g_L = 1 → r₀ ∣ m_R`), plus its sixth-power-free `61 ≤ g_L` pinch, and
   - the first- and second-block `ℤ√2` / cyclotomic order sieve on `I = l * t ^ 2` (`a > 1`,
     `geometricBlock q d % 8 = 1`, `8 * d ∣ l - 1`, `Coprime (geometricBlock q d) (2 * d * w * z)`,
     `1553 ≤ l` when `¬ 3 ∣ N`, and `9817 ≤ l` / `1447 ≤ r` when `¬ 3 ∣ N ∧ ¬ 5 ∣ N`).
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- **1. Global Carmichael–Totient, `multiplicity` Conservation, & Legendre Factorial Envelope**:
Preserves every conjunct from `CarmichaelExponentAndTotientTwoPowObstruction` and
`PadicValuationConservationAndLegendreFactorial`. -/
theorem odd_perfect_carmichael_totient_multiplicity_and_legendre_envelope {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) :
    let ω := N.primeFactors.card
    let rad := ∏ p ∈ N.primeFactors, p
    ArithmeticFunction.carmichael N =
      N.primeFactors.lcm (fun p => p ^ (N.factorization p - 1) * (p - 1)) ∧
    4 ∣ ArithmeticFunction.carmichael N ∧
    (∏ p ∈ N.primeFactors, p ^ (N.factorization p - 1)) ∣ ArithmeticFunction.carmichael N ∧
    (∀ q a m : ℕ, q.Prime → q % 4 = 1 → 0 < a → ¬ q ∣ m → N = q ^ a * m ^ 2 →
      4 * q ^ (a - 1) * m ∣ ArithmeticFunction.carmichael N ∧
      16 * N ≤ q * (ArithmeticFunction.carmichael N) ^ 2 ∧
      (1 < a → 16 * N < (ArithmeticFunction.carmichael N) ^ 2)) ∧
    2 ^ (ω + 1) ∣ N.totient ∧
    128 ∣ N.totient ∧
    2 ^ (ω + 1) * (∏ p ∈ N.primeFactors, p ^ (N.factorization p - 1)) ∣ N.totient ∧
    (∀ q a m : ℕ, q.Prime → q % 4 = 1 → 0 < a → ¬ q ∣ m → N = q ^ a * m ^ 2 →
      2 ^ (ω + 1) * q ^ (a - 1) * m ∣ N.totient) ∧
    ((∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) →
      149 ≤ ω ∧
      2 ^ 150 ∣ N.totient) ∧
    multiplicity 2 N = 0 ∧
    multiplicity 2 (sigma 1 N) = 1 ∧
    (∑ q ∈ N.primeFactors, multiplicity 2 (sigma 1 (ordProj[q] N))) = 1 ∧
    (∀ p : ℕ, p.Prime → Odd p →
      multiplicity p N = N.factorization p ∧
      multiplicity p (sigma 1 N) = N.factorization p ∧
      (∑ q ∈ N.primeFactors, multiplicity p (sigma 1 (ordProj[q] N))) = multiplicity p N) ∧
    (∃ q ∈ N.primeFactors, multiplicity 2 (sigma 1 (ordProj[q] N)) = 1 ∧
      ∀ r ∈ N.primeFactors, r ≠ q → multiplicity 2 (sigma 1 (ordProj[r] N)) = 0) ∧
    multiplicity 2 (Nat.factorial ω) + (Nat.digits 2 ω).sum = ω ∧
    multiplicity 2 (Nat.factorial ω) < ω ∧
    1 ≤ (Nat.digits 2 ω).sum ∧
    multiplicity 2 (2 ^ ω * Nat.factorial ω) = 2 * ω - (Nat.digits 2 ω).sum ∧
    2 ^ (2 * ω - (Nat.digits 2 ω).sum) ∣ 2 ^ ω * Nat.factorial ω ∧
    3 * 2 ^ (2 * ω - (Nat.digits 2 ω).sum) ≤ 2 ^ ω * Nat.factorial ω ∧
    3 * 2 ^ (2 * ω - (Nat.digits 2 ω).sum) < rad ∧
    (3 * 2 ^ (2 * ω - (Nat.digits 2 ω).sum)) ^ 6 < 3 * N ^ 4 := by
  intro ω rad
  obtain ⟨hc1, hc2, hc3, hc4⟩ :=
    odd_perfect_carmichael_exact_lcm_and_euler_cofactor_dvd ho hN
  obtain ⟨ht1, ht2, ht3, ht4, ht5⟩ :=
    odd_perfect_totient_two_pow_and_euler_divisibility ho hN
  obtain ⟨hm1, hm2, hm3, hm4, hm5⟩ :=
    odd_perfect_multiplicity_conservation_and_dyadic_isolation ho hN
  obtain ⟨hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8⟩ :=
    odd_perfect_legendre_factorial_dyadic_radical_bound ho hN
  exact ⟨hc1, hc2, hc3, hc4, ht1, ht2, ht3, ht4, ht5,
    hm1, hm2, hm3, hm4, hm5, hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8⟩

/-- **2. Tier 2 Wave Q Master Profile**:
Unconditionally synthesizes all four Wave Q component modules with 100% invariant preservation. -/
theorem odd_perfect_tier2_waveQ_master_profile {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) :
    let ω := N.primeFactors.card
    let rad := ∏ p ∈ N.primeFactors, p
    ArithmeticFunction.carmichael N =
      N.primeFactors.lcm (fun p => p ^ (N.factorization p - 1) * (p - 1)) ∧
    4 ∣ ArithmeticFunction.carmichael N ∧
    (∏ p ∈ N.primeFactors, p ^ (N.factorization p - 1)) ∣ ArithmeticFunction.carmichael N ∧
    (∀ q a m : ℕ, q.Prime → q % 4 = 1 → 0 < a → ¬ q ∣ m → N = q ^ a * m ^ 2 →
      4 * q ^ (a - 1) * m ∣ ArithmeticFunction.carmichael N ∧
      16 * N ≤ q * (ArithmeticFunction.carmichael N) ^ 2 ∧
      (1 < a → 16 * N < (ArithmeticFunction.carmichael N) ^ 2)) ∧
    2 ^ (ω + 1) ∣ N.totient ∧
    128 ∣ N.totient ∧
    2 ^ (ω + 1) * (∏ p ∈ N.primeFactors, p ^ (N.factorization p - 1)) ∣ N.totient ∧
    (∀ q a m : ℕ, q.Prime → q % 4 = 1 → 0 < a → ¬ q ∣ m → N = q ^ a * m ^ 2 →
      2 ^ (ω + 1) * q ^ (a - 1) * m ∣ N.totient) ∧
    ((∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) →
      149 ≤ ω ∧
      2 ^ 150 ∣ N.totient) ∧
    multiplicity 2 N = 0 ∧
    multiplicity 2 (sigma 1 N) = 1 ∧
    (∑ q ∈ N.primeFactors, multiplicity 2 (sigma 1 (ordProj[q] N))) = 1 ∧
    (∀ p : ℕ, p.Prime → Odd p →
      multiplicity p N = N.factorization p ∧
      multiplicity p (sigma 1 N) = N.factorization p ∧
      (∑ q ∈ N.primeFactors, multiplicity p (sigma 1 (ordProj[q] N))) = multiplicity p N) ∧
    (∃ q ∈ N.primeFactors, multiplicity 2 (sigma 1 (ordProj[q] N)) = 1 ∧
      ∀ r ∈ N.primeFactors, r ≠ q → multiplicity 2 (sigma 1 (ordProj[r] N)) = 0) ∧
    multiplicity 2 (Nat.factorial ω) + (Nat.digits 2 ω).sum = ω ∧
    multiplicity 2 (Nat.factorial ω) < ω ∧
    1 ≤ (Nat.digits 2 ω).sum ∧
    multiplicity 2 (2 ^ ω * Nat.factorial ω) = 2 * ω - (Nat.digits 2 ω).sum ∧
    2 ^ (2 * ω - (Nat.digits 2 ω).sum) ∣ 2 ^ ω * Nat.factorial ω ∧
    3 * 2 ^ (2 * ω - (Nat.digits 2 ω).sum) ≤ 2 ^ ω * Nat.factorial ω ∧
    3 * 2 ^ (2 * ω - (Nat.digits 2 ω).sum) < rad ∧
    (3 * 2 ^ (2 * ω - (Nat.digits 2 ω).sum)) ^ 6 < 3 * N ^ 4 ∧
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
        ∃ h₀ u₀ g_L g_R : ℕ,
          Odd h₀ ∧ Odd u₀ ∧ Odd g_L ∧ Odd g_R ∧
          1 ≤ h₀ ∧ 3 ≤ u₀ ∧ h₀ + 2 ≤ u₀ ∧ 1 ≤ g_L ∧ 1 ≤ g_R ∧
          Nat.Coprime h₀ u₀ ∧ Nat.Coprime g_L g_R ∧ Nat.Coprime g_L u₀ ∧ Nat.Coprime g_R h₀ ∧
          g = g_L * g_R ∧
          m_L = g_L * h₀ ∧ m_R = g_R * u₀ ∧
          L = g_L * h₀ ^ 2 ∧ R = g_R * u₀ ^ 2 ∧
          A = g_L * g_R * h₀ ^ 2 ∧ I = g_L * g_R * u₀ ^ 2 ∧ m = g_L * g_R * h₀ * u₀ ∧
          ∃ r₀ ∈ m.primeFactors,
            q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀)) ∧
            ((r₀ ∣ m_L ∧ ¬ r₀ ∣ m_R ∧
                let W_L := sigma 1 (m_L ^ 2) / q
                1 ≤ W_L ∧ Odd W_L ∧
                W_L * sigma 1 (m_R ^ 2) = g_L * g_R * u₀ ^ 2 ∧
                g_R * W_L * sigma 1 (m_R ^ 2) = g_L * m_R ^ 2 ∧
                (q + 1) * W_L * sigma 1 (m_R ^ 2) = 2 * m_L ^ 2 * m_R ^ 2 ∧
                g_R * W_L < g_L ∧ 3 ≤ g_L ∧ 3 ≤ g ∧ ¬ Nat.Coprime A I) ∨
             (r₀ ∣ m_R ∧ ¬ r₀ ∣ m_L ∧
                let W_R := sigma 1 (m_R ^ 2) / q
                1 ≤ W_R ∧ Odd W_R ∧
                W_R * sigma 1 (m_L ^ 2) = g_L * g_R * u₀ ^ 2 ∧
                (q + 1) * W_R * sigma 1 (m_L ^ 2) = 2 * m_L ^ 2 * m_R ^ 2)) ∧
            (g_L = 1 → r₀ ∣ m_R ∧ ¬ r₀ ∣ m_L)) ∧
      ((∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) →
        ∃ m₀ h₀ u₀ g_L g_R r₀ : ℕ,
          let A := (q + 1) / 2
          let I := componentIndex N q
          let L := Nat.factorizationLCMLeft A I
          let R := Nat.factorizationLCMRight A I
          Odd m₀ ∧ ¬ q ∣ m₀ ∧ N = q * m₀ ^ 2 ∧
          Odd h₀ ∧ Odd u₀ ∧ Odd g_L ∧ Odd g_R ∧
          1 ≤ h₀ ∧ 3 ≤ u₀ ∧ h₀ + 2 ≤ u₀ ∧ 1 ≤ g_L ∧ 1 ≤ g_R ∧
          Nat.Coprime h₀ u₀ ∧ Nat.Coprime g_L g_R ∧ Nat.Coprime g_L u₀ ∧ Nat.Coprime g_R h₀ ∧
          g_L * g_R = Nat.gcd A I ∧
          Nat.gcd m₀ L = g_L * h₀ ∧
          Nat.gcd m₀ R = g_R * u₀ ∧
          r₀ ∈ m₀.primeFactors ∧
          q ∣ sigma 1 (r₀ ^ (2 * m₀.factorization r₀)) ∧
          ((r₀ ∣ g_L * h₀ ∧ ¬ r₀ ∣ g_R * u₀ ∧
              61 ≤ g_L ∧ 61 ≤ g_L * h₀ ∧ 3783 ≤ sigma 1 ((g_L * h₀) ^ 2) ∧
              m₀.factorization r₀ = 2 ∧ r₀ ∈ largeSources N q ∧ 61 ≤ r₀) ∨
           (r₀ ∣ g_R * u₀ ∧ ¬ r₀ ∣ g_L * h₀)) ∧
          (g_L = 1 → r₀ ∣ g_R * u₀ ∧ ¬ r₀ ∣ g_L * h₀)) ∧
      (1 < a → ∀ l t : ℕ, l.Prime → sigma 1 (m ^ 2) / q ^ a = l * t ^ 2 →
        let d := (a + 1) / 2
        geometricBlock q d % 8 = 1 ∧
        l % 8 = 1 ∧
        8 * d ∣ l - 1 ∧
        8 * d + 1 ≤ l ∧
        137 ≤ l ∧
        (∀ r ∈ (geometricBlock q d).primeFactors,
          orderOf (q : ZMod r) = d ∧
          2 * d ∣ r - 1 ∧
          2 * d + 1 ≤ r ∧
          83 ≤ r ∧
          (d = 17 → 103 ≤ r)) ∧
        (∃ w z v : ℕ,
          q + 1 = 2 * d * w ^ 2 ∧
          (q ^ d + 1) / (q + 1) = d * z ^ 2 ∧
          geometricBlock q d = l * v ^ 2 ∧
          Nat.Coprime (geometricBlock q d) (2 * d * w * z) ∧
          Nat.Coprime l (2 * d * w * z) ∧
          Nat.Coprime v (2 * d * w * z)) ∧
        (¬ 3 ∣ N →
          73 ≤ d ∧
          1553 ≤ l ∧
          (d = 73 → 1753 ≤ l) ∧
          (∀ r ∈ (geometricBlock q d).primeFactors, 293 ≤ r)) ∧
        (¬ 3 ∣ N → ¬ 5 ∣ N →
          241 ≤ d ∧
          9817 ≤ l ∧
          (d = 241 → 26993 ≤ l) ∧
          (∀ r ∈ (geometricBlock q d).primeFactors, 1447 ≤ r))) := by
  intro ω rad
  obtain ⟨hc1, hc2, hc3, hc4, ht1, ht2, ht3, ht4, ht5,
    hm1, hm2, hm3, hm4, hm5, hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8⟩ :=
    odd_perfect_carmichael_totient_multiplicity_and_legendre_envelope ho hN
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _,
    q, a, m, hq, hq_mem, hq4, ha4, ha_pos, hqm, hform, _, _⟩ :=
    odd_perfect_tier2_waveP_master_profile ho hN
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
  refine ⟨hc1, hc2, hc3, hc4, ht1, ht2, ht3, ht4, ht5,
    hm1, hm2, hm3, hm4, hm5, hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8,
    q, a, m, hq, hq_mem, hq4, ha4, ha_pos, hqm, hform, ?_, ?_, ?_⟩
  · intro ha1
    have hform1 : N = q * m ^ 2 := by
      rw [hform, ha1, pow_one]
    exact linear_euler_gcd_coprime_split_and_quotient_duality ho hN hq hqm hform1
  · intro hfree
    exact sixth_power_free_gcd_coprime_split_gL_pinch ho hN hq_mem hq4 he_q hev_N hfree
  · intro ha_gt1 l t hl hi
    obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hs7⟩ :=
      exceptional_euler_first_block_mod_eight_and_order_sieve
        hN ho hq hq4 ha4 ha_gt1 hqm hform hl hi
    obtain ⟨hb3, hb35⟩ :=
      exceptional_euler_first_block_three_and_five_free_bounds
        hN ho hq hq4 ha4 ha_gt1 hqm hform hl hi
    exact ⟨hs1, hs2, hs3, hs4, hs5, hs6, hs7, hb3, hb35⟩

end OddPerfect
