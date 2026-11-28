module

public import OddPerfect.LinearEulerCycleDecay
public import OddPerfect.ZsqrtTwoArchimedeanObstruction
public import OddPerfect.UniversalSigmaTotientObstruction
public import OddPerfect.CyclotomicFactorizationSupply
public import OddPerfect.GlobalTier2WaveCObstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Global Tier 2 Wave D Synthesis (`OddPerfect.GlobalTier2WaveDObstruction`)

Unifies the four Priority Wave D structural advances into cross-module global profiles:
1. **Linear Euler Cycle Decay & Deficient Square Totient Envelope**
   (`linear_euler_cycle_decay_and_square_totient_profile`):
   eliminates closed all-full-power square cycles on `N = q * m ^ 2`, enforces exponential
   peeling decay (`156 ^ (k - 1) / 53 ^ (k - 1)` on sixth-power-free chains), and pins `m.totient`
   inside `3 * m ^ 3 < 4 * (2 * m ^ 2 - i_q) * m.totient < 4 * m ^ 3` (`27 / 32` when `¬ 3 ∣ N`).
2. **Tier 2 Wave D Master Profile** (`odd_perfect_tier2_waveD_master_profile`):
   synthesizes Ore-harmonic divisor–totient bounds, dual finite-field cyclotomic splitting over
   `ZMod r` and `ZMod p`, linear Euler cycle collapse + `m ^ 3` totient bounds at `a = 1`, and
   `ℤ√2` Archimedean positivity (`0 < toReal2 α`) + `|k| = 1` quartic `q`-floors (`147456 < q`,
   `186624 < q` at `k = -1`, and `6690816000 < q` when `¬ 3 ∣ N ∧ ¬ 5 ∣ N`) at `a > 1`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction Polynomial

/-- **1. Linear Euler Cycle Decay & Square-Cofactor Totient Profile**:
On any linear Euler odd perfect number `N = q * m ^ 2`:
- Every `Nodup` directed peeling cycle `L` in `m.primeFactors` fails full-power absorption on its
  closing edge and forces either `L.head ∣ (q + 1) / 2` or a `σ`-collision at `L.head`.
- The square cofactor `m ^ 2` satisfies `DeficientPerfectWith (m ^ 2) (componentIndex N q)`,
  `(2 * m ^ 2 - componentIndex N q) * m.totient < m ^ 3`,
  `(3 * m.primeFactors.card + 5) * m ^ 3 < (4 * m.primeFactors.card + 5) * (2 * m ^ 2 - componentIndex N q) * m.totient`,
  and `¬ 3 ∣ N → 27 * m ^ 3 < 32 * (2 * m ^ 2 - componentIndex N q) * m.totient`.
- Under sixth-power-freeness, every full-power peeling chain `L` of length `≥ 2` decays
  exponentially at rate `156 ^ (L.length - 1) * P(last) < 53 ^ (L.length - 1) * P(head)`. -/
theorem linear_euler_cycle_decay_and_square_totient_profile {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2) :
    ((∃ r' : ℕ, r'.Prime ∧
        ∃ p₁ ∈ m.primeFactors, ∃ p₂ ∈ m.primeFactors,
          p₁ ≠ p₂ ∧
          r' ∣ sigma 1 (ordProj[p₁] (m ^ 2)) ∧
          r' ∣ sigma 1 (ordProj[p₂] (m ^ 2))) ∨
      (∃ p ∈ m.primeFactors, p ∣ (q + 1) / 2)) ∧
    DeficientPerfectWith (m ^ 2) (componentIndex N q) ∧
    (2 * m ^ 2 - componentIndex N q) * m.totient < m ^ 3 ∧
    (3 * m.primeFactors.card + 5) * m ^ 3 <
      (4 * m.primeFactors.card + 5) * (2 * m ^ 2 - componentIndex N q) * m.totient ∧
    (¬ 3 ∣ N → 27 * m ^ 3 < 32 * (2 * m ^ 2 - componentIndex N q) * m.totient) ∧
    ((∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) →
      ∀ L : List ℕ, 2 ≤ L.length → (∀ p ∈ L, p ∈ m.primeFactors) →
        (∀ i : ℕ, ∀ (hi : i + 1 < L.length),
          L[i + 1] ^ (2 * m.factorization L[i + 1]) ∣ sigma 1 (ordProj[L[i]] (m ^ 2))) →
        ∀ hL : L ≠ [],
          156 ^ (L.length - 1) * (L.getLast hL) ^ (2 * m.factorization (L.getLast hL)) <
            53 ^ (L.length - 1) * (L.head hL) ^ (2 * m.factorization (L.head hL))) := by
  have hcoll := linear_euler_collision_or_half_succ_hit ho hN hq hqm hform
  obtain ⟨hdef, _, hlt_m3, hmain_m3, _, hnot3_m3⟩ :=
    odd_deficientPerfect_and_linear_euler_square_totient_bounds ho hN hq hqm hform
  refine ⟨hcoll, hdef, hlt_m3, hmain_m3, hnot3_m3, ?_⟩
  intro hfree L hlen hm_list hsteps hL
  exact sixth_power_free_peeling_chain_exponential_decay ho hN hq hqm hform hfree
    L hlen hm_list hsteps hL

/-- **2. Tier 2 Wave D Master Profile**:
Unifies universal Ore-harmonic totient–divisor bounds, dual finite-field cyclotomic splitting over
`ZMod r` and `ZMod p`, linear Euler cycle collapse + `m ^ 3` totient bounds (`a = 1`), and `ℤ√2`
Archimedean positivity + `|k| = 1` quartic `q`-floors (`a > 1`) on any odd perfect number `N`. -/
theorem odd_perfect_tier2_waveD_master_profile {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    let H := N * N.divisors.card / sigma 1 N
    N.divisors.card * N.totient < H * N ∧
    3 * H * N < 4 * N.divisors.card * N.totient ∧
    (¬ 3 ∣ N → 27 * H * N < 32 * N.divisors.card * N.totient) ∧
    (∀ (p : ℕ) (hp : p ∈ N.primeFactors) (d : ℕ), 1 < d → d ∣ N.factorization p + 1 →
      ∀ r : ℕ, r.Prime → ¬ r ∣ d → (r : ℤ) ∣ eval (p : ℤ) (cyclotomic d ℤ) →
        Odd r ∧ r ∈ N.primeFactors ∧ p ≠ r ∧ orderOf (p : ZMod r) = d ∧ d ∣ r - 1 ∧
        (letI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩;
          (UniqueFactorizationMonoid.normalizedFactors (cyclotomic r (ZMod p))).toFinset.card =
            (r - 1) / d ∧
          ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors (cyclotomic r (ZMod p)),
            P.natDegree = d ∧ P.Monic)) ∧
    ∃ q a m : ℕ,
      q.Prime ∧ q ∈ N.primeFactors ∧ q % 4 = 1 ∧ a % 4 = 1 ∧ 0 < a ∧ ¬ q ∣ m ∧
      N = q ^ a * m ^ 2 ∧
      (a = 1 →
        DeficientPerfectWith (m ^ 2) (componentIndex N q) ∧
        (2 * m ^ 2 - componentIndex N q) * m.totient < m ^ 3 ∧
        (3 * m.primeFactors.card + 5) * m ^ 3 <
          (4 * m.primeFactors.card + 5) * (2 * m ^ 2 - componentIndex N q) * m.totient) ∧
      (1 < a → ∀ l t : ℕ, l.Prime → sigma 1 (m ^ 2) / q ^ a = l * t ^ 2 →
        let d := (a + 1) / 2
        ∃ (y : ℕ) (k : ℤ) (α : ℤ√2),
          0 < y ∧ d ∣ y ∧ q ^ d + 1 = 2 * y ^ 2 ∧
          1 ≤ |k| ∧ 2 * |k| ≤ (d : ℤ) - 1 ∧
          (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d ∧
          0 < toReal2 α ∧
          (|k| = 1 →
            1 ≤ α.re ∧
            (d : ℤ) - 1 ≤ |α.im| ∧
            2 * (d : ℤ) ^ 2 * α.im ^ 2 < α.re ^ 2 ∧
            2 * (d ^ 2 - 1) * (d - 1) ^ 2 < q ∧
            147456 < q ∧
            (k = -1 → 2 * (d ^ 2 - 1) * (d + 1) ^ 2 < q ∧ 186624 < q) ∧
            (¬ 3 ∣ N → ¬ 5 ∣ N → 241 ≤ d ∧ 6690816000 < q))) := by
  intro H
  have hore : OreHarmonic N := (perfect_oreHarmonic hN).1
  obtain ⟨_, _, hHN_lt, _, h3HN, h27HN⟩ := odd_oreHarmonic_totient_divisor_envelope ho hore
  have hcyc : ∀ (p : ℕ) (hp : p ∈ N.primeFactors) (d : ℕ), 1 < d → d ∣ N.factorization p + 1 →
      ∀ r : ℕ, r.Prime → ¬ r ∣ d → (r : ℤ) ∣ eval (p : ℤ) (cyclotomic d ℤ) →
        Odd r ∧ r ∈ N.primeFactors ∧ p ≠ r ∧ orderOf (p : ZMod r) = d ∧ d ∣ r - 1 ∧
        (letI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩;
          (UniqueFactorizationMonoid.normalizedFactors (cyclotomic r (ZMod p))).toFinset.card =
            (r - 1) / d ∧
          ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors (cyclotomic r (ZMod p)),
            P.natDegree = d ∧ P.Monic) := by
    intro p hp d hd hlen r hr hnd hdvd
    obtain ⟨hr_odd, hr_mem, hp_ne_r, _, _, hord, hd_dvd_r1, _, _, hp_part⟩ :=
      odd_perfect_component_cyclotomic_dual_splitting ho hN hp hd hlen hr hnd hdvd
    exact ⟨hr_odd, hr_mem, hp_ne_r, hord, hd_dvd_r1, hp_part.1, hp_part.2.2⟩
  obtain ⟨_, q, a, m, hq, hq4, ha4, hqm, hform, _⟩ :=
    odd_perfect_tier2_waveC_master_profile ho hN
  have ha_pos : 0 < a := by omega
  have hq_mem : q ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr
      ⟨hq, hform ▸ dvd_mul_of_dvd_left (dvd_pow_self q (by omega)) _, hN.2.ne'⟩
  refine ⟨hHN_lt, h3HN, h27HN, hcyc, q, a, m, hq, hq_mem, hq4, ha4, ha_pos, hqm, hform, ?_, ?_⟩
  · intro ha1
    have hform1 : N = q * m ^ 2 := by simpa [ha1] using hform
    obtain ⟨_, hdef, hlt_m3, hmain_m3, _, _⟩ :=
      linear_euler_cycle_decay_and_square_totient_profile ho hN hq hqm hform1
    exact ⟨hdef, hlt_m3, hmain_m3⟩
  · intro ha_gt1 l t hl hi d
    obtain ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, hnorm, h1_cond⟩ :=
      exceptional_euler_unit_exponent_one_quartic_bound_of_silverUnit
        hN ho hq hq4 ha4 ha_gt1 hqm hform hl hi
    obtain ⟨_, _, hd8, _, _, _, _⟩ :=
      exceptional_index_fermat_witness hN ho hq hq4 ha4 ha_gt1 hqm hform hl hi
    have hd_odd : Odd d := Nat.odd_iff.mpr (by omega)
    obtain ⟨_, _, hα_pos, _⟩ := zsqrtTwo_fermat_toReal_pos hd_odd k α hz_eq
    exact ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, hα_pos, h1_cond⟩

end OddPerfect
