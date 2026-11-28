module

public import OddPerfect.PadicPadeApproximantObstruction
public import OddPerfect.ZsqrtTwoCubicObstruction
public import OddPerfect.DoubleCollisionExcessObstruction
public import OddPerfect.SixthPowerFreeHalfSuccPinch
public import OddPerfect.GlobalTier2WaveEObstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Global Tier 2 Wave F Synthesis (`OddPerfect.GlobalTier2WaveFObstruction`)

Unifies the four Priority Wave F structural advances into cross-module global theorems:
1. **Even Prime-Power Pell–Padé `6 ^ u` Cap & Full-Precision Divisibility Profile**
   (`even_prime_power_pade_six_pow_profile`):
   upgrades the exponential base cap on `i = p ^ (2 * u)` from `p < 8 ^ u` to **`p < 6 ^ u`**
   (`128 ≤ u`, `geometricBlock r l < 6 ^ u` for some `r ∈ {3, 5, 7, 11, 13}`) alongside full
   `(2 * u + 1)`-order Padé divisibility `(p : ℤ) ^ (2 * u + 1) ∣ s * padeSeqB u p - padeSeqA u p`.
2. **Tier 2 Wave F Master Profile** (`odd_perfect_tier2_waveF_master_profile`):
   synthesizes unconditional double-or-triple odd-prime `σ`-collisions (`2 ≤ collisionExcess N q`
   across ALL odd perfect numbers `N`), exact multiplicity splitting
   `Ω(N) = ω(N) + localRepeatExcess N q + collisionExcess N q`, sixth-power-free half-successor
   dichotomy (`61 ≤ s ∧ 2 * s ∣ q + 1` vs. `q % 48 = 1 ∧ 6961 ≤ q`), and unified `|k| ≤ 3`
   exceptional-Euler quartic `q`-floors (`1410 < q`, and `131924500 < q` when `¬ 3 ∣ N ∧ ¬ 5 ∣ N`).
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- **1. Even Prime-Power Pell–Padé `6 ^ u` Cap & Full-Precision Profile**:
On any even prime-power component index `i = p ^ (2 * u)` of an odd perfect number `N`:
- `128 ≤ u`, `(2 * u + 1).Prime`, and **`p < 6 ^ u`**;
- Some `r ∈ {3, 5, 7, 11, 13}` satisfies `r ^ 2 ∣ N` with `p = geometricBlock r l` (`l.Prime`, `2 < l`)
  and `geometricBlock r l < 6 ^ u`;
- The cofactor `s` satisfies full `(2 * u + 1)`-order Pell–Padé divisibility
  `((p : ℤ) ^ (2 * u + 1)) ∣ (s : ℤ) * padeSeqB u p - padeSeqA u p` together with
  `s ^ 2 ≡ 4 ^ u [MOD p - 2]`. -/
theorem even_prime_power_pade_six_pow_profile
    {N q a b i p u : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b) (hl : sigma 1 b = q ^ a * i)
    (hr : sigma 1 (q ^ a) * i = 2 * b) (hp : p.Prime) (hu : 0 < u) (hi : i = p ^ (2 * u)) :
    128 ≤ u ∧ (2 * u + 1).Prime ∧ p < 6 ^ u ∧
    (∃ r ∈ ({3, 5, 7, 11, 13} : Finset ℕ),
      r ^ 2 ∣ N ∧ ∃ l : ℕ, l.Prime ∧ 2 < l ∧ geometricBlock r l = p ∧ geometricBlock r l < 6 ^ u) ∧
    ∃ s : ℕ, Odd s ∧
      s < p ^ u ∧ p ^ u < 2 * s ∧
      s ^ 2 ≡ 4 ^ u [MOD p - 2] ∧
      ((p : ℤ) ^ (2 * u + 1)) ∣ (s : ℤ) * padeSeqB u p - padeSeqA u p := by
  obtain ⟨hu128, hp_lt_6u⟩ :=
    even_prime_power_component_base_lt_six_pow hN ho hq ha hform hqb hl hr hp hu hi
  obtain ⟨_, _, hlen_prime, _, ⟨r, hr_mem, hr2_dvd, l, hl_prime, hl_gt2, hgeom_eq, _⟩, _⟩ :=
    even_prime_power_runge_and_mod_sub_two_profile hN ho hq ha hform hqb hl hr hp hu hi
  obtain ⟨ha1, hσq⟩ :=
    even_prime_power_index_eq_selected_sigma hN ho hq ha hform hqb hl hr hp hu hi
  have hbo := ho.of_dvd_nat (hform ▸ dvd_mul_left b _)
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h4 : 4 ∣ 2 * b := hr ▸ hi ▸ (pow_dvd_pow 2 (by omega : 2 ≤ 2 * u)).trans (dvd_mul_left _ _)
    have := hbo.not_two_dvd_nat
    omega
  have hpo : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨m, _, _, _, rfl⟩ :=
    euler_form_of_odd_component_index hN ho hq ha hform hqb hl hr (hi ▸ hpo.pow)
  have hmo := ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2 ≠ 0)) _)
  rw [ha1, pow_one] at hform hl hr
  rw [hi] at hl hr
  obtain ⟨s, hso, _, _, _, hplus, hσs⟩ := even_prime_power_cofactor_split hq hp hmo hpo hu hl hr
  obtain ⟨_, _, hs_lt, hpu_lt_2s⟩ := even_index_cofactor_archimedean_sandwich hp hpo hu hσq hplus
  obtain ⟨hmod_p2, _⟩ := even_index_mod_sub_two_congruence hp hpo hσq hplus
  have hpade := even_index_pade_full_precision_divisibility hp hpo hso hu hσq hplus hσs
  refine ⟨hu128, hlen_prime, hp_lt_6u,
    ⟨r, hr_mem, hr2_dvd, l, hl_prime, hl_gt2, hgeom_eq, hgeom_eq.symm ▸ hp_lt_6u⟩,
    ⟨s, hso, hs_lt, hpu_lt_2s, hmod_p2, hpade⟩⟩

/-- **2. Tier 2 Wave F Master Profile**:
Unconditionally couples double-or-triple odd-prime `σ`-collisions (`2 ≤ collisionExcess N q`),
exact additive multiplicity decomposition `Ω(N) = ω(N) + localRepeatExcess N q + collisionExcess N q`,
least-prime logarithmic collision bounds, sixth-power-free half-successor `61 ≤ s` vs. `6961 ≤ q`
dichotomy, and unified `|k| ≤ 3` exceptional-Euler `q`-floors (`1410 < q`, and `131924500 < q`
when `¬ 3 ∣ N ∧ ¬ 5 ∣ N`). -/
theorem odd_perfect_tier2_waveF_master_profile {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    ((∃ r : ℕ, r.Prime ∧ Odd r ∧ r ∈ N.primeFactors ∧
        ∃ p₁ ∈ N.primeFactors, ∃ p₂ ∈ N.primeFactors, ∃ p₃ ∈ N.primeFactors,
          p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃ ∧
          r ∣ sigma 1 (ordProj[p₁] N) ∧
          r ∣ sigma 1 (ordProj[p₂] N) ∧
          r ∣ sigma 1 (ordProj[p₃] N)) ∨
      (∃ r₁ r₂ : ℕ, r₁.Prime ∧ r₂.Prime ∧ Odd r₁ ∧ Odd r₂ ∧
        r₁ ∈ N.primeFactors ∧ r₂ ∈ N.primeFactors ∧ r₁ ≠ r₂ ∧
        (∃ p₁ ∈ N.primeFactors, ∃ p₂ ∈ N.primeFactors,
          p₁ ≠ p₂ ∧ r₁ ∣ sigma 1 (ordProj[p₁] N) ∧ r₁ ∣ sigma 1 (ordProj[p₂] N)) ∧
        (∃ p₁ ∈ N.primeFactors, ∃ p₂ ∈ N.primeFactors,
          p₁ ≠ p₂ ∧ r₂ ∣ sigma 1 (ordProj[p₁] N) ∧ r₂ ∣ sigma 1 (ordProj[p₂] N)))) ∧
    ∃ q a m : ℕ,
      q.Prime ∧ q ∈ N.primeFactors ∧ q % 4 = 1 ∧ a % 4 = 1 ∧ 0 < a ∧ ¬ q ∣ m ∧
      N = q ^ a * m ^ 2 ∧
      2 ≤ collisionExcess N q ∧
      cardFactors N = N.primeFactors.card + localRepeatExcess N q + collisionExcess N q ∧
      ((N.minFac : ℝ) - 1) * Real.log 2 < 3 * (collisionExcess N q : ℝ) + 3 ∧
      ((∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) →
        (∃ s ∈ N.primeFactors.erase q,
          (s % 5 = 1 ∨ s % 3 = 1) ∧ 61 ≤ s ∧ 2 * s ∣ q + 1 ∧ s ∣ componentIndex N q ∧
          ∃ p ∈ N.primeFactors.erase q, p ≠ s ∧ s ∣ sigma 1 (ordProj[p] N)) ∨
        (Nat.Coprime ((q + 1) / 2) (componentIndex N q) ∧
          IsSquare ((q + 1) / 2) ∧ IsSquare (componentIndex N q) ∧
          q % 48 = 1 ∧ 6961 ≤ q ∧
          ∃ r' ∈ N.primeFactors,
            ∃ p₁ ∈ N.primeFactors.erase q, ∃ p₂ ∈ N.primeFactors.erase q,
              p₁ ≠ p₂ ∧
              r' ∣ sigma 1 (ordProj[p₁] N) ∧
              r' ∣ sigma 1 (ordProj[p₂] N))) ∧
      (1 < a → ∀ l t : ℕ, l.Prime → sigma 1 (m ^ 2) / q ^ a = l * t ^ 2 →
        let d := (a + 1) / 2
        ∃ (y : ℕ) (k : ℤ) (α : ℤ√2),
          0 < y ∧ d ∣ y ∧ q ^ d + 1 = 2 * y ^ 2 ∧
          1 ≤ |k| ∧ 2 * |k| ≤ (d : ℤ) - 1 ∧
          (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d ∧
          (|k| ≤ 3 →
            1410 < q ∧
            (¬ 3 ∣ N → ¬ 5 ∣ N → 241 ≤ d ∧ 131924500 < q ∧ 10 ^ 8 < q))) := by
  obtain ⟨hdt_coll, _⟩ := odd_perfect_double_or_triple_sigma_collision ho hN
  obtain ⟨_, q, a, m, hq, hq_mem, hq4, ha4, ha_pos, hqm, hform, _, _, _⟩ :=
    odd_perfect_tier2_waveE_master_profile ho hN
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
  have hE2 := two_le_collisionExcess_of_odd_perfect ho hN hq_mem hq4 he_q hev_N
  have hdecomp :=
    cardFactors_eq_primeFactors_add_localRepeat_add_collisionExcess ho hN hq_mem hq4 he_q hev_N
  have hlog := (collision_excess_least_prime_log_bound ho hN hq_mem hq4 he_q hev_N).1
  refine ⟨hdt_coll, q, a, m, hq, hq_mem, hq4, ha4, ha_pos, hqm, hform, hE2, hdecomp, hlog, ?_, ?_⟩
  · intro hfree
    exact sixth_power_free_unconditional_nontrivial_collision_and_q_dichotomy
      ho hN hq_mem hq4 he_q hev_N hfree
  · intro ha_gt1 l t hl hi d
    obtain ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, _, hk3_cond⟩ :=
      exceptional_euler_k_le_three_unified_floor hN ho hq hq4 ha4 ha_gt1 hqm hform hl hi
    exact ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, hk3_cond⟩

end OddPerfect
