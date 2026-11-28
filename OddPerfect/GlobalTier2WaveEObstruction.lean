module

public import OddPerfect.UniversalSigmaCollisionObstruction
public import OddPerfect.LinearEulerUnitaryHalfSuccPeeling
public import OddPerfect.ZsqrtTwoUniversalCone
public import OddPerfect.PadicRungeSubTwoObstruction
public import OddPerfect.GlobalTier2WaveDObstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Global Tier 2 Wave E Synthesis (`OddPerfect.GlobalTier2WaveEObstruction`)

Unifies the four Priority Wave E structural advances into cross-module global theorems:
1. **Even Prime-Power Runge Base Cap & Mod-`(p - 2)` Profile**
   (`even_prime_power_runge_and_mod_sub_two_profile`):
   couples the Runge `p`-adic-vs-Archimedean exponential cap `p < 8 ^ u`, pure algebraic small-`u`
   exclusion `5 ≤ u ∧ 11 ≤ 2 * u + 1`, prime length `(2 * u + 1).Prime`, and mod-`(p - 2)`
   congruence `s ^ 2 ≡ 4 ^ u [MOD p - 2]` with the `r ∈ {3, 5, 7, 11, 13}` primorial repunit base.
2. **Tier 2 Wave E Master Profile** (`odd_perfect_tier2_waveE_master_profile`):
   synthesizes unconditional odd-prime `σ`-collisions (`r ∈ N.primeFactors` dividing two distinct
   components) + Ljunggren collision excess `N.primeFactors.card ≤ 3 * E + 3` (`147 ≤ E` on
   sixth-power-free candidates), nontrivial linear-Euler `σ`-collisions with zero half-successor or
   cycle escape (`a = 1`), and the universal `ℤ√2` Archimedean cone across ALL `1 ≤ |k| ≤ (d - 1) / 2`
   plus `|k| = 2` quartic `q`-floors (`148403 < q`, `177065 < q`, `6703954379 < q`) (`a > 1`).
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- **1. Even Prime-Power Runge Exponential Cap & Mod-`(p - 2)` Profile**:
On any even prime-power component index `i = p ^ (2 * u)`:
- `5 ≤ u`, `11 ≤ 2 * u + 1`, `(2 * u + 1).Prime`, and **`p < 8 ^ u`**;
- Some `r ∈ {3, 5, 7, 11, 13}` satisfies `r ^ 2 ∣ N` with `p = geometricBlock r l` (`l.Prime`, `2 < l`),
  so `geometricBlock r l < 8 ^ u`;
- The cofactor `s` satisfies `p ^ u < 2 * s`, `s < p ^ u`, `s ^ 2 ≡ 4 ^ u [MOD p - 2]`, and
  `((p : ℤ) - 2) ∣ ((s : ℤ) - 2 ^ u) * ((s : ℤ) + 2 ^ u)`. -/
theorem even_prime_power_runge_and_mod_sub_two_profile
    {N q a b i p u : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b) (hl : sigma 1 b = q ^ a * i)
    (hr : sigma 1 (q ^ a) * i = 2 * b) (hp : p.Prime) (hu : 0 < u) (hi : i = p ^ (2 * u)) :
    5 ≤ u ∧ 11 ≤ 2 * u + 1 ∧ (2 * u + 1).Prime ∧ p < 8 ^ u ∧
    (∃ r ∈ ({3, 5, 7, 11, 13} : Finset ℕ),
      r ^ 2 ∣ N ∧ ∃ l : ℕ, l.Prime ∧ 2 < l ∧ geometricBlock r l = p ∧ geometricBlock r l < 8 ^ u) ∧
    ∃ s : ℕ, Odd s ∧
      s < p ^ u ∧ p ^ u < 2 * s ∧
      s ^ 2 ≡ 4 ^ u [MOD p - 2] ∧
      ((p : ℤ) - 2) ∣ ((s : ℤ) - 2 ^ u) * ((s : ℤ) + 2 ^ u) := by
  obtain ⟨ha1, hσq⟩ :=
    even_prime_power_index_eq_selected_sigma hN ho hq ha hform hqb hl hr hp hu hi
  have hlen_prime : (2 * u + 1).Prime := even_index_length_prime hq hp hu hσq
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
  obtain ⟨hu5, h11⟩ := even_index_small_u_exclusion hq hp hpo hso hu hσq hplus hσs
  have hp_lt_8u : p < 8 ^ u := even_index_prime_lt_eight_pow_u hp hpo hso hu hσq hplus hσs
  obtain ⟨_, _, hs_lt, hpu_lt_2s⟩ := even_index_cofactor_archimedean_sandwich hp hpo hu hσq hplus
  obtain ⟨hmod_p2, hdvd_p2⟩ := even_index_mod_sub_two_congruence hp hpo hσq hplus
  obtain ⟨⟨r, hr_mem, hr2_dvd, l, hl_prime, hl_gt2, hgeom_eq⟩, _⟩ :=
    even_prime_power_component_forces_small_repunit_base
      hN ho hq (by decide : 0 < 1) (by simpa using hform) hqb
      (by simpa [hi] using hl) (by simpa [hi] using hr) hp hu rfl
  refine ⟨hu5, h11, hlen_prime, hp_lt_8u,
    ⟨r, hr_mem, hr2_dvd, l, hl_prime, hl_gt2, hgeom_eq, hgeom_eq.symm ▸ hp_lt_8u⟩,
    ⟨s, hso, hs_lt, hpu_lt_2s, hmod_p2, hdvd_p2⟩⟩

/-- **2. Tier 2 Wave E Master Profile**:
Unconditionally couples global odd-prime `σ`-collisions (`r ∈ N.primeFactors` dividing two
distinct prime-power components) + Ljunggren collision-excess bounds (`147 ≤ E` when
sixth-power-free), nontrivial linear-Euler `σ`-collisions without half-successor or cycle escape
(`a = 1`), and the universal `ℤ√2` Archimedean cone across ALL `1 ≤ |k| ≤ (d - 1) / 2` together
with `|k| = 2` quartic `q`-floors (`a > 1`). -/
theorem odd_perfect_tier2_waveE_master_profile {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    (∃ r : ℕ, r.Prime ∧ Odd r ∧ r ∈ N.primeFactors ∧
      ∃ p₁ ∈ N.primeFactors, ∃ p₂ ∈ N.primeFactors,
        p₁ ≠ p₂ ∧ r ∣ sigma 1 (ordProj[p₁] N) ∧ r ∣ sigma 1 (ordProj[p₂] N)) ∧
    ∃ q a m : ℕ,
      q.Prime ∧ q ∈ N.primeFactors ∧ q % 4 = 1 ∧ a % 4 = 1 ∧ 0 < a ∧ ¬ q ∣ m ∧
      N = q ^ a * m ^ 2 ∧
      (let totalIncidences := ∑ p ∈ N.primeFactors, (oddComponentSigma N q p).primeFactors.card
       let E := totalIncidences - N.primeFactors.card
       1 ≤ E ∧ N.primeFactors.card ≤ 3 * E + 3 ∧
       (¬ 3 ∣ N → 2 ≤ E ∧ N.primeFactors.card ≤ 3 * E + 2) ∧
       ((∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) → 147 ≤ E ∧ 590 ≤ totalIncidences)) ∧
      (a = 1 →
        (∃ s ∈ m.primeFactors,
          s ∣ (q + 1) / 2 ∧ s ∣ componentIndex N q ∧
          ∃ p ∈ m.primeFactors, p ≠ s ∧ s ∣ sigma 1 (ordProj[p] (m ^ 2))) ∨
        (Nat.Coprime ((q + 1) / 2) (componentIndex N q) ∧
          IsSquare ((q + 1) / 2) ∧ IsSquare (componentIndex N q) ∧
          q % 8 = 1 ∧ (¬ 3 ∣ N → q % 24 = 1 ∧ 97 ≤ q) ∧
          ∃ r' : ℕ, r'.Prime ∧
            ∃ p₁ ∈ m.primeFactors, ∃ p₂ ∈ m.primeFactors,
              p₁ ≠ p₂ ∧
              r' ∣ sigma 1 (ordProj[p₁] (m ^ 2)) ∧
              r' ∣ sigma 1 (ordProj[p₂] (m ^ 2)))) ∧
      (1 < a → ∀ l t : ℕ, l.Prime → sigma 1 (m ^ 2) / q ^ a = l * t ^ 2 →
        let d := (a + 1) / 2
        ∃ (y : ℕ) (k : ℤ) (α : ℤ√2),
          0 < y ∧ d ∣ y ∧ q ^ d + 1 = 2 * y ^ 2 ∧
          1 ≤ |k| ∧ 2 * |k| ≤ (d : ℤ) - 1 ∧
          (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d ∧
          (Odd k → 1 ≤ α.re ∧ 48 * α.im ^ 2 < 5 * (q : ℤ)) ∧
          (Even k → 1 ≤ α.im ∧ 24 * α.re ^ 2 < 5 * (q : ℤ)) ∧
          (|k| = 2 →
            4 * (d : ℤ) - 3 ≤ |α.re| ∧
            (d ^ 2 - 8) * (4 * d - 3) ^ 2 < 8 * q ∧
            148403 < q ∧
            (k = -2 → 177065 < q) ∧
            (¬ 3 ∣ N → ¬ 5 ∣ N → 241 ≤ d ∧ 6703954379 < q ∧ (k = -2 → 6787927937 < q)))) := by
  obtain ⟨hcoll_all, _⟩ := odd_perfect_exists_odd_prime_sigma_collision ho hN
  obtain ⟨_, _, _, _, q, a, m, hq, hq_mem, hq4, ha4, ha_pos, hqm, hform, _, _⟩ :=
    odd_perfect_tier2_waveD_master_profile ho hN
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
  obtain ⟨hcard_le_inc, h3E3, _, h3E2_no3⟩ :=
    odd_perfect_collision_excess_bound ho hN hq_mem hq4 he_q hev_N
  have h5_card := five_le_distinct_prime_factor_count ho hN
  refine ⟨hcoll_all, q, a, m, hq, hq_mem, hq4, ha4, ha_pos, hqm, hform, ?_, ?_, ?_⟩
  · dsimp only
    have hE1 : 1 ≤ (∑ p ∈ N.primeFactors, (oddComponentSigma N q p).primeFactors.card) -
        N.primeFactors.card := by omega
    refine ⟨hE1, h3E3, ?_, ?_⟩
    · intro h3
      have h8 := eight_le_distinct_prime_factor_count_of_three_free ho hN h3
      have hb := h3E2_no3 h3
      exact ⟨by omega, hb⟩
    · intro hfree
      obtain ⟨_, h147, h590⟩ :=
        sixth_power_free_collision_excess_ge_147 ho hN hq_mem hq4 he_q hev_N hfree
      exact ⟨h147, h590⟩
  · intro ha1
    have hform1 : N = q * m ^ 2 := by simpa [ha1] using hform
    exact linear_euler_unconditional_nontrivial_sigma_collision ho hN hq hqm hform1
  · intro ha_gt1 l t hl hi d
    obtain ⟨_, hd17, hd8, _, _, _, _⟩ :=
      exceptional_index_fermat_witness hN ho hq hq4 ha4 ha_gt1 hqm hform hl hi
    have hq3 : 3 ≤ q := by have := hq.two_le; omega
    have hd_odd : Odd d := Nat.odd_iff.mpr (by omega)
    have hd3 : 3 ≤ d := by omega
    obtain ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, hnorm, hk2_cond⟩ :=
      exceptional_euler_unit_exponent_two_quartic_bound
        hN ho hq hq4 ha4 ha_gt1 hqm hform hl hi
    have hcone :=
      zsqrtTwo_universal_archimedean_cone hq3 hd_odd hd3 hy_pos hpow hk1 h2k hz_eq hnorm
    refine ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, ?_, ?_, ?_⟩
    · intro hk_odd
      have ho_c := hcone.2.2.2.2.2.2.2.2.2.1 hk_odd
      exact ⟨ho_c.2.1, ho_c.2.2.2.2.1⟩
    · intro hk_even
      have he_c := hcone.2.2.2.2.2.2.2.2.2.2 hk_even
      exact ⟨he_c.2.1, he_c.2.2.2.2.1⟩
    · intro hk_abs2
      obtain ⟨_, _, _, hre_lb, _, h8q_lt, h148, hm2_full, h241_b⟩ := hk2_cond hk_abs2
      exact ⟨hre_lb, h8q_lt, h148, fun hm2 => (hm2_full hm2).2.2, h241_b⟩

end OddPerfect
