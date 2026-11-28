module

public import OddPerfect.PadicPadeCongruenceAndParity
public import OddPerfect.PrimeByPrimeMultiplicityConservation
public import OddPerfect.ZsqrtTwoQuinticSexticObstruction
public import OddPerfect.LinearEulerCoprimeHalfSuccObstruction
public import OddPerfect.GlobalTier2WaveGObstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Global Tier 2 Wave H Synthesis (`OddPerfect.GlobalTier2WaveHObstruction`)

Unifies the four Priority Wave H structural advances into cross-module global theorems:
1. **Even Prime-Power Padé Parity, Doubled `40 * p < 6 ^ u` Contraction & `20 * p ^ 2 < 6 ^ u`
   Order Collapse Profile** (`even_prime_power_pade_parity_and_order_profile`):
   couples `20 * p < 6 ^ u`, doubled `40 * p < 6 ^ u` (`p % 4 = 3 ∨ Even u`), quadratic base
   collapse `20 * p ^ 2 < 6 ^ u` (`p ∣ 64 ^ u - 1`), exact `k_pade` parity laws, and the
   mod-`(p - 2)` congruence `2 ^ (u + 1) * k_pade ≡ (2 * u + 1) * s - 1 [ZMOD p - 2]`.
2. **Tier 2 Wave H Master Profile** (`odd_perfect_tier2_waveH_master_profile`):
   unifies prime-by-prime multiplicity conservation (`N.factorization r = indegAt + localRepeatAt`),
   exponent-two collision vs. square-repeat mutual exclusion, global exponential-radical lower
   bounds (`rad(N) * N.minFac ^ (M + E) ≤ N`, `53 ^ 1179 ≤ N` on sixth-power-free `N`),
   coprime half-successor quotient duality (`u ^ 2 = W * σ(h ^ 2)`, `σ(u ^ 2) = W * (2 * h ^ 2 - 1)`,
   `3 ≤ W` and `119 * W ≤ 2 * u ^ 2 - σ(u ^ 2)` on sixth-power-free `N`), and unified `|k| ≤ 6`
   exceptional-Euler `ℤ√2` floors (`10130 < q` when `¬ 3 ∣ N ∧ ¬ 5 ∣ N`).
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- **1. Even Prime-Power Padé Parity, Doubled Contraction & Order Collapse Profile**:
On any even prime-power component index `i = p ^ (2 * u)` of an odd perfect number `N`:
- `128 ≤ u`, `(2 * u + 1).Prime`, `20 * p < 6 ^ u`,
  `(p % 4 = 3 ∨ Even u → 40 * p < 6 ^ u)`, and `(p ∣ 64 ^ u - 1 → 20 * p ^ 2 < 6 ^ u)`;
- The `(2 * u + 1)`-order Padé quotient `k_pade` satisfies
  `(p % 4 = 3 → Even k_pade ∧ 2 ≤ k_pade)`, `(p % 4 = 1 → (Even k_pade ↔ Even u))`,
  `((p : ℤ) ∣ k_pade ↔ p ∣ 64 ^ u - 1)`, and
  `2 ^ (u + 1) * k_pade ≡ (2 * (u : ℤ) + 1) * (s : ℤ) - 1 [ZMOD (p : ℤ) - 2]`. -/
theorem even_prime_power_pade_parity_and_order_profile
    {N q a b i p u : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b) (hl : sigma 1 b = q ^ a * i)
    (hr : sigma 1 (q ^ a) * i = 2 * b) (hp : p.Prime) (hu : 0 < u) (hi : i = p ^ (2 * u)) :
    128 ≤ u ∧ (2 * u + 1).Prime ∧
    20 * p < 6 ^ u ∧
    (p % 4 = 3 ∨ Even u → 40 * p < 6 ^ u) ∧
    (p ∣ 64 ^ u - 1 → 20 * p ^ 2 < 6 ^ u) ∧
    ∃ s : ℕ, Odd s ∧
      s < p ^ u ∧ p ^ u < 2 * s ∧
      let k_pade : ℤ := ((s : ℤ) * padeSeqB u p - padeSeqA u p) / (p : ℤ) ^ (2 * u + 1)
      (s : ℤ) * padeSeqB u p - padeSeqA u p = (p : ℤ) ^ (2 * u + 1) * k_pade ∧
      1 ≤ k_pade ∧
      (p % 4 = 3 → Even k_pade ∧ 2 ≤ k_pade) ∧
      (p % 4 = 1 → (Even k_pade ↔ Even u)) ∧
      ((p : ℤ) ∣ k_pade ↔ p ∣ 64 ^ u - 1) ∧
      2 ^ (u + 1) * k_pade ≡ (2 * (u : ℤ) + 1) * (s : ℤ) - 1 [ZMOD (p : ℤ) - 2] := by
  obtain ⟨hu128, h20, h40_cond, h20sq_cond⟩ :=
    even_prime_power_component_parity_and_order_caps hN ho hq ha hform hqb hl hr hp hu hi
  obtain ⟨_, hlen_prime, _, _, _, _⟩ :=
    even_prime_power_pade_quadratic_and_20_cap_profile hN ho hq ha hform hqb hl hr hp hu hi
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
  obtain ⟨hmul, hk1, _, _, _⟩ :=
    even_index_pade_quotient_pos_and_quadratic_identity hp hpo hso hu hσq hplus hσs
  obtain ⟨hpar3, hpar1, _⟩ :=
    even_index_pade_quotient_parity_and_doubled_cap hp hpo hso hu hσq hplus hσs
  obtain ⟨hpdvd_iff, _, hmod_sub2⟩ :=
    even_index_pade_quotient_mod_p_and_sub_two hp hpo hso hu hσq hplus hσs
  exact ⟨hu128, hlen_prime, h20, h40_cond, h20sq_cond,
    ⟨s, hso, hs_lt, hpu_lt_2s, hmul, hk1, hpar3, hpar1, hpdvd_iff, hmod_sub2⟩⟩

/-- **2. Tier 2 Wave H Master Profile**:
Unconditionally synthesizes prime-by-prime multiplicity conservation, exponent-two mutual
exclusion, exponential-radical bounds (`rad(N) * N.minFac ^ (M + E) ≤ N`, `53 ^ 1179 ≤ N` on
sixth-power-free `N`), coprime half-successor quotient duality (`3 ≤ W` on sixth-power-free `N`),
and unified `|k| ≤ 6` exceptional-Euler `ℤ√2` floors (`10130 < q`). -/
theorem odd_perfect_tier2_waveH_master_profile {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    ∃ q a m : ℕ,
      q.Prime ∧ q ∈ N.primeFactors ∧ q % 4 = 1 ∧ a % 4 = 1 ∧ 0 < a ∧ ¬ q ∣ m ∧
      N = q ^ a * m ^ 2 ∧
      N.primeFactors.card ≤ 2 * collisionExcess N q + 3 ∧
      (∀ r ∈ N.primeFactors,
        1 ≤ indegAt N q r ∧
        N.factorization r = indegAt N q r + localRepeatAt N q r ∧
        indegAt N q r ≤ N.factorization r) ∧
      (∑ r ∈ N.primeFactors, localRepeatAt N q r) = localRepeatExcess N q ∧
      (∑ r ∈ N.primeFactors, (indegAt N q r - 1)) = collisionExcess N q ∧
      (∀ r ∈ N.primeFactors, N.factorization r = 2 →
        (indegAt N q r = 2 ∧ localRepeatAt N q r = 0 ∧
          ∀ p ∈ N.primeFactors, ¬ r ^ 2 ∣ oddComponentSigma N q p) ∨
        (indegAt N q r = 1 ∧ localRepeatAt N q r = 1 ∧
          ∃ p ∈ N.primeFactors, r ^ 2 ∣ oddComponentSigma N q p ∧
            ∀ x ∈ N.primeFactors, x ≠ p → ¬ r ∣ oddComponentSigma N q x)) ∧
      (∏ r ∈ N.primeFactors, r) * N.minFac ^ (localRepeatExcess N q + collisionExcess N q) ≤ N ∧
      (a = 1 → Nat.Coprime ((q + 1) / 2) (componentIndex N q) →
        ∃ h u W : ℕ,
          W = sigma 1 (u ^ 2) / q ∧ Odd h ∧ Odd u ∧ Odd W ∧ 3 ≤ h ∧ 3 ≤ u ∧ 1 ≤ W ∧
          Nat.Coprime h u ∧ Nat.Coprime h W ∧ m = h * u ∧ q = 2 * h ^ 2 - 1 ∧
          u ^ 2 = W * sigma 1 (h ^ 2) ∧ sigma 1 (u ^ 2) = W * (2 * h ^ 2 - 1) ∧
          2 * u ^ 2 - sigma 1 (u ^ 2) = W * (2 * (sigma 1 (h ^ 2) - h ^ 2) + 1) ∧
          (W = 1 → 2 ≤ h.primeFactors.card)) ∧
      ((∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) →
        53 ≤ N.minFac ∧ (∏ r ∈ N.primeFactors, r) * 53 ^ 736 ≤ N ∧ 53 ^ 1179 ≤ N ∧
        (Nat.Coprime ((q + 1) / 2) (componentIndex N q) →
          ∃ h u W : ℕ,
            59 ≤ h ∧ 6961 ≤ q ∧ 3 ≤ W ∧
            u ^ 2 = W * sigma 1 (h ^ 2) ∧ sigma 1 (u ^ 2) = W * (2 * h ^ 2 - 1) ∧
            119 * W ≤ 2 * u ^ 2 - sigma 1 (u ^ 2))) ∧
      (1 < a → ∀ l t : ℕ, l.Prime → sigma 1 (m ^ 2) / q ^ a = l * t ^ 2 →
        let d := (a + 1) / 2
        ∃ (y : ℕ) (k : ℤ) (α : ℤ√2),
          0 < y ∧ d ∣ y ∧ q ^ d + 1 = 2 * y ^ 2 ∧
          1 ≤ |k| ∧ 2 * |k| ≤ (d : ℤ) - 1 ∧
          (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d ∧
          (|k| ≤ 6 → ¬ 3 ∣ N → ¬ 5 ∣ N → 241 ≤ d ∧ 10130 < q)) := by
  obtain ⟨q, a, m, hq, hq_mem, hq4, ha4, ha_pos, hqm, hform, _, _, hhalf_u, _, _, _, _, _, _, _, _, _, _⟩ :=
    odd_perfect_tier2_waveG_master_profile ho hN
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
  obtain ⟨hcons, hsum_loc, hsum_coll⟩ :=
    factorization_eq_indegAt_add_localRepeatAt ho hN hq_mem hq4 he_q hev_N
  obtain ⟨_, hexp2_excl⟩ :=
    euler_linear_and_exponent_two_mutual_exclusion ho hN hq_mem hq4 he_q hev_N
  obtain ⟨hrad_min, _, h6free_rad⟩ :=
    rad_mul_minFac_pow_excess_le_self ho hN hq_mem hq4 he_q hev_N
  refine ⟨q, a, m, hq, hq_mem, hq4, ha4, ha_pos, hqm, hform, hhalf_u,
    hcons, hsum_loc, hsum_coll, hexp2_excl, hrad_min, ?_, ?_, ?_⟩
  · intro ha1 hcop
    have hform1 : N = q * m ^ 2 := by simpa [ha1] using hform
    obtain ⟨h, u, W, hW_def, hh_o, hu_o, hW_o, hh3, hu3, hW1, hcop_hu, hcop_hW, hm_eq, hq_eq, _,
        hu2_eq, hsig_u2, _, _, hdef_eq, _, _, _, hW1_imp⟩ :=
      linear_euler_coprime_half_succ_quotient_system ho hN hq hqm hform1 hcop
    exact ⟨h, u, W, hW_def, hh_o, hu_o, hW_o, hh3, hu3, hW1, hcop_hu, hcop_hW, hm_eq, hq_eq,
      hu2_eq, hsig_u2, hdef_eq, fun h1 => (hW1_imp h1).2⟩
  · intro hfree
    obtain ⟨h53, hrad53, hpow1179⟩ := h6free_rad hfree
    refine ⟨h53, hrad53, hpow1179, fun hcop => ?_⟩
    obtain ⟨h, u, W, _, _, _, _, hh59, _, _, hW3, _, _, _, _, _, _, hq6961, _, hu2_eq,
        hsig_u2, _, _, _, h119W⟩ :=
      sixth_power_free_coprime_half_succ_quotient_bounds ho hN hq_mem hq4 he_q hev_N hfree hcop
    exact ⟨h, u, W, hh59, hq6961, hW3, hu2_eq, hsig_u2, h119W⟩
  · intro ha_gt1 l t hl hi d
    obtain ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, _, hk6_cond⟩ :=
      exceptional_euler_k_le_six_unified_floor hN ho hq hq4 ha4 ha_gt1 hqm hform hl hi
    exact ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, hk6_cond⟩

end OddPerfect
