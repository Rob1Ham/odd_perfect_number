module

public import OddPerfect.HalfRankCollisionObstruction
public import OddPerfect.LocalRepeatSquarefreeObstruction
public import OddPerfect.ZsqrtTwoEvenKAndQuarticObstruction
public import OddPerfect.PadicPadeQuadraticQuotient
public import OddPerfect.GlobalTier2WaveFObstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Global Tier 2 Wave G Synthesis (`OddPerfect.GlobalTier2WaveGObstruction`)

Unifies the four Priority Wave G structural advances into cross-module global theorems:
1. **Even Prime-Power Pell–Padé Quadratic Quotient & `20 * p < 6 ^ u` Cap Profile**
   (`even_prime_power_pade_quadratic_and_20_cap_profile`):
   couples the `239 / 41` Padé contraction (`41 ^ (u - 2) * p < 41 * 239 ^ (u - 2)` and
   `20 * p < 6 ^ u` at `128 ≤ u`) with the exact Diophantine quadratic equation and positivity
   (`1 ≤ k_pade`) of the `(2 * u + 1)`-order Padé quotient `k_pade`.
2. **Tier 2 Wave G Master Profile** (`odd_perfect_tier2_waveG_master_profile`):
   unifies the half-rank Ljunggren collision-excess bound (`ω(N) ≤ 2 * E + 3`, `≤ 2 * E + 2`
   when `v₃(N) ≠ 4`, `3 ≤ E` when `¬ 3 ∣ N`, `221 ≤ E` on sixth-power-free `N`), the
   squarefree-component equivalence (`localRepeatExcess N q = 0 ↔ ∀ p, Squarefree ...`),
   `22 ≤ localRepeatExcess N q + collisionExcess N q` (`736 ≤ M + E` on sixth-power-free `N`),
   and the unified `|k| ≤ 4` exceptional-Euler `ℤ√2` quartic floor (`57993 < q` when
   `¬ 3 ∣ N ∧ ¬ 5 ∣ N`).
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- **1. Even Prime-Power Pell–Padé Quadratic Quotient & `20 * p < 6 ^ u` Profile**:
On any even prime-power component index `i = p ^ (2 * u)` of an odd perfect number `N`:
- `128 ≤ u`, `(2 * u + 1).Prime`, `41 ^ (u - 2) * p < 41 * 239 ^ (u - 2)`, and **`20 * p < 6 ^ u`**;
- Some `r ∈ {3, 5, 7, 11, 13}` satisfies `r ^ 2 ∣ N` with `p = geometricBlock r l` (`l.Prime`, `2 < l`)
  and `20 * geometricBlock r l < 6 ^ u`;
- The `(2 * u + 1)`-order Pell–Padé quotient `k_pade` satisfies `1 ≤ k_pade` and the exact
  quadratic Diophantine identity
  `2 * (p - 1) * p ^ (2 * u + 1) * k_pade ^ 2 + 4 * (p - 1) * padeSeqA u p * k_pade = padeSeqB u p ^ 2 - 1`. -/
theorem even_prime_power_pade_quadratic_and_20_cap_profile
    {N q a b i p u : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b) (hl : sigma 1 b = q ^ a * i)
    (hr : sigma 1 (q ^ a) * i = 2 * b) (hp : p.Prime) (hu : 0 < u) (hi : i = p ^ (2 * u)) :
    128 ≤ u ∧ (2 * u + 1).Prime ∧
    41 ^ (u - 2) * p < 41 * 239 ^ (u - 2) ∧ 20 * p < 6 ^ u ∧
    (∃ r ∈ ({3, 5, 7, 11, 13} : Finset ℕ),
      r ^ 2 ∣ N ∧ ∃ l : ℕ, l.Prime ∧ 2 < l ∧ geometricBlock r l = p ∧
        20 * geometricBlock r l < 6 ^ u) ∧
    ∃ s : ℕ, Odd s ∧
      s < p ^ u ∧ p ^ u < 2 * s ∧
      s ^ 2 ≡ 4 ^ u [MOD p - 2] ∧
      let k_pade : ℤ := ((s : ℤ) * padeSeqB u p - padeSeqA u p) / (p : ℤ) ^ (2 * u + 1)
      (s : ℤ) * padeSeqB u p - padeSeqA u p = (p : ℤ) ^ (2 * u + 1) * k_pade ∧
      1 ≤ k_pade ∧
      2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) * k_pade ^ 2 +
        4 * ((p : ℤ) - 1) * padeSeqA u p * k_pade = padeSeqB u p ^ 2 - 1 ∧
      k_pade ∣ (padeSeqB u p ^ 2 - 1) / (2 * ((p : ℤ) - 1)) := by
  obtain ⟨hu128, hcap239, h20_6u⟩ :=
    even_prime_power_component_sharpened_pade_cap hN ho hq ha hform hqb hl hr hp hu hi
  obtain ⟨_, hlen_prime, _, ⟨r, hr_mem, hr2_dvd, l, hl_prime, hl_gt2, hgeom_eq, _⟩, _⟩ :=
    even_prime_power_pade_six_pow_profile hN ho hq ha hform hqb hl hr hp hu hi
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
  obtain ⟨hmul, hk1, hquad, _, hk_dvd⟩ :=
    even_index_pade_quotient_pos_and_quadratic_identity hp hpo hso hu hσq hplus hσs
  refine ⟨hu128, hlen_prime, hcap239, h20_6u,
    ⟨r, hr_mem, hr2_dvd, l, hl_prime, hl_gt2, hgeom_eq, hgeom_eq.symm ▸ h20_6u⟩,
    ⟨s, hso, hs_lt, hpu_lt_2s, hmod_p2, hmul, hk1, hquad, hk_dvd⟩⟩

/-- **2. Tier 2 Wave G Master Profile**:
Unconditionally couples half-rank Ljunggren collision-excess bounds (`ω(N) ≤ 2 * E + 3`,
`≤ 2 * E + 2` when `v₃(N) ≠ 4`, `3 ≤ E` when `¬ 3 ∣ N`), least-prime logarithmic collision
bounds, local-repeat vs. squarefree component equivalence, `22 ≤ M + E`, sixth-power-free
`221 ≤ E ∧ 736 ≤ M + E`, and unified `|k| ≤ 4` exceptional-Euler quartic `q`-floors. -/
theorem odd_perfect_tier2_waveG_master_profile {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    ∃ q a m : ℕ,
      q.Prime ∧ q ∈ N.primeFactors ∧ q % 4 = 1 ∧ a % 4 = 1 ∧ 0 < a ∧ ¬ q ∣ m ∧
      N = q ^ a * m ^ 2 ∧
      2 ≤ collisionExcess N q ∧
      (¬ 3 ∣ N → 3 ≤ collisionExcess N q) ∧
      N.primeFactors.card ≤ 2 * collisionExcess N q + 3 ∧
      (N.factorization 3 ≠ 4 → N.primeFactors.card ≤ 2 * collisionExcess N q + 2) ∧
      ((N.minFac : ℝ) - 1) * Real.log 2 < 2 * (collisionExcess N q : ℝ) + 3 ∧
      (N.factorization 3 ≠ 4 →
        ((N.minFac : ℝ) - 1) * Real.log 2 < 2 * (collisionExcess N q : ℝ) + 2) ∧
      cardFactors N = N.primeFactors.card + localRepeatExcess N q + collisionExcess N q ∧
      (localRepeatExcess N q = 0 ↔
        ∀ p ∈ N.primeFactors, Squarefree (oddComponentSigma N q p)) ∧
      22 ≤ localRepeatExcess N q + collisionExcess N q ∧
      ((∀ p ∈ N.primeFactors, Squarefree (oddComponentSigma N q p)) →
        22 ≤ collisionExcess N q ∧ (¬ 3 ∣ N → 23 ≤ collisionExcess N q)) ∧
      13 * N.primeFactors.card + 11 * (twoModThreeLargeSources N q).card ≤
        8 * (localRepeatExcess N q + collisionExcess N q) + 39 ∧
      ((∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) →
        443 ≤ N.primeFactors.card ∧
        221 ≤ collisionExcess N q ∧
        736 ≤ localRepeatExcess N q + collisionExcess N q) ∧
      (1 < a → ∀ l t : ℕ, l.Prime → sigma 1 (m ^ 2) / q ^ a = l * t ^ 2 →
        let d := (a + 1) / 2
        ∃ (y : ℕ) (k : ℤ) (α : ℤ√2),
          0 < y ∧ d ∣ y ∧ q ^ d + 1 = 2 * y ^ 2 ∧
          1 ≤ |k| ∧ 2 * |k| ≤ (d : ℤ) - 1 ∧
          (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d ∧
          (|k| ≤ 4 → ¬ 3 ∣ N → ¬ 5 ∣ N → 241 ≤ d ∧ 57993 < q)) := by
  obtain ⟨_, q, a, m, hq, hq_mem, hq4, ha4, ha_pos, hqm, hform, hE2, hdecomp, _, _, _⟩ :=
    odd_perfect_tier2_waveF_master_profile ho hN
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
  obtain ⟨hhalf_u, hhalf_ne4, _⟩ :=
    odd_perfect_half_rank_collision_excess_bound ho hN hq_mem hq4 he_q hev_N
  obtain ⟨hlog_u, hlog_ne4, _⟩ :=
    half_rank_collision_least_prime_log_bound ho hN hq_mem hq4 he_q hev_N
  have hE3 : ¬ 3 ∣ N → 3 ≤ collisionExcess N q := fun h3 =>
    (three_le_collisionExcess_of_three_free ho hN hq_mem hq4 he_q hev_N h3).1
  have hsq_iff := localRepeatExcess_eq_zero_iff_all_squarefree ho hN hq_mem hq4 he_q hev_N
  obtain ⟨h22, _, hsq22⟩ := squarefree_components_force_22_collisions ho hN hq_mem hq4 he_q hev_N
  obtain ⟨h13, _, h736_f⟩ := cyclotomic_slope_excess_bounds ho hN hq_mem hq4 he_q hev_N
  refine ⟨q, a, m, hq, hq_mem, hq4, ha4, ha_pos, hqm, hform, hE2, hE3,
    hhalf_u, hhalf_ne4, hlog_u, hlog_ne4, hdecomp, hsq_iff, h22, hsq22, h13, ?_, ?_⟩
  · intro hfree
    obtain ⟨h443, h221, _⟩ :=
      sixth_power_free_collision_excess_ge_221 ho hN hq_mem hq4 he_q hev_N hfree
    exact ⟨h443, h221, h736_f hfree⟩
  · intro ha_gt1 l t hl hi d
    obtain ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, _, hk4_cond⟩ :=
      exceptional_euler_k_le_four_unified_floor hN ho hq hq4 ha4 ha_gt1 hqm hform hl hi
    exact ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, hk4_cond⟩

end OddPerfect
