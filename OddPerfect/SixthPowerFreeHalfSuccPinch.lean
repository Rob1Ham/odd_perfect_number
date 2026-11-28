module

public import OddPerfect.LinearEulerUnitaryHalfSuccPeeling
public import OddPerfect.QuarticTargetCapacity
public import OddPerfect.SixthPowerFreeCofactorObstruction
public import OddPerfect.OddValuationCycleObstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Sixth-Power-Free Half-Successor & Component-Index Pinch

Tightens `OddPerfect.LinearEulerUnitaryHalfSuccPeeling` on sixth-power-free odd perfect
numbers `N = q * m ^ 2` by combining `sixth_power_free_min_prime_ge_53`,
`sixth_power_free_incoming_source_vacuum`, and `sixth_power_free_euler_index_drop_and_support`:

1. `sixth_power_free_half_succ_not_coprime_index_profile`:
   When `¬ Nat.Coprime ((q + 1) / 2) (componentIndex N q)`, any common prime factor `s` satisfies
   `s ∈ N.primeFactors.erase q`, `s % 5 = 1 ∨ s % 3 = 1`, `61 ≤ s`, `122 ≤ q + 1`,
   `2 * s ∣ q + 1`, `s ∣ componentIndex N q`, and `s ∣ σ(ordProj[p] N)` for some
   `p ∈ N.primeFactors.erase q` with `p ≠ s`.
2. `sixth_power_free_coprime_half_succ_index_profile`:
   When `Nat.Coprime ((q + 1) / 2) (componentIndex N q)`, `(q + 1) / 2 = h ^ 2` and
   `componentIndex N q = u ^ 2` satisfy `59 ≤ h`, `6961 ≤ q`, `q % 48 = 1`,
   `q % 5 = 1 ∨ q % 5 = 2`, `(∏ p ∈ S₅₀, p) * (∏ v ∈ Q₂₃, v ^ 2) ∣ h`, and a nontrivial
   odd-prime `σ`-collision `r' ∈ N.primeFactors` (`53 ≤ r'`) between two distinct square
   components `p₁ ≠ p₂ ∈ N.primeFactors.erase q`.
3. `sixth_power_free_unconditional_nontrivial_collision_and_q_dichotomy`:
   Unconditional global synthesis of (1) and (2) for every sixth-power-free odd perfect number.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma sixth_power_free_linear_euler_data {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    ∃ m : ℕ,
      Odd m ∧ ¬ q ∣ m ∧ N = q * m ^ 2 ∧
      m.primeFactors = N.primeFactors.erase q ∧
      ∀ p : ℕ, p ≠ q → ordProj[p] (m ^ 2) = ordProj[p] N := by
  obtain ⟨m, _, hm_odd, hqm, hform, _⟩ :=
    sixth_power_free_unique_q_source_mirror_dichotomy ho hN hq hq4 he hev hfree
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hpf_eq : m.primeFactors = N.primeFactors.erase q := by
    ext p
    rw [Finset.mem_erase, Nat.mem_primeFactors, Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, hpm, _⟩
      have hpq : p ≠ q := fun h => hqm (h ▸ hpm)
      have hpN : p ∣ N := hform ▸ hpm.trans ((dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left _ _))
      exact ⟨hpq, hp, hpN, hN.2.ne'⟩
    · rintro ⟨hpq, hp, hpN, _⟩
      rw [hform] at hpN
      have hpm2 : p ∣ m ^ 2 := (hp.dvd_mul.mp hpN).resolve_left fun hq_dvd =>
        hpq (((Nat.dvd_prime hq_prime).mp hq_dvd).resolve_left hp.ne_one)
      exact ⟨hp, hp.dvd_of_dvd_pow hpm2, hm0⟩
  have hord_eq : ∀ p : ℕ, p ≠ q → ordProj[p] (m ^ 2) = ordProj[p] N := by
    intro p hpq
    by_cases hp1 : p = 1
    · subst hp1
      simp only [one_pow]
    · have hnot_q : ¬ p ∣ q := fun hd =>
        hpq (((Nat.dvd_prime hq_prime).mp hd).resolve_left hp1)
      have hfac : N.factorization p = (m ^ 2).factorization p := by
        rw [hform, Nat.factorization_mul hq_prime.ne_zero hm20, Finsupp.add_apply,
          Nat.factorization_eq_zero_of_not_dvd hnot_q, zero_add]
      rw [hfac]
  exact ⟨m, hm_odd, hqm, hform, hpf_eq, hord_eq⟩

private lemma dvd_of_sq_dvd_sq {a b : ℕ} (hb0 : b ≠ 0) (h : a ^ 2 ∣ b ^ 2) : a ∣ b := by
  by_cases ha0 : a = 0
  · subst ha0
    simp at h
    exact absurd h hb0
  rw [← Nat.factorization_le_iff_dvd ha0 hb0]
  intro p
  have hle := (Nat.factorization_le_iff_dvd (pow_ne_zero 2 ha0) (pow_ne_zero 2 hb0)).mpr h p
  rw [Nat.factorization_pow, Nat.factorization_pow, Finsupp.smul_apply, Finsupp.smul_apply,
    smul_eq_mul, smul_eq_mul] at hle
  omega

private lemma two_sq_sub_one_mod_48 {q h : ℕ}
    (hh_odd : Odd h) (hh3 : ¬ 3 ∣ h) (hq_eq : q = 2 * h ^ 2 - 1) : q % 48 = 1 := by
  have hh_pos : 0 < h := hh_odd.pos
  have hh2_pos : 1 ≤ h ^ 2 := Nat.one_le_pow 2 h hh_pos
  have hq_add : q + 1 = 2 * h ^ 2 := by omega
  have hh2_mod8 : h ^ 2 % 8 = 1 := by
    obtain ⟨k, rfl⟩ := hh_odd
    have hk2 : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
    have hkeven : 2 ∣ k * (k + 1) := by
      rcases Nat.even_or_odd k with ⟨t, ht⟩ | ⟨t, ht⟩
      · exact ⟨t * (k + 1), by rw [ht]; ring⟩
      · exact ⟨k * (t + 1), by rw [ht]; ring⟩
    obtain ⟨t, ht⟩ := hkeven
    rw [hk2, ht]
    omega
  have hh2_mod3 : h ^ 2 % 3 = 1 := by
    have hnz : h % 3 ≠ 0 := fun h0 => hh3 (Nat.dvd_of_mod_eq_zero h0)
    have hmod3 : h % 3 = 1 ∨ h % 3 = 2 := by omega
    rcases hmod3 with h1 | h2
    · rw [pow_two, Nat.mul_mod, h1]
    · rw [pow_two, Nat.mul_mod, h2]
  have hh2_mod24 : h ^ 2 % 24 = 1 := by omega
  omega

private lemma two_sq_sub_one_mod_5 {q h : ℕ}
    (hh_pos : 0 < h) (hh5 : ¬ 5 ∣ h) (hq_eq : q = 2 * h ^ 2 - 1) :
    q % 5 = 1 ∨ q % 5 = 2 := by
  have hh2_pos : 1 ≤ h ^ 2 := Nat.one_le_pow 2 h hh_pos
  have hq_add : q + 1 = 2 * h ^ 2 := by omega
  have hnz : h % 5 ≠ 0 := fun h0 => hh5 (Nat.dvd_of_mod_eq_zero h0)
  have hmod5 : h % 5 = 1 ∨ h % 5 = 2 ∨ h % 5 = 3 ∨ h % 5 = 4 := by omega
  have hh2_mod5 : h ^ 2 % 5 = 1 ∨ h ^ 2 % 5 = 4 := by
    rcases hmod5 with h1 | h2 | h3' | h4
    · left; rw [pow_two, Nat.mul_mod, h1]
    · right; rw [pow_two, Nat.mul_mod, h2]
    · right; rw [pow_two, Nat.mul_mod, h3']
    · left; rw [pow_two, Nat.mul_mod, h4]
  rcases hh2_mod5 with hm1 | hm4
  · left
    have hq1 : (q + 1) % 5 = 2 := by rw [hq_add, Nat.mul_mod, hm1]
    omega
  · right
    have hq1 : (q + 1) % 5 = 3 := by rw [hq_add, Nat.mul_mod, hm4]
    omega

/-- **1. Non-Coprime Half-Successor & Index Profile on Sixth-Power-Free Odd Perfect Numbers**:
When `¬ Nat.Coprime ((q + 1) / 2) (componentIndex N q)`, any common prime factor `s` lies in
`N.primeFactors.erase q`, satisfies `s % 5 = 1 ∨ s % 3 = 1`, `61 ≤ s`, `122 ≤ q + 1`,
`2 * s ∣ q + 1`, `s ∣ componentIndex N q`, and `s ∣ σ(ordProj[p] N)` for some distinct
`p ∈ N.primeFactors.erase q`. -/
theorem sixth_power_free_half_succ_not_coprime_index_profile {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N)
    (hncop : ¬ Nat.Coprime ((q + 1) / 2) (componentIndex N q)) :
    ∃ s ∈ N.primeFactors.erase q,
      s.Prime ∧
      Odd s ∧
      (s % 5 = 1 ∨ s % 3 = 1) ∧
      61 ≤ s ∧
      122 ≤ q + 1 ∧
      s ∣ (q + 1) / 2 ∧
      2 * s ∣ q + 1 ∧
      s ∣ sigma 1 (ordProj[q] N) ∧
      s ∣ componentIndex N q ∧
      ∃ p ∈ N.primeFactors.erase q, p ≠ s ∧ s ∣ sigma 1 (ordProj[p] N) := by
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  obtain ⟨m, _, hqm, hform, hpf_eq, hord_eq⟩ :=
    sixth_power_free_linear_euler_data ho hN hq hq4 he hev hfree
  obtain ⟨s, hs_m, p, hp_m, hs_prime, hs_odd, hs_ne_q, hp_ne_s, hp_ne_q,
    hs_half, hs_2_q1, hs_sig_q, hs_ci, _, hs_dvd_p⟩ :=
    linear_euler_half_succ_not_coprime_index_forces_euler_collision ho hN hq_prime hqm hform hncop
  have hs_er : s ∈ N.primeFactors.erase q := hpf_eq ▸ hs_m
  have hp_er : p ∈ N.primeFactors.erase q := hpf_eq ▸ hp_m
  have hs_N : s ∈ N.primeFactors := Finset.mem_of_mem_erase hs_er
  have hs_ge53 : 53 ≤ s := sixth_power_free_min_prime_ge_53 ho hN hfree hs_N
  obtain ⟨_, hci_pos⟩ := componentIndex_mul_eq_two_mul hN hq
  have hs_ci_mem : s ∈ (componentIndex N q).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hs_prime, hs_ci, hci_pos.ne'⟩
  have hs_mod : s % 5 = 1 ∨ s % 3 = 1 :=
    (sixth_power_free_euler_index_drop_and_support ho hN hq hq4 he hev hfree).2 s hs_ci_mem
  have hs_ge61 : 61 ≤ s := by
    by_contra! hlt
    have hs_cases : s = 54 ∨ s = 55 ∨ s = 56 ∨ s = 57 ∨ s = 58 ∨ s = 60 := by omega
    rcases hs_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (by decide : ¬ Nat.Prime _) hs_prime
  have hq1_ge122 : 122 ≤ q + 1 := by
    have hle : 2 * s ≤ q + 1 := Nat.le_of_dvd (Nat.succ_pos q) hs_2_q1
    omega
  refine ⟨s, hs_er, hs_prime, hs_odd, hs_mod, hs_ge61, hq1_ge122, hs_half, hs_2_q1,
    hs_sig_q, hs_ci, p, hp_er, hp_ne_s, ?_⟩
  rwa [← hord_eq p hp_ne_q]

/-- **2. Coprime Half-Successor & Index Profile on Sixth-Power-Free Odd Perfect Numbers**:
When `Nat.Coprime ((q + 1) / 2) (componentIndex N q)`, `(q + 1) / 2 = h ^ 2` and
`componentIndex N q = u ^ 2` satisfy `59 ≤ h`, `6961 ≤ q`, `q % 48 = 1`,
`q % 5 = 1 ∨ q % 5 = 2`, `(∏ p ∈ S₅₀, p) * (∏ v ∈ Q₂₃, v ^ 2) ∣ h`, and an explicit odd-prime
`σ`-collision `r' ∈ N.primeFactors` (`53 ≤ r'`) between two distinct square components
`p₁ ≠ p₂ ∈ N.primeFactors.erase q`. -/
theorem sixth_power_free_coprime_half_succ_index_profile {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N)
    (hcop : Nat.Coprime ((q + 1) / 2) (componentIndex N q)) :
    (∃ h u : ℕ,
      Odd h ∧ 59 ≤ h ∧ Odd u ∧ 1 < u ∧ Nat.Coprime h u ∧
      N = q * (h * u) ^ 2 ∧
      ¬ q ∣ h * u ∧
      (q + 1) / 2 = h ^ 2 ∧
      q = 2 * h ^ 2 - 1 ∧
      componentIndex N q = u ^ 2 ∧
      (∏ p ∈ (squareSources N).filter (· % 5 ≠ 1), p) *
        (∏ v ∈ twoModThreeLargeSources N q, v ^ 2) ∣ h) ∧
    IsSquare ((q + 1) / 2) ∧
    IsSquare (componentIndex N q) ∧
    6961 ≤ q ∧
    q % 24 = 1 ∧
    q % 48 = 1 ∧
    (q % 5 = 1 ∨ q % 5 = 2) ∧
    ∃ r' ∈ N.primeFactors,
      r'.Prime ∧ Odd r' ∧ 53 ≤ r' ∧
      ∃ p₁ ∈ N.primeFactors.erase q, ∃ p₂ ∈ N.primeFactors.erase q,
        p₁ ≠ p₂ ∧
        r' ∣ sigma 1 (ordProj[p₁] N) ∧
        r' ∣ sigma 1 (ordProj[p₂] N) := by
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have h3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  have h5 : ¬ 5 ∣ N := sixth_power_free_five_not_dvd ho hN hfree
  obtain ⟨m, hm_odd, hqm, hform, hpf_eq, hord_eq⟩ :=
    sixth_power_free_linear_euler_data ho hN hq hq4 he hev hfree
  obtain ⟨⟨h, u, hh_odd, _, hu_odd, hu_gt1, hcop_hu, hm_eq, hhalf_eq, hq_eq,
    hci_sq_eq, _, hh_ge7_fn⟩, _, _, h3_fn⟩ :=
    linear_euler_coprime_half_succ_index_square_split ho hN hq_prime hqm hform hcop
  have hh_ge7 : 7 ≤ h := hh_ge7_fn h3
  obtain ⟨hq_mod24, _⟩ := h3_fn h3
  have hh_dvd_N : h ∣ N := by
    rw [hform, hm_eq]
    exact (dvd_mul_right h u).trans
      ((dvd_pow_self (h * u) (by decide : 2 ≠ 0)).trans (dvd_mul_left _ q))
  have hh0 : h ≠ 0 := hh_odd.pos.ne'
  have hh_ge59 : 59 ≤ h := by
    let rh := h.minFac
    have hrh_prime : rh.Prime := Nat.minFac_prime (by omega)
    have hrh_dvd_h : rh ∣ h := Nat.minFac_dvd h
    have hrh_le_h : rh ≤ h := Nat.le_of_dvd (by omega) hrh_dvd_h
    have hrh_N : rh ∈ N.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hrh_prime, hrh_dvd_h.trans hh_dvd_N, hN.2.ne'⟩
    have hrh_ge53 : 53 ≤ rh := sixth_power_free_min_prime_ge_53 ho hN hfree hrh_N
    have hh_ge53 : 53 ≤ h := hrh_ge53.trans hrh_le_h
    have hh_ne53 : h ≠ 53 := by
      intro h53
      rw [h53] at hq_eq
      have hq5617 : q = 5617 := by norm_num at hq_eq; exact hq_eq
      have h41_dvd : 41 ∣ q := by rw [hq5617]; norm_num
      have h41_eq : 41 = q := ((Nat.dvd_prime hq_prime).mp h41_dvd).resolve_left (by norm_num)
      omega
    have hh_ne55 : h ≠ 55 := by
      intro h55
      exact h5 ((by norm_num : 5 ∣ 55).trans (h55 ▸ hh_dvd_N))
    have hh_ne57 : h ≠ 57 := by
      intro h57
      exact h3 ((by norm_num : 3 ∣ 57).trans (h57 ▸ hh_dvd_N))
    obtain ⟨k, hk⟩ := hh_odd
    omega
  have hq_ge6961 : 6961 ≤ q := by
    have hh2_ge : 59 ^ 2 ≤ h ^ 2 := Nat.pow_le_pow_left hh_ge59 2
    omega
  have hh_not3 : ¬ 3 ∣ h := fun hd => h3 (hd.trans hh_dvd_N)
  have hq_mod48 : q % 48 = 1 := two_sq_sub_one_mod_48 hh_odd hh_not3 hq_eq
  have hh_not5 : ¬ 5 ∣ h := fun hd => h5 (hd.trans hh_dvd_N)
  have hq_mod5 : q % 5 = 1 ∨ q % 5 = 2 :=
    two_sq_sub_one_mod_5 hh_odd.pos hh_not5 hq_eq
  have hvac := sixth_power_free_incoming_source_vacuum ho hN hq hq4 he hev hfree
  dsimp only at hvac
  have hprod_dvd_h :
      (∏ p ∈ (squareSources N).filter (· % 5 ≠ 1), p) *
        (∏ v ∈ twoModThreeLargeSources N q, v ^ 2) ∣ h := by
    have hsq_dvd :
        ((∏ p ∈ (squareSources N).filter (· % 5 ≠ 1), p) *
          (∏ v ∈ twoModThreeLargeSources N q, v ^ 2)) ^ 2 ∣ h ^ 2 := by
      have hprod_eq1 :
          (∏ p ∈ (squareSources N).filter (· % 5 ≠ 1), p) ^ 2 =
            ∏ p ∈ (squareSources N).filter (· % 5 ≠ 1), p ^ 2 :=
        (Finset.prod_pow ((squareSources N).filter (· % 5 ≠ 1)) 2 (f := fun p => p)).symm
      have hprod_eq2 :
          (∏ v ∈ twoModThreeLargeSources N q, v ^ 2) ^ 2 =
            ∏ v ∈ twoModThreeLargeSources N q, v ^ 4 := by
        rw [← Finset.prod_pow (twoModThreeLargeSources N q) 2 (f := fun v => v ^ 2)]
        refine Finset.prod_congr rfl fun v _ => by ring
      rw [mul_pow, hprod_eq1, hprod_eq2, ← hhalf_eq]
      exact hvac.2.1
    exact dvd_of_sq_dvd_sq hh0 hsq_dvd
  obtain ⟨r', hr'_prime, hr'_odd, p₁, hp₁_m, p₂, hp₂_m, hp_ne, hd₁, hd₂⟩ :=
    linear_euler_coprime_half_succ_forces_square_collision ho hN hq_prime hqm hform hcop
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hp₁_er : p₁ ∈ N.primeFactors.erase q := hpf_eq ▸ hp₁_m
  have hp₂_er : p₂ ∈ N.primeFactors.erase q := hpf_eq ▸ hp₂_m
  have hp₁_neq : p₁ ≠ q := (Finset.mem_erase.mp hp₁_er).1
  have hp₂_neq : p₂ ≠ q := (Finset.mem_erase.mp hp₂_er).1
  have hr'_dvd_sigm2 : r' ∣ sigma 1 (m ^ 2) := by
    have hprod : sigma 1 (m ^ 2) = ∏ p ∈ m.primeFactors, sigma 1 (ordProj[p] (m ^ 2)) := by
      rw [isMultiplicative_sigma.multiplicative_factorization (sigma 1) hm20]
      exact Finset.prod_congr
        ((m ^ 2).support_factorization.trans (Nat.primeFactors_pow m (by decide : 2 ≠ 0)))
        fun _ _ => rfl
    exact hd₁.trans (hprod ▸ Finset.dvd_prod_of_mem _ hp₁_m)
  have hr'_dvd_N : r' ∣ N := by
    have hq_cop_m2 : q.Coprime (m ^ 2) := (hq_prime.coprime_iff_not_dvd.mpr hqm).pow_right 2
    have hsig_N : sigma 1 N = 2 * N :=
      (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul ho.pos).mp hN)
    have hsig_dvd_2N : sigma 1 (m ^ 2) ∣ 2 * N := by
      rw [← hsig_N, hform, isMultiplicative_sigma.map_mul_of_coprime hq_cop_m2]
      exact dvd_mul_left _ _
    have hr'_dvd_2N : r' ∣ 2 * N := hr'_dvd_sigm2.trans hsig_dvd_2N
    exact (hr'_prime.dvd_mul.mp hr'_dvd_2N).resolve_left fun hr2 =>
      (by decide : ¬ Odd 2) (hr'_odd.of_dvd_nat (by
        have heq : r' = 2 := ((Nat.dvd_prime Nat.prime_two).mp hr2).resolve_left hr'_prime.ne_one
        rw [heq]))
  have hr'_N : r' ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hr'_prime, hr'_dvd_N, hN.2.ne'⟩
  have hr'_ge53 : 53 ≤ r' := sixth_power_free_min_prime_ge_53 ho hN hfree hr'_N
  refine ⟨⟨h, u, hh_odd, hh_ge59, hu_odd, hu_gt1, hcop_hu, ?_, ?_, hhalf_eq, hq_eq,
    hci_sq_eq, hprod_dvd_h⟩, ⟨h, by rw [hhalf_eq, pow_two]⟩, ⟨u, by rw [hci_sq_eq, pow_two]⟩,
    hq_ge6961, hq_mod24, hq_mod48, hq_mod5, r', hr'_N, hr'_prime, hr'_odd, hr'_ge53,
    p₁, hp₁_er, p₂, hp₂_er, hp_ne, ?_, ?_⟩
  · rw [hform, hm_eq]
  · rwa [← hm_eq]
  · rwa [← hord_eq p₁ hp₁_neq]
  · rwa [← hord_eq p₂ hp₂_neq]

/-- **3. Unconditional Nontrivial `σ`-Collision & `q`-Pinch Dichotomy**:
Every sixth-power-free odd perfect number `N` satisfies one of two non-vacuous structural cases:
- Either `(q + 1) / 2` and `componentIndex N q` share a prime `s ∈ N.primeFactors.erase q`
  satisfying `s % 5 = 1 ∨ s % 3 = 1`, `61 ≤ s`, `2 * s ∣ q + 1`, `s ∣ componentIndex N q`, and
  `s ∣ σ(ordProj[p] N)` for some `p ∈ N.primeFactors.erase q` with `p ≠ s`;
- Or `Nat.Coprime ((q + 1) / 2) (componentIndex N q)`, forcing `IsSquare ((q + 1) / 2)`,
  `IsSquare (componentIndex N q)`, `q % 48 = 1`, `6961 ≤ q`, and a nontrivial `σ`-collision
  `r' ∈ N.primeFactors` between two distinct square components `p₁ ≠ p₂ ∈ N.primeFactors.erase q`. -/
theorem sixth_power_free_unconditional_nontrivial_collision_and_q_dichotomy {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    (∃ s ∈ N.primeFactors.erase q,
      (s % 5 = 1 ∨ s % 3 = 1) ∧
      61 ≤ s ∧
      2 * s ∣ q + 1 ∧
      s ∣ componentIndex N q ∧
      ∃ p ∈ N.primeFactors.erase q, p ≠ s ∧ s ∣ sigma 1 (ordProj[p] N)) ∨
    (Nat.Coprime ((q + 1) / 2) (componentIndex N q) ∧
      IsSquare ((q + 1) / 2) ∧
      IsSquare (componentIndex N q) ∧
      q % 48 = 1 ∧
      6961 ≤ q ∧
      ∃ r' ∈ N.primeFactors,
        ∃ p₁ ∈ N.primeFactors.erase q, ∃ p₂ ∈ N.primeFactors.erase q,
          p₁ ≠ p₂ ∧
          r' ∣ sigma 1 (ordProj[p₁] N) ∧
          r' ∣ sigma 1 (ordProj[p₂] N)) := by
  by_cases hcop : Nat.Coprime ((q + 1) / 2) (componentIndex N q)
  · right
    obtain ⟨_, hsq_half, hsq_ci, hq_ge6961, _, hq_mod48, _, r', hr'_N, _, _, _,
      p₁, hp₁, p₂, hp₂, hp_ne, hd₁, hd₂⟩ :=
      sixth_power_free_coprime_half_succ_index_profile ho hN hq hq4 he hev hfree hcop
    exact ⟨hcop, hsq_half, hsq_ci, hq_mod48, hq_ge6961, r', hr'_N, p₁, hp₁, p₂, hp₂, hp_ne, hd₁, hd₂⟩
  · left
    obtain ⟨s, hs_er, _, _, hs_mod, hs_ge61, _, _, hs_2_q1, _, hs_ci, p, hp_er, hp_ne, hd⟩ :=
      sixth_power_free_half_succ_not_coprime_index_profile ho hN hq hq4 he hev hfree hcop
    exact ⟨s, hs_er, hs_mod, hs_ge61, hs_2_q1, hs_ci, p, hp_er, hp_ne, hd⟩

end OddPerfect
