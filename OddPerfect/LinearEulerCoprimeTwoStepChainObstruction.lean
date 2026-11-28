module

public import OddPerfect.LinearEulerCoprimeV0Obstruction
import OddPerfect.SixthPowerFreeEuler
import OddPerfect.GlobalWave5Obstruction
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Linear Euler Coprime Half-Successor Two-Step Chain & Eight-Digit `W` Obstruction

Formalizes the two-step prime-chain and eight-digit `W` dichotomy on the coprime
half-successor branch `Nat.Coprime ((q + 1) / 2) (componentIndex N q)` of a
sixth-power-free odd perfect number `N = q * (h * u) ^ 2`:

1. `sixth_power_free_coprime_half_succ_two_step_dichotomy`:
   Combines the reverse `σ`-edge `r₀ ∣ σ(s ^ (2 * v_s(U₀)))` with `61 ≤ r₀`, `61 ≤ s`,
   `¬ 3 ∣ N`, and sixth-power-freeness (`e₀, v_s(U₀) ∈ {1, 2}`) to obtain a sharp
   two-case dichotomy:
   - Either `v_s(U₀) = 1`: `s ≡ 1 [MOD 5]`, `71 ≤ s`, `r₀ ∣ s ^ 2 + s + 1`, `r₀ ≡ 1 [MOD 3]`,
     `e₀ = 2`, `r₀ ∈ oneModThreeLargeSources N q`, and `13845841 ≤ r₀ ^ (2 * e₀)`;
   - Or `v_s(U₀) = 2`: `s ∈ largeSources N q`, `r₀ ∣ s ^ 4 + s ^ 3 + s ^ 2 + s + 1`,
     `r₀ ≡ 1 [MOD 5]`, `3721 ≤ U₀`, `13849563 ≤ W`, and `1648097997 ≤ 2 * u ^ 2 - σ(u ^ 2)`.
2. `sixth_power_free_coprime_half_succ_source_or_w_eight_digit_floor`:
   Extracts the clean structural floor `13845841 ≤ r₀ ^ (2 * e₀)` or
   `3721 ≤ U₀ ∧ 13849563 ≤ W ∧ 1648097997 ≤ 2 * u ^ 2 - σ(u ^ 2)`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma sq_add_self_add_one_le_sigma_sq_of_gt_one {n : ℕ} (hn : 1 < n) :
    n ^ 2 + n + 1 ≤ sigma 1 (n ^ 2) := by
  have hn2_pos : 0 < n ^ 2 := pow_pos (by omega) 2
  have h1_mem : 1 ∈ (n ^ 2).divisors := Nat.mem_divisors.mpr ⟨one_dvd _, hn2_pos.ne'⟩
  have hn_mem : n ∈ (n ^ 2).divisors :=
    Nat.mem_divisors.mpr ⟨dvd_pow_self n (by decide : 2 ≠ 0), hn2_pos.ne'⟩
  have hn2_mem : n ^ 2 ∈ (n ^ 2).divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, hn2_pos.ne'⟩
  have hsub : ({1, n, n ^ 2} : Finset ℕ) ⊆ (n ^ 2).divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have h1_lt_n2 : 1 < n ^ 2 := by nlinarith only [hn]
  have hn_lt_n2 : n < n ^ 2 := by nlinarith only [hn]
  have hsum : ∑ d ∈ ({1, n, n ^ 2} : Finset ℕ), d ≤ sigma 1 (n ^ 2) := by
    rw [sigma_one_apply]
    exact Finset.sum_le_sum_of_subset hsub
  have hcard_sum : ∑ d ∈ ({1, n, n ^ 2} : Finset ℕ), d = n ^ 2 + n + 1 := by
    rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
    · ring
    · simp only [Finset.mem_singleton]
      exact hn_lt_n2.ne
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h) <;> omega
  linarith only [hsum, hcard_sum]

private lemma prime_u_mod_and_ge_61
    {N q h u p : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N)
    (hu_ne0 : u ≠ 0) (hform_hu : N = q * (h * u) ^ 2) (hci_sq_eq : componentIndex N q = u ^ 2)
    (hp_u : p ∈ u.primeFactors) :
    (p % 5 = 1 ∨ p % 3 = 1) ∧ 61 ≤ p := by
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_u
  have hp_dvd_u : p ∣ u := Nat.dvd_of_mem_primeFactors hp_u
  have hp_dvd_u2 : p ∣ u ^ 2 := hp_dvd_u.trans (dvd_pow_self u (by decide : 2 ≠ 0))
  have hp_dvd_N : p ∣ N := by
    rw [hform_hu]
    exact (hp_dvd_u.trans (dvd_mul_left u h)).trans
      ((dvd_pow_self (h * u) (by decide : 2 ≠ 0)).trans (dvd_mul_left _ q))
  have hp_N : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd_N, hN.2.ne'⟩
  have hp_ge53 : 53 ≤ p := sixth_power_free_min_prime_ge_53 ho hN hfree hp_N
  have hci_ne0 : componentIndex N q ≠ 0 := by
    rw [hci_sq_eq]
    exact pow_ne_zero 2 hu_ne0
  have hp_ci : p ∈ (componentIndex N q).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp_prime, hci_sq_eq ▸ hp_dvd_u2, hci_ne0⟩
  have hp_mod : p % 5 = 1 ∨ p % 3 = 1 :=
    (sixth_power_free_euler_index_drop_and_support ho hN hq hq4 he hev hfree).2 p hp_ci
  have hp_ge61 : 61 ≤ p := by
    by_contra! hlt
    have hp_cases : p = 53 ∨ p = 54 ∨ p = 55 ∨ p = 56 ∨ p = 57 ∨ p = 58 ∨ p = 59 ∨ p = 60 := by
      omega
    rcases hp_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (by decide : ¬ (53 % 5 = 1 ∨ 53 % 3 = 1)) hp_mod
    · exact (by decide : ¬ Nat.Prime 54) hp_prime
    · exact (by decide : ¬ Nat.Prime 55) hp_prime
    · exact (by decide : ¬ Nat.Prime 56) hp_prime
    · exact (by decide : ¬ Nat.Prime 57) hp_prime
    · exact (by decide : ¬ Nat.Prime 58) hp_prime
    · exact (by decide : ¬ (59 % 5 = 1 ∨ 59 % 3 = 1)) hp_mod
    · exact (by decide : ¬ Nat.Prime 60) hp_prime
  exact ⟨hp_mod, hp_ge61⟩

/-- **1. Sixth-Power-Free Coprime Half-Successor Two-Step Chain Dichotomy**:
On a sixth-power-free odd perfect number `N` in the coprime half-successor branch,
both `e₀` and `k_s := U₀.factorization s` lie in `{1, 2}`, and:
- If `k_s = 1`, then `s % 5 = 1`, `71 ≤ s`, `r₀ ∣ s ^ 2 + s + 1`, `r₀ % 3 = 1`, `e₀ = 2`,
  `r₀ ∈ oneModThreeLargeSources N q`, and `13845841 ≤ r₀ ^ (2 * e₀)`;
- If `k_s = 2`, then `s ∈ largeSources N q`, `r₀ ∣ s ^ 4 + s ^ 3 + s ^ 2 + s + 1`,
  `r₀ % 5 = 1`, `3721 ≤ U₀`, `13849563 ≤ W`, and `1648097997 ≤ 2 * u ^ 2 - σ(u ^ 2)`. -/
theorem sixth_power_free_coprime_half_succ_two_step_dichotomy {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N)
    (hcop : Nat.Coprime ((q + 1) / 2) (componentIndex N q)) :
    ∃ h u W r₀ e₀ U₀ c₀_u V₀ s : ℕ,
      W = sigma 1 (u ^ 2) / q ∧
      59 ≤ h ∧ 6961 ≤ q ∧ 71 ≤ U₀ ∧ 5113 ≤ W ∧
      ¬ IsPrimePow u ∧
      N = q * (h * u) ^ 2 ∧ componentIndex N q = u ^ 2 ∧
      u = r₀ ^ e₀ * U₀ ∧ W = c₀_u * sigma 1 (U₀ ^ 2) ∧ U₀ ^ 2 = c₀_u * V₀ ∧
      r₀ ^ (2 * e₀) * V₀ = sigma 1 (U₀ ^ 2) * sigma 1 (h ^ 2) ∧
      Nat.Coprime (r₀ ^ (2 * e₀)) V₀ ∧
      r₀.Prime ∧ s.Prime ∧ s ∈ U₀.primeFactors ∧ s ≠ r₀ ∧
      61 ≤ r₀ ∧ 61 ≤ s ∧
      e₀ ∈ ({1, 2} : Finset ℕ) ∧ U₀.factorization s ∈ ({1, 2} : Finset ℕ) ∧
      r₀ ∣ sigma 1 (s ^ (2 * U₀.factorization s)) ∧
      ((U₀.factorization s = 1 ∧
          s % 5 = 1 ∧ 71 ≤ s ∧
          r₀ ∣ s ^ 2 + s + 1 ∧ r₀ % 3 = 1 ∧
          e₀ = 2 ∧ r₀ ∈ oneModThreeLargeSources N q ∧
          13845841 ≤ r₀ ^ (2 * e₀)) ∨
       (U₀.factorization s = 2 ∧
          s ∈ largeSources N q ∧
          r₀ ∣ s ^ 4 + s ^ 3 + s ^ 2 + s + 1 ∧ r₀ % 5 = 1 ∧
          3721 ≤ U₀ ∧ 13849563 ≤ W ∧
          1648097997 ≤ 2 * u ^ 2 - sigma 1 (u ^ 2))) := by
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hfac_q : N.factorization q = 1 :=
    sixth_power_free_euler_exponent_one ho hN hq he hfree
  obtain ⟨h₁, u₁, W₁, hW₁_def, hh₁_odd, hu₁_odd, _, hh₁_ge59, hq_ge6961, _,
    hcop_h₁u₁, _, hform_h₁u₁, hci₁_eq, hu₁2_eq, _, h119_le, _, _⟩ :=
    sixth_power_free_coprime_half_succ_w_ge_61 ho hN hq hq4 he hev hfree hcop
  have hqm : ¬ q ∣ h₁ * u₁ := by
    intro hqd
    have hq3_dvd : q ^ 3 ∣ N := by
      rw [hform_h₁u₁]
      have hq2_dvd : q ^ 2 ∣ (h₁ * u₁) ^ 2 := pow_dvd_pow_of_dvd hqd 2
      have hmul : q * q ^ 2 ∣ q * (h₁ * u₁) ^ 2 := Nat.mul_dvd_mul_left q hq2_dvd
      rwa [show q * q ^ 2 = q ^ 3 by ring] at hmul
    have hle : 3 ≤ N.factorization q :=
      (hq_prime.pow_dvd_iff_le_factorization hN.2.ne').mp hq3_dvd
    omega
  obtain ⟨h₂, u₂, W₂, _, _, _, _, _, hW₂_def, _, _, _, _, _, _, _, hW_ge5113, _, _, _,
    _, hci₂_eq, _, _, _, _, _, _⟩ :=
    sixth_power_free_coprime_half_succ_w_ge_5113 ho hN hq hq4 he hev hfree hcop
  have hu₂_eq : u₂ = u₁ :=
    Nat.pow_left_injective (by decide : 2 ≠ 0) (hci₂_eq.symm.trans hci₁_eq)
  have hW₂_eq : W₂ = W₁ := by rw [hW₂_def, hW₁_def, hu₂_eq]
  rw [hW₂_eq] at hW_ge5113
  obtain ⟨h, u, W, r₀, e₀, U₀, c₀_u, V₀, hW_def, hm_eq, _, hci_sq_eq,
    hr₀_prime, hr₀_u, he₀_pos, he₀_eq_u, hU₀_def, hu_split, hsig_r₀_eq, hW_eq,
    hU₀2_eq, hbal_V₀, hrev⟩ :=
    linear_euler_coprime_half_succ_reverse_sigma_edge ho hN hq_prime hqm hform_h₁u₁ hcop
  have hu_eq : u = u₁ :=
    Nat.pow_left_injective (by decide : 2 ≠ 0) (hci_sq_eq.symm.trans hci₁_eq)
  have hh_eq : h = h₁ := by
    have hmul : h * u₁ = h₁ * u₁ := by
      calc
        h * u₁ = h * u := by rw [hu_eq]
        _ = h₁ * u₁ := hm_eq.symm
    exact Nat.mul_right_cancel hu₁_odd.pos hmul
  have hW_eq_W₁ : W = W₁ := by rw [hW_def, hW₁_def, hu_eq]
  subst hh_eq hu_eq hW_eq_W₁
  have hW_ge13 : 13 ≤ W := by omega
  obtain ⟨_, _, s, hs_U₀, hs_ne_r₀, hr₀_dvd_sigs⟩ := hrev hW_ge13
  have hh_ne0 : h ≠ 0 := hh₁_odd.pos.ne'
  have hu_ne0 : u ≠ 0 := hu₁_odd.pos.ne'
  have hU₀_odd : Odd U₀ := hu₁_odd.of_dvd_nat ⟨r₀ ^ e₀, by rw [mul_comm, ← hu_split]⟩
  have hU₀_ne0 : U₀ ≠ 0 := hU₀_odd.pos.ne'
  have hs_prime : s.Prime := Nat.prime_of_mem_primeFactors hs_U₀
  have hcop_pow_U₀ : Nat.Coprime (r₀ ^ e₀) U₀ := by
    rw [hU₀_def]
    exact (Nat.coprime_ordCompl hr₀_prime hu_ne0).pow_left e₀
  have hcop_r₀2_V₀ : Nat.Coprime (r₀ ^ (2 * e₀)) V₀ := by
    have hpow_eq : r₀ ^ (2 * e₀) = (r₀ ^ e₀) ^ 2 := by rw [← pow_mul, mul_comm]
    have hcop_U₀2 : Nat.Coprime (r₀ ^ (2 * e₀)) (U₀ ^ 2) := by
      rw [hpow_eq]
      exact (hcop_pow_U₀.pow_left 2).pow_right 2
    exact hcop_U₀2.coprime_dvd_right ⟨c₀_u, by rw [hU₀2_eq, mul_comm]⟩
  have hs_u : s ∈ u.primeFactors := by
    have hs_dvd_u : s ∣ u :=
      (Nat.dvd_of_mem_primeFactors hs_U₀).trans ⟨r₀ ^ e₀, by rw [hu_split, mul_comm]⟩
    exact Nat.mem_primeFactors.mpr ⟨hs_prime, hs_dvd_u, hu_ne0⟩
  have hnpp_u : ¬ IsPrimePow u := by
    intro hpp
    have hcard1 : u.primeFactors.card = 1 := isPrimePow_iff_card_primeFactors_eq_one.mp hpp
    have hsub : ({r₀, s} : Finset ℕ) ⊆ u.primeFactors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hr₀_u
      · exact hs_u
    have hcard_pair : ({r₀, s} : Finset ℕ).card = 2 :=
      Finset.card_pair hs_ne_r₀.symm
    have hle := Finset.card_le_card hsub
    omega
  obtain ⟨hr₀_mod, hr₀_ge61⟩ :=
    prime_u_mod_and_ge_61 ho hN hq hq4 he hev hfree hu_ne0 hform_h₁u₁ hci_sq_eq hr₀_u
  obtain ⟨hs_mod, hs_ge61⟩ :=
    prime_u_mod_and_ge_61 ho hN hq hq4 he hev hfree hu_ne0 hform_h₁u₁ hci_sq_eq hs_u
  have hnot3_N : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  have hr₀_dvd_u : r₀ ∣ u := Nat.dvd_of_mem_primeFactors hr₀_u
  have hs_dvd_U₀ : s ∣ U₀ := Nat.dvd_of_mem_primeFactors hs_U₀
  have hs_dvd_u : s ∣ u := hs_dvd_U₀.trans ⟨r₀ ^ e₀, by rw [hu_split, mul_comm]⟩
  have hr₀_neq : r₀ ≠ q := by
    intro heq
    exact hqm (heq ▸ hr₀_dvd_u.trans (dvd_mul_left u h))
  have hs_neq : s ≠ q := by
    intro heq
    exact hqm (heq ▸ hs_dvd_u.trans (dvd_mul_left u h))
  have hr₀_ndvd_q : ¬ r₀ ∣ q := fun hd =>
    hr₀_neq (((Nat.dvd_prime hq_prime).mp hd).resolve_left hr₀_prime.ne_one)
  have hs_ndvd_q : ¬ s ∣ q := fun hd =>
    hs_neq (((Nat.dvd_prime hq_prime).mp hd).resolve_left hs_prime.ne_one)
  have hr₀_ndvd_h : ¬ r₀ ∣ h := fun hd =>
    hr₀_prime.not_dvd_one (hcop_h₁u₁ ▸ Nat.dvd_gcd hd hr₀_dvd_u)
  have hs_ndvd_h : ¬ s ∣ h := fun hd =>
    hs_prime.not_dvd_one (hcop_h₁u₁ ▸ Nat.dvd_gcd hd hs_dvd_u)
  have hm_ne0 : h * u ≠ 0 := mul_ne_zero hh_ne0 hu_ne0
  have hm2_ne0 : (h * u) ^ 2 ≠ 0 := pow_ne_zero 2 hm_ne0
  have hfac_N_r₀ : N.factorization r₀ = 2 * e₀ := by
    rw [hform_h₁u₁, Nat.factorization_mul hq_prime.ne_zero hm2_ne0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hr₀_ndvd_q, zero_add,
      Nat.factorization_pow (h * u) 2, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_mul hh_ne0 hu_ne0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hr₀_ndvd_h, zero_add, ← he₀_eq_u]
  have hs_ndvd_r₀pow : ¬ s ∣ r₀ ^ e₀ := fun hd =>
    hs_ne_r₀ (((Nat.dvd_prime hr₀_prime).mp (hs_prime.dvd_of_dvd_pow hd)).resolve_left
      hs_prime.ne_one)
  have hfac_N_s : N.factorization s = 2 * U₀.factorization s := by
    rw [hform_h₁u₁, Nat.factorization_mul hq_prime.ne_zero hm2_ne0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hs_ndvd_q, zero_add,
      Nat.factorization_pow (h * u) 2, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_mul hh_ne0 hu_ne0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hs_ndvd_h, zero_add,
      hu_split, Nat.factorization_mul (pow_ne_zero e₀ hr₀_prime.ne_zero) hU₀_ne0,
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hs_ndvd_r₀pow, zero_add]
  have hr₀_fac_lt6 : N.factorization r₀ < 6 := by
    by_contra! hle
    exact hfree r₀ hr₀_prime ((hr₀_prime.pow_dvd_iff_le_factorization hN.2.ne').2 hle)
  have hs_fac_lt6 : N.factorization s < 6 := by
    by_contra! hle
    exact hfree s hs_prime ((hs_prime.pow_dvd_iff_le_factorization hN.2.ne').2 hle)
  have he₀_mem : e₀ ∈ ({1, 2} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hk_s_pos : 0 < U₀.factorization s :=
    (hs_prime.dvd_iff_one_le_factorization hU₀_ne0).mp hs_dvd_U₀
  have hk_s_mem : U₀.factorization s ∈ ({1, 2} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hr₀_dvd_N : r₀ ∣ N := by
    rw [hform_h₁u₁]
    exact (hr₀_dvd_u.trans (dvd_mul_left u h)).trans
      ((dvd_pow_self (h * u) (by decide : 2 ≠ 0)).trans (dvd_mul_left _ q))
  have hs_dvd_N : s ∣ N := by
    rw [hform_h₁u₁]
    exact (hs_dvd_u.trans (dvd_mul_left u h)).trans
      ((dvd_pow_self (h * u) (by decide : 2 ≠ 0)).trans (dvd_mul_left _ q))
  have hc₀_ge1 : 1 ≤ c₀_u := by
    have hsig_pos : 0 < sigma 1 (r₀ ^ (2 * e₀)) :=
      sigma_pos 1 (r₀ ^ (2 * e₀)) (pow_ne_zero _ hr₀_prime.ne_zero)
    by_contra! hc0
    have hcz : c₀_u = 0 := Nat.lt_one_iff.mp hc0
    rw [hcz, mul_zero] at hsig_r₀_eq
    omega
  have hsig_s_dvd_N : sigma 1 (s ^ (2 * U₀.factorization s)) ∣ N := by
    set k_s := U₀.factorization s
    have hU₀2_split : U₀ ^ 2 = s ^ (2 * k_s) * (ordCompl[s] U₀) ^ 2 := by
      have h1 : U₀ = s ^ k_s * ordCompl[s] U₀ := (Nat.ordProj_mul_ordCompl_eq_self U₀ s).symm
      calc
        U₀ ^ 2 = (s ^ k_s * ordCompl[s] U₀) ^ 2 := by rw [← h1]
        _ = (s ^ k_s) ^ 2 * (ordCompl[s] U₀) ^ 2 := by rw [mul_pow]
        _ = s ^ (2 * k_s) * (ordCompl[s] U₀) ^ 2 := by rw [← pow_mul, mul_comm k_s 2]
    have hcop_s_compl : Nat.Coprime (s ^ (2 * k_s)) ((ordCompl[s] U₀) ^ 2) :=
      ((Nat.coprime_ordCompl hs_prime hU₀_ne0).pow_left (2 * k_s)).pow_right 2
    have hsig_s_dvd : sigma 1 (s ^ (2 * k_s)) ∣ sigma 1 (U₀ ^ 2) := by
      rw [hU₀2_split, isMultiplicative_sigma.map_mul_of_coprime hcop_s_compl]
      exact dvd_mul_right _ _
    have hsigU₀_dvd_W : sigma 1 (U₀ ^ 2) ∣ W := ⟨c₀_u, by rw [hW_eq, mul_comm]⟩
    have hW_dvd_u2 : W ∣ u ^ 2 := ⟨sigma 1 (h ^ 2), hu₁2_eq⟩
    have hu2_dvd_N : u ^ 2 ∣ N := by
      rw [hform_h₁u₁, mul_pow]
      exact (dvd_mul_left (u ^ 2) (h ^ 2)).trans (dvd_mul_left _ q)
    exact ((hsig_s_dvd.trans hsigU₀_dvd_W).trans hW_dvd_u2).trans hu2_dvd_N
  have hnot3_sigs : ¬ 3 ∣ sigma 1 (s ^ (2 * U₀.factorization s)) := fun h3 =>
    hnot3_N (h3.trans hsig_s_dvd_N)
  have hqc₀_dvd_N : q * c₀_u ∣ N := by
    have hc₀_dvd_U₀2 : c₀_u ∣ U₀ ^ 2 := ⟨V₀, hU₀2_eq⟩
    have hU₀_dvd_u : U₀ ∣ u := ⟨r₀ ^ e₀, by rw [hu_split, mul_comm]⟩
    have hc₀_dvd_hu2 : c₀_u ∣ (h * u) ^ 2 :=
      hc₀_dvd_U₀2.trans (pow_dvd_pow_of_dvd (hU₀_dvd_u.trans (dvd_mul_left u h)) 2)
    rw [hform_h₁u₁]
    exact Nat.mul_dvd_mul_left q hc₀_dvd_hu2
  have hnot3_qc₀ : ¬ 3 ∣ sigma 1 (r₀ ^ (2 * e₀)) := fun h3 =>
    hnot3_N (h3.trans (hsig_r₀_eq ▸ hqc₀_dvd_N))
  have : Fact r₀.Prime := ⟨hr₀_prime⟩
  have hcase :
      (U₀.factorization s = 1 ∧
        s % 5 = 1 ∧ 71 ≤ s ∧
        r₀ ∣ s ^ 2 + s + 1 ∧ r₀ % 3 = 1 ∧
        e₀ = 2 ∧ r₀ ∈ oneModThreeLargeSources N q ∧
        13845841 ≤ r₀ ^ (2 * e₀)) ∨
      (U₀.factorization s = 2 ∧
        s ∈ largeSources N q ∧
        r₀ ∣ s ^ 4 + s ^ 3 + s ^ 2 + s + 1 ∧ r₀ % 5 = 1 ∧
        3721 ≤ U₀ ∧ 13849563 ≤ W ∧
        1648097997 ≤ 2 * u ^ 2 - sigma 1 (u ^ 2)) := by
    rcases (show U₀.factorization s = 1 ∨ U₀.factorization s = 2 by omega) with hk1 | hk2
    · left
      have hsig_eq : sigma 1 (s ^ (2 * U₀.factorization s)) = s ^ 2 + s + 1 := by
        rw [hk1, mul_one, sigma_one_apply_prime_pow hs_prime]
        simp [Finset.sum_range_succ]
        ring
      have hr₀_dvd_s2 : r₀ ∣ s ^ 2 + s + 1 := hsig_eq ▸ hr₀_dvd_sigs
      have hs_not3 : s % 3 ≠ 1 := by
        intro hs3
        obtain ⟨t, ht⟩ : ∃ t, s = 3 * t + 1 := ⟨s / 3, by omega⟩
        have h3_dvd : 3 ∣ sigma 1 (s ^ (2 * U₀.factorization s)) := by
          rw [hsig_eq, ht]
          exact ⟨3 * t ^ 2 + 3 * t + 1, by ring⟩
        exact hnot3_sigs h3_dvd
      have hs_mod5 : s % 5 = 1 := hs_mod.resolve_right hs_not3
      have hs_ge71 : 71 ≤ s := by
        by_contra! hlt
        have hs_cases : s = 61 ∨ s = 62 ∨ s = 63 ∨ s = 64 ∨ s = 65 ∨
            s = 66 ∨ s = 67 ∨ s = 68 ∨ s = 69 ∨ s = 70 := by omega
        rcases hs_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact hs_not3 (by decide)
        · exact (by decide : ¬ Nat.Prime 62) hs_prime
        · exact (by decide : ¬ Nat.Prime 63) hs_prime
        · exact (by decide : ¬ Nat.Prime 64) hs_prime
        · exact (by decide : ¬ Nat.Prime 65) hs_prime
        · exact (by decide : ¬ Nat.Prime 66) hs_prime
        · exact hs_not3 (by decide)
        · exact (by decide : ¬ Nat.Prime 68) hs_prime
        · exact (by decide : ¬ Nat.Prime 69) hs_prime
        · exact (by decide : ¬ Nat.Prime 70) hs_prime
      have hz_sum : (s : ZMod r₀) ^ 2 + (s : ZMod r₀) + 1 = 0 := by
        have hz := (ZMod.natCast_eq_zero_iff (s ^ 2 + s + 1) r₀).mpr hr₀_dvd_s2
        push_cast at hz
        exact hz
      have hz_pow3 : (s : ZMod r₀) ^ 3 = 1 := by
        have hsub : (s : ZMod r₀) ^ 3 - 1 = 0 := by
          calc
            (s : ZMod r₀) ^ 3 - 1 = ((s : ZMod r₀) - 1) * ((s : ZMod r₀) ^ 2 + (s : ZMod r₀) + 1) := by
              ring
            _ = ((s : ZMod r₀) - 1) * 0 := by rw [hz_sum]
            _ = 0 := mul_zero _
        exact sub_eq_zero.mp hsub
      have hz_ne0 : (s : ZMod r₀) ≠ 0 := by
        intro h0
        rw [h0, zero_pow (by decide : 3 ≠ 0)] at hz_pow3
        exact zero_ne_one hz_pow3
      have hz_ne1 : (s : ZMod r₀) ≠ 1 := by
        intro h1
        rw [h1] at hz_sum
        have h3_zero : ((3 : ℕ) : ZMod r₀) = 0 := by
          push_cast
          linear_combination hz_sum
        have hr₀_dvd_3 : r₀ ∣ 3 := (ZMod.natCast_eq_zero_iff 3 r₀).mp h3_zero
        have hr₀_le_3 : r₀ ≤ 3 := Nat.le_of_dvd (by decide) hr₀_dvd_3
        omega
      have : Fact (Nat.Prime 3) := ⟨by decide⟩
      have hord3 : orderOf (s : ZMod r₀) = 3 := orderOf_eq_prime hz_pow3 hz_ne1
      have h3_dvd_sub : 3 ∣ r₀ - 1 := by
        rw [← hord3]
        exact ZMod.orderOf_dvd_card_sub_one hz_ne0
      have hr₀_mod3 : r₀ % 3 = 1 := by omega
      have he₀_eq2 : e₀ = 2 := by
        by_contra he₀_ne2
        have he₀_eq1 : e₀ = 1 := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at he₀_mem
          omega
        have hsig_r₀_eq_poly : sigma 1 (r₀ ^ (2 * e₀)) = r₀ ^ 2 + r₀ + 1 := by
          rw [he₀_eq1, mul_one, sigma_one_apply_prime_pow hr₀_prime]
          simp [Finset.sum_range_succ]
          ring
        obtain ⟨t, ht⟩ : ∃ t, r₀ = 3 * t + 1 := ⟨r₀ / 3, by omega⟩
        have h3_dvd_r₀ : 3 ∣ sigma 1 (r₀ ^ (2 * e₀)) := by
          rw [hsig_r₀_eq_poly, ht]
          exact ⟨3 * t ^ 2 + 3 * t + 1, by ring⟩
        exact hnot3_qc₀ h3_dvd_r₀
      have hr₀_N : r₀ ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hr₀_prime, hr₀_dvd_N, hN.2.ne'⟩
      have hr₀_large : r₀ ∈ largeSources N q :=
        Finset.mem_filter.mpr ⟨hr₀_N, by omega, hr₀_neq, by omega⟩
      have hr₀_oneMod3 : r₀ ∈ oneModThreeLargeSources N q :=
        Finset.mem_filter.mpr ⟨hr₀_large, hr₀_mod3⟩
      have hr₀_pow_ge : 13845841 ≤ r₀ ^ (2 * e₀) := by
        have h61_pow4 : (13845841 : ℕ) = 61 ^ 4 := by norm_num
        have hr₀_pow4 : 61 ^ 4 ≤ r₀ ^ 4 := Nat.pow_le_pow_left hr₀_ge61 4
        rw [he₀_eq2, show 2 * 2 = 4 by norm_num]
        omega
      exact ⟨hk1, hs_mod5, hs_ge71, hr₀_dvd_s2, hr₀_mod3, he₀_eq2, hr₀_oneMod3, hr₀_pow_ge⟩
    · right
      have hs_N : s ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hs_prime, hs_dvd_N, hN.2.ne'⟩
      have hs_large : s ∈ largeSources N q :=
        Finset.mem_filter.mpr ⟨hs_N, by omega, hs_neq, by omega⟩
      have hsig_eq : sigma 1 (s ^ (2 * U₀.factorization s)) = s ^ 4 + s ^ 3 + s ^ 2 + s + 1 := by
        rw [hk2, show 2 * 2 = 4 by norm_num, sigma_one_apply_prime_pow hs_prime]
        simp [Finset.sum_range_succ]
        ring
      have hr₀_dvd_s4 : r₀ ∣ s ^ 4 + s ^ 3 + s ^ 2 + s + 1 := hsig_eq ▸ hr₀_dvd_sigs
      have hz_sum : (s : ZMod r₀) ^ 4 + (s : ZMod r₀) ^ 3 + (s : ZMod r₀) ^ 2 + (s : ZMod r₀) + 1 = 0 := by
        have hz := (ZMod.natCast_eq_zero_iff (s ^ 4 + s ^ 3 + s ^ 2 + s + 1) r₀).mpr hr₀_dvd_s4
        push_cast at hz
        exact hz
      have hz_pow5 : (s : ZMod r₀) ^ 5 = 1 := by
        have hsub : (s : ZMod r₀) ^ 5 - 1 = 0 := by
          calc
            (s : ZMod r₀) ^ 5 - 1 =
                ((s : ZMod r₀) - 1) *
                  ((s : ZMod r₀) ^ 4 + (s : ZMod r₀) ^ 3 + (s : ZMod r₀) ^ 2 + (s : ZMod r₀) + 1) := by
              ring
            _ = ((s : ZMod r₀) - 1) * 0 := by rw [hz_sum]
            _ = 0 := mul_zero _
        exact sub_eq_zero.mp hsub
      have hz_ne0 : (s : ZMod r₀) ≠ 0 := by
        intro h0
        rw [h0, zero_pow (by decide : 5 ≠ 0)] at hz_pow5
        exact zero_ne_one hz_pow5
      have hz_ne1 : (s : ZMod r₀) ≠ 1 := by
        intro h1
        rw [h1] at hz_sum
        have h5_zero : ((5 : ℕ) : ZMod r₀) = 0 := by
          push_cast
          linear_combination hz_sum
        have hr₀_dvd_5 : r₀ ∣ 5 := (ZMod.natCast_eq_zero_iff 5 r₀).mp h5_zero
        have hr₀_le_5 : r₀ ≤ 5 := Nat.le_of_dvd (by decide) hr₀_dvd_5
        omega
      have : Fact (Nat.Prime 5) := ⟨by decide⟩
      have hord5 : orderOf (s : ZMod r₀) = 5 := orderOf_eq_prime hz_pow5 hz_ne1
      have h5_dvd_sub : 5 ∣ r₀ - 1 := by
        rw [← hord5]
        exact ZMod.orderOf_dvd_card_sub_one hz_ne0
      have hr₀_mod5 : r₀ % 5 = 1 := by omega
      have hU₀_ge3721 : 3721 ≤ U₀ := by
        have hs2_dvd_U₀ : s ^ 2 ∣ U₀ := by
          rw [← hk2]
          exact Nat.ordProj_dvd U₀ s
        have hs2_le_U₀ : s ^ 2 ≤ U₀ := Nat.le_of_dvd hU₀_odd.pos hs2_dvd_U₀
        have h61_sq : (3721 : ℕ) = 61 ^ 2 := by norm_num
        have hs_sq_ge : 61 ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left hs_ge61 2
        omega
      have hW_ge_eight : 13849563 ≤ W := by
        have hU₀_gt1 : 1 < U₀ := by omega
        have hsig_ge : U₀ ^ 2 + U₀ + 1 ≤ sigma 1 (U₀ ^ 2) :=
          sq_add_self_add_one_le_sigma_sq_of_gt_one hU₀_gt1
        have hsig_le_W : sigma 1 (U₀ ^ 2) ≤ W := by
          rw [hW_eq]
          exact Nat.le_mul_of_pos_left _ hc₀_ge1
        have hsq_ge : 3721 ^ 2 ≤ U₀ ^ 2 := Nat.pow_le_pow_left hU₀_ge3721 2
        omega
      have hdiff_ge : 1648097997 ≤ 2 * u ^ 2 - sigma 1 (u ^ 2) := by omega
      exact ⟨hk2, hs_large, hr₀_dvd_s4, hr₀_mod5, hU₀_ge3721, hW_ge_eight, hdiff_ge⟩
  have hU₀_ge71 : 71 ≤ U₀ := by
    rcases hcase with ⟨_, _, hs_ge71, _, _, _, _, _⟩ | ⟨_, _, _, _, hU₀_ge3721, _, _⟩
    · exact hs_ge71.trans (Nat.le_of_dvd hU₀_odd.pos hs_dvd_U₀)
    · omega
  exact ⟨h, u, W, r₀, e₀, U₀, c₀_u, V₀, s, hW_def, hh₁_ge59, hq_ge6961, hU₀_ge71, hW_ge5113,
    hnpp_u, hform_h₁u₁, hci_sq_eq, hu_split, hW_eq, hU₀2_eq, hbal_V₀, hcop_r₀2_V₀,
    hr₀_prime, hs_prime, hs_U₀, hs_ne_r₀, hr₀_ge61, hs_ge61, he₀_mem, hk_s_mem,
    hr₀_dvd_sigs, hcase⟩

/-- **2. Source-Size or Eight-Digit `W` Floor on Sixth-Power-Free Coprime Half-Succ**:
Direct corollary of `sixth_power_free_coprime_half_succ_two_step_dichotomy` isolating either
`13845841 ≤ r₀ ^ (2 * e₀)` or the eight-digit floors `3721 ≤ U₀ ∧ 13849563 ≤ W ∧
1648097997 ≤ 2 * u ^ 2 - σ(u ^ 2)`. -/
theorem sixth_power_free_coprime_half_succ_source_or_w_eight_digit_floor {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N)
    (hcop : Nat.Coprime ((q + 1) / 2) (componentIndex N q)) :
    ∃ h u W r₀ e₀ U₀ : ℕ,
      W = sigma 1 (u ^ 2) / q ∧
      N = q * (h * u) ^ 2 ∧ componentIndex N q = u ^ 2 ∧
      u = r₀ ^ e₀ * U₀ ∧
      (13845841 ≤ r₀ ^ (2 * e₀) ∨
        (3721 ≤ U₀ ∧ 13849563 ≤ W ∧ 1648097997 ≤ 2 * u ^ 2 - sigma 1 (u ^ 2))) := by
  obtain ⟨h, u, W, r₀, e₀, U₀, _, _, _, hW_def, _, _, _, _, _, hform, hci, hu_split,
    _, _, _, _, _, _, _, _, _, _, _, _, _, hcase⟩ :=
    sixth_power_free_coprime_half_succ_two_step_dichotomy ho hN hq hq4 he hev hfree hcop
  refine ⟨h, u, W, r₀, e₀, U₀, hW_def, hform, hci, hu_split, ?_⟩
  rcases hcase with ⟨_, _, _, _, _, _, _, hr₀_ge⟩ | ⟨_, _, _, _, hU₀_ge, hW_ge, hdiff_ge⟩
  · exact Or.inl hr₀_ge
  · exact Or.inr ⟨hU₀_ge, hW_ge, hdiff_ge⟩

end OddPerfect
