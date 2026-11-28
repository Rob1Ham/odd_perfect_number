module

public import OddPerfect.LinearEulerCoprimeUniqueSourceSplit
public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Data.Nat.Factorization.PrimePow
import OddPerfect.TothSplitExistence
import OddPerfect.SixthPowerFreeEuler
import OddPerfect.OddValuationCycleObstruction
import OddPerfect.GlobalWave5Obstruction
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Linear Euler Coprime Half-Successor `V₀` Coprimality, Prime-Power Equivalence, and Reverse `σ`-Edge

Formalizes the coprimality, prime-power, and reverse `σ`-edge obstructions on the coprime
half-successor branch `Nat.Coprime ((q + 1) / 2) (componentIndex N q)` of a linear Euler
odd perfect number `N = q * m ^ 2`:

1. `linear_euler_coprime_half_succ_v0_coprime_and_prime_pow_equiv`:
   Establishes `Nat.Coprime (r₀ ^ (2 * e₀)) V₀`, `IsPrimePow u ↔ W = 1`,
   `¬ IsPrimePow u ↔ 13 ≤ W`, `IsSquare c₀_u ↔ IsSquare V₀`, and `c₀_u = 1 ↔ V₀ = U₀ ^ 2`.
2. `linear_euler_coprime_half_succ_reverse_sigma_edge`:
   When `13 ≤ W`, shows `¬ (r₀ ^ (2 * e₀) ∣ σ(h ^ 2))`, `r₀ ∣ σ(U₀ ^ 2)`, and produces a
   prime factor `s ∈ U₀.primeFactors` (`s ≠ r₀`) with `r₀ ∣ σ(s ^ (2 * v_s(U₀)))`.
3. `sixth_power_free_coprime_half_succ_reverse_edge_r0_ge_61`:
   Specializes to sixth-power-free odd perfect numbers, upgrading the reverse `σ`-edge to
   `61 ≤ r₀`, `5041 ≤ r₀ ^ (2 * e₀)`, and `61 ≤ s`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma align_coprime_half_succ_u_W
    {N q u W u' W' : ℕ}
    (hci : componentIndex N q = u ^ 2) (hW_def : W = sigma 1 (u ^ 2) / q)
    (hci' : componentIndex N q = u' ^ 2) (hW_def' : W' = sigma 1 (u' ^ 2) / q) :
    u' = u ∧ W' = W := by
  have hu_eq : u' = u := Nat.pow_left_injective (by decide : 2 ≠ 0) (hci'.symm.trans hci)
  have hW_eq : W' = W := by rw [hW_def', hW_def, hu_eq]
  exact ⟨hu_eq, hW_eq⟩

private lemma isSquare_mul_right_of_eq_sq {a b U₀ : ℕ} (ha : 1 ≤ a)
    (h : U₀ ^ 2 = a * b) (hsq : IsSquare a) : IsSquare b := by
  obtain ⟨r, hr⟩ := hsq
  have hr_ne0 : r ≠ 0 := by
    intro hr0
    rw [hr0, mul_zero] at hr
    omega
  have hr2_pos : 0 < r ^ 2 := pow_pos (Nat.pos_of_ne_zero hr_ne0) 2
  have hr2_dvd : r ^ 2 ∣ U₀ ^ 2 := ⟨b, by rw [h, hr, pow_two]⟩
  have hr_dvd : r ∣ U₀ := (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp hr2_dvd
  obtain ⟨k, hk⟩ := hr_dvd
  have hk2_eq : r ^ 2 * k ^ 2 = r ^ 2 * b := by
    calc
      r ^ 2 * k ^ 2 = (r * k) ^ 2 := by ring
      _ = U₀ ^ 2 := by rw [← hk]
      _ = a * b := h
      _ = r ^ 2 * b := by rw [hr, pow_two]
  have hk2_eq_b : k ^ 2 = b := Nat.mul_left_cancel hr2_pos hk2_eq
  exact ⟨k, by rw [← hk2_eq_b, pow_two]⟩

private lemma reverse_sigma_edge_of_factorization
    {h u W r₀ e₀ U₀ c₀_u V₀ : ℕ}
    (hh0 : h ≠ 0) (hU₀_ge1 : 1 ≤ U₀) (hc₀_ge1 : 1 ≤ c₀_u)
    (hr₀_prime : r₀.Prime) (he₀_pos : 0 < e₀)
    (hu_split : u = r₀ ^ e₀ * U₀) (hcop_pow_U₀ : Nat.Coprime (r₀ ^ e₀) U₀)
    (hU₀2_eq : U₀ ^ 2 = c₀_u * V₀)
    (hbal_V₀ : r₀ ^ (2 * e₀) * V₀ = sigma 1 (U₀ ^ 2) * sigma 1 (h ^ 2))
    (hW_iff_prime_pow : IsPrimePow u ↔ W = 1)
    (hW13 : 13 ≤ W) :
    ¬ (r₀ ^ (2 * e₀) ∣ sigma 1 (h ^ 2)) ∧
    r₀ ∣ sigma 1 (U₀ ^ 2) ∧
    ∃ s ∈ U₀.primeFactors, s ≠ r₀ ∧ r₀ ∣ sigma 1 (s ^ (2 * U₀.factorization s)) := by
  have hU₀_ne1 : U₀ ≠ 1 := by
    intro hU1
    have hu_pow : u = r₀ ^ e₀ := by rw [hu_split, hU1, mul_one]
    have hu_pp : IsPrimePow u := by
      rw [hu_pow]
      exact hr₀_prime.isPrimePow.pow he₀_pos.ne'
    have hW1 : W = 1 := hW_iff_prime_pow.mp hu_pp
    omega
  have hU₀2_gt1 : 1 < U₀ ^ 2 := by
    have hU₀_gt1 : 1 < U₀ := Nat.lt_of_le_of_ne hU₀_ge1 (Ne.symm hU₀_ne1)
    nlinarith only [hU₀_gt1]
  have hU₀2_lt_sig : U₀ ^ 2 < sigma 1 (U₀ ^ 2) := self_lt_sigma_of_one_lt hU₀2_gt1
  have hr₀_pow_pos : 0 < r₀ ^ (2 * e₀) := pow_pos hr₀_prime.pos (2 * e₀)
  have hmul_eq : (c₀_u * sigma 1 (h ^ 2)) * sigma 1 (U₀ ^ 2) = r₀ ^ (2 * e₀) * U₀ ^ 2 := by
    calc
      (c₀_u * sigma 1 (h ^ 2)) * sigma 1 (U₀ ^ 2)
          = c₀_u * (sigma 1 (U₀ ^ 2) * sigma 1 (h ^ 2)) := by ring
      _ = c₀_u * (r₀ ^ (2 * e₀) * V₀) := by rw [← hbal_V₀]
      _ = r₀ ^ (2 * e₀) * (c₀_u * V₀) := by ring
      _ = r₀ ^ (2 * e₀) * U₀ ^ 2 := by rw [← hU₀2_eq]
  have hmul_lt : (c₀_u * sigma 1 (h ^ 2)) * sigma 1 (U₀ ^ 2) <
      r₀ ^ (2 * e₀) * sigma 1 (U₀ ^ 2) := by
    rw [hmul_eq]
    exact Nat.mul_lt_mul_of_pos_left hU₀2_lt_sig hr₀_pow_pos
  have hc₀_sig_lt : c₀_u * sigma 1 (h ^ 2) < r₀ ^ (2 * e₀) :=
    Nat.lt_of_mul_lt_mul_right hmul_lt
  have hsig_h_le : sigma 1 (h ^ 2) ≤ c₀_u * sigma 1 (h ^ 2) :=
    Nat.le_mul_of_pos_left _ hc₀_ge1
  have hsig_h_lt : sigma 1 (h ^ 2) < r₀ ^ (2 * e₀) := lt_of_le_of_lt hsig_h_le hc₀_sig_lt
  have hsig_h_pos : 0 < sigma 1 (h ^ 2) := sigma_pos 1 (h ^ 2) (pow_ne_zero 2 hh0)
  have hnot_dvd_h : ¬ (r₀ ^ (2 * e₀) ∣ sigma 1 (h ^ 2)) := by
    intro hdvd
    have hle : r₀ ^ (2 * e₀) ≤ sigma 1 (h ^ 2) := Nat.le_of_dvd hsig_h_pos hdvd
    omega
  have hr₀_dvd_sigU₀ : r₀ ∣ sigma 1 (U₀ ^ 2) := by
    by_contra hndvd
    have hcop_base : Nat.Coprime r₀ (sigma 1 (U₀ ^ 2)) := hr₀_prime.coprime_iff_not_dvd.mpr hndvd
    have hcop_pow : Nat.Coprime (r₀ ^ (2 * e₀)) (sigma 1 (U₀ ^ 2)) := hcop_base.pow_left (2 * e₀)
    have hdvd_mul : r₀ ^ (2 * e₀) ∣ sigma 1 (U₀ ^ 2) * sigma 1 (h ^ 2) :=
      ⟨V₀, hbal_V₀.symm⟩
    exact hnot_dvd_h (hcop_pow.dvd_of_dvd_mul_left hdvd_mul)
  have hU₀_ne0 : U₀ ≠ 0 := by omega
  have hU₀2_ne0 : U₀ ^ 2 ≠ 0 := pow_ne_zero 2 hU₀_ne0
  have hsig_prod :
      sigma 1 (U₀ ^ 2) = ∏ s ∈ (U₀ ^ 2).primeFactors, sigma 1 (s ^ (U₀ ^ 2).factorization s) := by
    rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization (sigma 1)
      isMultiplicative_sigma hU₀2_ne0]
    rfl
  have hr₀_dvd_prod :
      r₀ ∣ ∏ s ∈ (U₀ ^ 2).primeFactors, sigma 1 (s ^ (U₀ ^ 2).factorization s) :=
    hsig_prod ▸ hr₀_dvd_sigU₀
  obtain ⟨s, hs_mem, hs_dvd⟩ :=
    (hr₀_prime.prime.dvd_finsetProd_iff _).mp hr₀_dvd_prod
  rw [Nat.primeFactors_pow U₀ (by decide : 2 ≠ 0)] at hs_mem
  rw [Nat.factorization_pow U₀ 2, Finsupp.smul_apply, smul_eq_mul] at hs_dvd
  have hs_ne_r₀ : s ≠ r₀ := by
    rintro rfl
    have hr₀_dvd_U₀ : s ∣ U₀ := Nat.dvd_of_mem_primeFactors hs_mem
    have hr₀_dvd_pow : s ∣ s ^ e₀ := dvd_pow_self s he₀_pos.ne'
    exact hr₀_prime.not_dvd_one (hcop_pow_U₀ ▸ Nat.dvd_gcd hr₀_dvd_pow hr₀_dvd_U₀)
  exact ⟨hnot_dvd_h, hr₀_dvd_sigU₀, s, hs_mem, hs_ne_r₀, hs_dvd⟩

private lemma sixth_power_free_u_prime_ge_61
    {N q h u s : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N)
    (hu_ne0 : u ≠ 0) (hform_hu : N = q * (h * u) ^ 2) (hci_sq_eq : componentIndex N q = u ^ 2)
    (hs_u : s ∈ u.primeFactors) :
    (s % 5 = 1 ∨ s % 3 = 1) ∧ 61 ≤ s := by
  have hs_prime : s.Prime := Nat.prime_of_mem_primeFactors hs_u
  have hs_dvd_u : s ∣ u := Nat.dvd_of_mem_primeFactors hs_u
  have hs_dvd_u2 : s ∣ u ^ 2 := hs_dvd_u.trans (dvd_pow_self u (by decide : 2 ≠ 0))
  have hs_dvd_N : s ∣ N := by
    rw [hform_hu]
    exact (hs_dvd_u.trans (dvd_mul_left u h)).trans
      ((dvd_pow_self (h * u) (by decide : 2 ≠ 0)).trans (dvd_mul_left _ q))
  have hs_N : s ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hs_prime, hs_dvd_N, hN.2.ne'⟩
  have hs_ge53 : 53 ≤ s := sixth_power_free_min_prime_ge_53 ho hN hfree hs_N
  have hci_ne0 : componentIndex N q ≠ 0 := by
    rw [hci_sq_eq]
    exact pow_ne_zero 2 hu_ne0
  have hs_ci : s ∈ (componentIndex N q).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hs_prime, hci_sq_eq ▸ hs_dvd_u2, hci_ne0⟩
  have hs_mod : s % 5 = 1 ∨ s % 3 = 1 :=
    (sixth_power_free_euler_index_drop_and_support ho hN hq hq4 he hev hfree).2 s hs_ci
  have hs_ge61 : 61 ≤ s := by
    by_contra! hlt
    have hs_cases : s = 53 ∨ s = 54 ∨ s = 55 ∨ s = 56 ∨ s = 57 ∨ s = 58 ∨ s = 59 ∨ s = 60 := by
      omega
    rcases hs_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (by decide : ¬ (53 % 5 = 1 ∨ 53 % 3 = 1)) hs_mod
    · exact (by decide : ¬ Nat.Prime 54) hs_prime
    · exact (by decide : ¬ Nat.Prime 55) hs_prime
    · exact (by decide : ¬ Nat.Prime 56) hs_prime
    · exact (by decide : ¬ Nat.Prime 57) hs_prime
    · exact (by decide : ¬ Nat.Prime 58) hs_prime
    · exact (by decide : ¬ (59 % 5 = 1 ∨ 59 % 3 = 1)) hs_mod
    · exact (by decide : ¬ Nat.Prime 60) hs_prime
  exact ⟨hs_mod, hs_ge61⟩

/-- **1. `V₀` Coprimality & `IsPrimePow u ↔ W = 1` Equivalence**:
On the coprime half-successor branch `Nat.Coprime ((q + 1) / 2) (componentIndex N q)`,
establishes `Nat.Coprime (r₀ ^ (2 * e₀)) V₀`, `IsPrimePow u ↔ W = 1`, `¬ IsPrimePow u ↔ 13 ≤ W`,
`IsSquare c₀_u ↔ IsSquare V₀`, and `c₀_u = 1 ↔ V₀ = U₀ ^ 2`. -/
theorem linear_euler_coprime_half_succ_v0_coprime_and_prime_pow_equiv {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hcop : Nat.Coprime ((q + 1) / 2) (componentIndex N q)) :
    ∃ h u W r₀ e₀ U₀ c₀_u V₀ : ℕ,
      W = sigma 1 (u ^ 2) / q ∧
      m = h * u ∧ q = 2 * h ^ 2 - 1 ∧ componentIndex N q = u ^ 2 ∧
      r₀.Prime ∧ r₀ ∈ u.primeFactors ∧ 0 < e₀ ∧
      e₀ = u.factorization r₀ ∧ U₀ = ordCompl[r₀] u ∧ u = r₀ ^ e₀ * U₀ ∧
      Nat.Coprime (r₀ ^ e₀) U₀ ∧
      sigma 1 (r₀ ^ (2 * e₀)) = q * c₀_u ∧
      W = c₀_u * sigma 1 (U₀ ^ 2) ∧ U₀ ^ 2 = c₀_u * V₀ ∧
      r₀ ^ (2 * e₀) * V₀ = sigma 1 (U₀ ^ 2) * sigma 1 (h ^ 2) ∧
      Nat.Coprime (r₀ ^ (2 * e₀)) V₀ ∧
      (IsPrimePow u ↔ W = 1) ∧
      (¬ IsPrimePow u ↔ 13 ≤ W) ∧
      (IsSquare c₀_u ↔ IsSquare V₀) ∧
      (c₀_u = 1 ↔ V₀ = U₀ ^ 2) := by
  obtain ⟨h, u, W, r₀, e₀, U₀, c₀_u, V₀, hW_def, _, _, _, _,
    _, _, _, hU₀_ge1, hc₀_ge1, hV₀_ge1, _, _, hm_eq, hq_eq, hci_sq_eq,
    hr₀_prime, hr₀_u, _, he₀_pos, he₀_eq_u, _, hU₀_def, hu_split, hcop_pow_U₀,
    hsig_r₀_eq, _, _, hW_eq, _, hU₀2_eq, hbal_V₀⟩ :=
    linear_euler_coprime_half_succ_unique_source_w_factorization ho hN hq hqm hform hcop
  obtain ⟨_, u₁, W₁, hW₁_def, _, _, _, _, _, _, _, _, hci₁_eq, _, _,
    hW₁_iff_card1, _, _⟩ :=
    linear_euler_coprime_half_succ_w_one_iff_prime_pow_u ho hN hq hqm hform hcop
  obtain ⟨hu₁_eq, hW₁_eq⟩ :=
    align_coprime_half_succ_u_W hci_sq_eq hW_def hci₁_eq hW₁_def
  have hW_iff_card1 : W = 1 ↔ u.primeFactors.card = 1 := by
    simpa only [hu₁_eq, hW₁_eq] using hW₁_iff_card1
  obtain ⟨_, u₂, W₂, _, _, _, _, _, hW₂_def, _, _, hci₂_eq,
    _, _, _, _, _, _, _, _, _, hW₂_gap, _⟩ :=
    linear_euler_coprime_half_succ_w_one_or_ge_thirteen ho hN hq hqm hform hcop
  obtain ⟨_, hW₂_eq⟩ :=
    align_coprime_half_succ_u_W hci_sq_eq hW_def hci₂_eq hW₂_def
  have hW_gap : W = 1 ∨ 13 ≤ W := by
    simpa only [hW₂_eq] using hW₂_gap
  have hcop_r₀2_V₀ : Nat.Coprime (r₀ ^ (2 * e₀)) V₀ := by
    have hpow_eq : r₀ ^ (2 * e₀) = (r₀ ^ e₀) ^ 2 := by rw [← pow_mul, mul_comm]
    have hcop_U₀2 : Nat.Coprime (r₀ ^ (2 * e₀)) (U₀ ^ 2) := by
      rw [hpow_eq]
      exact (hcop_pow_U₀.pow_left 2).pow_right 2
    exact hcop_U₀2.coprime_dvd_right ⟨c₀_u, by rw [hU₀2_eq, mul_comm]⟩
  have hpp_iff : IsPrimePow u ↔ W = 1 :=
    (isPrimePow_iff_card_primeFactors_eq_one).trans hW_iff_card1.symm
  have hnpp_iff : ¬ IsPrimePow u ↔ 13 ≤ W := by
    rw [hpp_iff]
    omega
  have hsq_iff : IsSquare c₀_u ↔ IsSquare V₀ := by
    constructor
    · exact isSquare_mul_right_of_eq_sq hc₀_ge1 hU₀2_eq
    · exact isSquare_mul_right_of_eq_sq hV₀_ge1 (by rw [hU₀2_eq, mul_comm])
  have hone_iff : c₀_u = 1 ↔ V₀ = U₀ ^ 2 := by
    constructor
    · intro hc1
      rw [hU₀2_eq, hc1, one_mul]
    · intro hVU
      have hU₀2_pos : 0 < U₀ ^ 2 := pow_pos hU₀_ge1 2
      have hmul : 1 * U₀ ^ 2 = c₀_u * U₀ ^ 2 := by
        calc
          1 * U₀ ^ 2 = U₀ ^ 2 := one_mul _
          _ = c₀_u * V₀ := hU₀2_eq
          _ = c₀_u * U₀ ^ 2 := by rw [hVU]
      exact (Nat.mul_right_cancel hU₀2_pos hmul).symm
  exact ⟨h, u, W, r₀, e₀, U₀, c₀_u, V₀, hW_def, hm_eq, hq_eq, hci_sq_eq,
    hr₀_prime, hr₀_u, he₀_pos, he₀_eq_u, hU₀_def, hu_split, hcop_pow_U₀,
    hsig_r₀_eq, hW_eq, hU₀2_eq, hbal_V₀, hcop_r₀2_V₀, hpp_iff, hnpp_iff, hsq_iff, hone_iff⟩

/-- **2. Reverse `σ`-Edge from `r₀` to `U₀`**:
When `13 ≤ W` on the coprime half-successor branch, `r₀ ^ (2 * e₀)` cannot divide `σ(h ^ 2)`,
forcing `r₀ ∣ σ(U₀ ^ 2)` and the existence of a prime factor `s ∈ U₀.primeFactors` (`s ≠ r₀`)
satisfying `r₀ ∣ σ(s ^ (2 * v_s(U₀)))`. -/
theorem linear_euler_coprime_half_succ_reverse_sigma_edge {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hcop : Nat.Coprime ((q + 1) / 2) (componentIndex N q)) :
    ∃ h u W r₀ e₀ U₀ c₀_u V₀ : ℕ,
      W = sigma 1 (u ^ 2) / q ∧
      m = h * u ∧ q = 2 * h ^ 2 - 1 ∧ componentIndex N q = u ^ 2 ∧
      r₀.Prime ∧ r₀ ∈ u.primeFactors ∧ 0 < e₀ ∧
      e₀ = u.factorization r₀ ∧ U₀ = ordCompl[r₀] u ∧ u = r₀ ^ e₀ * U₀ ∧
      sigma 1 (r₀ ^ (2 * e₀)) = q * c₀_u ∧
      W = c₀_u * sigma 1 (U₀ ^ 2) ∧ U₀ ^ 2 = c₀_u * V₀ ∧
      r₀ ^ (2 * e₀) * V₀ = sigma 1 (U₀ ^ 2) * sigma 1 (h ^ 2) ∧
      (13 ≤ W →
        ¬ (r₀ ^ (2 * e₀) ∣ sigma 1 (h ^ 2)) ∧
        r₀ ∣ sigma 1 (U₀ ^ 2) ∧
        ∃ s ∈ U₀.primeFactors, s ≠ r₀ ∧ r₀ ∣ sigma 1 (s ^ (2 * U₀.factorization s))) := by
  obtain ⟨h, u, W, r₀, e₀, U₀, c₀_u, V₀, hW_def, hm_eq, hq_eq, hci_sq_eq,
    hr₀_prime, hr₀_u, he₀_pos, he₀_eq_u, hU₀_def, hu_split, hcop_pow_U₀,
    hsig_r₀_eq, hW_eq, hU₀2_eq, hbal_V₀, _, hpp_iff, _, _, _⟩ :=
    linear_euler_coprime_half_succ_v0_coprime_and_prime_pow_equiv ho hN hq hqm hform hcop
  have hm_ne0 : m ≠ 0 := by
    intro hm0
    rw [hm0, zero_pow (by decide : 2 ≠ 0), mul_zero] at hform
    exact hN.2.ne' hform
  have hh0 : h ≠ 0 := by
    intro hh0
    rw [hh0, zero_mul] at hm_eq
    exact hm_ne0 hm_eq
  have hU₀_ge1 : 1 ≤ U₀ := by
    by_contra! hU0
    have hUz : U₀ = 0 := Nat.lt_one_iff.mp hU0
    rw [hUz, mul_zero] at hu_split
    rw [hu_split, mul_zero] at hm_eq
    exact hm_ne0 hm_eq
  have hc₀_ge1 : 1 ≤ c₀_u := by
    have hsig_pos : 0 < sigma 1 (r₀ ^ (2 * e₀)) :=
      sigma_pos 1 (r₀ ^ (2 * e₀)) (pow_ne_zero _ hr₀_prime.ne_zero)
    by_contra! hc0
    have hcz : c₀_u = 0 := Nat.lt_one_iff.mp hc0
    rw [hcz, mul_zero] at hsig_r₀_eq
    omega
  refine ⟨h, u, W, r₀, e₀, U₀, c₀_u, V₀, hW_def, hm_eq, hq_eq, hci_sq_eq,
    hr₀_prime, hr₀_u, he₀_pos, he₀_eq_u, hU₀_def, hu_split,
    hsig_r₀_eq, hW_eq, hU₀2_eq, hbal_V₀, ?_⟩
  intro hW13
  exact reverse_sigma_edge_of_factorization hh0 hU₀_ge1 hc₀_ge1 hr₀_prime he₀_pos
    hu_split hcop_pow_U₀ hU₀2_eq hbal_V₀ hpp_iff hW13

/-- **3. Sixth-Power-Free Reverse `σ`-Edge with `61 ≤ r₀`, `5041 ≤ r₀ ^ (2 * e₀)`, `61 ≤ s`**:
Specializes the reverse `σ`-edge to sixth-power-free odd perfect numbers, combining
`5113 ≤ W`, `r₀ % 5 = 1 ∨ r₀ % 3 = 1`, and `¬ 3 ∣ σ(r₀ ^ (2 * e₀))` (`¬ 3 ∣ N`) to force
`61 ≤ r₀`, `5041 ≤ r₀ ^ (2 * e₀)`, and `61 ≤ s` for the target prime `s ∈ U₀.primeFactors`. -/
theorem sixth_power_free_coprime_half_succ_reverse_edge_r0_ge_61 {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N)
    (hcop : Nat.Coprime ((q + 1) / 2) (componentIndex N q)) :
    ∃ h u W r₀ e₀ U₀ c₀_u V₀ : ℕ,
      W = sigma 1 (u ^ 2) / q ∧
      59 ≤ h ∧ 6961 ≤ q ∧ 71 ≤ U₀ ∧ 5113 ≤ W ∧
      ¬ IsPrimePow u ∧
      N = q * (h * u) ^ 2 ∧ componentIndex N q = u ^ 2 ∧
      u = r₀ ^ e₀ * U₀ ∧ W = c₀_u * sigma 1 (U₀ ^ 2) ∧ U₀ ^ 2 = c₀_u * V₀ ∧
      r₀ ^ (2 * e₀) * V₀ = sigma 1 (U₀ ^ 2) * sigma 1 (h ^ 2) ∧
      Nat.Coprime (r₀ ^ (2 * e₀)) V₀ ∧
      (r₀ % 5 = 1 ∨ r₀ % 3 = 1) ∧ 61 ≤ r₀ ∧ 5041 ≤ r₀ ^ (2 * e₀) ∧
      r₀ ∣ sigma 1 (U₀ ^ 2) ∧
      ∃ s ∈ U₀.primeFactors, s ≠ r₀ ∧ 61 ≤ s ∧ r₀ ∣ sigma 1 (s ^ (2 * U₀.factorization s)) := by
  obtain ⟨h, u, W, _, _, _, _, _, hW_def, hh_odd, hu_odd, _, _,
    hh_ge59, hq_ge6961, _, hW_ge5113, _, _, _,
    hform_hu, hci_sq_eq, _, _, _, _, _, _⟩ :=
    sixth_power_free_coprime_half_succ_w_ge_5113 ho hN hq hq4 he hev hfree hcop
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hfac_q : N.factorization q = 1 :=
    sixth_power_free_euler_exponent_one ho hN hq he hfree
  have hqm : ¬ q ∣ h * u := by
    intro hqd
    have hq3_dvd : q ^ 3 ∣ N := by
      rw [hform_hu]
      have hq2_dvd : q ^ 2 ∣ (h * u) ^ 2 := pow_dvd_pow_of_dvd hqd 2
      have hmul : q * q ^ 2 ∣ q * (h * u) ^ 2 := Nat.mul_dvd_mul_left q hq2_dvd
      rwa [show q * q ^ 2 = q ^ 3 by ring] at hmul
    have hle : 3 ≤ N.factorization q :=
      (hq_prime.pow_dvd_iff_le_factorization hN.2.ne').mp hq3_dvd
    omega
  obtain ⟨h₁, u₁, W₁, r₀, e₀, U₀, c₀_u, V₀, hW₁_def, hm₁_eq, _, hci₁_eq,
    hr₀_prime, hr₀_u₁, he₀_pos, _, _, hu₁_split, hcop_pow_U₀,
    hsig_r₀_eq, hW₁_eq, hU₀2_eq, hbal_V₀, hcop_r₀2_V₀, hpp_iff, hnpp_iff, _, _⟩ :=
    linear_euler_coprime_half_succ_v0_coprime_and_prime_pow_equiv ho hN hq_prime hqm hform_hu hcop
  obtain ⟨hu₁_eq, hW₁_eq'⟩ :=
    align_coprime_half_succ_u_W hci_sq_eq hW_def hci₁_eq hW₁_def
  have hh₁_eq : h₁ = h := by
    have hmul : h₁ * u = h * u := by
      calc
        h₁ * u = h₁ * u₁ := by rw [hu₁_eq]
        _ = h * u := hm₁_eq.symm
    exact Nat.mul_right_cancel hu_odd.pos hmul
  subst hh₁_eq hu₁_eq
  rw [← hW₁_eq'] at hW_ge5113
  have hh_ne0 : h₁ ≠ 0 := hh_odd.pos.ne'
  have hu_ne0 : u₁ ≠ 0 := hu_odd.pos.ne'
  have hU₀_odd : Odd U₀ := hu_odd.of_dvd_nat ⟨r₀ ^ e₀, by rw [mul_comm, ← hu₁_split]⟩
  have hU₀_ge1 : 1 ≤ U₀ := hU₀_odd.pos
  have hc₀_ge1 : 1 ≤ c₀_u := by
    have hsig_pos : 0 < sigma 1 (r₀ ^ (2 * e₀)) :=
      sigma_pos 1 (r₀ ^ (2 * e₀)) (pow_ne_zero _ hr₀_prime.ne_zero)
    by_contra! hc0
    have hcz : c₀_u = 0 := Nat.lt_one_iff.mp hc0
    rw [hcz, mul_zero] at hsig_r₀_eq
    omega
  have hnpp_u : ¬ IsPrimePow u₁ := hnpp_iff.mpr (by omega)
  obtain ⟨_, hr₀_dvd_sigU₀, s, hs_U₀, hs_ne_r₀, hr₀_dvd_sigs⟩ :=
    reverse_sigma_edge_of_factorization hh_ne0 hU₀_ge1 hc₀_ge1 hr₀_prime he₀_pos
      hu₁_split hcop_pow_U₀ hU₀2_eq hbal_V₀ hpp_iff (by omega : 13 ≤ W₁)
  obtain ⟨hr₀_mod, hr₀_ge61⟩ :=
    sixth_power_free_u_prime_ge_61 ho hN hq hq4 he hev hfree hu_ne0 hform_hu hci_sq_eq hr₀_u₁
  have hs_u : s ∈ u₁.primeFactors := by
    have hs_prime : s.Prime := Nat.prime_of_mem_primeFactors hs_U₀
    have hs_dvd_u : s ∣ u₁ :=
      (Nat.dvd_of_mem_primeFactors hs_U₀).trans ⟨r₀ ^ e₀, by rw [hu₁_split, mul_comm]⟩
    exact Nat.mem_primeFactors.mpr ⟨hs_prime, hs_dvd_u, hu_ne0⟩
  obtain ⟨hs_mod, hs_ge61⟩ :=
    sixth_power_free_u_prime_ge_61 ho hN hq hq4 he hev hfree hu_ne0 hform_hu hci_sq_eq hs_u
  have hnot3_N : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  have hU₀2_dvd_N : U₀ ^ 2 ∣ N := by
    have hU₀_dvd_u : U₀ ∣ u₁ := ⟨r₀ ^ e₀, by rw [hu₁_split, mul_comm]⟩
    have hu_dvd_hu : u₁ ∣ h₁ * u₁ := dvd_mul_left u₁ h₁
    have hpow : U₀ ^ 2 ∣ (h₁ * u₁) ^ 2 := pow_dvd_pow_of_dvd (hU₀_dvd_u.trans hu_dvd_hu) 2
    rw [hform_hu]
    exact hpow.trans (dvd_mul_left _ q)
  have hW₁_dvd_N : W₁ ∣ N := by
    obtain ⟨_, u₂, W₂, hW₂_def, _, _, _, _, _, _, _, _, hci₂_eq, hu₂_sq_eq, _, _, _, _⟩ :=
      linear_euler_coprime_half_succ_w_one_iff_prime_pow_u ho hN hq_prime hqm hform_hu hcop
    obtain ⟨hu₂_eq, hW₂_eq⟩ :=
      align_coprime_half_succ_u_W hci_sq_eq hW₁_def hci₂_eq hW₂_def
    have hW₁_dvd_u₁2 : W₁ ∣ u₁ ^ 2 := by
      rw [← hu₂_eq, ← hW₂_eq]
      exact ⟨_, hu₂_sq_eq⟩
    have hu₁2_dvd_N : u₁ ^ 2 ∣ N := by
      rw [hform_hu, mul_pow]
      exact (dvd_mul_left (u₁ ^ 2) (h₁ ^ 2)).trans (dvd_mul_left _ q)
    exact hW₁_dvd_u₁2.trans hu₁2_dvd_N
  have hU₀_ge71 : 71 ≤ U₀ := by
    have hU₀_ne0 : U₀ ≠ 0 := hU₀_odd.pos.ne'
    set k_s := U₀.factorization s
    have hk_s_ge1 : 1 ≤ k_s :=
      (Nat.prime_of_mem_primeFactors hs_U₀).dvd_iff_one_le_factorization hU₀_ne0 |>.mp
        (Nat.dvd_of_mem_primeFactors hs_U₀)
    have hsig_s_dvd_N : sigma 1 (s ^ (2 * k_s)) ∣ N := by
      have hU₀2_split : U₀ ^ 2 = s ^ (2 * k_s) * (ordCompl[s] U₀) ^ 2 := by
        have h1 : U₀ = s ^ k_s * ordCompl[s] U₀ := (Nat.ordProj_mul_ordCompl_eq_self U₀ s).symm
        calc
          U₀ ^ 2 = (s ^ k_s * ordCompl[s] U₀) ^ 2 := by rw [← h1]
          _ = (s ^ k_s) ^ 2 * (ordCompl[s] U₀) ^ 2 := by rw [mul_pow]
          _ = s ^ (2 * k_s) * (ordCompl[s] U₀) ^ 2 := by rw [← pow_mul, mul_comm k_s 2]
      have hs_prime : s.Prime := Nat.prime_of_mem_primeFactors hs_U₀
      have hcop_s_compl : Nat.Coprime (s ^ (2 * k_s)) ((ordCompl[s] U₀) ^ 2) :=
        ((Nat.coprime_ordCompl hs_prime hU₀_ne0).pow_left (2 * k_s)).pow_right 2
      have hsig_s_dvd : sigma 1 (s ^ (2 * k_s)) ∣ sigma 1 (U₀ ^ 2) := by
        rw [hU₀2_split, isMultiplicative_sigma.map_mul_of_coprime hcop_s_compl]
        exact dvd_mul_right _ _
      have hsigU₀_dvd_W : sigma 1 (U₀ ^ 2) ∣ W₁ := ⟨c₀_u, by rw [hW₁_eq, mul_comm]⟩
      exact (hsig_s_dvd.trans hsigU₀_dvd_W).trans hW₁_dvd_N
    have hnot3_sigs : ¬ 3 ∣ sigma 1 (s ^ (2 * k_s)) := fun h3 => hnot3_N (h3.trans hsig_s_dvd_N)
    have hs_prime : s.Prime := Nat.prime_of_mem_primeFactors hs_U₀
    by_cases hs3 : s % 3 = 1
    · have hk_ge2 : 2 ≤ k_s := by
        by_contra! hk_lt2
        have hk1 : k_s = 1 := by omega
        have hsig_eq : sigma 1 (s ^ (2 * k_s)) = s ^ 2 + s + 1 := by
          rw [hk1, mul_one, sigma_one_apply_prime_pow hs_prime]
          simp [Finset.sum_range_succ]
          ring
        have h3_dvd : 3 ∣ sigma 1 (s ^ (2 * k_s)) := by
          rw [hsig_eq]
          obtain ⟨t, ht⟩ : ∃ t, s = 3 * t + 1 := ⟨s / 3, by omega⟩
          rw [ht]
          exact ⟨3 * t ^ 2 + 3 * t + 1, by ring⟩
        exact hnot3_sigs h3_dvd
      have hpow_dvd_U₀ : s ^ k_s ∣ U₀ := Nat.ordProj_dvd U₀ s
      have hs2_le_pow : s ^ 2 ≤ s ^ k_s := Nat.pow_le_pow_right hs_prime.pos hk_ge2
      have hpow_le_U₀ : s ^ k_s ≤ U₀ := Nat.le_of_dvd hU₀_odd.pos hpow_dvd_U₀
      have h61_sq : 61 ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left hs_ge61 2
      linarith only [h61_sq, hs2_le_pow, hpow_le_U₀]
    · have hs_ge71 : 71 ≤ s := by
        by_contra! hlt
        have hs_cases : s = 61 ∨ s = 62 ∨ s = 63 ∨ s = 64 ∨ s = 65 ∨
            s = 66 ∨ s = 67 ∨ s = 68 ∨ s = 69 ∨ s = 70 := by omega
        rcases hs_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact hs3 (by decide)
        · exact (by decide : ¬ Nat.Prime 62) hs_prime
        · exact (by decide : ¬ Nat.Prime 63) hs_prime
        · exact (by decide : ¬ Nat.Prime 64) hs_prime
        · exact (by decide : ¬ Nat.Prime 65) hs_prime
        · exact (by decide : ¬ Nat.Prime 66) hs_prime
        · exact hs3 (by decide)
        · exact (by decide : ¬ Nat.Prime 68) hs_prime
        · exact (by decide : ¬ Nat.Prime 69) hs_prime
        · exact (by decide : ¬ Nat.Prime 70) hs_prime
      exact hs_ge71.trans (Nat.le_of_dvd hU₀_odd.pos (Nat.dvd_of_mem_primeFactors hs_U₀))
  have hr₀_pow_ge5041 : 5041 ≤ r₀ ^ (2 * e₀) := by
    by_cases he2 : 2 ≤ e₀
    · have h4_le : 4 ≤ 2 * e₀ := by omega
      have h61_pow4 : (5041 : ℕ) ≤ 61 ^ 4 := by norm_num
      have hr₀4_le : 61 ^ 4 ≤ r₀ ^ 4 := Nat.pow_le_pow_left hr₀_ge61 4
      have hr₀pow_le : r₀ ^ 4 ≤ r₀ ^ (2 * e₀) := Nat.pow_le_pow_right hr₀_prime.pos h4_le
      exact h61_pow4.trans (hr₀4_le.trans hr₀pow_le)
    · have he1 : e₀ = 1 := by omega
      have hqc₀_dvd_N : q * c₀_u ∣ N := by
        have hc₀_dvd_U₀2 : c₀_u ∣ U₀ ^ 2 := ⟨V₀, hU₀2_eq⟩
        have hc₀_dvd_hu2 : c₀_u ∣ (h₁ * u₁) ^ 2 := by
          have hU₀_dvd_u : U₀ ∣ u₁ := ⟨r₀ ^ e₀, by rw [hu₁_split, mul_comm]⟩
          exact hc₀_dvd_U₀2.trans (pow_dvd_pow_of_dvd (hU₀_dvd_u.trans (dvd_mul_left u₁ h₁)) 2)
        rw [hform_hu]
        exact Nat.mul_dvd_mul_left q hc₀_dvd_hu2
      have hnot3_qc₀ : ¬ 3 ∣ sigma 1 (r₀ ^ (2 * e₀)) := fun h3 =>
        hnot3_N (h3.trans (hsig_r₀_eq ▸ hqc₀_dvd_N))
      have hr₀_not3 : r₀ % 3 ≠ 1 := by
        intro hr₀3
        have hsig_eq : sigma 1 (r₀ ^ (2 * e₀)) = r₀ ^ 2 + r₀ + 1 := by
          rw [he1, mul_one, sigma_one_apply_prime_pow hr₀_prime]
          simp [Finset.sum_range_succ]
          ring
        have h3_dvd : 3 ∣ sigma 1 (r₀ ^ (2 * e₀)) := by
          rw [hsig_eq]
          obtain ⟨t, ht⟩ : ∃ t, r₀ = 3 * t + 1 := ⟨r₀ / 3, by omega⟩
          rw [ht]
          exact ⟨3 * t ^ 2 + 3 * t + 1, by ring⟩
        exact hnot3_qc₀ h3_dvd
      have hr₀_ge71 : 71 ≤ r₀ := by
        by_contra! hlt
        have hr₀_cases : r₀ = 61 ∨ r₀ = 62 ∨ r₀ = 63 ∨ r₀ = 64 ∨ r₀ = 65 ∨
            r₀ = 66 ∨ r₀ = 67 ∨ r₀ = 68 ∨ r₀ = 69 ∨ r₀ = 70 := by omega
        rcases hr₀_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact hr₀_not3 (by decide)
        · exact (by decide : ¬ Nat.Prime 62) hr₀_prime
        · exact (by decide : ¬ Nat.Prime 63) hr₀_prime
        · exact (by decide : ¬ Nat.Prime 64) hr₀_prime
        · exact (by decide : ¬ Nat.Prime 65) hr₀_prime
        · exact (by decide : ¬ Nat.Prime 66) hr₀_prime
        · exact hr₀_not3 (by decide)
        · exact (by decide : ¬ Nat.Prime 68) hr₀_prime
        · exact (by decide : ¬ Nat.Prime 69) hr₀_prime
        · exact (by decide : ¬ Nat.Prime 70) hr₀_prime
      have h71_sq : (5041 : ℕ) = 71 ^ 2 := by norm_num
      have hr₀2_ge : 71 ^ 2 ≤ r₀ ^ 2 := Nat.pow_le_pow_left hr₀_ge71 2
      rw [he1, mul_one]
      omega
  exact ⟨h₁, u₁, W₁, r₀, e₀, U₀, c₀_u, V₀, hW₁_def, hh_ge59, hq_ge6961, hU₀_ge71, hW_ge5113,
    hnpp_u, hform_hu, hci_sq_eq, hu₁_split, hW₁_eq, hU₀2_eq, hbal_V₀, hcop_r₀2_V₀,
    hr₀_mod, hr₀_ge61, hr₀_pow_ge5041, hr₀_dvd_sigU₀, s, hs_U₀, hs_ne_r₀, hs_ge61, hr₀_dvd_sigs⟩

end OddPerfect
