module

public import OddPerfect.LinearEulerRightSourceForcing
import OddPerfect.LinearEulerOrderObstruction
import OddPerfect.Reciprocity
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Linear Euler Right-Branch Structure

BRANCH_MAP: A1
Closure: Eliminates all r₀ ≡ 3 (mod 4) (including r₀ = 3), all k_R > 2b, and all (b = 1, k_R ≥ 2) from Branch R1 (r₀ ∣ (q+1)/2) across all of A1, sharpens A < r₀^(v_{r₀}(I)), and excludes Fermat q on R1.

Structural analysis of Branch R1 (`r₀ ∣ g_R`, equivalently `r₀ ∣ (q + 1) / 2`) on any linear Euler
odd perfect number `N = q * m ^ 2` (`¬ q ∣ m`).
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma sum_odd_pow_mod_two {r : ℕ} (hr : r % 2 = 1) (n : ℕ) :
    (∑ i ∈ Finset.range n, r ^ i) % 2 = n % 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih, Nat.pow_mod, hr, one_pow]
    omega

private lemma r1_diophantine_b1_kR_eq_one {r₀ k_R C u : ℕ} {z : ℤ}
    (hr0_ge5 : 5 ≤ r₀) (hkR_pos : 1 ≤ k_R) (hkR_le2 : k_R ≤ 2)
    (hC_pos : 1 ≤ C) (hu_pos : 1 ≤ u) (hz_odd : z % 2 = 1)
    (hE1 : 2 * (C : ℤ) - ((r₀ : ℤ) - 1) * (u : ℤ) + 1 = z * (r₀ : ℤ) ^ k_R)
    (hE2 : 2 * (C : ℤ) * (((r₀ : ℤ) - 1) * (u : ℤ) - 1) + z = (r₀ : ℤ) ^ 3)
    (hE3 : 4 * (C : ℤ) ^ 2 - (r₀ : ℤ) ^ 3 = z * (2 * (C : ℤ) * (r₀ : ℤ) ^ k_R - 1)) :
    k_R = 1 := by
  by_contra hkR_ne1
  have hkR2 : k_R = 2 := by omega
  subst hkR2
  have hrZ_ge5 : (5 : ℤ) ≤ (r₀ : ℤ) := by exact_mod_cast hr0_ge5
  have hCZ_ge1 : (1 : ℤ) ≤ (C : ℤ) := by exact_mod_cast hC_pos
  have huZ_ge1 : (1 : ℤ) ≤ (u : ℤ) := by exact_mod_cast hu_pos
  have hz_ne0 : z ≠ 0 := by omega
  have hrZ3_ge : 5 * (r₀ : ℤ) ^ 2 ≤ (r₀ : ℤ) ^ 3 := by
    have hrZ3_eq : (r₀ : ℤ) ^ 3 = (r₀ : ℤ) * (r₀ : ℤ) ^ 2 := by ring
    nlinarith only [hrZ_ge5, hrZ3_eq, sq_nonneg (r₀ : ℤ)]
  rcases lt_or_gt_of_ne hz_ne0 with hz_neg | hz_pos
  · let tz : ℕ := (-z).toNat
    have htz_eq : (tz : ℤ) = -z := by omega
    have htz_ge1 : 1 ≤ tz := by omega
    have htz_odd : tz % 2 = 1 := by omega
    have hE3_neg : (r₀ : ℤ) ^ 3 = 4 * (C : ℤ) ^ 2 + (tz : ℤ) * (2 * (C : ℤ) * (r₀ : ℤ) ^ 2 - 1) := by
      have : z * (2 * (C : ℤ) * (r₀ : ℤ) ^ 2 - 1) =
          -((tz : ℤ) * (2 * (C : ℤ) * (r₀ : ℤ) ^ 2 - 1)) := by
        rw [htz_eq]
        ring
      linarith [hE3, this]
    have htz_lt_r0 : tz < r₀ := by
      by_contra hle
      have hrZ_le_tz : (r₀ : ℤ) ≤ (tz : ℤ) := by exact_mod_cast Nat.not_lt.mp hle
      have h_prod : (r₀ : ℤ) * (2 * (r₀ : ℤ) ^ 2 - 1) ≤
          (tz : ℤ) * (2 * (C : ℤ) * (r₀ : ℤ) ^ 2 - 1) :=
        mul_le_mul hrZ_le_tz
          (by nlinarith only [hCZ_ge1, sq_nonneg (r₀ : ℤ)])
          (by nlinarith only [hrZ_ge5])
          (by omega)
      have h_exp : (r₀ : ℤ) * (2 * (r₀ : ℤ) ^ 2 - 1) = 2 * (r₀ : ℤ) ^ 3 - (r₀ : ℤ) := by ring
      have hrZ_cu_ge : 25 * (r₀ : ℤ) ≤ (r₀ : ℤ) ^ 3 := by
        have hrZ_sq_ge : 25 ≤ (r₀ : ℤ) ^ 2 := by nlinarith only [hrZ_ge5]
        have hrZ_cu_eq : (r₀ : ℤ) ^ 3 = (r₀ : ℤ) * (r₀ : ℤ) ^ 2 := by ring
        nlinarith only [hrZ_ge5, hrZ_sq_ge, hrZ_cu_eq]
      nlinarith only [hE3_neg, h_prod, h_exp, hrZ_cu_ge, hCZ_ge1]
    have htz_lt_sq : tz < r₀ ^ 2 := by nlinarith only [htz_lt_r0, hr0_ge5]
    have h4C2_lt_sq : 4 * C ^ 2 < r₀ ^ 2 := by
      have htzZ : (1 : ℤ) ≤ (tz : ℤ) := by exact_mod_cast htz_ge1
      have h_prod : 2 * (C : ℤ) * (r₀ : ℤ) ^ 2 - 1 ≤
          (tz : ℤ) * (2 * (C : ℤ) * (r₀ : ℤ) ^ 2 - 1) :=
        le_mul_of_one_le_left (by nlinarith only [hCZ_ge1, hrZ_ge5]) htzZ
      have h2C_rZ2_lt : 2 * (C : ℤ) * (r₀ : ℤ) ^ 2 < (r₀ : ℤ) * (r₀ : ℤ) ^ 2 := by
        have hrZ3_eq : (r₀ : ℤ) ^ 3 = (r₀ : ℤ) * (r₀ : ℤ) ^ 2 := by ring
        nlinarith only [hE3_neg, h_prod, hCZ_ge1, hrZ3_eq]
      have h2C_lt_r0 : 2 * (C : ℤ) < (r₀ : ℤ) := by
        by_contra hle
        have hrZ_le_2C : (r₀ : ℤ) ≤ 2 * (C : ℤ) := by omega
        have := mul_le_mul_of_nonneg_right hrZ_le_2C (sq_nonneg (r₀ : ℤ))
        linarith
      have h4C2Z : 4 * (C : ℤ) ^ 2 < (r₀ : ℤ) ^ 2 := by
        nlinarith only [h2C_lt_r0, hCZ_ge1, hrZ_ge5]
      exact_mod_cast h4C2Z
    have hnat_eq : r₀ ^ 2 * r₀ + tz = r₀ ^ 2 * (2 * C * tz) + 4 * C ^ 2 := by
      zify
      calc
        (r₀ : ℤ) ^ 2 * (r₀ : ℤ) + (tz : ℤ)
            = (r₀ : ℤ) ^ 3 + (tz : ℤ) := by ring
        _ = 4 * (C : ℤ) ^ 2 + (tz : ℤ) * (2 * (C : ℤ) * (r₀ : ℤ) ^ 2 - 1) + (tz : ℤ) := by
            rw [hE3_neg]
        _ = (r₀ : ℤ) ^ 2 * (2 * (C : ℤ) * (tz : ℤ)) + 4 * (C : ℤ) ^ 2 := by ring
    have hmod_eq : tz = 4 * C ^ 2 := by
      have hmod := congr_arg (· % r₀ ^ 2) hnat_eq
      rw [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod,
        Nat.mod_eq_of_lt htz_lt_sq] at hmod
      rw [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod,
        Nat.mod_eq_of_lt h4C2_lt_sq] at hmod
      exact hmod
    omega
  · have hu_cases : (u : ℤ) = 1 ∨ 2 ≤ (u : ℤ) := by omega
    rcases hu_cases with hu1 | hu2
    · have hz_cases : z = 1 ∨ 2 ≤ z := by omega
      rcases hz_cases with hz1 | hz2
      · have h2C_eq : 2 * (C : ℤ) = (r₀ : ℤ) ^ 2 + (r₀ : ℤ) - 2 := by
          have h1 := hE1
          rw [hu1, hz1] at h1
          linarith
        have hcontra : (r₀ : ℤ) ^ 3 = ((r₀ : ℤ) ^ 2 + (r₀ : ℤ) - 2) * ((r₀ : ℤ) - 2) + 1 := by
          have h2 := hE2
          rw [hu1, hz1, h2C_eq] at h2
          rw [← h2]
          ring
        have hexp : ((r₀ : ℤ) ^ 2 + (r₀ : ℤ) - 2) * ((r₀ : ℤ) - 2) + 1 =
            (r₀ : ℤ) ^ 3 - (r₀ : ℤ) ^ 2 - 4 * (r₀ : ℤ) + 5 := by ring
        nlinarith only [hcontra, hexp, hrZ_ge5]
      · have h2C_ge : 2 * (r₀ : ℤ) ^ 2 + (r₀ : ℤ) - 2 ≤ 2 * (C : ℤ) := by
          have h1 := hE1
          rw [hu1] at h1
          nlinarith only [h1, hz2, sq_nonneg (r₀ : ℤ)]
        have hcontra : (2 * (r₀ : ℤ) ^ 2 + (r₀ : ℤ) - 2) * ((r₀ : ℤ) - 2) + 2 ≤ (r₀ : ℤ) ^ 3 := by
          have h2 := hE2
          rw [hu1] at h2
          nlinarith only [h2, h2C_ge, hrZ_ge5, hz2]
        have hexp : (2 * (r₀ : ℤ) ^ 2 + (r₀ : ℤ) - 2) * ((r₀ : ℤ) - 2) + 2 =
            2 * (r₀ : ℤ) ^ 3 - 3 * (r₀ : ℤ) ^ 2 - 4 * (r₀ : ℤ) + 6 := by ring
        nlinarith only [hcontra, hexp, hrZ3_ge, hrZ_ge5]
    · have h_tZ_ge : 2 * (r₀ : ℤ) - 3 ≤ ((r₀ : ℤ) - 1) * (u : ℤ) - 1 := by
        nlinarith only [hrZ_ge5, hu2]
      have h2C_ge : (r₀ : ℤ) ^ 2 + 2 * (r₀ : ℤ) - 3 ≤ 2 * (C : ℤ) := by
        nlinarith only [hE1, hz_pos, h_tZ_ge, sq_nonneg (r₀ : ℤ)]
      have hcontra : ((r₀ : ℤ) ^ 2 + 2 * (r₀ : ℤ) - 3) * (2 * (r₀ : ℤ) - 3) + 1 ≤
          (r₀ : ℤ) ^ 3 := by
        nlinarith only [hE2, hz_pos, h_tZ_ge, h2C_ge, hrZ_ge5]
      have hexp : ((r₀ : ℤ) ^ 2 + 2 * (r₀ : ℤ) - 3) * (2 * (r₀ : ℤ) - 3) + 1 =
          2 * (r₀ : ℤ) ^ 3 + (r₀ : ℤ) ^ 2 - 12 * (r₀ : ℤ) + 10 := by ring
      nlinarith only [hcontra, hexp, hrZ3_ge, hrZ_ge5]

private lemma r1_diophantine_bounds {r₀ k_R b C u c₀ q : ℕ}
    (hr0_ge5 : 5 ≤ r₀) (hr0_odd : Odd r₀) (hkR_pos : 1 ≤ k_R) (hb_pos : 1 ≤ b)
    (hC_pos : 1 ≤ C) (hu_pos : 1 ≤ u) (hodd_u : Odd k_R → 2 ≤ u)
    (hq1 : q + 1 = 2 * C * r₀ ^ k_R)
    (ht_u : (r₀ - 1) * c₀ = 1 + ((r₀ - 1) * u - 1) * r₀ ^ k_R)
    (hpow : (r₀ - 1) * c₀ * q + 1 = r₀ ^ (2 * b + 1) * (r₀ ^ k_R) ^ 2) :
    C < r₀ ^ (2 * b) ∧ (Odd k_R → 2 * C < r₀ ^ (2 * b)) ∧ k_R ≤ 2 * b ∧ (b = 1 → k_R = 1) := by
  have hrZ_ge5 : (5 : ℤ) ≤ (r₀ : ℤ) := by exact_mod_cast hr0_ge5
  have hCZ_ge1 : (1 : ℤ) ≤ (C : ℤ) := by exact_mod_cast hC_pos
  have huZ_ge1 : (1 : ℤ) ≤ (u : ℤ) := by exact_mod_cast hu_pos
  have hX_ge_r0 : r₀ ≤ r₀ ^ k_R := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < r₀) hkR_pos
  have hXZ_ge5 : (5 : ℤ) ≤ (r₀ : ℤ) ^ k_R := by
    exact_mod_cast le_trans hr0_ge5 hX_ge_r0
  have hXZ0 : (r₀ : ℤ) ^ k_R ≠ 0 := pow_ne_zero k_R (by omega)
  have hpZ_eq : (r₀ : ℤ) ^ (2 * b + 1) = (r₀ : ℤ) * (r₀ : ℤ) ^ (2 * b) := by
    rw [pow_succ']
  have hB2_ge_sq : (r₀ : ℤ) ^ 2 ≤ (r₀ : ℤ) ^ (2 * b) := by
    exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < r₀) (by omega : 2 ≤ 2 * b)
  have hqZ_eq : (q : ℤ) = 2 * (C : ℤ) * (r₀ : ℤ) ^ k_R - 1 := by
    have hq1Z : (q : ℤ) + 1 = 2 * (C : ℤ) * (r₀ : ℤ) ^ k_R := by exact_mod_cast hq1
    linarith
  have h_mul_u_ge1 : 1 ≤ (r₀ - 1) * u := Nat.mul_pos (by omega) hu_pos
  have hc0Z_eq : ((r₀ : ℤ) - 1) * (c₀ : ℤ) = 1 + (((r₀ : ℤ) - 1) * (u : ℤ) - 1) * (r₀ : ℤ) ^ k_R := by
    zify [h_mul_u_ge1, show 1 ≤ r₀ from by omega] at ht_u
    exact ht_u
  have hpowZ_eq : ((r₀ : ℤ) - 1) * (c₀ : ℤ) * (q : ℤ) + 1 =
      (r₀ : ℤ) ^ (2 * b + 1) * ((r₀ : ℤ) ^ k_R) ^ 2 := by
    zify [show 1 ≤ r₀ from by omega] at hpow
    exact hpow
  have hpoly : 2 * (C : ℤ) * (((r₀ : ℤ) - 1) * (u : ℤ) - 1) * ((r₀ : ℤ) ^ k_R) ^ 2 +
      (2 * (C : ℤ) - ((r₀ : ℤ) - 1) * (u : ℤ) + 1) * (r₀ : ℤ) ^ k_R =
      (r₀ : ℤ) ^ (2 * b + 1) * ((r₀ : ℤ) ^ k_R) ^ 2 := by
    calc
      2 * (C : ℤ) * (((r₀ : ℤ) - 1) * (u : ℤ) - 1) * ((r₀ : ℤ) ^ k_R) ^ 2 +
          (2 * (C : ℤ) - ((r₀ : ℤ) - 1) * (u : ℤ) + 1) * (r₀ : ℤ) ^ k_R
          = (1 + (((r₀ : ℤ) - 1) * (u : ℤ) - 1) * (r₀ : ℤ) ^ k_R) *
              (2 * (C : ℤ) * (r₀ : ℤ) ^ k_R - 1) + 1 := by ring
      _ = ((r₀ : ℤ) - 1) * (c₀ : ℤ) * (q : ℤ) + 1 := by rw [← hc0Z_eq, ← hqZ_eq]
      _ = (r₀ : ℤ) ^ (2 * b + 1) * ((r₀ : ℤ) ^ k_R) ^ 2 := hpowZ_eq
  let z : ℤ := (r₀ : ℤ) ^ (2 * b + 1) - 2 * (C : ℤ) * (((r₀ : ℤ) - 1) * (u : ℤ) - 1)
  have hE1 : 2 * (C : ℤ) - ((r₀ : ℤ) - 1) * (u : ℤ) + 1 = z * (r₀ : ℤ) ^ k_R := by
    apply mul_right_cancel₀ hXZ0
    calc
      (2 * (C : ℤ) - ((r₀ : ℤ) - 1) * (u : ℤ) + 1) * (r₀ : ℤ) ^ k_R
          = (r₀ : ℤ) ^ (2 * b + 1) * ((r₀ : ℤ) ^ k_R) ^ 2 -
              2 * (C : ℤ) * (((r₀ : ℤ) - 1) * (u : ℤ) - 1) * ((r₀ : ℤ) ^ k_R) ^ 2 := by
            linarith [hpoly]
      _ = (z * (r₀ : ℤ) ^ k_R) * (r₀ : ℤ) ^ k_R := by dsimp [z]; ring
  have hE2 : 2 * (C : ℤ) * (((r₀ : ℤ) - 1) * (u : ℤ) - 1) + z = (r₀ : ℤ) ^ (2 * b + 1) := by
    dsimp [z]
    ring
  have hE3 : 4 * (C : ℤ) ^ 2 - (r₀ : ℤ) ^ (2 * b + 1) = z * (q : ℤ) := by
    calc
      4 * (C : ℤ) ^ 2 - (r₀ : ℤ) ^ (2 * b + 1)
          = 4 * (C : ℤ) ^ 2 - (2 * (C : ℤ) * (((r₀ : ℤ) - 1) * (u : ℤ) - 1) + z) := by rw [hE2]
      _ = 2 * (C : ℤ) * (2 * (C : ℤ) - ((r₀ : ℤ) - 1) * (u : ℤ) + 1) - z := by ring
      _ = 2 * (C : ℤ) * (z * (r₀ : ℤ) ^ k_R) - z := by rw [hE1]
      _ = z * (2 * (C : ℤ) * (r₀ : ℤ) ^ k_R - 1) := by ring
      _ = z * (q : ℤ) := by rw [← hqZ_eq]
  have hz_odd : z % 2 = 1 := by
    have hX_odd : Odd (r₀ ^ k_R) := hr0_odd.pow
    obtain ⟨rk, hrk⟩ := hr0_odd
    obtain ⟨xk, hxk⟩ := hX_odd
    have hrZ1 : (r₀ : ℤ) - 1 = 2 * (rk : ℤ) := by omega
    have hXZ1 : (r₀ : ℤ) ^ k_R = 2 * (xk : ℤ) + 1 := by exact_mod_cast hxk
    have h_parity : z = 2 * ((C : ℤ) - (rk : ℤ) * (u : ℤ) - z * (xk : ℤ)) + 1 := by
      have h1 := hE1
      rw [hrZ1, hXZ1] at h1
      linarith
    omega
  have hz_ne0 : z ≠ 0 := by omega
  have h_main_ineq : (((r₀ : ℤ) - 1) * (u : ℤ) - 1) * (2 * (C : ℤ) * (r₀ : ℤ) ^ k_R - 1) +
      2 * (C : ℤ) = (r₀ : ℤ) ^ (2 * b + 1) * (r₀ : ℤ) ^ k_R := by
    calc
      (((r₀ : ℤ) - 1) * (u : ℤ) - 1) * (2 * (C : ℤ) * (r₀ : ℤ) ^ k_R - 1) + 2 * (C : ℤ)
          = 2 * (C : ℤ) * (((r₀ : ℤ) - 1) * (u : ℤ) - 1) * (r₀ : ℤ) ^ k_R +
              (2 * (C : ℤ) - ((r₀ : ℤ) - 1) * (u : ℤ) + 1) := by ring
      _ = 2 * (C : ℤ) * (((r₀ : ℤ) - 1) * (u : ℤ) - 1) * (r₀ : ℤ) ^ k_R +
            z * (r₀ : ℤ) ^ k_R := by rw [hE1]
      _ = (2 * (C : ℤ) * (((r₀ : ℤ) - 1) * (u : ℤ) - 1) + z) * (r₀ : ℤ) ^ k_R := by ring
      _ = (r₀ : ℤ) ^ (2 * b + 1) * (r₀ : ℤ) ^ k_R := by rw [hE2]
  have hC_lt_B2 : C < r₀ ^ (2 * b) := by
    by_contra hle
    have hC_ge : (r₀ : ℤ) ^ (2 * b) ≤ (C : ℤ) := by exact_mod_cast Nat.not_lt.mp hle
    have h_tZ_ge : (r₀ : ℤ) - 2 ≤ ((r₀ : ℤ) - 1) * (u : ℤ) - 1 := by
      nlinarith only [hrZ_ge5, huZ_ge1]
    have h_qZ_pos : 0 ≤ 2 * (C : ℤ) * (r₀ : ℤ) ^ k_R - 1 := by
      nlinarith only [hCZ_ge1, hXZ_ge5]
    have h_step : ((r₀ : ℤ) - 2) * (2 * (C : ℤ) * (r₀ : ℤ) ^ k_R - 1) + 2 * (C : ℤ) ≤
        (r₀ : ℤ) ^ (2 * b + 1) * (r₀ : ℤ) ^ k_R := by
      have : ((r₀ : ℤ) - 2) * (2 * (C : ℤ) * (r₀ : ℤ) ^ k_R - 1) ≤
          (((r₀ : ℤ) - 1) * (u : ℤ) - 1) * (2 * (C : ℤ) * (r₀ : ℤ) ^ k_R - 1) :=
        mul_le_mul_of_nonneg_right h_tZ_ge h_qZ_pos
      linarith [h_main_ineq]
    have h_step_exp : ((r₀ : ℤ) - 2) * (2 * (C : ℤ) * (r₀ : ℤ) ^ k_R - 1) + 2 * (C : ℤ) =
        2 * (C : ℤ) * ((r₀ : ℤ) - 2) * (r₀ : ℤ) ^ k_R + (2 * (C : ℤ) - (r₀ : ℤ) + 2) := by ring
    have h_pos1 : 0 < 2 * (C : ℤ) - (r₀ : ℤ) + 2 := by
      nlinarith only [hrZ_ge5, hB2_ge_sq, hC_ge]
    have h_pos2_base : (r₀ : ℤ) * (r₀ : ℤ) ^ (2 * b) < 2 * (C : ℤ) * ((r₀ : ℤ) - 2) := by
      nlinarith only [hrZ_ge5, hC_ge, show (0 : ℤ) < (r₀ : ℤ) ^ (2 * b) from by positivity]
    have h_pos2 : (r₀ : ℤ) ^ (2 * b + 1) * (r₀ : ℤ) ^ k_R <
        2 * (C : ℤ) * ((r₀ : ℤ) - 2) * (r₀ : ℤ) ^ k_R := by
      rw [hpZ_eq]
      exact mul_lt_mul_of_pos_right h_pos2_base (by omega)
    linarith [h_step, h_step_exp, h_pos1, h_pos2]
  have h2C_lt_B2 : Odd k_R → 2 * C < r₀ ^ (2 * b) := by
    intro hkR_odd
    have hu2 : 2 ≤ u := hodd_u hkR_odd
    have huZ2 : (2 : ℤ) ≤ (u : ℤ) := by exact_mod_cast hu2
    by_contra hle
    have h2C_ge : (r₀ : ℤ) ^ (2 * b) ≤ 2 * (C : ℤ) := by exact_mod_cast Nat.not_lt.mp hle
    have h_tZ_ge : 2 * (r₀ : ℤ) - 3 ≤ ((r₀ : ℤ) - 1) * (u : ℤ) - 1 := by
      nlinarith only [hrZ_ge5, huZ2]
    have h_qZ_pos : 0 ≤ 2 * (C : ℤ) * (r₀ : ℤ) ^ k_R - 1 := by
      nlinarith only [hCZ_ge1, hXZ_ge5]
    have h_step : (2 * (r₀ : ℤ) - 3) * (2 * (C : ℤ) * (r₀ : ℤ) ^ k_R - 1) + 2 * (C : ℤ) ≤
        (r₀ : ℤ) ^ (2 * b + 1) * (r₀ : ℤ) ^ k_R := by
      have : (2 * (r₀ : ℤ) - 3) * (2 * (C : ℤ) * (r₀ : ℤ) ^ k_R - 1) ≤
          (((r₀ : ℤ) - 1) * (u : ℤ) - 1) * (2 * (C : ℤ) * (r₀ : ℤ) ^ k_R - 1) :=
        mul_le_mul_of_nonneg_right h_tZ_ge h_qZ_pos
      linarith [h_main_ineq]
    have h_step_exp : (2 * (r₀ : ℤ) - 3) * (2 * (C : ℤ) * (r₀ : ℤ) ^ k_R - 1) + 2 * (C : ℤ) =
        2 * (C : ℤ) * (2 * (r₀ : ℤ) - 3) * (r₀ : ℤ) ^ k_R +
          (2 * (C : ℤ) - (2 * (r₀ : ℤ) - 3)) := by ring
    have h_pos1 : 0 < 2 * (C : ℤ) - (2 * (r₀ : ℤ) - 3) := by
      nlinarith only [hrZ_ge5, hB2_ge_sq, h2C_ge]
    have h_pos2_base : (r₀ : ℤ) * (r₀ : ℤ) ^ (2 * b) < 2 * (C : ℤ) * (2 * (r₀ : ℤ) - 3) := by
      nlinarith only [hrZ_ge5, h2C_ge, show (0 : ℤ) < (r₀ : ℤ) ^ (2 * b) from by positivity]
    have h_pos2 : (r₀ : ℤ) ^ (2 * b + 1) * (r₀ : ℤ) ^ k_R <
        2 * (C : ℤ) * (2 * (r₀ : ℤ) - 3) * (r₀ : ℤ) ^ k_R := by
      rw [hpZ_eq]
      exact mul_lt_mul_of_pos_right h_pos2_base (by omega)
    linarith [h_step, h_step_exp, h_pos1, h_pos2]
  have hkR_le_2b : k_R ≤ 2 * b := by
    have hXZ_lt_pZ : (r₀ : ℤ) ^ k_R < (r₀ : ℤ) ^ (2 * b + 1) := by
      rcases lt_or_gt_of_ne hz_ne0 with hz_neg | hz_pos
      · have htz_ge1 : 1 ≤ -z := by omega
        have hqZ_ge : 2 * (r₀ : ℤ) ^ k_R - 1 ≤ (q : ℤ) := by
          nlinarith only [hCZ_ge1, hXZ_ge5, hqZ_eq]
        have h1 : 4 * (C : ℤ) ^ 2 + (-z) * (q : ℤ) = (r₀ : ℤ) ^ (2 * b + 1) := by
          nlinarith only [hE3]
        nlinarith only [htz_ge1, hqZ_ge, h1, hCZ_ge1, hXZ_ge5]
      · have h_tZ_ge : 3 ≤ ((r₀ : ℤ) - 1) * (u : ℤ) - 1 := by
          nlinarith only [hrZ_ge5, huZ_ge1]
        have h2C_lb : (r₀ : ℤ) ^ k_R + 3 ≤ 2 * (C : ℤ) := by
          nlinarith only [hz_pos, hXZ_ge5, h_tZ_ge, hE1]
        nlinarith only [hz_pos, h_tZ_ge, h2C_lb, hE2, hXZ_ge5]
    have hX_lt_pow : r₀ ^ k_R < r₀ ^ (2 * b + 1) := by exact_mod_cast hXZ_lt_pZ
    by_contra hgt
    have hle : 2 * b + 1 ≤ k_R := by omega
    have hpow_le : r₀ ^ (2 * b + 1) ≤ r₀ ^ k_R := Nat.pow_le_pow_right (by omega : 0 < r₀) hle
    omega
  have hb1_kR1 : b = 1 → k_R = 1 := by
    intro hb1
    have hkR_le2 : k_R ≤ 2 := by omega
    have hE2' : 2 * (C : ℤ) * (((r₀ : ℤ) - 1) * (u : ℤ) - 1) + z = (r₀ : ℤ) ^ 3 := by
      have h1 := hE2
      rw [hb1] at h1
      exact h1
    have hE3' : 4 * (C : ℤ) ^ 2 - (r₀ : ℤ) ^ 3 = z * (2 * (C : ℤ) * (r₀ : ℤ) ^ k_R - 1) := by
      have h1 := hE3
      rw [hb1, hqZ_eq] at h1
      exact h1
    exact r1_diophantine_b1_kR_eq_one hr0_ge5 hkR_pos hkR_le2 hC_pos hu_pos hz_odd hE1 hE2' hE3'
  exact ⟨hC_lt_B2, h2C_lt_B2, hkR_le_2b, hb1_kR1⟩

/-- **Linear Euler Right-Branch (`r₀ ∣ g_R`) Structure**:
On any linear Euler odd perfect number `N = q * m ^ 2` with `¬ q ∣ m`, the unique `q`-source `r₀`
satisfies `r₀ = 3 → q % 12 = 1`, and on Branch R1 (`r₀ ∣ g_R`):
- `r₀ % 4 = 1`, `5 ≤ r₀`, `r₀ ≠ 3`, and `q` is non-Fermat with an odd prime `l ≠ r₀` dividing
  `gcd (2 * e₀ + 1) ((q - 1) / 4)`;
- sharp upper bounds `C < r₀ ^ (2 * b)`, `A < r₀ ^ (I.factorization r₀)`,
  `q < 2 * r₀ ^ (I.factorization r₀)`, and doubled bounds when `Odd k_R`;
- valuation gap `k_R ≤ 2 * b`, `3 * k_R ≤ 2 * e₀`, `2 * k_R ≤ I.factorization r₀`, and
  `b = 1 → k_R = 1`. -/
theorem linear_euler_right_branch_structure {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2) :
    let A := (q + 1) / 2
    let I := componentIndex N q
    let L := Nat.factorizationLCMLeft A I
    let R := Nat.factorizationLCMRight A I
    let m_L := Nat.gcd m L
    let m_R := Nat.gcd m R
    ∃ h₀ u₀ g_L g_R r₀ : ℕ,
      A = g_L * g_R * h₀ ^ 2 ∧
      I = g_L * g_R * u₀ ^ 2 ∧
      m_L = g_L * h₀ ∧
      m_R = g_R * u₀ ∧
      r₀ ∈ m.primeFactors ∧
      q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀)) ∧
      ¬ r₀ ∣ m_L ∧
      r₀ ∣ m_R ∧
      r₀ ∣ u₀ ∧
      (r₀ = 3 → q % 12 = 1) ∧
      (r₀ ∣ g_R →
        let k_R := A.factorization r₀
        let b := u₀.factorization r₀
        let e₀ := m.factorization r₀
        let C := A / r₀ ^ k_R
        1 ≤ k_R ∧
        1 ≤ b ∧
        e₀ = k_R + b ∧
        I.factorization r₀ = k_R + 2 * b ∧
        r₀ % 4 = 1 ∧
        5 ≤ r₀ ∧
        r₀ ≠ 3 ∧
        (∃ l : ℕ, l.Prime ∧ Odd l ∧ l ∣ 2 * e₀ + 1 ∧ 4 * l ∣ q - 1 ∧ l ≠ r₀ ∧ 13 ≤ q) ∧
        C < r₀ ^ (2 * b) ∧
        A < r₀ ^ (I.factorization r₀) ∧
        q < 2 * r₀ ^ (I.factorization r₀) ∧
        (Odd k_R → 2 * C < r₀ ^ (2 * b) ∧ 2 * A < r₀ ^ (I.factorization r₀)) ∧
        k_R ≤ 2 * b ∧
        3 * k_R ≤ 2 * e₀ ∧
        2 * k_R ≤ I.factorization r₀ ∧
        (b = 1 → k_R = 1)) := by
  intro A I L R m_L m_R
  obtain ⟨h₀, u₀, g_L, g_R, r₀,
    hh0_odd, hu0_odd, hgL_odd, hgR_odd,
    _, _, _, _,
    _, _, _, _, _, _,
    hmL_eq, hmR_eq, hA_eq, hI_eq, hm_eq,
    hr₀_m, hq_dvd_r0, hr0_not_mL, hr0_mR, hr0_u0, _, _, _⟩ :=
    linear_euler_unique_source_right_forcing ho hN hq hqm hform
  change m_L = g_L * h₀ at hmL_eq
  change m_R = g_R * u₀ at hmR_eq
  change A = g_L * g_R * h₀ ^ 2 at hA_eq
  change I = g_L * g_R * u₀ ^ 2 at hI_eq
  change ¬ r₀ ∣ m_L at hr0_not_mL
  change r₀ ∣ m_R at hr0_mR
  have hq_odd : Odd q := ho.of_dvd_nat (hform ▸ dvd_mul_right q (m ^ 2))
  have hq1_eq : q + 1 = 2 * A := by
    change q + 1 = 2 * ((q + 1) / 2)
    obtain ⟨kq, hkq⟩ := hq_odd
    omega
  have hA_odd : Odd A := by
    rw [hA_eq]
    exact (hgL_odd.mul hgR_odd).mul hh0_odd.pow
  have hq4 : q % 4 = 1 := by
    obtain ⟨kA, hkA⟩ := hA_odd
    omega
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀_m
  have hm_odd : Odd m :=
    ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
  have hr₀_odd : Odd r₀ := hm_odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr₀_m)
  have h_mod4_of_gR : r₀ ∣ g_R → r₀ % 4 = 1 := by
    intro hr0_gR
    have hr0_A : r₀ ∣ A := by
      rw [hA_eq]
      exact (hr0_gR.trans (dvd_mul_left g_R g_L)).trans (dvd_mul_right _ (h₀ ^ 2))
    have hr0_q1 : r₀ ∣ q + 1 := hr0_A.trans ⟨2, by omega⟩
    have hr0_4cases : r₀ % 4 = 1 ∨ r₀ % 4 = 3 := by
      obtain ⟨kr, hkr⟩ := hr₀_odd
      omega
    rcases hr0_4cases with h1 | h3
    · exact h1
    · exfalso
      exact not_dvd_sigma_even_of_dvd_succ hq hr₀_prime hq4 h3 hr0_q1
        ⟨m.factorization r₀, by ring⟩ hq_dvd_r0
  have hr0_eq3_mod12 : r₀ = 3 → q % 12 = 1 := by
    intro hr0_3
    have h3_not_gR : ¬ 3 ∣ g_R := by
      intro h3gR
      have h1 : r₀ % 4 = 1 := h_mod4_of_gR (hr0_3 ▸ h3gR)
      omega
    have h3_not_mL : ¬ 3 ∣ m_L := hr0_3 ▸ hr0_not_mL
    have h3_not_gL : ¬ 3 ∣ g_L := fun hd => h3_not_mL (hmL_eq ▸ hd.trans (dvd_mul_right g_L h₀))
    have h3_not_h0 : ¬ 3 ∣ h₀ := fun hd => h3_not_mL (hmL_eq ▸ hd.trans (dvd_mul_left h₀ g_L))
    have h3_not_h02 : ¬ 3 ∣ h₀ ^ 2 := fun hd => h3_not_h0 (Nat.Prime.dvd_of_dvd_pow (by decide) hd)
    have h3_not_A : ¬ 3 ∣ A := by
      rw [hA_eq]
      intro hd
      rcases (Nat.Prime.dvd_mul (by decide : Nat.Prime 3)).mp hd with hg | hh
      · rcases (Nat.Prime.dvd_mul (by decide : Nat.Prime 3)).mp hg with hgL | hgR
        · exact h3_not_gL hgL
        · exact h3_not_gR hgR
      · exact h3_not_h02 hh
    have hA_mod3_ne0 : A % 3 ≠ 0 := mt Nat.dvd_of_mod_eq_zero h3_not_A
    have hA_mod3 : A % 3 = 1 ∨ A % 3 = 2 := by omega
    rcases hA_mod3 with hA1 | hA2
    · omega
    · exfalso
      have h3_dvd_q : 3 ∣ q := Nat.dvd_of_mod_eq_zero (by omega)
      have hq_eq3 : q = 3 := ((hq.eq_one_or_self_of_dvd 3 h3_dvd_q).resolve_left (by decide)).symm
      omega
  refine ⟨h₀, u₀, g_L, g_R, r₀,
    hA_eq, hI_eq, hmL_eq, hmR_eq,
    hr₀_m, hq_dvd_r0, hr0_not_mL, hr0_mR, hr0_u0,
    hr0_eq3_mod12, ?_⟩
  intro hr0_gR k_R b e₀ C
  have hgL0 : g_L ≠ 0 := hgL_odd.pos.ne'
  have hgR0 : g_R ≠ 0 := hgR_odd.pos.ne'
  have hh00 : h₀ ≠ 0 := hh0_odd.pos.ne'
  have hu00 : u₀ ≠ 0 := hu0_odd.pos.ne'
  have hr0_ndvd_gL : ¬ r₀ ∣ g_L := fun hd =>
    hr0_not_mL (hmL_eq ▸ hd.trans (dvd_mul_right g_L h₀))
  have hr0_ndvd_h0 : ¬ r₀ ∣ h₀ := fun hd =>
    hr0_not_mL (hmL_eq ▸ hd.trans (dvd_mul_left h₀ g_L))
  have hgL_zero : g_L.factorization r₀ = 0 := Nat.factorization_eq_zero_of_not_dvd hr0_ndvd_gL
  have hh0_zero : h₀.factorization r₀ = 0 := Nat.factorization_eq_zero_of_not_dvd hr0_ndvd_h0
  have hkR_eq : k_R = g_R.factorization r₀ := by
    dsimp [k_R]
    rw [hA_eq, Nat.factorization_mul (mul_ne_zero hgL0 hgR0) (pow_ne_zero 2 hh00),
      Finsupp.add_apply, Nat.factorization_mul hgL0 hgR0, Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hgL_zero, zero_add,
      hh0_zero, mul_zero, add_zero]
  have he0_eq : e₀ = k_R + b := by
    dsimp [e₀, b]
    rw [hkR_eq, hm_eq, Nat.factorization_mul (mul_ne_zero (mul_ne_zero hgL0 hgR0) hh00) hu00,
      Finsupp.add_apply, Nat.factorization_mul (mul_ne_zero hgL0 hgR0) hh00,
      Finsupp.add_apply, Nat.factorization_mul hgL0 hgR0, Finsupp.add_apply,
      hgL_zero, zero_add, hh0_zero, add_zero]
  have hI_fact : I.factorization r₀ = k_R + 2 * b := by
    dsimp [b]
    rw [hkR_eq, hI_eq, Nat.factorization_mul (mul_ne_zero hgL0 hgR0) (pow_ne_zero 2 hu00),
      Finsupp.add_apply, Nat.factorization_mul hgL0 hgR0, Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hgL_zero, zero_add]
  have hkR_pos : 1 ≤ k_R := by
    rw [hkR_eq]
    exact (hr₀_prime.dvd_iff_one_le_factorization hgR0).mp hr0_gR
  have hb_pos : 1 ≤ b :=
    (hr₀_prime.dvd_iff_one_le_factorization hu00).mp hr0_u0
  have hr0_mod4 : r₀ % 4 = 1 := h_mod4_of_gR hr0_gR
  have hr0_ge5 : 5 ≤ r₀ := by
    have := hr₀_prime.two_le
    omega
  have hr0_ne3 : r₀ ≠ 3 := by omega
  -- Claim 2: non-Fermat cyclotomic order forcing
  have hr0_dvd_A : r₀ ∣ A := by
    rw [hA_eq]
    exact (hr0_gR.trans (dvd_mul_left g_R g_L)).trans (dvd_mul_right _ (h₀ ^ 2))
  have h2r0_dvd_q1 : 2 * r₀ ∣ q + 1 := by
    rw [hq1_eq]
    exact Nat.mul_dvd_mul_left 2 hr0_dvd_A
  have h2r0_le_q1 : 2 * r₀ ≤ q + 1 := Nat.le_of_dvd (Nat.succ_pos q) h2r0_dvd_q1
  have hr0_lt_q : r₀ < q := by omega
  have hr0_mod_q_ne1 : r₀ % q ≠ 1 := by
    rw [Nat.mod_eq_of_lt hr0_lt_q]
    omega
  have hl_exists : ∃ l : ℕ, l.Prime ∧ Odd l ∧ l ∣ 2 * e₀ + 1 ∧ 4 * l ∣ q - 1 ∧ l ≠ r₀ ∧ 13 ≤ q := by
    obtain ⟨r₀', hr₀'_m, _, hq_dvd_r0', _, hdich⟩ :=
      linear_euler_unique_source_order_dichotomy ho hN hq hq4 hqm hform
    obtain ⟨_, _, _, _, _, _, _, huniq⟩ :=
      linear_euler_unique_q_source_and_bound ho hN hq hqm hform
    have hr_eq : r₀' = r₀ := (huniq r₀' hr₀'_m hq_dvd_r0').trans (huniq r₀ hr₀_m hq_dvd_r0).symm
    rw [hr_eq] at hdich
    rcases hdich with ⟨hr0q1, _⟩ | ⟨l, hl_prime, hl_odd, hl_dvd_exp, h4l_dvd, hq13⟩
    · exact False.elim (hr0_mod_q_ne1 hr0q1)
    · have hl_ne_r0 : l ≠ r₀ := by
        intro hlr
        rw [hlr] at h4l_dvd
        have hr0_dvd_qsub1 : r₀ ∣ q - 1 := (dvd_mul_left r₀ 4).trans h4l_dvd
        have hr0_dvd_qadd1 : r₀ ∣ q + 1 := hr0_dvd_A.trans ⟨2, by omega⟩
        obtain ⟨a, ha⟩ := hr0_dvd_qsub1
        obtain ⟨c, hc⟩ := hr0_dvd_qadd1
        have hrel : r₀ * c = r₀ * a + 2 := by omega
        have hac : a + 1 ≤ c := by nlinarith only [hrel, hr0_ge5]
        nlinarith only [hrel, hac, hr0_ge5]
      exact ⟨l, hl_prime, hl_odd, hl_dvd_exp, h4l_dvd, hl_ne_r0, hq13⟩
  -- Exact R1 Diophantine equations and bounds
  let X := r₀ ^ k_R
  have hX_dvd_A : X ∣ A := Nat.ordProj_dvd A r₀
  have hA_C : C * X = A := Nat.div_mul_cancel hX_dvd_A
  have hC_odd : Odd C := hA_odd.of_dvd_nat ⟨X, hA_C.symm⟩
  have hX_odd : Odd X := hr₀_odd.pow
  have hC_pos : 1 ≤ C := hC_odd.pos
  have hq1_eq_C : q + 1 = 2 * C * r₀ ^ k_R := by
    rw [hq1_eq, ← hA_C]
    change 2 * (C * X) = 2 * C * X
    ring
  let c₀ := sigma 1 (r₀ ^ (2 * e₀)) / q
  obtain ⟨hsig_eq, _, hc0_odd, _⟩ :=
    linear_euler_cofactor_quotient_structure_of_source ho hN hq hqm hform hr₀_m hq_dvd_r0
  have hc0_pos : 1 ≤ c₀ := hc0_odd.pos
  have hgeom : (r₀ - 1) * sigma 1 (r₀ ^ (2 * e₀)) + 1 = r₀ ^ (2 * e₀ + 1) := by
    rw [sigma_one_apply_prime_pow hr₀_prime, mul_comm]
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ r₀)] using
      geom_sum_mul_add (r₀ - 1) (2 * e₀ + 1)
  have hq_c0_pow : (r₀ - 1) * q * c₀ + 1 = r₀ ^ (2 * e₀ + 1) := by
    rw [← hgeom, hsig_eq]
    ring
  have hpow_split : r₀ ^ (2 * e₀ + 1) = r₀ ^ (2 * b + 1) * (r₀ ^ k_R) ^ 2 := by
    have hexp : 2 * e₀ + 1 = (2 * b + 1) + k_R * 2 := by omega
    rw [hexp, pow_add, pow_mul]
  have hq1_c0_pow : (r₀ - 1) * (q + 1) * c₀ + 1 = r₀ ^ (2 * e₀ + 1) + (r₀ - 1) * c₀ := by
    calc
      (r₀ - 1) * (q + 1) * c₀ + 1
          = ((r₀ - 1) * q * c₀ + 1) + (r₀ - 1) * c₀ := by ring
      _ = r₀ ^ (2 * e₀ + 1) + (r₀ - 1) * c₀ := by rw [hq_c0_pow]
  have hX_dvd_pow : X ∣ r₀ ^ (2 * e₀ + 1) := ⟨r₀ ^ (2 * b + 1) * X, by rw [hpow_split]; ring⟩
  obtain ⟨P, hP⟩ := hX_dvd_pow
  have hmod_eq : X * ((r₀ - 1) * 2 * C * c₀) + 1 = X * P + (r₀ - 1) * c₀ := by
    calc
      X * ((r₀ - 1) * 2 * C * c₀) + 1
          = (r₀ - 1) * (2 * C * X) * c₀ + 1 := by ring
      _ = (r₀ - 1) * (q + 1) * c₀ + 1 := by rw [← hq1_eq_C]
      _ = r₀ ^ (2 * e₀ + 1) + (r₀ - 1) * c₀ := hq1_c0_pow
      _ = X * P + (r₀ - 1) * c₀ := by rw [hP]
  have hmod1 : 1 ≡ (r₀ - 1) * c₀ [MOD X] := by
    have h1 : X * ((r₀ - 1) * 2 * C * c₀) + 1 ≡ 1 [MOD X] := Nat.ModEq.modulus_mul_add
    have h2 : X * P + (r₀ - 1) * c₀ ≡ (r₀ - 1) * c₀ [MOD X] := Nat.ModEq.modulus_mul_add
    rw [hmod_eq] at h1
    exact h1.symm.trans h2
  have h1_le : 1 ≤ (r₀ - 1) * c₀ := Nat.mul_pos (by omega) hc0_pos
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_exists_eq_add h1_le).mp hmod1
  have hr0_sub_mod : X ≡ 1 [MOD r₀ - 1] := by
    have hsub : r₀ ≡ 1 [MOD r₀ - 1] := Nat.modEq_sub (by omega : 1 ≤ r₀)
    simpa only [one_pow] using hsub.pow k_R
  have h1t_mod : 1 + X * t ≡ 1 + t [MOD r₀ - 1] := by
    have hXt := hr0_sub_mod.mul_right t
    rw [one_mul] at hXt
    exact hXt.add_left 1
  have hc0_mod_zero : 0 ≡ (r₀ - 1) * c₀ [MOD r₀ - 1] :=
    (Nat.modEq_zero_iff_dvd.mpr ⟨c₀, rfl⟩).symm
  have h0_mod_1t : 0 ≡ 1 + t [MOD r₀ - 1] := by
    rw [← ht] at h1t_mod
    exact hc0_mod_zero.trans h1t_mod
  have hdvd_1t : r₀ - 1 ∣ 1 + t := Nat.modEq_zero_iff_dvd.mp h0_mod_1t.symm
  obtain ⟨u, hu⟩ := hdvd_1t
  have hu_pos : 1 ≤ u := by
    by_contra hu0
    have hu_eq0 : u = 0 := by omega
    rw [hu_eq0, mul_zero] at hu
    omega
  have h_mul_u_ge1 : 1 ≤ (r₀ - 1) * u := Nat.mul_pos (by omega) hu_pos
  have ht_u : (r₀ - 1) * c₀ = 1 + ((r₀ - 1) * u - 1) * r₀ ^ k_R := by
    have ht_eq : t = (r₀ - 1) * u - 1 := by omega
    rw [ht, ht_eq, mul_comm X]
  have h_odd_kR_u : Odd k_R → 2 ≤ u := by
    intro hkR_odd
    let S := ∑ i ∈ Finset.range k_R, r₀ ^ i
    have hX_geom : (r₀ - 1) * S + 1 = X := by
      dsimp [S, X]
      rw [mul_comm]
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ r₀)] using geom_sum_mul_add (r₀ - 1) k_R
    let m_u := (r₀ - 1) * u - 1
    have hm_u : m_u + 1 = (r₀ - 1) * u := Nat.sub_add_cancel h_mul_u_ge1
    have h_cancel : (r₀ - 1) * (c₀ + S) = (r₀ - 1) * (u * X) := by
      calc
        (r₀ - 1) * (c₀ + S) = (r₀ - 1) * c₀ + (r₀ - 1) * S := by ring
        _ = (1 + m_u * X) + (r₀ - 1) * S := by rw [ht_u]
        _ = m_u * X + ((r₀ - 1) * S + 1) := by ring
        _ = m_u * X + X := by rw [hX_geom]
        _ = (m_u + 1) * X := by ring
        _ = (r₀ - 1) * u * X := by rw [hm_u]
        _ = (r₀ - 1) * (u * X) := by ring
    have hsum_eq : c₀ + S = u * X :=
      Nat.eq_of_mul_eq_mul_left (by omega : 0 < r₀ - 1) h_cancel
    have hsum_mod2 : S % 2 = k_R % 2 := sum_odd_pow_mod_two (Nat.odd_iff.mp hr₀_odd) k_R
    have hc0_mod2 : c₀ % 2 = 1 := Nat.odd_iff.mp hc0_odd
    have hkR_mod2 : k_R % 2 = 1 := Nat.odd_iff.mp hkR_odd
    have hX_mod2 : X % 2 = 1 := Nat.odd_iff.mp hX_odd
    have huX_mod2 : (u * X) % 2 = 0 := by
      rw [← hsum_eq, Nat.add_mod, hc0_mod2, hsum_mod2, hkR_mod2]
    have hu_mod2 : u % 2 = 0 := by
      rw [Nat.mul_mod, hX_mod2, mul_one, Nat.mod_mod] at huX_mod2
      exact huX_mod2
    omega
  have hpow_dioph : (r₀ - 1) * c₀ * q + 1 = r₀ ^ (2 * b + 1) * (r₀ ^ k_R) ^ 2 := by
    calc
      (r₀ - 1) * c₀ * q + 1 = (r₀ - 1) * q * c₀ + 1 := by ring
      _ = r₀ ^ (2 * e₀ + 1) := hq_c0_pow
      _ = r₀ ^ (2 * b + 1) * (r₀ ^ k_R) ^ 2 := hpow_split
  obtain ⟨hC_lt_B2, h2C_lt_B2, hkR_le_2b, hb1_kR1⟩ :=
    r1_diophantine_bounds hr0_ge5 hr₀_odd hkR_pos hb_pos hC_pos hu_pos h_odd_kR_u
      hq1_eq_C ht_u hpow_dioph
  have hA_lt_Ipow : A < r₀ ^ (I.factorization r₀) := by
    rw [hI_fact, ← hA_C, add_comm k_R (2 * b), pow_add]
    exact Nat.mul_lt_mul_of_pos_right hC_lt_B2 (pow_pos hr₀_prime.pos k_R)
  have hq_lt_2Ipow : q < 2 * r₀ ^ (I.factorization r₀) := by
    omega
  have h_odd_doubled : Odd k_R → 2 * C < r₀ ^ (2 * b) ∧ 2 * A < r₀ ^ (I.factorization r₀) := by
    intro hkR_odd
    have h2C_lt : 2 * C < r₀ ^ (2 * b) := h2C_lt_B2 hkR_odd
    have h2A_lt : 2 * A < r₀ ^ (I.factorization r₀) := by
      rw [hI_fact, ← hA_C, add_comm k_R (2 * b), pow_add, ← mul_assoc]
      exact Nat.mul_lt_mul_of_pos_right h2C_lt (pow_pos hr₀_prime.pos k_R)
    exact ⟨h2C_lt, h2A_lt⟩
  have h3kR_le_2e0 : 3 * k_R ≤ 2 * e₀ := by omega
  have h2kR_le_I : 2 * k_R ≤ I.factorization r₀ := by omega
  exact ⟨hkR_pos, hb_pos, he0_eq, hI_fact, hr0_mod4, hr0_ge5, hr0_ne3, hl_exists,
    hC_lt_B2, hA_lt_Ipow, hq_lt_2Ipow, h_odd_doubled, hkR_le_2b, h3kR_le_2e0, h2kR_le_I, hb1_kR1⟩

/-- **Corollary (`r₀ = 3 → q ≡ 1 [MOD 12]`)**:
Whenever the unique `q`-source of a linear Euler odd perfect number `N = q * m ^ 2` (`¬ q ∣ m`)
is `r₀ = 3`, we must have `q % 12 = 1`. -/
theorem linear_euler_r0_eq_three_mod_twelve {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (h3 : 3 ∈ m.primeFactors) (hq3 : q ∣ sigma 1 (3 ^ (2 * m.factorization 3))) :
    q % 12 = 1 := by
  obtain ⟨h₀, u₀, g_L, g_R, r₀, _, _, _, _, hr₀_m, hq_dvd_r0, _, _, _, h3_imp, _⟩ :=
    linear_euler_right_branch_structure ho hN hq hqm hform
  obtain ⟨_, _, _, _, _, _, _, huniq⟩ :=
    linear_euler_unique_q_source_and_bound ho hN hq hqm hform
  have hr₀_eq3 : r₀ = 3 := (huniq r₀ hr₀_m hq_dvd_r0).trans (huniq 3 h3 hq3).symm
  exact h3_imp hr₀_eq3

end OddPerfect
