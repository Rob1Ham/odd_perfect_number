module

public import OddPerfect.ZsqrtTwoModEightFrobenius
public import Mathlib.NumberTheory.Zsqrtd.ToReal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Archimedean & Frobenius Obstructions in `ℤ√2` (`OddPerfect.ZsqrtTwoArchimedeanObstruction`)

Combines the real embedding `toReal2 : ℤ√2 →+* ℝ` with the mod-`(8 * d)` Frobenius laws of
`OddPerfect.ZsqrtTwoModEightFrobenius` to establish sharp Archimedean coordinate bounds on
solutions `1 + y√2 = silverUnit ^ k * α ^ d` of `q ^ d + 1 = 2 * y ^ 2`:

1. `zsqrtTwo_toReal_add_and_sub_star` and `zsqrtTwo_toReal_mul_star_eq_norm`:
   exact conjugate sum/difference and norm identities under `toReal2`.
2. `zsqrtTwo_pos_coords_lower_bound_pow_im`:
   for `1 ≤ α.re`, `1 ≤ α.im`, and odd `d ≥ 3`, proves `(α ^ n).re ≥ α.re ^ n` and the sharp
   lower bound `2 + (d : ℤ) * α.re ^ (d - 1) * α.im ≤ (α ^ d).im`.
3. `silverUnit_four_cases`, `zsqrtTwo_fermat_k_neg_one_obstruction`, and
   `zsqrtTwo_fermat_k_pos_one_obstruction`:
   forces `1 ≤ |α.re|`, `1 ≤ |α.im|`, `2 * (d : ℤ) ^ 2 * α.im ^ 2 < α.re ^ 2`, and quartic lower
   bounds on `q` (`2 * (d ^ 2 - 1) * (d + 1) ^ 2 < q` for `k = -1` and
   `2 * (d ^ 2 - 1) * (d - 1) ^ 2 < q` for `k = 1`, under `(silverUnit : ℤ√2) = ⟨1, 1⟩`).
4. `exceptional_euler_toReal_silverUnit_bounds`, `exceptional_euler_toReal_abs_bounds`, and
   `exceptional_euler_unit_exponent_one_quartic_bound`:
   proves `0 < |(α.re : ℝ) + (α.im : ℝ) * Real.sqrt 2|` unconditionally (and
   `0 < (α.re : ℝ) + (α.im : ℝ) * Real.sqrt 2` under `(silverUnit : ℤ√2) = ⟨1, 1⟩`) for ALL `k`,
   and unconditionally derives the `|k| = 1` quartic floors (`147456 < q`, and
   `6690816000 < q` when `¬ 3 ∣ N ∧ ¬ 5 ∣ N`).
-/

public section

namespace OddPerfect

open ArithmeticFunction

/-- The real embedding `ℤ√2 →+* ℝ` sending `√2` to `Real.sqrt 2`. -/
@[expose] noncomputable def toReal2 : ℤ√2 →+* ℝ :=
  Zsqrtd.toReal (by decide : (0 : ℤ) ≤ 2)

/-! ## 1. Real Conjugate Sum/Difference and Norm Identities -/

/-- Exact real embedding identities for `α`, `star α`, `toReal2 α + toReal2 (star α)`, and
`toReal2 α - toReal2 (star α)`. -/
theorem zsqrtTwo_toReal_add_and_sub_star (α : ℤ√2) :
    toReal2 α = (α.re : ℝ) + (α.im : ℝ) * Real.sqrt 2 ∧
    toReal2 (star α) = (α.re : ℝ) - (α.im : ℝ) * Real.sqrt 2 ∧
    toReal2 α + toReal2 (star α) = 2 * (α.re : ℝ) ∧
    toReal2 α - toReal2 (star α) = 2 * (α.im : ℝ) * Real.sqrt 2 := by
  have h1 : toReal2 α = (α.re : ℝ) + (α.im : ℝ) * Real.sqrt 2 := by
    simp [toReal2, Zsqrtd.toReal_apply]
  have h2 : toReal2 (star α) = (α.re : ℝ) - (α.im : ℝ) * Real.sqrt 2 := by
    simp [toReal2, Zsqrtd.toReal_apply, sub_eq_add_neg]
  refine ⟨h1, h2, ?_, ?_⟩ <;> linarith

/-- Under `toReal2`, the product of `α` and `star α` equals `(α.norm : ℝ)`. -/
theorem zsqrtTwo_toReal_mul_star_eq_norm (α : ℤ√2) :
    toReal2 α * toReal2 (star α) = (α.norm : ℝ) := by
  rw [← map_mul, ← Zsqrtd.norm_eq_mul_conj, map_intCast]

/-- For odd `d`, `(x : ℝ) ^ d > 0 ↔ x > 0` and `(x : ℝ) ^ d < y ^ d ↔ x < y`. -/
theorem odd_real_pow_pos_and_lt_iff {d : ℕ} (hd : Odd d) (x y : ℝ) :
    (0 < x ^ d ↔ 0 < x) ∧ (x ^ d < y ^ d ↔ x < y) :=
  ⟨hd.pow_pos_iff, hd.strictMono_pow.lt_iff_lt⟩

/-! ## 2. Sharp Lower Bound on `(α ^ d).im` for Positive Coordinates -/

/-- For `α : ℤ√2` with `1 ≤ α.re` and `1 ≤ α.im`, all positive powers satisfy
`1 ≤ (α ^ n).re` and `1 ≤ (α ^ n).im`, and every `n : ℕ` satisfies `α.re ^ n ≤ (α ^ n).re`. -/
theorem zsqrtTwo_pos_coords_pow_bounds {α : ℤ√2} (hre : 1 ≤ α.re) (him : 1 ≤ α.im) :
    (∀ n : ℕ, 1 ≤ n → 1 ≤ (α ^ n).re ∧ 1 ≤ (α ^ n).im) ∧
    (∀ n : ℕ, α.re ^ n ≤ (α ^ n).re) := by
  have hpos : ∀ n : ℕ, 1 ≤ n → 1 ≤ (α ^ n).re ∧ 1 ≤ (α ^ n).im := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simpa using ⟨hre, him⟩
    | succ k hk ih =>
      rw [pow_succ, Zsqrtd.re_mul, Zsqrtd.im_mul]
      refine ⟨?_, ?_⟩ <;> nlinarith [ih.1, ih.2]
  have hre_pow : ∀ n : ℕ, α.re ^ n ≤ (α ^ n).re := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      by_cases hk0 : k = 0
      · subst hk0; simp
      · have hkim : 1 ≤ (α ^ k).im := (hpos k (Nat.pos_of_ne_zero hk0)).2
        rw [pow_succ, pow_succ, Zsqrtd.re_mul]
        nlinarith
  exact ⟨hpos, hre_pow⟩

/-- For `α : ℤ√2` with `1 ≤ α.re` and `1 ≤ α.im`, and every odd `d ≥ 3`,
`(α ^ d).im` satisfies the sharp lower bound `2 + (d : ℤ) * α.re ^ (d - 1) * α.im ≤ (α ^ d).im`
(together with `1 ≤ (α ^ n).re`, `1 ≤ (α ^ n).im`, and `α.re ^ n ≤ (α ^ n).re`). -/
theorem zsqrtTwo_pos_coords_lower_bound_pow_im {α : ℤ√2} (hre : 1 ≤ α.re) (him : 1 ≤ α.im)
    {d : ℕ} (hd_odd : Odd d) (hd3 : 3 ≤ d) :
    (∀ n : ℕ, 1 ≤ n → 1 ≤ (α ^ n).re ∧ 1 ≤ (α ^ n).im) ∧
    (∀ n : ℕ, α.re ^ n ≤ (α ^ n).re) ∧
    2 + (d : ℤ) * α.re ^ (d - 1) * α.im ≤ (α ^ d).im := by
  obtain ⟨hpos, hre_pow⟩ := zsqrtTwo_pos_coords_pow_bounds hre him
  refine ⟨hpos, hre_pow, ?_⟩
  obtain ⟨k, rfl⟩ := hd_odd
  have hk1 : 1 ≤ k := by omega
  induction k, hk1 using Nat.le_induction with
  | base =>
    have him3 : 1 ≤ α.im ^ 3 := one_le_pow₀ him
    have h3 : (α ^ (2 * 1 + 1)).im = 3 * α.re ^ 2 * α.im + 2 * α.im ^ 3 := by
      have hpow3 : α ^ (2 * 1 + 1) = α ^ 2 * α := by ring
      rw [hpow3, pow_two, Zsqrtd.im_mul, Zsqrtd.re_mul, Zsqrtd.im_mul]
      ring
    rw [h3]
    push_cast
    linarith
  | succ k hk ih =>
    set m : ℕ := 2 * k + 1
    have hm3 : 3 ≤ m := by omega
    have ih' : 2 + (m : ℤ) * α.re ^ (m - 1) * α.im ≤ (α ^ m).im := ih (by omega)
    have hpow_step : α ^ (2 * (k + 1) + 1) = α ^ m * α ^ 2 := by
      rw [show 2 * (k + 1) + 1 = m + 2 by omega, pow_add]
    have hre2 : (α ^ 2).re = α.re ^ 2 + 2 * α.im ^ 2 := by
      rw [pow_two, Zsqrtd.re_mul]
      ring
    have him2 : (α ^ 2).im = 2 * α.re * α.im := by
      rw [pow_two, Zsqrtd.im_mul]
      ring
    have hm_re : α.re ^ m ≤ (α ^ m).re := hre_pow m
    have hre_pow_ge1 : 1 ≤ α.re ^ 2 := by nlinarith
    have hpow_eq1 : α.re ^ (m + 1) = α.re ^ m * α.re := by
      rw [pow_succ]
    have hpow_eq2 : α.re ^ (m + 1) = α.re ^ (m - 1) * α.re ^ 2 := by
      rw [← pow_add, show m - 1 + 2 = m + 1 by omega]
    have h1 : α.re ^ m * (2 * α.re * α.im) ≤ (α ^ m).re * (2 * α.re * α.im) :=
      mul_le_mul_of_nonneg_right hm_re (by positivity)
    have h2 : (2 + (m : ℤ) * α.re ^ (m - 1) * α.im) * α.re ^ 2 ≤
        (α ^ m).im * (α.re ^ 2 + 2 * α.im ^ 2) := by
      have him_nonneg : 0 ≤ (α ^ m).im := by
        have := (hpos m (by omega)).2
        linarith
      calc
        (2 + (m : ℤ) * α.re ^ (m - 1) * α.im) * α.re ^ 2
            ≤ (α ^ m).im * α.re ^ 2 :=
          mul_le_mul_of_nonneg_right ih' (by positivity)
        _ ≤ (α ^ m).im * (α.re ^ 2 + 2 * α.im ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith [sq_nonneg α.im]) him_nonneg
    have him_step : (α ^ (2 * (k + 1) + 1)).im =
        (α ^ m).re * (2 * α.re * α.im) + (α ^ m).im * (α.re ^ 2 + 2 * α.im ^ 2) := by
      rw [hpow_step, Zsqrtd.im_mul, hre2, him2]
    have hsub_idx : 2 * (k + 1) + 1 - 1 = m + 1 := by omega
    have hcast_m : ((2 * (k + 1) + 1 : ℕ) : ℤ) = (m : ℤ) + 2 := by
      dsimp [m]
      ring
    rw [him_step, hsub_idx, hcast_m]
    calc
      2 + ((m : ℤ) + 2) * α.re ^ (m + 1) * α.im
          ≤ 2 * α.re ^ 2 + ((m : ℤ) + 2) * α.re ^ (m + 1) * α.im := by linarith
      _ = 2 * α.re ^ 2 + 2 * α.re ^ (m + 1) * α.im + (m : ℤ) * α.re ^ (m + 1) * α.im := by ring
      _ = 2 * α.re ^ 2 + 2 * (α.re ^ m * α.re) * α.im +
            (m : ℤ) * (α.re ^ (m - 1) * α.re ^ 2) * α.im := by
        rw [← hpow_eq1, ← hpow_eq2]
      _ = α.re ^ m * (2 * α.re * α.im) + (2 + (m : ℤ) * α.re ^ (m - 1) * α.im) * α.re ^ 2 := by
        ring
      _ ≤ (α ^ m).re * (2 * α.re * α.im) + (α ^ m).im * (α.re ^ 2 + 2 * α.im ^ 2) :=
        add_le_add h1 h2

/-! ## 3. Identification of `silverUnit` up to `±1` and Inversion -/

private def fundSilverUnit : (ℤ√2)ˣ :=
  ⟨⟨1, 1⟩, ⟨-1, 1⟩, by ext <;> simp, by ext <;> simp⟩

private lemma zsqrtTwo_unit_abs_toReal_ge (w : (ℤ√2)ˣ)
    (hgt : 1 < |toReal2 (w : ℤ√2)|) :
    1 + Real.sqrt 2 ≤ |toReal2 (w : ℤ√2)| ∧
      ((|toReal2 (w : ℤ√2)| = 1 + Real.sqrt 2) →
        (w : ℤ√2) = ⟨1, 1⟩ ∨ (w : ℤ√2) = ⟨-1, -1⟩) := by
  set a : ℤ := (w : ℤ√2).re
  set b : ℤ := (w : ℤ√2).im
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hnorm_unit : IsUnit (w : ℤ√2).norm := (Zsqrtd.isUnit_iff_norm_isUnit (w : ℤ√2)).mp w.isUnit
  have hnorm_pm : a ^ 2 - 2 * b ^ 2 = 1 ∨ a ^ 2 - 2 * b ^ 2 = -1 := by
    have h := Int.isUnit_iff.mp hnorm_unit
    rwa [show (w : ℤ√2).norm = a ^ 2 - 2 * b ^ 2 by simp [a, b, Zsqrtd.norm_def]; ring] at h
  have hb0 : b ≠ 0 := by
    intro hb
    rw [hb] at hnorm_pm
    have ha_sq : a ^ 2 = 1 := by
      rcases hnorm_pm with h1 | hm1
      · linarith
      · exfalso; nlinarith [sq_nonneg a]
    have ha_pm : a = 1 ∨ a = -1 := sq_eq_one_iff.mp ha_sq
    have hreal : toReal2 (w : ℤ√2) = (a : ℝ) := by
      rw [(zsqrtTwo_toReal_add_and_sub_star (w : ℤ√2)).1]
      change (a : ℝ) + (b : ℝ) * Real.sqrt 2 = (a : ℝ)
      rw [hb]
      simp
    rw [hreal] at hgt
    rcases ha_pm with h1 | hm1
    · rw [h1] at hgt; norm_num at hgt
    · rw [hm1] at hgt; norm_num at hgt
  have hb_abs : 1 ≤ |b| := Int.one_le_abs hb0
  have ha_sq : 1 ≤ a ^ 2 := by
    have hb_sq : 1 ≤ b ^ 2 := by nlinarith [sq_abs b]
    omega
  have ha_abs : 1 ≤ |a| := by
    refine Int.one_le_abs ?_
    intro h0
    rw [h0] at ha_sq
    norm_num at ha_sq
  have hreal_eq : toReal2 (w : ℤ√2) = (a : ℝ) + (b : ℝ) * Real.sqrt 2 :=
    (zsqrtTwo_toReal_add_and_sub_star (w : ℤ√2)).1
  have habs_a_real : (1 : ℝ) ≤ (|a| : ℝ) := by exact_mod_cast ha_abs
  have habs_b_real : (1 : ℝ) ≤ (|b| : ℝ) := by exact_mod_cast hb_abs
  have hsum_ge : 1 + Real.sqrt 2 ≤ (|a| : ℝ) + (|b| : ℝ) * Real.sqrt 2 := by nlinarith
  have hprod_abs : ((|a| : ℝ) + (|b| : ℝ) * Real.sqrt 2) *
      |(|a| : ℝ) - (|b| : ℝ) * Real.sqrt 2| = 1 := by
    have hsq : ((|a| : ℝ) + (|b| : ℝ) * Real.sqrt 2) * ((|a| : ℝ) - (|b| : ℝ) * Real.sqrt 2) =
        ((a ^ 2 - 2 * b ^ 2 : ℤ) : ℝ) := by
      push_cast
      have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      have ha2 : |(a : ℝ)| ^ 2 = (a : ℝ) ^ 2 := sq_abs (a : ℝ)
      have hb2 : |(b : ℝ)| ^ 2 = (b : ℝ) ^ 2 := sq_abs (b : ℝ)
      nlinarith
    have hpos_sum : 0 < (|a| : ℝ) + (|b| : ℝ) * Real.sqrt 2 := by positivity
    rw [← abs_of_pos hpos_sum, ← abs_mul, hsq]
    rcases hnorm_pm with h1 | hm1
    · rw [h1]; norm_num
    · rw [hm1]; norm_num
  have hdiff_lt_one : |(|a| : ℝ) - (|b| : ℝ) * Real.sqrt 2| < 1 := by
    have hsum_gt1 : 1 < (|a| : ℝ) + (|b| : ℝ) * Real.sqrt 2 := by linarith
    nlinarith [abs_nonneg ((|a| : ℝ) - (|b| : ℝ) * Real.sqrt 2)]
  have hsame_sign : (0 ≤ a ∧ 0 ≤ b) ∨ (a ≤ 0 ∧ b ≤ 0) := by
    rcases le_total 0 a with ha0 | ha0 <;> rcases le_total 0 b with hb0' | hb0'
    · exact Or.inl ⟨ha0, hb0'⟩
    · exfalso
      have h1 : (|a| : ℝ) = (a : ℝ) := by exact_mod_cast abs_of_nonneg ha0
      have h2 : (|b| : ℝ) = -(b : ℝ) := by exact_mod_cast abs_of_nonpos hb0'
      have heq : |toReal2 (w : ℤ√2)| = |(|a| : ℝ) - (|b| : ℝ) * Real.sqrt 2| := by
        rw [hreal_eq, h1, h2]
        ring_nf
      linarith
    · exfalso
      have h1 : (|a| : ℝ) = -(a : ℝ) := by exact_mod_cast abs_of_nonpos ha0
      have h2 : (|b| : ℝ) = (b : ℝ) := by exact_mod_cast abs_of_nonneg hb0'
      have heq : |toReal2 (w : ℤ√2)| = |(|a| : ℝ) - (|b| : ℝ) * Real.sqrt 2| := by
        rw [hreal_eq, h1, h2, ← abs_neg]
        ring_nf
      linarith
    · exact Or.inr ⟨ha0, hb0'⟩
  have habs_val : |toReal2 (w : ℤ√2)| = (|a| : ℝ) + (|b| : ℝ) * Real.sqrt 2 := by
    rcases hsame_sign with ⟨ha0, hb0'⟩ | ⟨ha0, hb0'⟩
    · have h1 : (|a| : ℝ) = (a : ℝ) := by exact_mod_cast abs_of_nonneg ha0
      have h2 : (|b| : ℝ) = (b : ℝ) := by exact_mod_cast abs_of_nonneg hb0'
      rw [hreal_eq, abs_of_nonneg (by positivity), h1, h2]
    · have ha_le : (a : ℝ) ≤ 0 := by exact_mod_cast ha0
      have hb_le : (b : ℝ) ≤ 0 := by exact_mod_cast hb0'
      have h1 : (|a| : ℝ) = -(a : ℝ) := by exact_mod_cast abs_of_nonpos ha0
      have h2 : (|b| : ℝ) = -(b : ℝ) := by exact_mod_cast abs_of_nonpos hb0'
      rw [hreal_eq, ← abs_neg, abs_of_nonneg (by nlinarith), h1, h2]
      ring
  refine ⟨habs_val ▸ hsum_ge, ?_⟩
  intro heq
  rw [habs_val] at heq
  have ha_eq : |a| = 1 := by
    have : ((|a| : ℝ) - 1) + ((|b| : ℝ) - 1) * Real.sqrt 2 = 0 := by linarith
    have hna : 0 ≤ (|a| : ℝ) - 1 := by linarith
    have hnb : 0 ≤ ((|b| : ℝ) - 1) * Real.sqrt 2 := by nlinarith
    have ha1 : (|a| : ℝ) = 1 := by linarith
    exact_mod_cast ha1
  have hb_eq : |b| = 1 := by
    have : ((|a| : ℝ) - 1) + ((|b| : ℝ) - 1) * Real.sqrt 2 = 0 := by linarith
    have hna : 0 ≤ (|a| : ℝ) - 1 := by linarith
    have hnb : 0 ≤ ((|b| : ℝ) - 1) * Real.sqrt 2 := by nlinarith
    have hb1 : ((|b| : ℝ) - 1) * Real.sqrt 2 = 0 := by linarith
    rcases mul_eq_zero.mp hb1 with h | h
    · exact_mod_cast (show (|b| : ℝ) = 1 by linarith)
    · linarith
  rcases hsame_sign with ⟨ha0, hb0'⟩ | ⟨ha0, hb0'⟩
  · have ha1 : a = 1 := by linarith [abs_of_nonneg ha0]
    have hb1 : b = 1 := by linarith [abs_of_nonneg hb0']
    left
    ext
    · exact ha1
    · exact hb1
  · have ham1 : a = -1 := by linarith [abs_of_nonpos ha0]
    have hbm1 : b = -1 := by linarith [abs_of_nonpos hb0']
    right
    ext
    · exact ham1
    · exact hbm1

/-- Because `silverUnit` generates `(ℤ√2)ˣ / {±1}` via `zsqrtTwo_unit_eq_silverUnit_zpow`,
`(silverUnit : ℤ√2)` must be one of `±(1 + √2)` or `±(-1 + √2)`. -/
theorem silverUnit_four_cases :
    (silverUnit : ℤ√2) = ⟨1, 1⟩ ∨
    (silverUnit : ℤ√2) = ⟨-1, -1⟩ ∨
    (silverUnit : ℤ√2) = ⟨-1, 1⟩ ∨
    (silverUnit : ℤ√2) = ⟨1, -1⟩ := by
  obtain ⟨n, hn⟩ := zsqrtTwo_unit_eq_silverUnit_zpow fundSilverUnit
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hfund_real : toReal2 (fundSilverUnit : ℤ√2) = 1 + Real.sqrt 2 := by
    rw [(zsqrtTwo_toReal_add_and_sub_star (fundSilverUnit : ℤ√2)).1]
    simp [fundSilverUnit]
  have hfund_abs : |toReal2 (fundSilverUnit : ℤ√2)| = 1 + Real.sqrt 2 := by
    rw [hfund_real, abs_of_pos (by positivity)]
  set v : (ℤ√2)ˣ := if 0 ≤ n then silverUnit else silverUnit⁻¹
  set m : ℕ := n.natAbs
  have hv_pow : fundSilverUnit = v ^ m ∨ fundSilverUnit = -(v ^ m) := by
    have hvm : silverUnit ^ n = v ^ m := by
      by_cases hn0 : 0 ≤ n
      · simp only [v, hn0, ↓reduceIte, m]
        rw [← zpow_natCast, Int.natAbs_of_nonneg hn0]
      · have hn_neg : n < 0 := lt_of_not_ge hn0
        simp only [v, hn0, ↓reduceIte]
        have hn_eq : n = -((m : ℤ)) := by
          dsimp [m]
          omega
        rw [hn_eq, zpow_neg, zpow_natCast, inv_pow]
    rcases hn with h | h
    · exact Or.inl (h.trans hvm)
    · exact Or.inr (h.trans (congrArg Neg.neg hvm))
  have hm_real : |toReal2 (v : ℤ√2)| ^ m = 1 + Real.sqrt 2 := by
    rcases hv_pow with h | h <;>
    · have h' := congrArg (fun x : (ℤ√2)ˣ => |toReal2 (x : ℤ√2)|) h
      simpa [hfund_abs, Units.val_neg, Units.val_pow_eq_pow_val, map_neg, map_pow, abs_neg,
        abs_pow] using h'.symm
  have hm0 : m ≠ 0 := by
    intro hm
    rw [hm, pow_zero] at hm_real
    linarith
  have hgt1 : 1 < |toReal2 (v : ℤ√2)| := by
    by_contra! hle1
    have hpow_le : |toReal2 (v : ℤ√2)| ^ m ≤ 1 := pow_le_one₀ (abs_nonneg _) hle1
    linarith
  obtain ⟨hge_silv, hv_cases⟩ := zsqrtTwo_unit_abs_toReal_ge v hgt1
  have hm1 : m = 1 := by
    by_contra hm_ne1
    have hm2 : 2 ≤ m := by omega
    have hpow2 : (1 + Real.sqrt 2) ^ 2 ≤ |toReal2 (v : ℤ√2)| ^ m := by
      calc
        (1 + Real.sqrt 2) ^ 2 ≤ |toReal2 (v : ℤ√2)| ^ 2 :=
          pow_le_pow_left₀ (by positivity) hge_silv 2
        _ ≤ |toReal2 (v : ℤ√2)| ^ m :=
          pow_le_pow_right₀ (by linarith) hm2
    have hsq2 : (1 + Real.sqrt 2) ^ 2 = 3 + 2 * Real.sqrt 2 := by
      have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      nlinarith
    linarith
  rw [hm1, pow_one] at hm_real
  rcases hv_cases hm_real with hv1 | hvm1
  · by_cases hn0 : 0 ≤ n
    · simp only [v, hn0, ↓reduceIte] at hv1
      exact Or.inl hv1
    · simp only [v, hn0, ↓reduceIte] at hv1
      have hmul : (silverUnit : ℤ√2) * ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [hv1] at hmul
      have hinv : (silverUnit : ℤ√2) = ⟨-1, 1⟩ := by
        have h2 : (⟨-1, 1⟩ : ℤ√2) * ⟨1, 1⟩ = 1 := by ext <;> simp
        calc
          (silverUnit : ℤ√2) = (silverUnit : ℤ√2) * 1 := (mul_one _).symm
          _ = (silverUnit : ℤ√2) * (⟨1, 1⟩ * ⟨-1, 1⟩) := by
            rw [mul_comm (⟨1, 1⟩ : ℤ√2), h2]
          _ = ((silverUnit : ℤ√2) * ⟨1, 1⟩) * ⟨-1, 1⟩ := (mul_assoc _ _ _).symm
          _ = 1 * ⟨-1, 1⟩ := by rw [hmul]
          _ = ⟨-1, 1⟩ := one_mul _
      exact Or.inr (Or.inr (Or.inl hinv))
  · by_cases hn0 : 0 ≤ n
    · simp only [v, hn0, ↓reduceIte] at hvm1
      exact Or.inr (Or.inl hvm1)
    · simp only [v, hn0, ↓reduceIte] at hvm1
      have hmul : (silverUnit : ℤ√2) * ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [hvm1] at hmul
      have hinv : (silverUnit : ℤ√2) = ⟨1, -1⟩ := by
        have h2 : (⟨1, -1⟩ : ℤ√2) * ⟨-1, -1⟩ = 1 := by ext <;> simp
        calc
          (silverUnit : ℤ√2) = (silverUnit : ℤ√2) * 1 := (mul_one _).symm
          _ = (silverUnit : ℤ√2) * (⟨-1, -1⟩ * ⟨1, -1⟩) := by
            rw [mul_comm (⟨-1, -1⟩ : ℤ√2), h2]
          _ = ((silverUnit : ℤ√2) * ⟨-1, -1⟩) * ⟨1, -1⟩ := (mul_assoc _ _ _).symm
          _ = 1 * ⟨1, -1⟩ := by rw [hmul]
          _ = ⟨1, -1⟩ := one_mul _
      exact Or.inr (Or.inr (Or.inr hinv))

/-! ## 4. Archimedean + Frobenius Obstructions at `|k| = 1` -/

private lemma zsqrtTwo_pos_beta_sign_extraction {q d : ℕ} (hq : q.Prime) (hd_odd : Odd d)
    (β : ℤ√2) (hnorm : β.norm = (q : ℤ))
    (hpow_pos : 0 < toReal2 (β ^ d)) (hpow_diff_pos : 0 < toReal2 (β ^ d) - toReal2 (star (β ^ d))) :
    1 ≤ β.re ∧ 1 ≤ β.im := by
  have hreal_pow : toReal2 (β ^ d) = (toReal2 β) ^ d := map_pow toReal2 β d
  have hstar_pow : toReal2 (star (β ^ d)) = (toReal2 (star β)) ^ d := by
    rw [star_pow, map_pow]
  have hpos_beta : 0 < toReal2 β :=
    hd_odd.pow_pos_iff.mp (hreal_pow ▸ hpow_pos)
  have hnorm_pow_pos : (0 : ℝ) < ((β ^ d).norm : ℝ) := by
    have hnp : (β ^ d).norm = β.norm ^ d := map_pow Zsqrtd.normMonoidHom β d
    rw [hnp, hnorm]
    exact_mod_cast pow_pos hq.pos d
  have hmul_pos : 0 < toReal2 (β ^ d) * toReal2 (star (β ^ d)) := by
    rw [zsqrtTwo_toReal_mul_star_eq_norm]
    exact hnorm_pow_pos
  have hstar_pow_pos : 0 < toReal2 (star (β ^ d)) :=
    pos_of_mul_pos_right hmul_pos hpow_pos.le
  have hpos_star_beta : 0 < toReal2 (star β) :=
    hd_odd.pow_pos_iff.mp (hstar_pow ▸ hstar_pow_pos)
  have hlt_pow : (toReal2 (star β)) ^ d < (toReal2 β) ^ d := by
    rw [← hstar_pow, ← hreal_pow]
    linarith
  have hlt_beta : toReal2 (star β) < toReal2 β :=
    hd_odd.strictMono_pow.lt_iff_lt.mp hlt_pow
  obtain ⟨_, _, hadd, hsub⟩ := zsqrtTwo_toReal_add_and_sub_star β
  have hre_real : (0 : ℝ) < (β.re : ℝ) := by linarith
  have him_sqrt : (0 : ℝ) < (β.im : ℝ) * Real.sqrt 2 := by linarith
  have him_real : (0 : ℝ) < (β.im : ℝ) :=
    pos_of_mul_pos_left him_sqrt (Real.sqrt_pos.mpr (by norm_num)).le
  have hre_int : (0 : ℤ) < β.re := Int.cast_pos.mp hre_real
  have him_int : (0 : ℤ) < β.im := Int.cast_pos.mp him_real
  exact ⟨by omega, by omega⟩

private lemma zsqrtTwo_archimedean_sq_ineq {q d y : ℕ} (hd3 : 3 ≤ d)
    (hpow : q ^ d + 1 = 2 * y ^ 2) {β : ℤ√2} (hre : 1 ≤ β.re) (him : 1 ≤ β.im)
    (hnorm : β.norm = (q : ℤ)) (hbd : (d : ℤ) * β.re ^ (d - 1) * β.im < (y : ℤ)) :
    2 * (d : ℤ) ^ 2 * β.im ^ 2 < β.re ^ 2 := by
  have hd_pos : (0 : ℤ) < d := by omega
  have hre_pos : (0 : ℤ) < β.re := by omega
  have him_pos : (0 : ℤ) < β.im := by omega
  have hlhs_pos : 0 < (d : ℤ) * β.re ^ (d - 1) * β.im := by positivity
  have hsq_lt : ((d : ℤ) * β.re ^ (d - 1) * β.im) ^ 2 < (y : ℤ) ^ 2 := by
    nlinarith
  have h2sq_lt : 2 * ((d : ℤ) * β.re ^ (d - 1) * β.im) ^ 2 < 2 * (y : ℤ) ^ 2 := by
    linarith
  have hpow_z : (q : ℤ) ^ d + 1 = 2 * (y : ℤ) ^ 2 := by
    exact_mod_cast hpow
  have hnorm_eq : (q : ℤ) = β.re ^ 2 - 2 * β.im ^ 2 := by
    rw [← hnorm, Zsqrtd.norm_def]
    ring
  have hq_lt_re2 : (q : ℤ) < β.re ^ 2 := by
    have him2 : 1 ≤ β.im ^ 2 := by nlinarith
    linarith
  have hq_nonneg : (0 : ℤ) ≤ (q : ℤ) := Int.natCast_nonneg q
  have hqd_lt : (q : ℤ) ^ d < (β.re ^ 2) ^ d :=
    pow_lt_pow_left₀ hq_lt_re2 hq_nonneg (by omega)
  have hqd1_le : (q : ℤ) ^ d + 1 ≤ (β.re ^ 2) ^ d := by
    omega
  have h2d_split : (β.re ^ 2) ^ d = β.re ^ (2 * d - 2) * β.re ^ 2 := by
    rw [← pow_mul, ← pow_add, show 2 * d - 2 + 2 = 2 * d by omega]
  have hmul_lt : β.re ^ (2 * d - 2) * (2 * (d : ℤ) ^ 2 * β.im ^ 2) <
      β.re ^ (2 * d - 2) * β.re ^ 2 := by
    have hexp : ((d : ℤ) * β.re ^ (d - 1) * β.im) ^ 2 =
        (d : ℤ) ^ 2 * β.re ^ (2 * d - 2) * β.im ^ 2 := by
      rw [mul_pow, mul_pow, ← pow_mul, show (d - 1) * 2 = 2 * d - 2 by omega]
    calc
      β.re ^ (2 * d - 2) * (2 * (d : ℤ) ^ 2 * β.im ^ 2)
          = 2 * ((d : ℤ) * β.re ^ (d - 1) * β.im) ^ 2 := by rw [hexp]; ring
      _ < 2 * (y : ℤ) ^ 2 := h2sq_lt
      _ = (q : ℤ) ^ d + 1 := hpow_z.symm
      _ ≤ (β.re ^ 2) ^ d := hqd1_le
      _ = β.re ^ (2 * d - 2) * β.re ^ 2 := h2d_split
  have hpow_re_pos : 0 < β.re ^ (2 * d - 2) := pow_pos hre_pos _
  exact lt_of_mul_lt_mul_left hmul_lt hpow_re_pos.le

private lemma zsqrtTwo_quartic_from_sq_ineq {q d : ℕ} (hd3 : 3 ≤ d) {α : ℤ√2}
    (hnorm : α.norm = (q : ℤ)) (hsq : 2 * (d : ℤ) ^ 2 * α.im ^ 2 < α.re ^ 2)
    {m : ℕ} (hm_le : (m : ℤ) ≤ |α.im|) :
    2 * (d ^ 2 - 1) * m ^ 2 < q := by
  have hnorm_eq : (q : ℤ) = α.re ^ 2 - 2 * α.im ^ 2 := by
    rw [← hnorm, Zsqrtd.norm_def]
    ring
  have h1 : 2 * ((d : ℤ) ^ 2 - 1) * α.im ^ 2 < (q : ℤ) := by
    linarith
  have hm_sq : ((m : ℤ)) ^ 2 ≤ α.im ^ 2 := by
    have habs_sq : |α.im| ^ 2 = α.im ^ 2 := sq_abs α.im
    rw [← habs_sq]
    exact sq_le_sq' (by linarith [Int.natCast_nonneg m]) hm_le
  have hd2_nonneg : 0 ≤ (d : ℤ) ^ 2 - 1 := by
    have : (3 : ℤ) ≤ d := by exact_mod_cast hd3
    nlinarith
  have h2 : 2 * ((d : ℤ) ^ 2 - 1) * (m : ℤ) ^ 2 ≤ 2 * ((d : ℤ) ^ 2 - 1) * α.im ^ 2 :=
    mul_le_mul_of_nonneg_left hm_sq (by linarith)
  have hlt_z : 2 * ((d : ℤ) ^ 2 - 1) * (m : ℤ) ^ 2 < (q : ℤ) := lt_of_le_of_lt h2 h1
  have hcast : ((2 * (d ^ 2 - 1) * m ^ 2 : ℕ) : ℤ) = 2 * ((d : ℤ) ^ 2 - 1) * (m : ℤ) ^ 2 := by
    have hd2 : 1 ≤ d ^ 2 := by nlinarith
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hd2, Nat.cast_pow, Nat.cast_pow,
      Nat.cast_one]
  exact Int.ofNat_lt.mp (hcast ▸ hlt_z)

private lemma zsqrtTwo_explicit_neg_one_obstruction {q d y : ℕ}
    (hq : q.Prime) (hd_odd : Odd d) (hd3 : 3 ≤ d) (hpow : q ^ d + 1 = 2 * y ^ 2)
    {α : ℤ√2}
    (hpow_coord : α ^ d = ⟨2 * (y : ℤ) + 1, (y : ℤ) + 1⟩)
    (hnorm : α.norm = (q : ℤ)) :
    1 ≤ α.re ∧
    1 ≤ α.im ∧
    2 * (d : ℤ) ^ 2 * α.im ^ 2 < α.re ^ 2 ∧
    (Even α.im → α.im ≡ 1 [ZMOD (d : ℤ)] →
      (d : ℤ) + 1 ≤ α.im ∧ 2 * (d ^ 2 - 1) * (d + 1) ^ 2 < q) := by
  have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hy_nonneg : (0 : ℝ) ≤ y := Nat.cast_nonneg y
  obtain ⟨hreal_pow, _, _, hsub_pow⟩ := zsqrtTwo_toReal_add_and_sub_star (α ^ d)
  have hpow_pos : 0 < toReal2 (α ^ d) := by
    rw [hreal_pow, hpow_coord]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_one]
    nlinarith
  have hpow_diff_pos : 0 < toReal2 (α ^ d) - toReal2 (star (α ^ d)) := by
    rw [hsub_pow, hpow_coord]
    simp only [Int.cast_add, Int.cast_natCast, Int.cast_one]
    nlinarith
  obtain ⟨hre, him⟩ := zsqrtTwo_pos_beta_sign_extraction hq hd_odd α hnorm hpow_pos hpow_diff_pos
  have him_bound := (zsqrtTwo_pos_coords_lower_bound_pow_im hre him hd_odd hd3).2.2
  have him_lt : (d : ℤ) * α.re ^ (d - 1) * α.im < (y : ℤ) := by
    have hpow_im : (α ^ d).im = (y : ℤ) + 1 := by rw [hpow_coord]
    linarith
  have hsq := zsqrtTwo_archimedean_sq_ineq hd3 hpow hre him hnorm him_lt
  refine ⟨hre, him, hsq, ?_⟩
  intro hev hmod
  obtain ⟨t, ht⟩ := Int.modEq_iff_add_fac.mp hmod.symm
  have hd_pos : (0 : ℤ) < d := by omega
  have ht_pos : 1 ≤ t := by
    by_contra! ht0
    have hdt : (d : ℤ) * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hd_pos.le (by omega)
    have him1 : α.im = 1 := by linarith
    rw [him1] at hev
    exact (by decide : ¬ Even (1 : ℤ)) hev
  have hd1_le : (d : ℤ) + 1 ≤ α.im := by
    have : (d : ℤ) * 1 ≤ (d : ℤ) * t := mul_le_mul_of_nonneg_left ht_pos hd_pos.le
    linarith
  have habs_le : ((d + 1 : ℕ) : ℤ) ≤ |α.im| := by
    rw [abs_of_nonneg (by omega)]
    push_cast
    exact hd1_le
  exact ⟨hd1_le, zsqrtTwo_quartic_from_sq_ineq hd3 hnorm hsq habs_le⟩

private lemma zsqrtTwo_explicit_pos_one_obstruction {q d y : ℕ}
    (hq : q.Prime) (hd_odd : Odd d) (hd3 : 3 ≤ d) (hpow : q ^ d + 1 = 2 * y ^ 2)
    {α : ℤ√2}
    (hpow_coord : α ^ d = ⟨2 * (y : ℤ) - 1, 1 - (y : ℤ)⟩)
    (hnorm : α.norm = (q : ℤ)) :
    (star α) ^ d = ⟨2 * (y : ℤ) - 1, (y : ℤ) - 1⟩ ∧
    1 ≤ α.re ∧
    α.im ≤ -1 ∧
    2 * (d : ℤ) ^ 2 * α.im ^ 2 < α.re ^ 2 ∧
    (α.im ≡ 1 [ZMOD (d : ℤ)] →
      (d : ℤ) - 1 ≤ -α.im ∧ 2 * (d ^ 2 - 1) * (d - 1) ^ 2 < q) := by
  have hy2 : 2 ≤ y := by
    have hq2 : 2 ≤ q := hq.two_le
    have hqd : 8 ≤ q ^ d := by
      have : 2 ^ 3 ≤ q ^ d :=
        (Nat.pow_le_pow_left hq2 3).trans (Nat.pow_le_pow_right (by omega) hd3)
      omega
    nlinarith
  set β : ℤ√2 := star α
  have hbeta_pow : β ^ d = ⟨2 * (y : ℤ) - 1, (y : ℤ) - 1⟩ := by
    dsimp [β]
    rw [← star_pow, hpow_coord]
    ext <;> simp
  have hbeta_norm : β.norm = (q : ℤ) := by
    dsimp [β]
    rw [Zsqrtd.norm_conj, hnorm]
  have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hy_ge2 : (2 : ℝ) ≤ y := by exact_mod_cast hy2
  obtain ⟨hreal_pow, _, _, hsub_pow⟩ := zsqrtTwo_toReal_add_and_sub_star (β ^ d)
  have hpow_pos : 0 < toReal2 (β ^ d) := by
    rw [hreal_pow, hbeta_pow]
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_one]
    nlinarith
  have hpow_diff_pos : 0 < toReal2 (β ^ d) - toReal2 (star (β ^ d)) := by
    rw [hsub_pow, hbeta_pow]
    simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one]
    nlinarith
  obtain ⟨hre_b, him_b⟩ :=
    zsqrtTwo_pos_beta_sign_extraction hq hd_odd β hbeta_norm hpow_pos hpow_diff_pos
  have hre : 1 ≤ α.re := hre_b
  have him : α.im ≤ -1 := by
    have : 1 ≤ -α.im := him_b
    omega
  have him_bound := (zsqrtTwo_pos_coords_lower_bound_pow_im hre_b him_b hd_odd hd3).2.2
  have him_lt : (d : ℤ) * β.re ^ (d - 1) * β.im < (y : ℤ) := by
    have hpow_im : (β ^ d).im = (y : ℤ) - 1 := by rw [hbeta_pow]
    linarith
  have hsq_b := zsqrtTwo_archimedean_sq_ineq hd3 hpow hre_b him_b hbeta_norm him_lt
  have hsq : 2 * (d : ℤ) ^ 2 * α.im ^ 2 < α.re ^ 2 := by
    simpa [β] using hsq_b
  refine ⟨hbeta_pow, hre, him, hsq, ?_⟩
  intro hmod
  have hdvd : (d : ℤ) ∣ -α.im + 1 := by
    have h1 : -α.im + 1 ≡ 0 [ZMOD (d : ℤ)] := by
      have := hmod.neg.add_right 1
      simpa using this
    exact Int.modEq_zero_iff_dvd.mp h1
  have hpos_neg : 0 < -α.im + 1 := by omega
  have hd_le : (d : ℤ) ≤ -α.im + 1 := Int.le_of_dvd hpos_neg hdvd
  have hdm1_le : (d : ℤ) - 1 ≤ -α.im := by omega
  have habs_le : ((d - 1 : ℕ) : ℤ) ≤ |α.im| := by
    rw [abs_of_nonpos (by omega), Nat.cast_sub (by omega), Nat.cast_one]
    exact hdm1_le
  exact ⟨hdm1_le, zsqrtTwo_quartic_from_sq_ineq hd3 hnorm hsq habs_le⟩

/-- Archimedean + Frobenius obstruction at unit exponent `k = -1`:
forces `1 ≤ α.re`, `1 ≤ α.im`, `2 * (d : ℤ) ^ 2 * α.im ^ 2 < α.re ^ 2`, and (when `Even α.im`
and `α.im ≡ 1 [ZMOD d]`) forces `d + 1 ≤ α.im` and `2 * (d ^ 2 - 1) * (d + 1) ^ 2 < q`. -/
theorem zsqrtTwo_fermat_k_neg_one_obstruction
    {q d y : ℕ}
    (hq : q.Prime) (hd_odd : Odd d) (hd3 : 3 ≤ d) (hpow : q ^ d + 1 = 2 * y ^ 2)
    {α : ℤ√2}
    (hz : (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ (-1 : ℤ) : (ℤ√2)ˣ) : ℤ√2) * α ^ d)
    (hnorm : α.norm = (q : ℤ)) :
    α ^ d = ⟨2 * (y : ℤ) + 1, (y : ℤ) + 1⟩ ∧
    1 ≤ α.re ∧
    1 ≤ α.im ∧
    2 * (d : ℤ) ^ 2 * α.im ^ 2 < α.re ^ 2 ∧
    (Even α.im → α.im ≡ 1 [ZMOD (d : ℤ)] →
      (d : ℤ) + 1 ≤ α.im ∧ 2 * (d ^ 2 - 1) * (d + 1) ^ 2 < q) := by
  have hsu : (silverUnit : ℤ√2) = ⟨1, 1⟩ := silverUnit_val
  have hpow_coord : α ^ d = ⟨2 * (y : ℤ) + 1, (y : ℤ) + 1⟩ := by
    have h := (zsqrtTwo_fermat_coordinate_divisibility hd_odd (-1) α hz).1
    have hu : ((silverUnit ^ (-(-1 : ℤ)) : (ℤ√2)ˣ) : ℤ√2) = ⟨1, 1⟩ := by
      simpa using hsu
    rw [hu] at h
    exact h.trans (by ext <;> simp [add_comm])
  exact ⟨hpow_coord, zsqrtTwo_explicit_neg_one_obstruction hq hd_odd hd3 hpow hpow_coord hnorm⟩

/-- Archimedean + Frobenius obstruction at unit exponent `k = 1`:
forces `1 ≤ α.re`, `α.im ≤ -1`, `2 * (d : ℤ) ^ 2 * α.im ^ 2 < α.re ^ 2`, and (when
`α.im ≡ 1 [ZMOD d]`) forces `(d : ℤ) - 1 ≤ -α.im` and `2 * (d ^ 2 - 1) * (d - 1) ^ 2 < q`. -/
theorem zsqrtTwo_fermat_k_pos_one_obstruction
    {q d y : ℕ}
    (hq : q.Prime) (hd_odd : Odd d) (hd3 : 3 ≤ d) (hpow : q ^ d + 1 = 2 * y ^ 2)
    {α : ℤ√2}
    (hz : (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ (1 : ℤ) : (ℤ√2)ˣ) : ℤ√2) * α ^ d)
    (hnorm : α.norm = (q : ℤ)) :
    (star α) ^ d = ⟨2 * (y : ℤ) - 1, (y : ℤ) - 1⟩ ∧
    1 ≤ α.re ∧
    α.im ≤ -1 ∧
    2 * (d : ℤ) ^ 2 * α.im ^ 2 < α.re ^ 2 ∧
    (α.im ≡ 1 [ZMOD (d : ℤ)] →
      (d : ℤ) - 1 ≤ -α.im ∧ 2 * (d ^ 2 - 1) * (d - 1) ^ 2 < q) := by
  have hsu : (silverUnit : ℤ√2) = ⟨1, 1⟩ := silverUnit_val
  have hpow_coord : α ^ d = ⟨2 * (y : ℤ) - 1, 1 - (y : ℤ)⟩ := by
    have h := (zsqrtTwo_fermat_coordinate_divisibility hd_odd 1 α hz).1
    have hu : ((silverUnit ^ (-(1 : ℤ)) : (ℤ√2)ˣ) : ℤ√2) = ⟨-1, 1⟩ := by
      have hmul : (silverUnit : ℤ√2) * ((silverUnit ^ (-(1 : ℤ)) : (ℤ√2)ˣ) : ℤ√2) = 1 := by
        rw [← Units.val_mul, zpow_neg_one, mul_inv_cancel, Units.val_one]
      rw [hsu] at hmul
      have h2 : (⟨-1, 1⟩ : ℤ√2) * ⟨1, 1⟩ = 1 := by ext <;> simp
      calc
        ((silverUnit ^ (-(1 : ℤ)) : (ℤ√2)ˣ) : ℤ√2)
            = 1 * ((silverUnit ^ (-(1 : ℤ)) : (ℤ√2)ˣ) : ℤ√2) := (one_mul _).symm
        _ = (⟨-1, 1⟩ * ⟨1, 1⟩) * ((silverUnit ^ (-(1 : ℤ)) : (ℤ√2)ˣ) : ℤ√2) := by rw [h2]
        _ = ⟨-1, 1⟩ * (⟨1, 1⟩ * ((silverUnit ^ (-(1 : ℤ)) : (ℤ√2)ˣ) : ℤ√2)) := mul_assoc _ _ _
        _ = ⟨-1, 1⟩ := by rw [hmul, mul_one]
    rw [hu] at h
    exact h.trans (by ext <;> simp [add_comm, sub_eq_add_neg])
  exact zsqrtTwo_explicit_pos_one_obstruction hq hd_odd hd3 hpow hpow_coord hnorm

/-! ## 5. Exceptional Euler-Index `toReal2` Positivity and `|k| = 1` Quartic Floors -/

/-- Unconditional `toReal2` nonvanishing and absolute value identity for EVERY `k`:
`0 < |toReal2 α|` and `0 < |(α.re : ℝ) + (α.im : ℝ) * Real.sqrt 2|`. -/
theorem zsqrtTwo_fermat_toReal_abs_pos {d y : ℕ} (hd_odd : Odd d) (k : ℤ) (α : ℤ√2)
    (hz : (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d) :
    0 < |toReal2 ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2)| ∧
    0 < |toReal2 α| ∧
    0 < |(α.re : ℝ) + (α.im : ℝ) * Real.sqrt 2| ∧
    |toReal2 α| ^ d = (1 + (y : ℝ) * Real.sqrt 2) * |toReal2 ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2)| := by
  have hz_real : toReal2 ⟨1, (y : ℤ)⟩ =
      toReal2 ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * (toReal2 α) ^ d := by
    have h := congrArg toReal2 hz
    rwa [map_mul, map_pow] at h
  have h1y_pos : 0 < toReal2 ⟨1, (y : ℤ)⟩ := by
    rw [(zsqrtTwo_toReal_add_and_sub_star ⟨1, (y : ℤ)⟩).1]
    simp only [Int.cast_one, Int.cast_natCast]
    positivity
  have habs_mul : 1 + (y : ℝ) * Real.sqrt 2 =
      |toReal2 ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2)| * |toReal2 α| ^ d := by
    have h1y_eq : toReal2 ⟨1, (y : ℤ)⟩ = 1 + (y : ℝ) * Real.sqrt 2 := by
      rw [(zsqrtTwo_toReal_add_and_sub_star ⟨1, (y : ℤ)⟩).1]
      simp
    have h := congrArg abs hz_real
    rw [h1y_eq, abs_of_pos (by positivity), abs_mul, abs_pow] at h
    exact h
  have huk_ne : toReal2 ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) ≠ 0 := by
    intro h0
    rw [h0, abs_zero, zero_mul] at habs_mul
    linarith [show (0 : ℝ) ≤ (y : ℝ) * Real.sqrt 2 by positivity]
  have hα_ne : toReal2 α ≠ 0 := by
    intro h0
    rw [h0, abs_zero, zero_pow hd_odd.pos.ne', mul_zero] at habs_mul
    linarith [show (0 : ℝ) ≤ (y : ℝ) * Real.sqrt 2 by positivity]
  have huk_inv : |toReal2 ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2)| *
      |toReal2 ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2)| = 1 := by
    rw [← abs_mul, ← map_mul, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero,
      Units.val_one, map_one, abs_one]
  have hpow_eq : |toReal2 α| ^ d =
      (1 + (y : ℝ) * Real.sqrt 2) * |toReal2 ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2)| := by
    calc
      |toReal2 α| ^ d = 1 * |toReal2 α| ^ d := (one_mul _).symm
      _ = (|toReal2 ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2)| *
            |toReal2 ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2)|) * |toReal2 α| ^ d := by
        rw [mul_comm |toReal2 ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2)|, huk_inv]
      _ = |toReal2 ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2)| *
            (|toReal2 ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2)| * |toReal2 α| ^ d) := mul_assoc _ _ _
      _ = (1 + (y : ℝ) * Real.sqrt 2) * |toReal2 ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2)| := by
        rw [← habs_mul, mul_comm]
  refine ⟨abs_pos.mpr huk_ne, abs_pos.mpr hα_ne, ?_, hpow_eq⟩
  rwa [← (zsqrtTwo_toReal_add_and_sub_star α).1, abs_pos]

/-- For any solution `⟨1, y⟩ = silverUnit ^ k * α ^ d` with `d` odd,
`toReal2 (silverUnit ^ k) = (1 + √2) ^ k > 0`, hence `0 < toReal2 α` and
`0 < (α.re : ℝ) + (α.im : ℝ) * Real.sqrt 2`. -/
theorem zsqrtTwo_fermat_toReal_pos
    {d y : ℕ} (hd_odd : Odd d) (k : ℤ) (α : ℤ√2)
    (hz : (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d) :
    toReal2 ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) = (1 + Real.sqrt 2) ^ k ∧
    0 < toReal2 ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) ∧
    0 < toReal2 α ∧
    0 < (α.re : ℝ) + (α.im : ℝ) * Real.sqrt 2 := by
  have hsu : (silverUnit : ℤ√2) = ⟨1, 1⟩ := silverUnit_val
  have hbase_pos : 0 < 1 + Real.sqrt 2 := by positivity
  have hbase_ne : 1 + Real.sqrt 2 ≠ 0 := hbase_pos.ne'
  have hsu_real : toReal2 (silverUnit : ℤ√2) = 1 + Real.sqrt 2 := by
    rw [hsu, (zsqrtTwo_toReal_add_and_sub_star ⟨1, 1⟩).1]
    simp
  have hsu_inv : toReal2 ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2) = (1 + Real.sqrt 2)⁻¹ := by
    have hmul : toReal2 (silverUnit : ℤ√2) * toReal2 ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2) = 1 := by
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    rw [hsu_real] at hmul
    exact eq_inv_of_mul_eq_one_right hmul
  have hunit_pow : ∀ m : ℤ, toReal2 ((silverUnit ^ m : (ℤ√2)ˣ) : ℤ√2) = (1 + Real.sqrt 2) ^ m := by
    intro m
    induction m using Int.induction_on with
    | zero => simp
    | succ n ih =>
      rw [zpow_add_one, Units.val_mul, map_mul, ih, hsu_real, zpow_add_one₀ hbase_ne]
    | pred n ih =>
      rw [sub_eq_add_neg, zpow_add, zpow_neg_one, Units.val_mul, map_mul, ih, hsu_inv,
        ← zpow_neg_one, ← zpow_add₀ hbase_ne, ← sub_eq_add_neg]
  have huk_eq := hunit_pow k
  have huk_pos : 0 < toReal2 ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) := by
    rw [huk_eq]
    exact zpow_pos hbase_pos k
  have hz_real : toReal2 ⟨1, (y : ℤ)⟩ =
      toReal2 ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * (toReal2 α) ^ d := by
    have h := congrArg toReal2 hz
    rwa [map_mul, map_pow] at h
  have h1y_pos : 0 < toReal2 ⟨1, (y : ℤ)⟩ := by
    rw [(zsqrtTwo_toReal_add_and_sub_star ⟨1, (y : ℤ)⟩).1]
    simp only [Int.cast_one, Int.cast_natCast]
    positivity
  have hpow_pos : 0 < (toReal2 α) ^ d := by
    rw [hz_real] at h1y_pos
    exact pos_of_mul_pos_right h1y_pos huk_pos.le
  have hα_pos : 0 < toReal2 α := hd_odd.pow_pos_iff.mp hpow_pos
  have hcoord_pos : 0 < (α.re : ℝ) + (α.im : ℝ) * Real.sqrt 2 := by
    rwa [← (zsqrtTwo_toReal_add_and_sub_star α).1]
  exact ⟨huk_eq, huk_pos, hα_pos, hcoord_pos⟩

/-- Unconditional `toReal2` nonvanishing on ANY exceptional Euler index
`sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`): for ALL `k`,
`0 < |toReal2 α|` and `0 < |(α.re : ℝ) + (α.im : ℝ) * Real.sqrt 2|`. -/
theorem exceptional_euler_toReal_abs_bounds {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    let d := (a + 1) / 2
    ∃ (y : ℕ) (k : ℤ) (α : ℤ√2),
      0 < y ∧ d ∣ y ∧ q ^ d + 1 = 2 * y ^ 2 ∧
      1 ≤ |k| ∧ 2 * |k| ≤ (d : ℤ) - 1 ∧
      (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d ∧
      α.norm = (if Even k then -(q : ℤ) else (q : ℤ)) ∧
      0 < |toReal2 α| ∧
      0 < |(α.re : ℝ) + (α.im : ℝ) * Real.sqrt 2| ∧
      |toReal2 α| ^ d = (1 + (y : ℝ) * Real.sqrt 2) * |toReal2 ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2)| := by
  intro d
  obtain ⟨_, _, hd8, _, _, _, _⟩ :=
    exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
  have hd_odd : Odd d := Nat.odd_iff.mpr (by omega)
  obtain ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, hnorm, _⟩ :=
    exceptional_euler_zsqrtTwo_mod_eight_d_profile hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨_, hα_pos, hcoord_pos, hpow_eq⟩ :=
    zsqrtTwo_fermat_toReal_abs_pos hd_odd k α hz_eq
  exact ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, hnorm, hα_pos, hcoord_pos, hpow_eq⟩

/-- On ANY exceptional Euler index `sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`),
for every `k` produced by `exceptional_euler_zsqrtTwo_mod_eight_d_profile`, `0 < toReal2 α`
(i.e., `0 < (α.re : ℝ) + (α.im : ℝ) * Real.sqrt 2`) and
`(toReal2 α) ^ d = (1 + (y : ℝ) * Real.sqrt 2) * (1 + Real.sqrt 2) ^ (-k)`. -/
theorem exceptional_euler_toReal_silverUnit_bounds
    {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    let d := (a + 1) / 2
    ∃ (y : ℕ) (k : ℤ) (α : ℤ√2),
      0 < y ∧ d ∣ y ∧ q ^ d + 1 = 2 * y ^ 2 ∧
      1 ≤ |k| ∧ 2 * |k| ≤ (d : ℤ) - 1 ∧
      (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d ∧
      α.norm = (if Even k then -(q : ℤ) else (q : ℤ)) ∧
      toReal2 ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) = (1 + Real.sqrt 2) ^ k ∧
      0 < toReal2 α ∧
      0 < (α.re : ℝ) + (α.im : ℝ) * Real.sqrt 2 ∧
      (toReal2 α) ^ d = (1 + (y : ℝ) * Real.sqrt 2) * (1 + Real.sqrt 2) ^ (-k) := by
  intro d
  obtain ⟨_, _, hd8, _, _, _, _⟩ :=
    exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
  have hd_odd : Odd d := Nat.odd_iff.mpr (by omega)
  obtain ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, hnorm, _⟩ :=
    exceptional_euler_zsqrtTwo_mod_eight_d_profile hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨huk_eq, huk_pos, hα_pos, hcoord_pos⟩ :=
    zsqrtTwo_fermat_toReal_pos hd_odd k α hz_eq
  have hz_real : 1 + (y : ℝ) * Real.sqrt 2 =
      (1 + Real.sqrt 2) ^ k * (toReal2 α) ^ d := by
    have h := congrArg toReal2 hz_eq
    rw [map_mul, map_pow, huk_eq, (zsqrtTwo_toReal_add_and_sub_star ⟨1, (y : ℤ)⟩).1] at h
    simpa using h
  have hpow_eq : (toReal2 α) ^ d =
      (1 + (y : ℝ) * Real.sqrt 2) * (1 + Real.sqrt 2) ^ (-k) := by
    rw [hz_real, mul_comm ((1 + Real.sqrt 2) ^ k), mul_assoc, ← zpow_add₀ (by positivity),
      add_neg_cancel, zpow_zero, mul_one]
  exact ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, hnorm, huk_eq, hα_pos, hcoord_pos, hpow_eq⟩

private lemma quartic_floor_17 (d : ℕ) (hd17 : 17 ≤ d) :
    147456 ≤ 2 * (d ^ 2 - 1) * (d - 1) ^ 2 := by
  have h1 : 17 ^ 2 - 1 ≤ d ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hd17 2) 1
  have h2 : (17 - 1) ^ 2 ≤ (d - 1) ^ 2 := Nat.pow_le_pow_left (Nat.sub_le_sub_right hd17 1) 2
  have hmul : (17 ^ 2 - 1) * (17 - 1) ^ 2 ≤ (d ^ 2 - 1) * (d - 1) ^ 2 := Nat.mul_le_mul h1 h2
  calc
    147456 = 2 * ((17 ^ 2 - 1) * (17 - 1) ^ 2) := by norm_num
    _ ≤ 2 * ((d ^ 2 - 1) * (d - 1) ^ 2) := Nat.mul_le_mul_left 2 hmul
    _ = 2 * (d ^ 2 - 1) * (d - 1) ^ 2 := (mul_assoc _ _ _).symm

private lemma quartic_floor_17_plus_one (d : ℕ) (hd17 : 17 ≤ d) :
    186624 ≤ 2 * (d ^ 2 - 1) * (d + 1) ^ 2 := by
  have h1 : 17 ^ 2 - 1 ≤ d ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hd17 2) 1
  have h2 : (17 + 1) ^ 2 ≤ (d + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hmul : (17 ^ 2 - 1) * (17 + 1) ^ 2 ≤ (d ^ 2 - 1) * (d + 1) ^ 2 := Nat.mul_le_mul h1 h2
  calc
    186624 = 2 * ((17 ^ 2 - 1) * (17 + 1) ^ 2) := by norm_num
    _ ≤ 2 * ((d ^ 2 - 1) * (d + 1) ^ 2) := Nat.mul_le_mul_left 2 hmul
    _ = 2 * (d ^ 2 - 1) * (d + 1) ^ 2 := (mul_assoc _ _ _).symm

private lemma quartic_floor_241 (d : ℕ) (hd241 : 241 ≤ d) :
    6690816000 ≤ 2 * (d ^ 2 - 1) * (d - 1) ^ 2 := by
  have h1 : 241 ^ 2 - 1 ≤ d ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hd241 2) 1
  have h2 : (241 - 1) ^ 2 ≤ (d - 1) ^ 2 := Nat.pow_le_pow_left (Nat.sub_le_sub_right hd241 1) 2
  have hmul : (241 ^ 2 - 1) * (241 - 1) ^ 2 ≤ (d ^ 2 - 1) * (d - 1) ^ 2 := Nat.mul_le_mul h1 h2
  calc
    6690816000 = 2 * ((241 ^ 2 - 1) * (241 - 1) ^ 2) := by norm_num
    _ ≤ 2 * ((d ^ 2 - 1) * (d - 1) ^ 2) := Nat.mul_le_mul_left 2 hmul
    _ = 2 * (d ^ 2 - 1) * (d - 1) ^ 2 := (mul_assoc _ _ _).symm

private lemma zsqrtTwo_unit_abs_one_obstruction {q d y : ℕ}
    (hq : q.Prime) (hd_odd : Odd d) (hd3 : 3 ≤ d) (hpow : q ^ d + 1 = 2 * y ^ 2)
    {k : ℤ} (hk_abs : |k| = 1) {α : ℤ√2}
    (hz_eq : (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d)
    (hnorm_pos : α.norm = (q : ℤ))
    (hev_im : Even α.im)
    (him_d : α.im ≡ ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2).im [ZMOD (d : ℤ)]) :
    1 ≤ |α.re| ∧
    (d : ℤ) - 1 ≤ |α.im| ∧
    2 * (d : ℤ) ^ 2 * α.im ^ 2 < α.re ^ 2 ∧
    2 * (d ^ 2 - 1) * (d - 1) ^ 2 < q := by
  let u_k : ℤ√2 := ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2)
  have hcoord : α ^ d = ⟨u_k.re + 2 * u_k.im * (y : ℤ), u_k.re * (y : ℤ) + u_k.im⟩ :=
    (zsqrtTwo_fermat_coordinate_divisibility hd_odd k α hz_eq).1
  have hk_cases : k = 1 ∨ k = -1 := abs_eq (by norm_num : (0 : ℤ) ≤ 1) |>.mp hk_abs
  have hu_cases : u_k = ⟨1, 1⟩ ∨ u_k = ⟨-1, -1⟩ ∨ u_k = ⟨-1, 1⟩ ∨ u_k = ⟨1, -1⟩ := by
    have hmul : (silverUnit : ℤ√2) * ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hinv_cases : ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2) = ⟨-1, 1⟩ ∨
        ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2) = ⟨1, -1⟩ ∨
        ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2) = ⟨1, 1⟩ ∨
        ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2) = ⟨-1, -1⟩ := by
      rcases silverUnit_four_cases with h | h | h | h
      · rw [h] at hmul
        left
        have h2 : (⟨-1, 1⟩ : ℤ√2) * ⟨1, 1⟩ = 1 := by ext <;> simp
        calc
          ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2)
              = 1 * ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2) := (one_mul _).symm
          _ = (⟨-1, 1⟩ * ⟨1, 1⟩) * ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2) := by rw [h2]
          _ = ⟨-1, 1⟩ * (⟨1, 1⟩ * ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2)) := mul_assoc _ _ _
          _ = ⟨-1, 1⟩ := by rw [hmul, mul_one]
      · rw [h] at hmul
        right; left
        have h2 : (⟨1, -1⟩ : ℤ√2) * ⟨-1, -1⟩ = 1 := by ext <;> simp
        calc
          ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2)
              = 1 * ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2) := (one_mul _).symm
          _ = (⟨1, -1⟩ * ⟨-1, -1⟩) * ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2) := by rw [h2]
          _ = ⟨1, -1⟩ * (⟨-1, -1⟩ * ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2)) := mul_assoc _ _ _
          _ = ⟨1, -1⟩ := by rw [hmul, mul_one]
      · rw [h] at hmul
        right; right; left
        have h2 : (⟨1, 1⟩ : ℤ√2) * ⟨-1, 1⟩ = 1 := by ext <;> simp
        calc
          ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2)
              = 1 * ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2) := (one_mul _).symm
          _ = (⟨1, 1⟩ * ⟨-1, 1⟩) * ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2) := by rw [h2]
          _ = ⟨1, 1⟩ * (⟨-1, 1⟩ * ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2)) := mul_assoc _ _ _
          _ = ⟨1, 1⟩ := by rw [hmul, mul_one]
      · rw [h] at hmul
        right; right; right
        have h2 : (⟨-1, -1⟩ : ℤ√2) * ⟨1, -1⟩ = 1 := by ext <;> simp
        calc
          ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2)
              = 1 * ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2) := (one_mul _).symm
          _ = (⟨-1, -1⟩ * ⟨1, -1⟩) * ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2) := by rw [h2]
          _ = ⟨-1, -1⟩ * (⟨1, -1⟩ * ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2)) := mul_assoc _ _ _
          _ = ⟨-1, -1⟩ := by rw [hmul, mul_one]
    rcases hk_cases with rfl | rfl
    · have hu_eq : u_k = ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2) := by simp [u_k]
      rw [hu_eq]
      rcases hinv_cases with h | h | h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · have hu_eq : u_k = (silverUnit : ℤ√2) := by simp [u_k]
      rw [hu_eq]
      exact silverUnit_four_cases
  have him_mod_pm : α.im ≡ 1 [ZMOD (d : ℤ)] ∨ α.im ≡ -1 [ZMOD (d : ℤ)] := by
    change α.im ≡ u_k.im [ZMOD (d : ℤ)] at him_d
    rcases hu_cases with h | h | h | h <;> rw [h] at him_d
    · exact Or.inl him_d
    · exact Or.inr him_d
    · exact Or.inl him_d
    · exact Or.inr him_d
  rcases hu_cases with h | h | h | h
  · have hpow_c : α ^ d = ⟨2 * (y : ℤ) + 1, (y : ℤ) + 1⟩ := by
      rw [h] at hcoord
      exact hcoord.trans (by ext <;> simp [add_comm])
    obtain ⟨hre, him, hsq, _⟩ :=
      zsqrtTwo_explicit_neg_one_obstruction hq hd_odd hd3 hpow hpow_c hnorm_pos
    have hdm1 : (d : ℤ) - 1 ≤ |α.im| := by
      rcases him_mod_pm with hm1 | hmm1
      · obtain ⟨t, ht⟩ := Int.modEq_iff_add_fac.mp hm1.symm
        have hd_pos : (0 : ℤ) < d := by omega
        have ht_pos : 1 ≤ t := by
          by_contra! ht0
          have hdt : (d : ℤ) * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hd_pos.le (by omega)
          have him1 : α.im = 1 := by linarith
          rw [him1] at hev_im
          exact (by decide : ¬ Even (1 : ℤ)) hev_im
        have : (d : ℤ) * 1 ≤ (d : ℤ) * t := mul_le_mul_of_nonneg_left ht_pos hd_pos.le
        rw [abs_of_nonneg (by omega)]
        linarith
      · have hdvd : (d : ℤ) ∣ α.im + 1 := by
          have h1 : α.im + 1 ≡ 0 [ZMOD (d : ℤ)] := by
            have := hmm1.add_right 1
            simpa using this
          exact Int.modEq_zero_iff_dvd.mp h1
        have hd_le : (d : ℤ) ≤ α.im + 1 := Int.le_of_dvd (by omega) hdvd
        rw [abs_of_nonneg (by omega)]
        omega
    have habs_le : ((d - 1 : ℕ) : ℤ) ≤ |α.im| := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
      exact hdm1
    exact ⟨by rwa [abs_of_nonneg (by omega)], hdm1, hsq,
      zsqrtTwo_quartic_from_sq_ineq hd3 hnorm_pos hsq habs_le⟩
  · have hpow_neg : (-α) ^ d = ⟨2 * (y : ℤ) + 1, (y : ℤ) + 1⟩ := by
      rw [h] at hcoord
      rw [hd_odd.neg_pow, hcoord]
      ext <;> simp [add_comm]
    have hnorm_neg : (-α).norm = (q : ℤ) := by
      rw [Zsqrtd.norm_neg, hnorm_pos]
    obtain ⟨hre, him, hsq_neg, _⟩ :=
      zsqrtTwo_explicit_neg_one_obstruction hq hd_odd hd3 hpow hpow_neg hnorm_neg
    have hsq : 2 * (d : ℤ) ^ 2 * α.im ^ 2 < α.re ^ 2 := by
      simpa using hsq_neg
    have hdm1 : (d : ℤ) - 1 ≤ |α.im| := by
      have him_le : α.im ≤ -1 := by
        change -α.im ≥ 1 at him
        omega
      rcases him_mod_pm with hm1 | hmm1
      · have hdvd : (d : ℤ) ∣ -α.im + 1 := by
          have h1 : -α.im + 1 ≡ 0 [ZMOD (d : ℤ)] := by
            have := hm1.neg.add_right 1
            simpa using this
          exact Int.modEq_zero_iff_dvd.mp h1
        have hd_le : (d : ℤ) ≤ -α.im + 1 := Int.le_of_dvd (by omega) hdvd
        rw [abs_of_nonpos (by omega)]
        omega
      · obtain ⟨t, ht⟩ := Int.modEq_iff_add_fac.mp hmm1.neg.symm
        have ht' : -α.im = 1 + (d : ℤ) * t := by linarith
        have hd_pos : (0 : ℤ) < d := by omega
        have ht_pos : 1 ≤ t := by
          by_contra! ht0
          have hdt : (d : ℤ) * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hd_pos.le (by omega)
          have him1 : (-α).im = 1 := by
            change -α.im = 1
            linarith
          have hev_neg : Even (-α).im := by simpa using hev_im.neg
          rw [him1] at hev_neg
          exact (by decide : ¬ Even (1 : ℤ)) hev_neg
        have : (d : ℤ) * 1 ≤ (d : ℤ) * t := mul_le_mul_of_nonneg_left ht_pos hd_pos.le
        rw [abs_of_nonpos (by omega)]
        linarith
    have habs_le : ((d - 1 : ℕ) : ℤ) ≤ |α.im| := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
      exact hdm1
    have hre_abs : 1 ≤ |α.re| := by
      change 1 ≤ -α.re at hre
      rw [abs_of_nonpos (by omega)]
      exact hre
    exact ⟨hre_abs, hdm1, hsq, zsqrtTwo_quartic_from_sq_ineq hd3 hnorm_pos hsq habs_le⟩
  · have hpow_c : α ^ d = ⟨2 * (y : ℤ) - 1, 1 - (y : ℤ)⟩ := by
      rw [h] at hcoord
      exact hcoord.trans (by ext <;> simp [add_comm, sub_eq_add_neg])
    obtain ⟨_, hre, him, hsq, _⟩ :=
      zsqrtTwo_explicit_pos_one_obstruction hq hd_odd hd3 hpow hpow_c hnorm_pos
    have hdm1 : (d : ℤ) - 1 ≤ |α.im| := by
      rcases him_mod_pm with hm1 | hmm1
      · have hdvd : (d : ℤ) ∣ -α.im + 1 := by
          have h1 : -α.im + 1 ≡ 0 [ZMOD (d : ℤ)] := by
            have := hm1.neg.add_right 1
            simpa using this
          exact Int.modEq_zero_iff_dvd.mp h1
        have hd_le : (d : ℤ) ≤ -α.im + 1 := Int.le_of_dvd (by omega) hdvd
        rw [abs_of_nonpos (by omega)]
        omega
      · obtain ⟨t, ht⟩ := Int.modEq_iff_add_fac.mp hmm1.neg.symm
        have hd_pos : (0 : ℤ) < d := by omega
        have ht_pos : 1 ≤ t := by
          by_contra! ht0
          have hdt : (d : ℤ) * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hd_pos.le (by omega)
          have him1 : -α.im = 1 := by linarith
          have hev_neg : Even (-α.im) := hev_im.neg
          rw [him1] at hev_neg
          exact (by decide : ¬ Even (1 : ℤ)) hev_neg
        have : (d : ℤ) * 1 ≤ (d : ℤ) * t := mul_le_mul_of_nonneg_left ht_pos hd_pos.le
        rw [abs_of_nonpos (by omega)]
        linarith
    have habs_le : ((d - 1 : ℕ) : ℤ) ≤ |α.im| := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
      exact hdm1
    exact ⟨by rwa [abs_of_nonneg (by omega)], hdm1, hsq,
      zsqrtTwo_quartic_from_sq_ineq hd3 hnorm_pos hsq habs_le⟩
  · have hpow_neg : (-α) ^ d = ⟨2 * (y : ℤ) - 1, 1 - (y : ℤ)⟩ := by
      rw [h] at hcoord
      rw [hd_odd.neg_pow, hcoord]
      ext <;> simp [add_comm, sub_eq_add_neg]
    have hnorm_neg : (-α).norm = (q : ℤ) := by
      rw [Zsqrtd.norm_neg, hnorm_pos]
    obtain ⟨_, hre, him, hsq_neg, _⟩ :=
      zsqrtTwo_explicit_pos_one_obstruction hq hd_odd hd3 hpow hpow_neg hnorm_neg
    have hsq : 2 * (d : ℤ) ^ 2 * α.im ^ 2 < α.re ^ 2 := by
      simpa using hsq_neg
    have him_pos : 1 ≤ α.im := by
      change -α.im ≤ -1 at him
      omega
    have hdm1 : (d : ℤ) - 1 ≤ |α.im| := by
      rcases him_mod_pm with hm1 | hmm1
      · obtain ⟨t, ht⟩ := Int.modEq_iff_add_fac.mp hm1.symm
        have hd_pos : (0 : ℤ) < d := by omega
        have ht_pos : 1 ≤ t := by
          by_contra! ht0
          have hdt : (d : ℤ) * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hd_pos.le (by omega)
          have him1 : α.im = 1 := by linarith
          rw [him1] at hev_im
          exact (by decide : ¬ Even (1 : ℤ)) hev_im
        have : (d : ℤ) * 1 ≤ (d : ℤ) * t := mul_le_mul_of_nonneg_left ht_pos hd_pos.le
        rw [abs_of_nonneg (by omega)]
        linarith
      · have hdvd : (d : ℤ) ∣ α.im + 1 := by
          have h1 : α.im + 1 ≡ 0 [ZMOD (d : ℤ)] := by
            have := hmm1.add_right 1
            simpa using this
          exact Int.modEq_zero_iff_dvd.mp h1
        have hd_le : (d : ℤ) ≤ α.im + 1 := Int.le_of_dvd (by omega) hdvd
        rw [abs_of_nonneg (by omega)]
        omega
    have habs_le : ((d - 1 : ℕ) : ℤ) ≤ |α.im| := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
      exact hdm1
    have hre_abs : 1 ≤ |α.re| := by
      change 1 ≤ -α.re at hre
      rw [abs_of_nonpos (by omega)]
      exact hre
    exact ⟨hre_abs, hdm1, hsq, zsqrtTwo_quartic_from_sq_ineq hd3 hnorm_pos hsq habs_le⟩

/-- Unconditional `|k| = 1` quartic obstruction on any exceptional Euler-index witness
`sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`):
forces `1 ≤ |α.re|`, `(d : ℤ) - 1 ≤ |α.im|`, `2 * (d : ℤ) ^ 2 * α.im ^ 2 < α.re ^ 2`,
`2 * (d ^ 2 - 1) * (d - 1) ^ 2 < q`, `147456 < q`, and `6690816000 < q` when `¬ 3 ∣ N ∧ ¬ 5 ∣ N`. -/
theorem exceptional_euler_unit_exponent_one_quartic_bound {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    let d := (a + 1) / 2
    ∃ (y : ℕ) (k : ℤ) (α : ℤ√2),
      0 < y ∧ d ∣ y ∧ q ^ d + 1 = 2 * y ^ 2 ∧
      1 ≤ |k| ∧ 2 * |k| ≤ (d : ℤ) - 1 ∧
      (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d ∧
      α.norm = (if Even k then -(q : ℤ) else (q : ℤ)) ∧
      (|k| = 1 →
        1 ≤ |α.re| ∧
        (d : ℤ) - 1 ≤ |α.im| ∧
        2 * (d : ℤ) ^ 2 * α.im ^ 2 < α.re ^ 2 ∧
        2 * (d ^ 2 - 1) * (d - 1) ^ 2 < q ∧
        147456 < q ∧
        (¬ 3 ∣ N → ¬ 5 ∣ N → 241 ≤ d ∧ 6690816000 < q)) := by
  intro d
  obtain ⟨hd, hd17, hd8, _, _, _, _⟩ :=
    exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
  have hd_odd : Odd d := Nat.odd_iff.mpr (by omega)
  have hd3 : 3 ≤ d := by omega
  obtain ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, hnorm, _, _, _, _, him_d,
      _, _, hk_odd⟩ :=
    exceptional_euler_zsqrtTwo_mod_eight_d_profile hN ho hq hq4 ha4 ha hqm hform hl hi
  refine ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, hnorm, ?_⟩
  intro hk_abs
  have hk_cases : k = 1 ∨ k = -1 := abs_eq (by norm_num : (0 : ℤ) ≤ 1) |>.mp hk_abs
  have hk_odd_val : Odd k := by
    rcases hk_cases with rfl | rfl
    · exact odd_one
    · exact Int.odd_iff.mpr (by norm_num)
  have hnot_even : ¬ Even k := Int.not_even_iff_odd.mpr hk_odd_val
  have hnorm_pos : α.norm = (q : ℤ) := by
    rw [hnorm, ite_eq_right_iff.mpr (fun h => absurd h hnot_even)]
  have hev_im : Even α.im := (hk_odd hk_odd_val).1
  obtain ⟨hre_abs, him_abs, hsq, hq_lt⟩ :=
    zsqrtTwo_unit_abs_one_obstruction hq hd_odd hd3 hpow hk_abs hz_eq hnorm_pos hev_im him_d
  refine ⟨hre_abs, him_abs, hsq, hq_lt, lt_of_le_of_lt (quartic_floor_17 d hd17) hq_lt, ?_⟩
  intro h3 h5
  obtain ⟨_, _, _, hd241, _⟩ :=
    exceptional_euler_of_not_three_or_five_dvd hN ho hq hq4 ha4 ha hqm hform hl hi h3 h5
  exact ⟨hd241, lt_of_le_of_lt (quartic_floor_241 d hd241) hq_lt⟩

/-- Sharp unconditional `|k| = 1` sign-pinned quartic obstruction on any exceptional Euler-index
witness `sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`):
pins `1 ≤ α.re`, `(d : ℤ) - 1 ≤ |α.im|`, `2 * (d : ℤ) ^ 2 * α.im ^ 2 < α.re ^ 2`,
`2 * (d ^ 2 - 1) * (d - 1) ^ 2 < q` (`147456 < q`), the sharper `k = -1` bound
`2 * (d ^ 2 - 1) * (d + 1) ^ 2 < q` (`186624 < q`), and `6690816000 < q` when `¬ 3 ∣ N ∧ ¬ 5 ∣ N`. -/
theorem exceptional_euler_unit_exponent_one_quartic_bound_of_silverUnit
    {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    let d := (a + 1) / 2
    ∃ (y : ℕ) (k : ℤ) (α : ℤ√2),
      0 < y ∧ d ∣ y ∧ q ^ d + 1 = 2 * y ^ 2 ∧
      1 ≤ |k| ∧ 2 * |k| ≤ (d : ℤ) - 1 ∧
      (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d ∧
      α.norm = (if Even k then -(q : ℤ) else (q : ℤ)) ∧
      (|k| = 1 →
        1 ≤ α.re ∧
        (d : ℤ) - 1 ≤ |α.im| ∧
        2 * (d : ℤ) ^ 2 * α.im ^ 2 < α.re ^ 2 ∧
        2 * (d ^ 2 - 1) * (d - 1) ^ 2 < q ∧
        147456 < q ∧
        (k = -1 → 2 * (d ^ 2 - 1) * (d + 1) ^ 2 < q ∧ 186624 < q) ∧
        (¬ 3 ∣ N → ¬ 5 ∣ N → 241 ≤ d ∧ 6690816000 < q)) := by
  have hsu : (silverUnit : ℤ√2) = ⟨1, 1⟩ := silverUnit_val
  intro d
  obtain ⟨hd, hd17, hd8, _, _, _, _⟩ :=
    exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
  have hd_odd : Odd d := Nat.odd_iff.mpr (by omega)
  have hd3 : 3 ≤ d := by omega
  obtain ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, hnorm, _, _, _, _, him_d,
      _, _, hk_odd⟩ :=
    exceptional_euler_zsqrtTwo_mod_eight_d_profile hN ho hq hq4 ha4 ha hqm hform hl hi
  refine ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, hnorm, ?_⟩
  intro hk_abs
  have hk_cases : k = 1 ∨ k = -1 := abs_eq (by norm_num : (0 : ℤ) ≤ 1) |>.mp hk_abs
  have hk_odd_val : Odd k := by
    rcases hk_cases with rfl | rfl
    · exact odd_one
    · exact Int.odd_iff.mpr (by norm_num)
  have hnot_even : ¬ Even k := Int.not_even_iff_odd.mpr hk_odd_val
  have hnorm_pos : α.norm = (q : ℤ) := by
    rw [hnorm, ite_eq_right_iff.mpr (fun h => absurd h hnot_even)]
  have hev_im : Even α.im := (hk_odd hk_odd_val).1
  have hfloor241 : ∀ (h3 : ¬ 3 ∣ N) (h5 : ¬ 5 ∣ N),
      241 ≤ d ∧ 6690816000 ≤ 2 * (d ^ 2 - 1) * (d - 1) ^ 2 := by
    intro h3 h5
    obtain ⟨_, _, _, hd241, _⟩ :=
      exceptional_euler_of_not_three_or_five_dvd hN ho hq hq4 ha4 ha hqm hform hl hi h3 h5
    exact ⟨hd241, quartic_floor_241 d hd241⟩
  rcases hk_cases with rfl | rfl
  · have hu : ((silverUnit ^ (-(1 : ℤ)) : (ℤ√2)ˣ) : ℤ√2).im = 1 := by
      have hu_eq : ((silverUnit ^ (-(1 : ℤ)) : (ℤ√2)ˣ) : ℤ√2) = ⟨-1, 1⟩ := by
        simpa using silverUnit_inv_val
      rw [hu_eq]
    have him_mod : α.im ≡ 1 [ZMOD (d : ℤ)] := by rwa [hu] at him_d
    obtain ⟨_, hre, him, hsq, hcong⟩ :=
      zsqrtTwo_fermat_k_pos_one_obstruction hq hd_odd hd3 hpow hz_eq hnorm_pos
    obtain ⟨hdm1, hq_lt⟩ := hcong him_mod
    have habs_im : (d : ℤ) - 1 ≤ |α.im| := by rwa [abs_of_nonpos (by omega)]
    refine ⟨hre, habs_im, hsq, hq_lt, lt_of_le_of_lt (quartic_floor_17 d hd17) hq_lt, ?_, ?_⟩
    · intro hneg; omega
    · intro h3 h5
      obtain ⟨hd241, hf⟩ := hfloor241 h3 h5
      exact ⟨hd241, lt_of_le_of_lt hf hq_lt⟩
  · have hu : ((silverUnit ^ (-(-1 : ℤ)) : (ℤ√2)ˣ) : ℤ√2).im = 1 := by
      have hu_eq : ((silverUnit ^ (-(-1 : ℤ)) : (ℤ√2)ˣ) : ℤ√2) = ⟨1, 1⟩ := by simpa using hsu
      rw [hu_eq]
    have him_mod : α.im ≡ 1 [ZMOD (d : ℤ)] := by rwa [hu] at him_d
    obtain ⟨_, hre, him, hsq, hcong⟩ :=
      zsqrtTwo_fermat_k_neg_one_obstruction hq hd_odd hd3 hpow hz_eq hnorm_pos
    obtain ⟨hdp1, hq_lt_p1⟩ := hcong hev_im him_mod
    have hdm1 : (d : ℤ) - 1 ≤ |α.im| := by
      rw [abs_of_nonneg (by omega)]
      linarith
    have hmono : 2 * (d ^ 2 - 1) * (d - 1) ^ 2 ≤ 2 * (d ^ 2 - 1) * (d + 1) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    have hq_lt_m1 : 2 * (d ^ 2 - 1) * (d - 1) ^ 2 < q := lt_of_le_of_lt hmono hq_lt_p1
    refine ⟨hre, hdm1, hsq, hq_lt_m1, lt_of_le_of_lt (quartic_floor_17 d hd17) hq_lt_m1, ?_, ?_⟩
    · intro _
      exact ⟨hq_lt_p1, lt_of_le_of_lt (quartic_floor_17_plus_one d hd17) hq_lt_p1⟩
    · intro h3 h5
      obtain ⟨hd241, hf⟩ := hfloor241 h3 h5
      exact ⟨hd241, lt_of_le_of_lt hf hq_lt_m1⟩

end OddPerfect
