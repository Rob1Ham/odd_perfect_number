module

public import OddPerfect.ZsqrtTwoUniversalCone
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# General Odd-`k` Diophantine Inequality & Sharp `|k| = 3` Quartic Floors in `ℤ√2`
(`OddPerfect.ZsqrtTwoCubicObstruction`)

Extends `OddPerfect.ZsqrtTwoUniversalCone` to all odd unit exponents `k` and specializes to
`|k| = 3` (`silverUnit ^ 3 = ⟨7, 5⟩`), unifying the quartic `q`-floor tower across `1 ≤ |k| ≤ 3`:

1. `zsqrtTwo_pos_coords_lower_bound_pow_im_ge5` and `zsqrtTwo_fermat_general_odd_k_obstruction`:
   for every odd `k` with `1 ≤ |k|` and `2 * |k| ≤ d - 1` on `q ^ d + 1 = 2 * y ^ 2`, sets
   `m := k.natAbs`, `U := (silverUnit ^ m).re`, `V := (silverUnit ^ m).im`, proves
   `1 ≤ U`, `1 ≤ V`, `U ^ 2 - 2 * V ^ 2 = -1`, `silverUnit ^ (-m) = ⟨-U, V⟩`, `3 ≤ α.re`,
   the sign-unified binomial bound `(d : ℤ) * α.re ^ (d - 1) * |α.im| < (U + V) * (y : ℤ)`,
   `2 * (d : ℤ) ^ 2 * α.im ^ 2 < (U + V) ^ 2 * α.re ^ 2`, and
   `2 * ((d : ℤ) ^ 2 - (U + V) ^ 2) * α.im ^ 2 < (U + V) ^ 2 * (q : ℤ)`.
   At `|k| = 3` (`U = 7, V = 5`, `d ≥ 5`), sharpens this to
   `(d : ℤ) * α.re ^ (d - 1) * |α.im| < 7 * (y : ℤ)`,
   `2 * (d : ℤ) ^ 2 * α.im ^ 2 < 49 * α.re ^ 2`, and
   `2 * ((d : ℤ) ^ 2 - 49) * α.im ^ 2 < 49 * (q : ℤ)`.
2. `zsqrtTwo_fermat_k_abs_three_obstruction` and
   `exceptional_euler_unit_exponent_three_quartic_bound`:
   pins `(d : ℤ) - 5 ≤ |α.im|` (`(d : ℤ) + 5 ≤ α.im` for `k = -3`), yielding
   `2 * (d ^ 2 - 49) * (d - 5) ^ 2 < 49 * q`, `1410 < q` unconditionally (`4741 < q` for `k = -3`),
   and `131924500 < q` (`10 ^ 8 < q`; `143341408 < q` for `k = -3`) when `¬ 3 ∣ N ∧ ¬ 5 ∣ N`.
3. `exceptional_euler_k_le_three_unified_floor`:
   unifies `|k| = 1`, `|k| = 2`, and `|k| = 3` into a single floor for all `|k| ≤ 3`:
   `1410 < q` unconditionally, and `131924500 < q` (`10 ^ 8 < q`) when `¬ 3 ∣ N ∧ ¬ 5 ∣ N`.
-/

public section

namespace OddPerfect

open ArithmeticFunction

/-! ## 1. Sharp `d ≥ 5` Positive-Coordinate Power Lower Bound & Odd `silverUnit` Powers -/

/-- For `β : ℤ√2` with `1 ≤ β.re` and `1 ≤ β.im`, and every odd `d ≥ 5`,
`(β ^ d).im` satisfies the sharpened lower bound
`6 + (d : ℤ) * β.re ^ (d - 1) * β.im ≤ (β ^ d).im`. -/
theorem zsqrtTwo_pos_coords_lower_bound_pow_im_ge5 {β : ℤ√2}
    (hre : 1 ≤ β.re) (him : 1 ≤ β.im) {d : ℕ} (hd_odd : Odd d) (hd5 : 5 ≤ d) :
    6 + (d : ℤ) * β.re ^ (d - 1) * β.im ≤ (β ^ d).im := by
  obtain ⟨hpos, hre_pow⟩ := zsqrtTwo_pos_coords_pow_bounds hre him
  obtain ⟨k, rfl⟩ := hd_odd
  have hk2 : 2 ≤ k := by omega
  induction k, hk2 using Nat.le_induction with
  | base =>
    have hβ2 : β ^ 2 = ⟨β.re ^ 2 + 2 * β.im ^ 2, 2 * β.re * β.im⟩ := by
      ext <;> simp [pow_two] <;> ring
    have hpow5 : (β ^ (2 * 2 + 1)).im =
        5 * β.re ^ 4 * β.im + 20 * β.re ^ 2 * β.im ^ 3 + 4 * β.im ^ 5 := by
      have h5 : β ^ (2 * 2 + 1) = (β ^ 2 * β ^ 2) * β := by ring
      rw [h5, hβ2]
      simp only [Zsqrtd.im_mul, Zsqrtd.re_mul]
      ring
    have hre2 : 1 ≤ β.re ^ 2 := by nlinarith
    have him3 : 1 ≤ β.im ^ 3 := one_le_pow₀ him
    have him5 : 1 ≤ β.im ^ 5 := one_le_pow₀ him
    have hterm2 : 1 ≤ β.re ^ 2 * β.im ^ 3 := by nlinarith
    rw [hpow5]
    push_cast
    linarith
  | succ k hk ih =>
    set m : ℕ := 2 * k + 1
    have ih' : 6 + (m : ℤ) * β.re ^ (m - 1) * β.im ≤ (β ^ m).im := ih (by omega)
    have hpow_step : β ^ (2 * (k + 1) + 1) = β ^ m * β ^ 2 := by
      rw [show 2 * (k + 1) + 1 = m + 2 by omega, pow_add]
    have hre2 : (β ^ 2).re = β.re ^ 2 + 2 * β.im ^ 2 := by
      rw [pow_two, Zsqrtd.re_mul]
      ring
    have him2 : (β ^ 2).im = 2 * β.re * β.im := by
      rw [pow_two, Zsqrtd.im_mul]
      ring
    have hm_re : β.re ^ m ≤ (β ^ m).re := hre_pow m
    have hre_pow_ge1 : 1 ≤ β.re ^ 2 := by nlinarith
    have hpow_eq1 : β.re ^ (m + 1) = β.re ^ m * β.re := by rw [pow_succ]
    have hpow_eq2 : β.re ^ (m + 1) = β.re ^ (m - 1) * β.re ^ 2 := by
      rw [← pow_add, show m - 1 + 2 = m + 1 by omega]
    have h1 : β.re ^ m * (2 * β.re * β.im) ≤ (β ^ m).re * (2 * β.re * β.im) :=
      mul_le_mul_of_nonneg_right hm_re (by positivity)
    have h2 : (6 + (m : ℤ) * β.re ^ (m - 1) * β.im) * β.re ^ 2 ≤
        (β ^ m).im * (β.re ^ 2 + 2 * β.im ^ 2) := by
      have him_nonneg : 0 ≤ (β ^ m).im := by
        have := (hpos m (by omega)).2
        linarith
      calc
        (6 + (m : ℤ) * β.re ^ (m - 1) * β.im) * β.re ^ 2
            ≤ (β ^ m).im * β.re ^ 2 :=
          mul_le_mul_of_nonneg_right ih' (by positivity)
        _ ≤ (β ^ m).im * (β.re ^ 2 + 2 * β.im ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith [sq_nonneg β.im]) him_nonneg
    have him_step : (β ^ (2 * (k + 1) + 1)).im =
        (β ^ m).re * (2 * β.re * β.im) + (β ^ m).im * (β.re ^ 2 + 2 * β.im ^ 2) := by
      rw [hpow_step, Zsqrtd.im_mul, hre2, him2]
    have hsub_idx : 2 * (k + 1) + 1 - 1 = m + 1 := by omega
    have hcast_m : ((2 * (k + 1) + 1 : ℕ) : ℤ) = (m : ℤ) + 2 := by
      dsimp [m]
      ring
    rw [him_step, hsub_idx, hcast_m]
    calc
      6 + ((m : ℤ) + 2) * β.re ^ (m + 1) * β.im
          ≤ 6 * β.re ^ 2 + ((m : ℤ) + 2) * β.re ^ (m + 1) * β.im := by linarith
      _ = 6 * β.re ^ 2 + 2 * β.re ^ (m + 1) * β.im + (m : ℤ) * β.re ^ (m + 1) * β.im := by ring
      _ = 6 * β.re ^ 2 + 2 * (β.re ^ m * β.re) * β.im +
            (m : ℤ) * (β.re ^ (m - 1) * β.re ^ 2) * β.im := by
        rw [← hpow_eq1, ← hpow_eq2]
      _ = β.re ^ m * (2 * β.re * β.im) + (6 + (m : ℤ) * β.re ^ (m - 1) * β.im) * β.re ^ 2 := by
        ring
      _ ≤ (β ^ m).re * (2 * β.re * β.im) + (β ^ m).im * (β.re ^ 2 + 2 * β.im ^ 2) :=
        add_le_add h1 h2

/-- Coordinates, norm, and inverse formula for odd positive powers of `silverUnit`. -/
theorem silverUnit_odd_pow_coords {m : ℕ} (hm_odd : Odd m) (hm1 : 1 ≤ m) :
    let U : ℤ := ((silverUnit ^ m : (ℤ√2)ˣ) : ℤ√2).re
    let V : ℤ := ((silverUnit ^ m : (ℤ√2)ˣ) : ℤ√2).im
    1 ≤ U ∧ 1 ≤ V ∧ U ^ 2 - 2 * V ^ 2 = -1 ∧
    ((silverUnit ^ (-(m : ℤ)) : (ℤ√2)ˣ) : ℤ√2) = ⟨-U, V⟩ := by
  intro U V
  set u : ℤ√2 := ((silverUnit ^ m : (ℤ√2)ˣ) : ℤ√2)
  have hu_pow : u = (⟨1, 1⟩ : ℤ√2) ^ m := by
    change ((silverUnit ^ m : (ℤ√2)ˣ) : ℤ√2) = (⟨1, 1⟩ : ℤ√2) ^ m
    rw [Units.val_pow_eq_pow_val, silverUnit_val]
  have hpos := (zsqrtTwo_pos_coords_pow_bounds (α := ⟨1, 1⟩) le_rfl le_rfl).1 m hm1
  have hU1 : 1 ≤ U := by
    change 1 ≤ u.re
    rw [hu_pow]
    exact hpos.1
  have hV1 : 1 ≤ V := by
    change 1 ≤ u.im
    rw [hu_pow]
    exact hpos.2
  have hnorm : U ^ 2 - 2 * V ^ 2 = -1 := by
    have hnorm_u : u.norm = U ^ 2 - 2 * V ^ 2 := by
      change u.norm = u.re ^ 2 - 2 * u.im ^ 2
      simp [Zsqrtd.norm_def]
      ring
    have hnorm_pow : u.norm = ((⟨1, 1⟩ : ℤ√2).norm) ^ m := by
      rw [hu_pow]
      exact map_pow Zsqrtd.normMonoidHom (⟨1, 1⟩ : ℤ√2) m
    have hnorm_base : (⟨1, 1⟩ : ℤ√2).norm = -1 := by
      simp [Zsqrtd.norm_def]
    rw [← hnorm_u, hnorm_pow, hnorm_base, hm_odd.neg_one_pow]
  have hinv_pow : ((silverUnit ^ (-(m : ℤ)) : (ℤ√2)ˣ) : ℤ√2) = ⟨-U, V⟩ := by
    have h1 : (silverUnit ^ (-(m : ℤ)) : (ℤ√2)ˣ) = (silverUnit⁻¹) ^ m := by
      rw [zpow_neg, zpow_natCast, inv_pow]
    have hinv_val : ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2) = -star (⟨1, 1⟩ : ℤ√2) := by
      rw [silverUnit_inv_val]
      ext <;> simp
    rw [h1, Units.val_pow_eq_pow_val, hinv_val, hm_odd.neg_pow, ← star_pow, ← hu_pow]
    change -star u = ⟨-u.re, u.im⟩
    ext <;> simp
  exact ⟨hU1, hV1, hnorm, hinv_pow⟩

private lemma silverUnit_zpow_three_val :
    ((silverUnit ^ (3 : ℤ) : (ℤ√2)ˣ) : ℤ√2) = ⟨7, 5⟩ := by
  have h3 : (silverUnit ^ (3 : ℤ) : (ℤ√2)ˣ) = silverUnit ^ (3 : ℕ) := rfl
  rw [h3, Units.val_pow_eq_pow_val, silverUnit_val, show (3 : ℕ) = 2 + 1 by rfl, pow_succ, pow_two]
  ext <;> simp

private lemma silverUnit_zpow_neg_three_val :
    ((silverUnit ^ (-3 : ℤ) : (ℤ√2)ˣ) : ℤ√2) = ⟨-7, 5⟩ := by
  have h := (silverUnit_odd_pow_coords (m := 3) (by decide) (by omega)).2.2.2
  have h3 : ((silverUnit ^ (3 : ℕ) : (ℤ√2)ˣ) : ℤ√2) = ⟨7, 5⟩ := by
    simpa using silverUnit_zpow_three_val
  simpa [h3] using h

private lemma general_odd_k_sq_ineq {q d y : ℕ} (hd3 : 3 ≤ d)
    (hpow : q ^ d + 1 = 2 * y ^ 2) {α : ℤ√2} (hnorm : α.norm = (q : ℤ))
    (hre : 1 ≤ α.re) (him_abs : 1 ≤ |α.im|) {C : ℤ} (_hC_pos : 0 < C)
    (hbd : (d : ℤ) * α.re ^ (d - 1) * |α.im| < C * (y : ℤ)) :
    2 * (d : ℤ) ^ 2 * α.im ^ 2 < C ^ 2 * α.re ^ 2 ∧
    2 * ((d : ℤ) ^ 2 - C ^ 2) * α.im ^ 2 < C ^ 2 * (q : ℤ) := by
  have hd_pos : (0 : ℤ) < d := by omega
  have hre_pos : (0 : ℤ) < α.re := by omega
  have hlhs_pos : 0 < (d : ℤ) * α.re ^ (d - 1) * |α.im| := by positivity
  have hsq_lt : ((d : ℤ) * α.re ^ (d - 1) * |α.im|) ^ 2 < (C * (y : ℤ)) ^ 2 := by
    nlinarith
  have hpow_z : (q : ℤ) ^ d + 1 = 2 * (y : ℤ) ^ 2 := by exact_mod_cast hpow
  have hnorm_eq : (q : ℤ) = α.re ^ 2 - 2 * α.im ^ 2 := by
    rw [← hnorm, Zsqrtd.norm_def]
    ring
  have him_sq : 1 ≤ α.im ^ 2 := by
    rw [← sq_abs α.im]
    nlinarith
  have hq_lt_re2 : (q : ℤ) < α.re ^ 2 := by linarith
  have hq_nonneg : (0 : ℤ) ≤ (q : ℤ) := Int.natCast_nonneg q
  have hqd_lt : (q : ℤ) ^ d < (α.re ^ 2) ^ d :=
    pow_lt_pow_left₀ hq_lt_re2 hq_nonneg (by omega)
  have hqd1_le : (q : ℤ) ^ d + 1 ≤ (α.re ^ 2) ^ d := by omega
  have h2d_split : (α.re ^ 2) ^ d = α.re ^ (2 * d - 2) * α.re ^ 2 := by
    rw [← pow_mul, ← pow_add, show 2 * d - 2 + 2 = 2 * d by omega]
  have hmul_lt : α.re ^ (2 * d - 2) * (2 * (d : ℤ) ^ 2 * α.im ^ 2) <
      α.re ^ (2 * d - 2) * (C ^ 2 * α.re ^ 2) := by
    calc
      α.re ^ (2 * d - 2) * (2 * (d : ℤ) ^ 2 * α.im ^ 2)
          = 2 * ((d : ℤ) * α.re ^ (d - 1) * |α.im|) ^ 2 := by
        rw [mul_pow, mul_pow, ← pow_mul, show (d - 1) * 2 = 2 * d - 2 by omega, sq_abs]
        ring
      _ < C ^ 2 * (2 * (y : ℤ) ^ 2) := by
        calc
          2 * ((d : ℤ) * α.re ^ (d - 1) * |α.im|) ^ 2 < 2 * (C * (y : ℤ)) ^ 2 := by linarith
          _ = C ^ 2 * (2 * (y : ℤ) ^ 2) := by ring
      _ = C ^ 2 * ((q : ℤ) ^ d + 1) := by rw [hpow_z]
      _ ≤ C ^ 2 * (α.re ^ 2) ^ d := mul_le_mul_of_nonneg_left hqd1_le (sq_nonneg C)
      _ = α.re ^ (2 * d - 2) * (C ^ 2 * α.re ^ 2) := by
        rw [h2d_split]
        ring
  have h1 : 2 * (d : ℤ) ^ 2 * α.im ^ 2 < C ^ 2 * α.re ^ 2 :=
    lt_of_mul_lt_mul_left hmul_lt (pow_pos hre_pos _).le
  have h2 : 2 * ((d : ℤ) ^ 2 - C ^ 2) * α.im ^ 2 < C ^ 2 * (q : ℤ) := by
    rw [hnorm_eq]
    linarith
  exact ⟨h1, h2⟩

/-! ## 2. General Symbolic Odd-`k` Diophantine Inequality & Sharp `|k| = 3` Bound -/

/-- General symbolic odd-`k` Diophantine inequality on `q ^ d + 1 = 2 * y ^ 2`, together with
the exact sharp `49` bound when `|k| = 3`. -/
theorem zsqrtTwo_fermat_general_odd_k_obstruction
    {q d y : ℕ} (hq3 : 3 ≤ q) (hd_odd : Odd d) (hd3 : 3 ≤ d) (hy_pos : 0 < y)
    (hpow : q ^ d + 1 = 2 * y ^ 2) {k : ℤ} (hk_odd : Odd k)
    (hk1 : 1 ≤ |k|) (h2k : 2 * |k| ≤ (d : ℤ) - 1) {α : ℤ√2}
    (hz : (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d)
    (hnorm : α.norm = (q : ℤ)) :
    let m : ℕ := k.natAbs
    let U : ℤ := ((silverUnit ^ m : (ℤ√2)ˣ) : ℤ√2).re
    let V : ℤ := ((silverUnit ^ m : (ℤ√2)ˣ) : ℤ√2).im
    Odd m ∧ 1 ≤ m ∧
    1 ≤ U ∧ 1 ≤ V ∧ U ^ 2 - 2 * V ^ 2 = -1 ∧
    ((silverUnit ^ (-(m : ℤ)) : (ℤ√2)ˣ) : ℤ√2) = ⟨-U, V⟩ ∧
    1 ≤ α.re ∧
    3 ≤ α.re ∧
    1 ≤ |α.im| ∧
    (k < 0 →
      α ^ d = ⟨U + 2 * V * (y : ℤ), U * (y : ℤ) + V⟩ ∧
      1 ≤ α.im ∧
      2 + (d : ℤ) * α.re ^ (d - 1) * α.im ≤ U * (y : ℤ) + V) ∧
    (0 < k →
      (star α) ^ d = ⟨2 * V * (y : ℤ) - U, U * (y : ℤ) - V⟩ ∧
      α.im ≤ -1 ∧
      2 + (d : ℤ) * α.re ^ (d - 1) * (-α.im) ≤ U * (y : ℤ) - V) ∧
    (d : ℤ) * α.re ^ (d - 1) * |α.im| < (U + V) * (y : ℤ) ∧
    2 * (d : ℤ) ^ 2 * α.im ^ 2 < (U + V) ^ 2 * α.re ^ 2 ∧
    2 * ((d : ℤ) ^ 2 - (U + V) ^ 2) * α.im ^ 2 < (U + V) ^ 2 * (q : ℤ) ∧
    (|k| = 3 →
      U = 7 ∧ V = 5 ∧ 5 ≤ d ∧
      (d : ℤ) * α.re ^ (d - 1) * |α.im| < 7 * (y : ℤ) ∧
      2 * (d : ℤ) ^ 2 * α.im ^ 2 < 49 * α.re ^ 2 ∧
      2 * ((d : ℤ) ^ 2 - 49) * α.im ^ 2 < 49 * (q : ℤ)) := by
  intro m U V
  have hm_cast : (m : ℤ) = |k| := by simp [m]
  have hm_odd : Odd m := by
    rw [Nat.odd_iff]
    have := Int.odd_iff.mp hk_odd
    omega
  have hm1 : 1 ≤ m := by omega
  obtain ⟨hU1, hV1, hUV_norm, hinv_m⟩ := silverUnit_odd_pow_coords hm_odd hm1
  have hnot_ev : ¬ Even k := Int.not_even_iff_odd.mpr hk_odd
  have hnorm_if : α.norm = (if Even k then -(q : ℤ) else (q : ℤ)) := by
    rw [ite_eq_right_iff.mpr (fun h => absurd h hnot_ev), hnorm]
  obtain ⟨_, _, _, _, _, _, _, _, _, hodd, _⟩ :=
    zsqrtTwo_universal_archimedean_cone hq3 hd_odd hd3 hy_pos hpow hk1 h2k hz hnorm_if
  obtain ⟨_, hre1, hneg_im, hpos_im, _, _⟩ := hodd hk_odd
  have hk_ne0 : k ≠ 0 := by omega
  have him_abs : 1 ≤ |α.im| := by
    rcases lt_or_gt_of_ne hk_ne0 with hk_neg | hk_pos
    · have := hneg_im hk_neg
      have him0 : 0 ≤ α.im := by omega
      rw [abs_of_nonneg him0]
      exact this
    · have := hpos_im hk_pos
      have him0 : α.im ≤ 0 := by omega
      rw [abs_of_nonpos him0]
      omega
  have hre3 : 3 ≤ α.re := by
    have hnorm_eq : α.re ^ 2 - 2 * α.im ^ 2 = (q : ℤ) := by
      rw [← hnorm, Zsqrtd.norm_def]
      ring
    have him_sq : 1 ≤ α.im ^ 2 := by
      rw [← sq_abs α.im]
      nlinarith
    have hre_sq : 5 ≤ α.re ^ 2 := by
      have : (3 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq3
      linarith
    nlinarith
  have hcoord := (zsqrtTwo_fermat_coordinate_divisibility hd_odd k α hz).1
  have hneg_branch : k < 0 →
      α ^ d = ⟨U + 2 * V * (y : ℤ), U * (y : ℤ) + V⟩ ∧
      1 ≤ α.im ∧
      2 + (d : ℤ) * α.re ^ (d - 1) * α.im ≤ U * (y : ℤ) + V := by
    intro hk_neg
    have him1 : 1 ≤ α.im := hneg_im hk_neg
    have hmk : -k = (m : ℤ) := by omega
    have hu_eq : ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2) = ⟨U, V⟩ := by
      rw [hmk, zpow_natCast]
    have hpow_c : α ^ d = ⟨U + 2 * V * (y : ℤ), U * (y : ℤ) + V⟩ := by
      rw [hu_eq] at hcoord
      exact hcoord.trans (by ext <;> simp [add_comm])
    have hlb := (zsqrtTwo_pos_coords_lower_bound_pow_im hre1 him1 hd_odd hd3).2.2
    have him_eq : (α ^ d).im = U * (y : ℤ) + V := by rw [hpow_c]
    exact ⟨hpow_c, him1, by linarith⟩
  have hpos_branch : 0 < k →
      (star α) ^ d = ⟨2 * V * (y : ℤ) - U, U * (y : ℤ) - V⟩ ∧
      α.im ≤ -1 ∧
      2 + (d : ℤ) * α.re ^ (d - 1) * (-α.im) ≤ U * (y : ℤ) - V := by
    intro hk_pos
    have him_le : α.im ≤ -1 := hpos_im hk_pos
    have hmk : -k = -(m : ℤ) := by omega
    have hu_eq : ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2) = ⟨-U, V⟩ := by
      rw [hmk]
      exact hinv_m
    have hpow_c : (star α) ^ d = ⟨2 * V * (y : ℤ) - U, U * (y : ℤ) - V⟩ := by
      rw [hu_eq] at hcoord
      rw [← star_pow, hcoord]
      ext <;> simp <;> ring
    set β : ℤ√2 := star α
    have hbre : 1 ≤ β.re := hre1
    have hbim : 1 ≤ β.im := by
      change 1 ≤ -α.im
      omega
    have hlb := (zsqrtTwo_pos_coords_lower_bound_pow_im hbre hbim hd_odd hd3).2.2
    have him_eq : (β ^ d).im = U * (y : ℤ) - V := by rw [hpow_c]
    have hlb' : 2 + (d : ℤ) * α.re ^ (d - 1) * (-α.im) ≤ U * (y : ℤ) - V := by
      change 2 + (d : ℤ) * β.re ^ (d - 1) * β.im ≤ U * (y : ℤ) - V
      linarith
    exact ⟨hpow_c, him_le, hlb'⟩
  have hbd_uv : (d : ℤ) * α.re ^ (d - 1) * |α.im| < (U + V) * (y : ℤ) := by
    have hy1 : (1 : ℤ) ≤ (y : ℤ) := by exact_mod_cast hy_pos
    have hVy : V ≤ V * (y : ℤ) := by nlinarith
    rcases lt_or_gt_of_ne hk_ne0 with hk_neg | hk_pos
    · obtain ⟨_, him1, hlb⟩ := hneg_branch hk_neg
      have him0 : 0 ≤ α.im := by omega
      rw [abs_of_nonneg him0]
      nlinarith
    · obtain ⟨_, him_le, hlb⟩ := hpos_branch hk_pos
      have him0 : α.im ≤ 0 := by omega
      rw [abs_of_nonpos him0]
      nlinarith
  have hsq_uv := general_odd_k_sq_ineq hd3 hpow hnorm hre1 him_abs (by omega) hbd_uv
  refine ⟨hm_odd, hm1, hU1, hV1, hUV_norm, hinv_m, hre1, hre3, him_abs,
    hneg_branch, hpos_branch, hbd_uv, hsq_uv.1, hsq_uv.2, ?_⟩
  intro hk3
  have hm3 : m = 3 := by omega
  have hd5 : 5 ≤ d := by omega
  have hsu3 : ((silverUnit ^ m : (ℤ√2)ˣ) : ℤ√2) = ⟨7, 5⟩ := by
    rw [hm3]
    simpa using silverUnit_zpow_three_val
  have hU7 : U = 7 := by
    change ((silverUnit ^ m : (ℤ√2)ˣ) : ℤ√2).re = 7
    rw [hsu3]
  have hV5 : V = 5 := by
    change ((silverUnit ^ m : (ℤ√2)ˣ) : ℤ√2).im = 5
    rw [hsu3]
  have hbd_7 : (d : ℤ) * α.re ^ (d - 1) * |α.im| < 7 * (y : ℤ) := by
    rcases lt_or_gt_of_ne hk_ne0 with hk_neg | hk_pos
    · obtain ⟨hpow_c, him1, _⟩ := hneg_branch hk_neg
      have hlb5 := zsqrtTwo_pos_coords_lower_bound_pow_im_ge5 hre1 him1 hd_odd hd5
      have him_eq : (α ^ d).im = 7 * (y : ℤ) + 5 := by
        rw [hpow_c, hU7, hV5]
      rw [abs_of_nonneg (by omega)]
      linarith
    · obtain ⟨_, him_le, hlb⟩ := hpos_branch hk_pos
      have him0 : α.im ≤ 0 := by omega
      rw [abs_of_nonpos him0]
      rw [hU7, hV5] at hlb
      linarith
  have hsq_7 := general_odd_k_sq_ineq hd3 hpow hnorm hre1 him_abs (by norm_num) hbd_7
  exact ⟨hU7, hV5, hd5, hbd_7, hsq_7.1, hsq_7.2⟩

/-! ## 3. Sharp `|k| = 3` Quartic `q`-Floor -/

private lemma zsqrtTwo_quartic_49_from_sq_ineq {q d : ℕ} (hd7 : 7 ≤ d) {α : ℤ√2}
    (hsq : 2 * ((d : ℤ) ^ 2 - 49) * α.im ^ 2 < 49 * (q : ℤ))
    {r : ℕ} (hr_le : (r : ℤ) ≤ |α.im|) :
    2 * (d ^ 2 - 49) * r ^ 2 < 49 * q := by
  have hr_sq : (r : ℤ) ^ 2 ≤ α.im ^ 2 := by
    rw [← sq_abs α.im]
    exact sq_le_sq' (by linarith [Int.natCast_nonneg r]) hr_le
  have hd2_nonneg : 0 ≤ (d : ℤ) ^ 2 - 49 := by
    have : (7 : ℤ) ≤ d := by exact_mod_cast hd7
    nlinarith
  have hlt_z : 2 * ((d : ℤ) ^ 2 - 49) * (r : ℤ) ^ 2 < 49 * (q : ℤ) :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hr_sq (by linarith)) hsq
  have hd2 : 49 ≤ d ^ 2 := by nlinarith
  have hcast : ((2 * (d ^ 2 - 49) * r ^ 2 : ℕ) : ℤ) =
      2 * ((d : ℤ) ^ 2 - 49) * (r : ℤ) ^ 2 := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hd2, Nat.cast_pow, Nat.cast_pow,
      Nat.cast_ofNat]
  exact Int.ofNat_lt.mp (by simpa [hcast] using hlt_z)

/-- Sharp `|k| = 3` Archimedean + congruence obstruction on `q ^ d + 1 = 2 * y ^ 2`. -/
theorem zsqrtTwo_fermat_k_abs_three_obstruction
    {q d y : ℕ} (hq3 : 3 ≤ q) (hd_odd : Odd d) (hd7 : 7 ≤ d) (hy_pos : 0 < y)
    (hpow : q ^ d + 1 = 2 * y ^ 2) {k : ℤ} (hk_abs : |k| = 3) {α : ℤ√2}
    (hz : (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d)
    (hnorm : α.norm = (q : ℤ)) :
    (k = -3 →
      α ^ d = ⟨7 + 10 * (y : ℤ), 7 * (y : ℤ) + 5⟩ ∧
      3 ≤ α.re ∧ 1 ≤ α.im ∧
      (d : ℤ) * α.re ^ (d - 1) * α.im < 7 * (y : ℤ)) ∧
    (k = 3 →
      (star α) ^ d = ⟨10 * (y : ℤ) - 7, 7 * (y : ℤ) - 5⟩ ∧
      3 ≤ α.re ∧ α.im ≤ -1 ∧
      (d : ℤ) * α.re ^ (d - 1) * (-α.im) < 7 * (y : ℤ)) ∧
    3 ≤ α.re ∧
    1 ≤ |α.im| ∧
    2 * (d : ℤ) ^ 2 * α.im ^ 2 < 49 * α.re ^ 2 ∧
    2 * ((d : ℤ) ^ 2 - 49) * α.im ^ 2 < 49 * (q : ℤ) ∧
    (Even α.im →
      α.im ≡ ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2).im [ZMOD (d : ℤ)] →
      (k = -3 → (d : ℤ) + 5 ≤ α.im ∧ 2 * (d ^ 2 - 49) * (d + 5) ^ 2 < 49 * q) ∧
      (k = 3 → (d : ℤ) - 5 ≤ -α.im) ∧
      (d : ℤ) - 5 ≤ |α.im| ∧
      2 * (d ^ 2 - 49) * (d - 5) ^ 2 < 49 * q) := by
  have hd3 : 3 ≤ d := by omega
  have hk_cases : k = 3 ∨ k = -3 := abs_eq (by norm_num : (0 : ℤ) ≤ 3) |>.mp hk_abs
  have hk_odd : Odd k := by
    rcases hk_cases with rfl | rfl <;> decide
  have hk1 : 1 ≤ |k| := by omega
  have h2k : 2 * |k| ≤ (d : ℤ) - 1 := by omega
  obtain ⟨_, _, _, _, _, _, _, hre3, him_abs, hneg_b, hpos_b, _, _, _, hk3_b⟩ :=
    zsqrtTwo_fermat_general_odd_k_obstruction hq3 hd_odd hd3 hy_pos hpow hk_odd hk1 h2k hz hnorm
  obtain ⟨hU7, hV5, _, hbd_7, hsq_49_re, hsq_49_q⟩ := hk3_b hk_abs
  have hm3_branch : k = -3 →
      α ^ d = ⟨7 + 10 * (y : ℤ), 7 * (y : ℤ) + 5⟩ ∧
      3 ≤ α.re ∧ 1 ≤ α.im ∧
      (d : ℤ) * α.re ^ (d - 1) * α.im < 7 * (y : ℤ) := by
    rintro rfl
    obtain ⟨hpow_c, him1, _⟩ := hneg_b (by norm_num)
    rw [hU7, hV5] at hpow_c
    have hpow_c' : α ^ d = ⟨7 + 10 * (y : ℤ), 7 * (y : ℤ) + 5⟩ := by
      simpa [mul_assoc] using hpow_c
    have hbd' : (d : ℤ) * α.re ^ (d - 1) * α.im < 7 * (y : ℤ) := by
      rwa [abs_of_nonneg (by omega)] at hbd_7
    exact ⟨hpow_c', hre3, him1, hbd'⟩
  have hp3_branch : k = 3 →
      (star α) ^ d = ⟨10 * (y : ℤ) - 7, 7 * (y : ℤ) - 5⟩ ∧
      3 ≤ α.re ∧ α.im ≤ -1 ∧
      (d : ℤ) * α.re ^ (d - 1) * (-α.im) < 7 * (y : ℤ) := by
    rintro rfl
    obtain ⟨hpow_c, him_le, _⟩ := hpos_b (by norm_num)
    rw [hU7, hV5] at hpow_c
    have hpow_c' : (star α) ^ d = ⟨10 * (y : ℤ) - 7, 7 * (y : ℤ) - 5⟩ := by
      simpa [mul_assoc] using hpow_c
    have hbd' : (d : ℤ) * α.re ^ (d - 1) * (-α.im) < 7 * (y : ℤ) := by
      rwa [abs_of_nonpos (by omega)] at hbd_7
    exact ⟨hpow_c', hre3, him_le, hbd'⟩
  refine ⟨hm3_branch, hp3_branch, hre3, him_abs, hsq_49_re, hsq_49_q, ?_⟩
  intro hev_im him_mod
  have him_mod5 : α.im ≡ 5 [ZMOD (d : ℤ)] := by
    rcases hk_cases with rfl | rfl
    · have hu : ((silverUnit ^ (-(3 : ℤ)) : (ℤ√2)ˣ) : ℤ√2).im = 5 := by
        rw [silverUnit_zpow_neg_three_val]
      rwa [hu] at him_mod
    · have hu : ((silverUnit ^ (-(-3 : ℤ)) : (ℤ√2)ˣ) : ℤ√2).im = 5 := by
        simpa using congrArg Zsqrtd.im silverUnit_zpow_three_val
      rwa [hu] at him_mod
  have hm3_cong : k = -3 → (d : ℤ) + 5 ≤ α.im ∧ 2 * (d ^ 2 - 49) * (d + 5) ^ 2 < 49 * q := by
    rintro rfl
    have him1 : 1 ≤ α.im := (hm3_branch rfl).2.2.1
    obtain ⟨t, ht⟩ := Int.modEq_iff_add_fac.mp him_mod5.symm
    have hd_pos : (0 : ℤ) < d := by omega
    have ht_pos : 1 ≤ t := by
      by_contra! ht0
      have ht_le : t ≤ 0 := by omega
      rcases lt_or_eq_of_le ht_le with ht_neg | rfl
      · have hdt : (d : ℤ) * t ≤ -(d : ℤ) := by nlinarith
        linarith
      · have him5 : α.im = 5 := by linarith
        rw [him5] at hev_im
        exact (by decide : ¬ Even (5 : ℤ)) hev_im
    have hdp5_le : (d : ℤ) + 5 ≤ α.im := by
      have : (d : ℤ) * 1 ≤ (d : ℤ) * t := mul_le_mul_of_nonneg_left ht_pos hd_pos.le
      linarith
    have habs_le : ((d + 5 : ℕ) : ℤ) ≤ |α.im| := by
      rw [abs_of_nonneg (by omega)]
      push_cast
      exact hdp5_le
    exact ⟨hdp5_le, zsqrtTwo_quartic_49_from_sq_ineq hd7 hsq_49_q habs_le⟩
  have hp3_cong : k = 3 → (d : ℤ) - 5 ≤ -α.im := by
    rintro rfl
    have him_le : α.im ≤ -1 := (hp3_branch rfl).2.2.1
    have hdvd : (d : ℤ) ∣ -α.im + 5 := by
      have h1 : -α.im + 5 ≡ 0 [ZMOD (d : ℤ)] := by
        have := him_mod5.neg.add_right 5
        simpa using this
      exact Int.modEq_zero_iff_dvd.mp h1
    have hd_le : (d : ℤ) ≤ -α.im + 5 := Int.le_of_dvd (by omega) hdvd
    omega
  have hdm5_abs : (d : ℤ) - 5 ≤ |α.im| := by
    rcases hk_cases with rfl | rfl
    · rw [abs_of_nonpos (by have := (hp3_branch rfl).2.2.1; omega)]
      exact hp3_cong rfl
    · rw [abs_of_nonneg (by have := (hm3_branch rfl).2.2.1; omega)]
      have := (hm3_cong rfl).1
      omega
  have habs_nat_le : ((d - 5 : ℕ) : ℤ) ≤ |α.im| := by
    rw [Nat.cast_sub (by omega), Nat.cast_ofNat]
    exact hdm5_abs
  exact ⟨hm3_cong, hp3_cong, hdm5_abs, zsqrtTwo_quartic_49_from_sq_ineq hd7 hsq_49_q habs_nat_le⟩

private lemma k3_floor_17 (d : ℕ) (hd17 : 17 ≤ d) :
    1410 * 49 < 2 * (d ^ 2 - 49) * (d - 5) ^ 2 := by
  have h1 : 17 ^ 2 - 49 ≤ d ^ 2 - 49 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hd17 2) 49
  have h2 : (17 - 5) ^ 2 ≤ (d - 5) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hmul : 2 * ((17 ^ 2 - 49) * (17 - 5) ^ 2) ≤ 2 * ((d ^ 2 - 49) * (d - 5) ^ 2) :=
    Nat.mul_le_mul_left 2 (Nat.mul_le_mul h1 h2)
  have h17 : 1410 * 49 < 2 * ((17 ^ 2 - 49) * (17 - 5) ^ 2) := by norm_num
  have hassoc : 2 * ((d ^ 2 - 49) * (d - 5) ^ 2) = 2 * (d ^ 2 - 49) * (d - 5) ^ 2 := by ring
  omega

private lemma k3_floor_17_plus (d : ℕ) (hd17 : 17 ≤ d) :
    4741 * 49 < 2 * (d ^ 2 - 49) * (d + 5) ^ 2 := by
  have h1 : 17 ^ 2 - 49 ≤ d ^ 2 - 49 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hd17 2) 49
  have h2 : (17 + 5) ^ 2 ≤ (d + 5) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hmul : 2 * ((17 ^ 2 - 49) * (17 + 5) ^ 2) ≤ 2 * ((d ^ 2 - 49) * (d + 5) ^ 2) :=
    Nat.mul_le_mul_left 2 (Nat.mul_le_mul h1 h2)
  have h17 : 4741 * 49 < 2 * ((17 ^ 2 - 49) * (17 + 5) ^ 2) := by norm_num
  have hassoc : 2 * ((d ^ 2 - 49) * (d + 5) ^ 2) = 2 * (d ^ 2 - 49) * (d + 5) ^ 2 := by ring
  omega

private lemma k3_floor_241 (d : ℕ) (hd241 : 241 ≤ d) :
    131924500 * 49 < 2 * (d ^ 2 - 49) * (d - 5) ^ 2 := by
  have h1 : 241 ^ 2 - 49 ≤ d ^ 2 - 49 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hd241 2) 49
  have h2 : (241 - 5) ^ 2 ≤ (d - 5) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hmul : 2 * ((241 ^ 2 - 49) * (241 - 5) ^ 2) ≤ 2 * ((d ^ 2 - 49) * (d - 5) ^ 2) :=
    Nat.mul_le_mul_left 2 (Nat.mul_le_mul h1 h2)
  have h241 : 131924500 * 49 < 2 * ((241 ^ 2 - 49) * (241 - 5) ^ 2) := by norm_num
  have hassoc : 2 * ((d ^ 2 - 49) * (d - 5) ^ 2) = 2 * (d ^ 2 - 49) * (d - 5) ^ 2 := by ring
  omega

private lemma k3_floor_241_plus (d : ℕ) (hd241 : 241 ≤ d) :
    143341408 * 49 < 2 * (d ^ 2 - 49) * (d + 5) ^ 2 := by
  have h1 : 241 ^ 2 - 49 ≤ d ^ 2 - 49 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hd241 2) 49
  have h2 : (241 + 5) ^ 2 ≤ (d + 5) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hmul : 2 * ((241 ^ 2 - 49) * (241 + 5) ^ 2) ≤ 2 * ((d ^ 2 - 49) * (d + 5) ^ 2) :=
    Nat.mul_le_mul_left 2 (Nat.mul_le_mul h1 h2)
  have h241 : 143341408 * 49 < 2 * ((241 ^ 2 - 49) * (241 + 5) ^ 2) := by norm_num
  have hassoc : 2 * ((d ^ 2 - 49) * (d + 5) ^ 2) = 2 * (d ^ 2 - 49) * (d + 5) ^ 2 := by ring
  omega

/-- Unconditional `|k| = 3` quartic obstruction on any exceptional Euler-index witness
`sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`):
forces `Even α.im`, `3 ≤ α.re`, `(d : ℤ) - 5 ≤ |α.im|`,
`2 * (d : ℤ) ^ 2 * α.im ^ 2 < 49 * α.re ^ 2`, `2 * (d ^ 2 - 49) * (d - 5) ^ 2 < 49 * q`,
`1410 < q` (`4741 < q` when `k = -3`), and `131924500 < q` (`10 ^ 8 < q`; `143341408 < q` when
`k = -3`) when `¬ 3 ∣ N ∧ ¬ 5 ∣ N`. -/
theorem exceptional_euler_unit_exponent_three_quartic_bound
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
      (|k| = 3 →
        Even α.im ∧
        3 ≤ α.re ∧
        (d : ℤ) - 5 ≤ |α.im| ∧
        2 * (d : ℤ) ^ 2 * α.im ^ 2 < 49 * α.re ^ 2 ∧
        2 * (d ^ 2 - 49) * (d - 5) ^ 2 < 49 * q ∧
        1410 < q ∧
        (k = -3 → (d : ℤ) + 5 ≤ α.im ∧ 2 * (d ^ 2 - 49) * (d + 5) ^ 2 < 49 * q ∧ 4741 < q) ∧
        (¬ 3 ∣ N → ¬ 5 ∣ N →
          241 ≤ d ∧ 131924500 < q ∧ 10 ^ 8 < q ∧ (k = -3 → 143341408 < q))) := by
  intro d
  obtain ⟨_, hd17, hd8, _, _, _, _⟩ :=
    exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hd_odd : Odd d := Nat.odd_iff.mpr (by omega)
  have hd7 : 7 ≤ d := by omega
  obtain ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, hnorm, _, _, _, _, him_d,
      _, _, hk_odd_prof⟩ :=
    exceptional_euler_zsqrtTwo_mod_eight_d_profile hN ho hq hq4 ha4 ha hqm hform hl hi
  refine ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, hnorm, ?_⟩
  intro hk_abs
  have hk_cases : k = 3 ∨ k = -3 := abs_eq (by norm_num : (0 : ℤ) ≤ 3) |>.mp hk_abs
  have hk_odd_val : Odd k := by
    rcases hk_cases with rfl | rfl <;> decide
  have hnot_even : ¬ Even k := Int.not_even_iff_odd.mpr hk_odd_val
  have hnorm_pos : α.norm = (q : ℤ) := by
    rw [hnorm, ite_eq_right_iff.mpr (fun h => absurd h hnot_even)]
  have hev_im : Even α.im := (hk_odd_prof hk_odd_val).1
  obtain ⟨_, _, hre3, _, hsq_49, _, hcong⟩ :=
    zsqrtTwo_fermat_k_abs_three_obstruction hq3 hd_odd hd7 hy_pos hpow hk_abs hz_eq hnorm_pos
  obtain ⟨hm3_cong, _, hdm5, h49q⟩ := hcong hev_im him_d
  have h1410 : 1410 < q := by
    have hfl := k3_floor_17 d hd17
    omega
  have hm3_full : k = -3 →
      (d : ℤ) + 5 ≤ α.im ∧ 2 * (d ^ 2 - 49) * (d + 5) ^ 2 < 49 * q ∧ 4741 < q := by
    intro hkm3
    obtain ⟨him_p, hq_p⟩ := hm3_cong hkm3
    have hfl := k3_floor_17_plus d hd17
    exact ⟨him_p, hq_p, by omega⟩
  have h241_branch : ¬ 3 ∣ N → ¬ 5 ∣ N →
      241 ≤ d ∧ 131924500 < q ∧ 10 ^ 8 < q ∧ (k = -3 → 143341408 < q) := by
    intro h3 h5
    obtain ⟨_, _, _, hd241, _⟩ :=
      exceptional_euler_of_not_three_or_five_dvd hN ho hq hq4 ha4 ha hqm hform hl hi h3 h5
    have hfl := k3_floor_241 d hd241
    have h131m : 131924500 < q := by omega
    refine ⟨hd241, h131m, by omega, ?_⟩
    intro hkm3
    obtain ⟨_, hq_p⟩ := hm3_cong hkm3
    have hfl_p := k3_floor_241_plus d hd241
    omega
  exact ⟨hev_im, hre3, hdm5, hsq_49, h49q, h1410, hm3_full, h241_branch⟩

/-! ## 4. Unified `|k| ≤ 3` Quartic `q`-Floor -/

private lemma k1_floor_17 (d : ℕ) (hd17 : 17 ≤ d) :
    147456 ≤ 2 * (d ^ 2 - 1) * (d - 1) ^ 2 := by
  have h1 : 17 ^ 2 - 1 ≤ d ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hd17 2) 1
  have h2 : (17 - 1) ^ 2 ≤ (d - 1) ^ 2 := Nat.pow_le_pow_left (Nat.sub_le_sub_right hd17 1) 2
  have hmul : (17 ^ 2 - 1) * (17 - 1) ^ 2 ≤ (d ^ 2 - 1) * (d - 1) ^ 2 := Nat.mul_le_mul h1 h2
  calc
    147456 = 2 * ((17 ^ 2 - 1) * (17 - 1) ^ 2) := by norm_num
    _ ≤ 2 * ((d ^ 2 - 1) * (d - 1) ^ 2) := Nat.mul_le_mul_left 2 hmul
    _ = 2 * (d ^ 2 - 1) * (d - 1) ^ 2 := (mul_assoc _ _ _).symm

private lemma k1_floor_241 (d : ℕ) (hd241 : 241 ≤ d) :
    6690816000 ≤ 2 * (d ^ 2 - 1) * (d - 1) ^ 2 := by
  have h1 : 241 ^ 2 - 1 ≤ d ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hd241 2) 1
  have h2 : (241 - 1) ^ 2 ≤ (d - 1) ^ 2 := Nat.pow_le_pow_left (Nat.sub_le_sub_right hd241 1) 2
  have hmul : (241 ^ 2 - 1) * (241 - 1) ^ 2 ≤ (d ^ 2 - 1) * (d - 1) ^ 2 := Nat.mul_le_mul h1 h2
  calc
    6690816000 = 2 * ((241 ^ 2 - 1) * (241 - 1) ^ 2) := by norm_num
    _ ≤ 2 * ((d ^ 2 - 1) * (d - 1) ^ 2) := Nat.mul_le_mul_left 2 hmul
    _ = 2 * (d ^ 2 - 1) * (d - 1) ^ 2 := (mul_assoc _ _ _).symm

/-- Unified `|k| ≤ 3` quartic `q`-floor on any exceptional Euler-index witness
`sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`):
combines `|k| = 1` (`147456 < q`, `6690816000 < q`), `|k| = 2` (`148403 < q`, `6703954379 < q`),
and `|k| = 3` (`1410 < q`, `131924500 < q`) into `1410 < q` unconditionally and
`131924500 < q` (`10 ^ 8 < q`) when `¬ 3 ∣ N ∧ ¬ 5 ∣ N`. -/
theorem exceptional_euler_k_le_three_unified_floor
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
      (|k| ≤ 3 →
        1410 < q ∧
        (¬ 3 ∣ N → ¬ 5 ∣ N → 241 ≤ d ∧ 131924500 < q ∧ 10 ^ 8 < q)) := by
  intro d
  obtain ⟨_, hd17, hd8, hq16, _, _, _⟩ :=
    exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hd_odd : Odd d := Nat.odd_iff.mpr (by omega)
  have hd3 : 3 ≤ d := by omega
  have hd5 : 5 ≤ d := by omega
  have hd7 : 7 ≤ d := by omega
  obtain ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, hnorm, _, _, _,
      hre_d, him_d, hre8, _, hk_odd_prof⟩ :=
    exceptional_euler_zsqrtTwo_mod_eight_d_profile hN ho hq hq4 ha4 ha hqm hform hl hi
  refine ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, hnorm, ?_⟩
  intro hkle3
  have hk_cases : |k| = 1 ∨ |k| = 2 ∨ |k| = 3 := by omega
  rcases hk_cases with hk1_eq | hk2_eq | hk3_eq
  · have hq_lt : 2 * (d ^ 2 - 1) * (d - 1) ^ 2 < q := by
      have hk_pm : k = 1 ∨ k = -1 := abs_eq (by norm_num : (0 : ℤ) ≤ 1) |>.mp hk1_eq
      have hk_odd_val : Odd k := by rcases hk_pm with rfl | rfl <;> decide
      have hnot_even : ¬ Even k := Int.not_even_iff_odd.mpr hk_odd_val
      have hnorm_pos : α.norm = (q : ℤ) := by
        rw [hnorm, ite_eq_right_iff.mpr (fun h => absurd h hnot_even)]
      have hev_im : Even α.im := (hk_odd_prof hk_odd_val).1
      rcases hk_pm with rfl | rfl
      · have hu : ((silverUnit ^ (-(1 : ℤ)) : (ℤ√2)ˣ) : ℤ√2).im = 1 := by
          have hu_eq : ((silverUnit ^ (-(1 : ℤ)) : (ℤ√2)ˣ) : ℤ√2) = ⟨-1, 1⟩ := by
            simpa using silverUnit_inv_val
          rw [hu_eq]
        have him_mod : α.im ≡ 1 [ZMOD (d : ℤ)] := by rwa [hu] at him_d
        exact ((zsqrtTwo_fermat_k_pos_one_obstruction hq hd_odd hd3 hpow hz_eq hnorm_pos).2.2.2.2
          him_mod).2
      · have hu : ((silverUnit ^ (-(-1 : ℤ)) : (ℤ√2)ˣ) : ℤ√2).im = 1 := by
          have hu_eq : ((silverUnit ^ (-(-1 : ℤ)) : (ℤ√2)ˣ) : ℤ√2) = ⟨1, 1⟩ := by
            simpa using silverUnit_val
          rw [hu_eq]
        have him_mod : α.im ≡ 1 [ZMOD (d : ℤ)] := by rwa [hu] at him_d
        have hlt_p1 := ((zsqrtTwo_fermat_k_neg_one_obstruction hq hd_odd hd3 hpow hz_eq
          hnorm_pos).2.2.2.2 hev_im him_mod).2
        have hmono : 2 * (d ^ 2 - 1) * (d - 1) ^ 2 ≤ 2 * (d ^ 2 - 1) * (d + 1) ^ 2 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
        exact lt_of_le_of_lt hmono hlt_p1
    have h147456 : 147456 < q := lt_of_le_of_lt (k1_floor_17 d hd17) hq_lt
    refine ⟨by omega, ?_⟩
    intro h3 h5
    obtain ⟨_, _, _, hd241, _⟩ :=
      exceptional_euler_of_not_three_or_five_dvd hN ho hq hq4 ha4 ha hqm hform hl hi h3 h5
    have h669 : 6690816000 < q := lt_of_le_of_lt (k1_floor_241 d hd241) hq_lt
    exact ⟨hd241, by omega, by omega⟩
  · have hk_pm : k = 2 ∨ k = -2 := abs_eq (by norm_num : (0 : ℤ) ≤ 2) |>.mp hk2_eq
    have hk_even : Even k := by rcases hk_pm with rfl | rfl <;> decide
    have hnorm_neg : α.norm = -(q : ℤ) := by
      rw [hnorm, ite_eq_left_iff.mpr (fun h => absurd hk_even h)]
    obtain ⟨_, _, _, _, _, _, hcong⟩ :=
      zsqrtTwo_fermat_k_abs_two_obstruction hq3 hd_odd hd5 hy_pos hpow hk2_eq hz_eq hnorm_neg
    obtain ⟨_, _, _, _, h8q⟩ := hcong hd8 hq16 hre_d hre8
    have h148 : 148403 < q := by
      have h1 : 17 ^ 2 - 8 ≤ d ^ 2 - 8 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hd17 2) 8
      have h2 : (4 * 17 - 3) ^ 2 ≤ (4 * d - 3) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have hmul : (17 ^ 2 - 8) * (4 * 17 - 3) ^ 2 ≤ (d ^ 2 - 8) * (4 * d - 3) ^ 2 :=
        Nat.mul_le_mul h1 h2
      have h17 : 148403 * 8 < (17 ^ 2 - 8) * (4 * 17 - 3) ^ 2 := by norm_num
      omega
    refine ⟨by omega, ?_⟩
    intro h3 h5
    obtain ⟨_, _, _, hd241, _⟩ :=
      exceptional_euler_of_not_three_or_five_dvd hN ho hq hq4 ha4 ha hqm hform hl hi h3 h5
    have h670 : 6703954379 < q := by
      have h1 : 241 ^ 2 - 8 ≤ d ^ 2 - 8 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hd241 2) 8
      have h2 : (4 * 241 - 3) ^ 2 ≤ (4 * d - 3) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have hmul : (241 ^ 2 - 8) * (4 * 241 - 3) ^ 2 ≤ (d ^ 2 - 8) * (4 * d - 3) ^ 2 :=
        Nat.mul_le_mul h1 h2
      have h241 : 6703954379 * 8 < (241 ^ 2 - 8) * (4 * 241 - 3) ^ 2 := by norm_num
      omega
    exact ⟨hd241, by omega, by omega⟩
  · have hk_pm : k = 3 ∨ k = -3 := abs_eq (by norm_num : (0 : ℤ) ≤ 3) |>.mp hk3_eq
    have hk_odd_val : Odd k := by rcases hk_pm with rfl | rfl <;> decide
    have hnot_even : ¬ Even k := Int.not_even_iff_odd.mpr hk_odd_val
    have hnorm_pos : α.norm = (q : ℤ) := by
      rw [hnorm, ite_eq_right_iff.mpr (fun h => absurd h hnot_even)]
    have hev_im : Even α.im := (hk_odd_prof hk_odd_val).1
    obtain ⟨_, _, _, _, _, _, hcong⟩ :=
      zsqrtTwo_fermat_k_abs_three_obstruction hq3 hd_odd hd7 hy_pos hpow hk3_eq hz_eq hnorm_pos
    obtain ⟨_, _, _, h49q⟩ := hcong hev_im him_d
    have h1410 : 1410 < q := by
      have hfl := k3_floor_17 d hd17
      omega
    refine ⟨h1410, ?_⟩
    intro h3 h5
    obtain ⟨_, _, _, hd241, _⟩ :=
      exceptional_euler_of_not_three_or_five_dvd hN ho hq hq4 ha4 ha hqm hform hl hi h3 h5
    have hfl := k3_floor_241 d hd241
    exact ⟨hd241, by omega, by omega⟩

end OddPerfect
