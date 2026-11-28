module

public import OddPerfect.ZsqrtTwoCubicObstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# General Even-`k` Diophantine Inequality & Sharp `|k| = 4` Quartic Floors in `ℤ√2`
(`OddPerfect.ZsqrtTwoEvenKAndQuarticObstruction`)

Completes the symbolic arbitrary-`k` Diophantine theory in `ℤ√2` by proving the general even-`k`
obstruction (`Even k`, `k ≠ 0`, complementing `OddPerfect.ZsqrtTwoCubicObstruction` for `Odd k`)
and specializing to `|k| = 4` (`silverUnit ^ 4 = ⟨17, 12⟩`), unifying the `q`-floor tower across
all `|k| ≤ 4`:

1. `silverUnit_even_pow_coords` and `zsqrtTwo_pos_coords_lower_bound_pow_re_ge5_sharp`:
   for even `m ≥ 2`, sets `U := (silverUnit ^ m).re`, `V := (silverUnit ^ m).im`, proves
   `3 ≤ U`, `2 ≤ V`, `U ^ 2 - 2 * V ^ 2 = 1`, `silverUnit ^ (-m) = ⟨U, -V⟩`; and for `1 ≤ β.re`,
   `2 ≤ β.im`, and odd `d ≥ 5`, strengthens the real-part power lower bound to
   `81 + (d : ℤ) * β.re * 2 ^ ((d - 1) / 2) * β.im ^ (d - 1) ≤ (β ^ d).re`.
2. `zsqrtTwo_fermat_general_even_k_obstruction` and `zsqrtTwo_fermat_k_abs_four_obstruction`:
   for every even `k` with `1 ≤ |k|` and `2 * |k| ≤ d - 1` on `q ^ d + 1 = 2 * y ^ 2`, proves
   `1 ≤ |α.re|`, `2 ≤ α.im`,
   `(d : ℤ) * |α.re| * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1) < (U + 2 * V) * (y : ℤ)`,
   `(d : ℤ) ^ 2 * α.re ^ 2 < (U + 2 * V) ^ 2 * α.im ^ 2`, and
   `(2 * (d : ℤ) ^ 2 - (U + 2 * V) ^ 2) * α.re ^ 2 < (U + 2 * V) ^ 2 * (q : ℤ)`.
   At `|k| = 4` (`U = 17, V = 12`, `d ≥ 5`), uses `81 > 17` to sharpen this to
   `(d : ℤ) * |α.re| * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1) < 24 * (y : ℤ)`,
   `(d : ℤ) ^ 2 * α.re ^ 2 < 576 * α.im ^ 2`, and
   `((d : ℤ) ^ 2 - 288) * α.re ^ 2 < 288 * (q : ℤ)`.
3. `exceptional_euler_unit_exponent_four_bound` and `exceptional_euler_k_le_four_unified_floor`:
   on any exceptional Euler-index witness (`sigma 1 (m ^ 2) / q ^ a = l * t ^ 2`, `a > 1`,
   `l.Prime`), pins `17 ≤ |α.re|` (`17 ≤ α.re` for `k = -4`, `d - 17 ≤ -α.re` for `k = 4`) when
   `¬ 3 ∣ N ∧ ¬ 5 ∣ N` (`241 ≤ d`), yielding `(241 ^ 2 - 288) * 17 ^ 2 < 288 * q` and hence
   `57993 < q` (`10068824 < q` when `k = 4`), and unifies all `|k| ≤ 4` into `241 ≤ d ∧ 57993 < q`.
-/

public section

namespace OddPerfect

open ArithmeticFunction

/-! ## 1. Even `silverUnit` Powers & Sharp `81` Real-Part Power Lower Bound -/

/-- Coordinates, norm, and inverse formula for even positive powers of `silverUnit`. -/
theorem silverUnit_even_pow_coords {m : ℕ} (hm_even : Even m) (hm2 : 2 ≤ m) :
    let U : ℤ := ((silverUnit ^ m : (ℤ√2)ˣ) : ℤ√2).re
    let V : ℤ := ((silverUnit ^ m : (ℤ√2)ˣ) : ℤ√2).im
    3 ≤ U ∧ 2 ≤ V ∧ U ^ 2 - 2 * V ^ 2 = 1 ∧
    ((silverUnit ^ (-(m : ℤ)) : (ℤ√2)ˣ) : ℤ√2) = ⟨U, -V⟩ := by
  intro U V
  set u : ℤ√2 := ((silverUnit ^ m : (ℤ√2)ˣ) : ℤ√2)
  have hu_pow : u = (⟨1, 1⟩ : ℤ√2) ^ m := by
    change ((silverUnit ^ m : (ℤ√2)ˣ) : ℤ√2) = (⟨1, 1⟩ : ℤ√2) ^ m
    rw [Units.val_pow_eq_pow_val, silverUnit_val]
  obtain ⟨j, hj⟩ := hm_even
  have hj1 : 1 ≤ j := by omega
  have hm_eq : m = 2 * j := by omega
  have hu_sq_pow : u = (⟨3, 2⟩ : ℤ√2) ^ j := by
    have hsq : (⟨1, 1⟩ : ℤ√2) ^ 2 = ⟨3, 2⟩ := by
      rw [pow_two]
      ext <;> simp
    rw [hu_pow, hm_eq, pow_mul, hsq]
  have hbounds : ∀ n : ℕ, 1 ≤ n →
      3 ≤ ((⟨3, 2⟩ : ℤ√2) ^ n).re ∧ 2 ≤ ((⟨3, 2⟩ : ℤ√2) ^ n).im := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      rw [pow_succ, Zsqrtd.re_mul, Zsqrtd.im_mul]
      refine ⟨?_, ?_⟩ <;> nlinarith [ih.1, ih.2]
  have hU3 : 3 ≤ U := by
    change 3 ≤ u.re
    rw [hu_sq_pow]
    exact (hbounds j hj1).1
  have hV2 : 2 ≤ V := by
    change 2 ≤ u.im
    rw [hu_sq_pow]
    exact (hbounds j hj1).2
  have hnorm : U ^ 2 - 2 * V ^ 2 = 1 := by
    have hnorm_u : u.norm = U ^ 2 - 2 * V ^ 2 := by
      change u.norm = u.re ^ 2 - 2 * u.im ^ 2
      simp [Zsqrtd.norm_def]
      ring
    have hnorm_pow : u.norm = ((⟨1, 1⟩ : ℤ√2).norm) ^ m := by
      rw [hu_pow]
      exact map_pow Zsqrtd.normMonoidHom (⟨1, 1⟩ : ℤ√2) m
    have hnorm_base : (⟨1, 1⟩ : ℤ√2).norm = -1 := by
      simp [Zsqrtd.norm_def]
    rw [← hnorm_u, hnorm_pow, hnorm_base, hm_eq, pow_mul]
    norm_num
  have hinv_pow : ((silverUnit ^ (-(m : ℤ)) : (ℤ√2)ˣ) : ℤ√2) = ⟨U, -V⟩ := by
    have h1 : (silverUnit ^ (-(m : ℤ)) : (ℤ√2)ˣ) = (silverUnit⁻¹) ^ m := by
      rw [zpow_neg, zpow_natCast, inv_pow]
    have hinv_val : ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2) = -star (⟨1, 1⟩ : ℤ√2) := by
      rw [silverUnit_inv_val]
      ext <;> simp
    rw [h1, Units.val_pow_eq_pow_val, hinv_val, hm_eq, pow_mul, neg_sq, ← pow_mul, ← hm_eq,
      ← star_pow, ← hu_pow]
    change star u = ⟨u.re, -u.im⟩
    ext <;> simp
  exact ⟨hU3, hV2, hnorm, hinv_pow⟩

/-- Sharpened `d ≥ 5` real-part power lower bound for `β : ℤ√2` with `1 ≤ β.re` and `2 ≤ β.im`:
`81 + (d : ℤ) * β.re * 2 ^ ((d - 1) / 2) * β.im ^ (d - 1) ≤ (β ^ d).re`. -/
theorem zsqrtTwo_pos_coords_lower_bound_pow_re_ge5_sharp {β : ℤ√2}
    (hre : 1 ≤ β.re) (him : 2 ≤ β.im) {d : ℕ} (hd_odd : Odd d) (hd5 : 5 ≤ d) :
    81 + (d : ℤ) * β.re * 2 ^ ((d - 1) / 2) * β.im ^ (d - 1) ≤ (β ^ d).re := by
  have him1 : 1 ≤ β.im := by omega
  have hpos := (zsqrtTwo_pos_coords_pow_bounds hre him1).1
  have him_pow := (zsqrtTwo_pos_coords_lower_bound_pow_re_k2 hre him hd_odd hd5).1
  obtain ⟨j, rfl⟩ := hd_odd
  have hj2 : 2 ≤ j := by omega
  induction j, hj2 using Nat.le_induction with
  | base =>
    have hβ2 : β ^ 2 = ⟨β.re ^ 2 + 2 * β.im ^ 2, 2 * β.re * β.im⟩ := by
      ext <;> simp [pow_two] <;> ring
    have hpow5 : (β ^ (2 * 2 + 1)).re =
        β.re ^ 5 + 20 * β.re ^ 3 * β.im ^ 2 + 20 * β.re * β.im ^ 4 := by
      have h5 : β ^ (2 * 2 + 1) = (β ^ 2 * β ^ 2) * β := by ring
      rw [h5, hβ2]
      simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
      ring
    have hre5 : 1 ≤ β.re ^ 5 := one_le_pow₀ hre
    have hterm2 : 80 ≤ 20 * β.re ^ 3 * β.im ^ 2 := by
      have h1 : 1 ≤ β.re ^ 3 := one_le_pow₀ hre
      have h2 : 4 ≤ β.im ^ 2 := by nlinarith
      nlinarith
    rw [hpow5]
    norm_num
    linarith
  | succ j hj ih =>
    set m : ℕ := 2 * j + 1
    have hm_odd : Odd m := ⟨j, rfl⟩
    have ih' : 81 + (m : ℤ) * β.re * 2 ^ ((m - 1) / 2) * β.im ^ (m - 1) ≤ (β ^ m).re :=
      ih (by omega)
    have him_m : 2 ^ ((m - 1) / 2) * β.im ^ m ≤ (β ^ m).im := him_pow m hm_odd
    have hstep : β ^ (2 * (j + 1) + 1) = β ^ m * β ^ 2 := by
      rw [show 2 * (j + 1) + 1 = m + 2 by omega, pow_add]
    have hre2 : (β ^ 2).re = β.re ^ 2 + 2 * β.im ^ 2 := by
      rw [pow_two, Zsqrtd.re_mul]; ring
    have him2 : (β ^ 2).im = 2 * β.re * β.im := by
      rw [pow_two, Zsqrtd.im_mul]; ring
    have hm_re_nonneg : 0 ≤ (β ^ m).re := by
      have := (hpos m (by omega)).1
      linarith
    have hsq_le : 2 * β.im ^ 2 ≤ β.re ^ 2 + 2 * β.im ^ 2 := by
      nlinarith [sq_nonneg β.re]
    have h1 : (81 + (m : ℤ) * β.re * 2 ^ ((m - 1) / 2) * β.im ^ (m - 1)) * (2 * β.im ^ 2) ≤
        (β ^ m).re * (β.re ^ 2 + 2 * β.im ^ 2) := by
      calc
        (81 + (m : ℤ) * β.re * 2 ^ ((m - 1) / 2) * β.im ^ (m - 1)) * (2 * β.im ^ 2)
            ≤ (β ^ m).re * (2 * β.im ^ 2) := mul_le_mul_of_nonneg_right ih' (by positivity)
        _ ≤ (β ^ m).re * (β.re ^ 2 + 2 * β.im ^ 2) :=
          mul_le_mul_of_nonneg_left hsq_le hm_re_nonneg
    have h2 : 2 * (2 ^ ((m - 1) / 2) * β.im ^ m) * (2 * β.re * β.im) ≤
        2 * (β ^ m).im * (2 * β.re * β.im) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left him_m (by norm_num)) (by positivity)
    have him2_ge4 : 4 ≤ β.im ^ 2 := by nlinarith
    have hidx_m : (m - 1) / 2 = j := by dsimp [m]; omega
    have hidx_next : (2 * (j + 1) + 1 - 1) / 2 = j + 1 := by omega
    have hm1_eq : 2 * (j + 1) + 1 - 1 = (m - 1) + 2 := by dsimp [m]; omega
    have hm_eq : m + 1 = (m - 1) + 2 := by omega
    rw [hstep, Zsqrtd.re_mul, hre2, him2, hidx_next, hm1_eq]
    rw [hidx_m] at h1 h2
    have hlhs_expand :
        (81 + (m : ℤ) * β.re * 2 ^ j * β.im ^ (m - 1)) * (2 * β.im ^ 2) +
          2 * (2 ^ j * β.im ^ m) * (2 * β.re * β.im) =
        162 * β.im ^ 2 + ((m : ℤ) + 2) * β.re * 2 ^ (j + 1) * β.im ^ ((m - 1) + 2) := by
      have hp1 : β.im ^ ((m - 1) + 2) = β.im ^ (m - 1) * β.im ^ 2 := by rw [pow_add]
      have hp2 : β.im ^ ((m - 1) + 2) = β.im ^ m * β.im := by rw [← hm_eq, pow_succ]
      rw [pow_succ (2 : ℤ) j]
      calc
        (81 + (m : ℤ) * β.re * 2 ^ j * β.im ^ (m - 1)) * (2 * β.im ^ 2) +
            2 * (2 ^ j * β.im ^ m) * (2 * β.re * β.im)
            = 162 * β.im ^ 2 + (m : ℤ) * β.re * (2 ^ j * 2) * (β.im ^ (m - 1) * β.im ^ 2) +
              2 * β.re * (2 ^ j * 2) * (β.im ^ m * β.im) := by ring
        _ = 162 * β.im ^ 2 + ((m : ℤ) + 2) * β.re * (2 ^ j * 2) * β.im ^ ((m - 1) + 2) := by
          rw [← hp1, ← hp2]
          ring
    have hcast : ((2 * (j + 1) + 1 : ℕ) : ℤ) = (m : ℤ) + 2 := by
      dsimp [m]; omega
    rw [hcast]
    linarith

private lemma silverUnit_zpow_four_val :
    ((silverUnit ^ (4 : ℤ) : (ℤ√2)ˣ) : ℤ√2) = ⟨17, 12⟩ := by
  have h4 : (silverUnit ^ (4 : ℤ) : (ℤ√2)ˣ) = silverUnit ^ (4 : ℕ) := rfl
  rw [h4, Units.val_pow_eq_pow_val, silverUnit_val, show (4 : ℕ) = 2 + 2 by rfl, pow_add, pow_two]
  ext <;> simp

private lemma silverUnit_zpow_neg_four_val :
    ((silverUnit ^ (-4 : ℤ) : (ℤ√2)ˣ) : ℤ√2) = ⟨17, -12⟩ := by
  have h := (silverUnit_even_pow_coords (m := 4) (by decide) (by omega)).2.2.2
  have h4 : ((silverUnit ^ (4 : ℕ) : (ℤ√2)ˣ) : ℤ√2) = ⟨17, 12⟩ := by
    simpa using silverUnit_zpow_four_val
  simpa [h4] using h

private lemma general_even_k_sq_ineq {q d y : ℕ} (hd_odd : Odd d) (hd5 : 5 ≤ d)
    (hpow : q ^ d + 1 = 2 * y ^ 2) {α : ℤ√2} (hnorm : α.norm = -(q : ℤ))
    (hre_abs : 1 ≤ |α.re|) (him : 2 ≤ α.im) {C : ℤ} (_hC_pos : 0 < C)
    (hbd : (d : ℤ) * |α.re| * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1) < C * (y : ℤ)) :
    (d : ℤ) ^ 2 * α.re ^ 2 < C ^ 2 * α.im ^ 2 ∧
    (2 * (d : ℤ) ^ 2 - C ^ 2) * α.re ^ 2 < C ^ 2 * (q : ℤ) := by
  have hd_pos : (0 : ℤ) < d := by omega
  have hre_abs_pos : 0 < |α.re| := by omega
  have him_pos : 0 < α.im := by omega
  have hlhs_pos : 0 < (d : ℤ) * |α.re| * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1) := by positivity
  have hsq_lt : ((d : ℤ) * |α.re| * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1)) ^ 2 < (C * (y : ℤ)) ^ 2 := by
    nlinarith
  have hpow_z : (q : ℤ) ^ d + 1 = 2 * (y : ℤ) ^ 2 := by exact_mod_cast hpow
  have hnorm_eq : (q : ℤ) = 2 * α.im ^ 2 - α.re ^ 2 := by
    have hn : α.norm = α.re ^ 2 - 2 * α.im ^ 2 := by simp [Zsqrtd.norm_def]; ring
    linarith
  have hq_nonneg : (0 : ℤ) ≤ (q : ℤ) := Int.natCast_nonneg q
  have hre_sq : 1 ≤ α.re ^ 2 := by
    rw [← sq_abs α.re]
    nlinarith
  have hq_lt_2im2 : (q : ℤ) < 2 * α.im ^ 2 := by linarith
  have hqd_lt : (q : ℤ) ^ d < (2 * α.im ^ 2) ^ d :=
    pow_lt_pow_left₀ hq_lt_2im2 hq_nonneg (by omega)
  have hqd1_le : (q : ℤ) ^ d + 1 ≤ (2 * α.im ^ 2) ^ d := by omega
  have hd_sub_even : (d - 1) / 2 * 2 = d - 1 := by
    obtain ⟨j, rfl⟩ := hd_odd
    omega
  have hexp_lhs : 2 * ((d : ℤ) * |α.re| * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1)) ^ 2 =
      (2 ^ d * α.im ^ (2 * d - 2)) * ((d : ℤ) ^ 2 * α.re ^ 2) := by
    rw [mul_pow, mul_pow, mul_pow, ← pow_mul (2 : ℤ), ← pow_mul α.im, hd_sub_even, sq_abs,
      show (d - 1) * 2 = 2 * d - 2 by omega]
    have hp2 : (2 : ℤ) ^ d = 2 * 2 ^ (d - 1) := by
      rw [mul_comm, ← pow_succ, show d - 1 + 1 = d by omega]
    rw [hp2]
    ring
  have hexp_rhs : C ^ 2 * (2 * α.im ^ 2) ^ d =
      (2 ^ d * α.im ^ (2 * d - 2)) * (C ^ 2 * α.im ^ 2) := by
    rw [mul_pow, ← pow_mul α.im]
    have hpim : α.im ^ (2 * d) = α.im ^ (2 * d - 2) * α.im ^ 2 := by
      rw [← pow_add, show 2 * d - 2 + 2 = 2 * d by omega]
    rw [hpim]
    ring
  have hmul_lt : (2 ^ d * α.im ^ (2 * d - 2)) * ((d : ℤ) ^ 2 * α.re ^ 2) <
      (2 ^ d * α.im ^ (2 * d - 2)) * (C ^ 2 * α.im ^ 2) := by
    calc
      (2 ^ d * α.im ^ (2 * d - 2)) * ((d : ℤ) ^ 2 * α.re ^ 2)
          = 2 * ((d : ℤ) * |α.re| * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1)) ^ 2 := hexp_lhs.symm
      _ < C ^ 2 * (2 * (y : ℤ) ^ 2) := by
        calc
          2 * ((d : ℤ) * |α.re| * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1)) ^ 2
              < 2 * (C * (y : ℤ)) ^ 2 := by linarith
          _ = C ^ 2 * (2 * (y : ℤ) ^ 2) := by ring
      _ = C ^ 2 * ((q : ℤ) ^ d + 1) := by rw [hpow_z]
      _ ≤ C ^ 2 * (2 * α.im ^ 2) ^ d := mul_le_mul_of_nonneg_left hqd1_le (sq_nonneg C)
      _ = (2 ^ d * α.im ^ (2 * d - 2)) * (C ^ 2 * α.im ^ 2) := hexp_rhs
  have hfac_pos : 0 < (2 : ℤ) ^ d * α.im ^ (2 * d - 2) := by positivity
  have h1 : (d : ℤ) ^ 2 * α.re ^ 2 < C ^ 2 * α.im ^ 2 := lt_of_mul_lt_mul_left hmul_lt hfac_pos.le
  have h2 : (2 * (d : ℤ) ^ 2 - C ^ 2) * α.re ^ 2 < C ^ 2 * (q : ℤ) := by
    nlinarith
  exact ⟨h1, h2⟩

/-! ## 2. General Symbolic Even-`k` Diophantine Inequality & Sharp `|k| = 4` Bound -/

/-- General symbolic even-`k` Diophantine inequality on `q ^ d + 1 = 2 * y ^ 2`, together with
the exact sharp `|k| = 4` (`24` / `576` / `288`) obstruction. -/
theorem zsqrtTwo_fermat_general_even_k_obstruction
    {q d y : ℕ} (hq3 : 3 ≤ q) (hd_odd : Odd d) (hd5 : 5 ≤ d) (hy_pos : 0 < y)
    (hpow : q ^ d + 1 = 2 * y ^ 2) {k : ℤ} (hk_even : Even k)
    (hk1 : 1 ≤ |k|) (h2k : 2 * |k| ≤ (d : ℤ) - 1) {α : ℤ√2}
    (hz : (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d)
    (hnorm : α.norm = -(q : ℤ)) :
    let m : ℕ := k.natAbs
    let U : ℤ := ((silverUnit ^ m : (ℤ√2)ˣ) : ℤ√2).re
    let V : ℤ := ((silverUnit ^ m : (ℤ√2)ˣ) : ℤ√2).im
    Even m ∧ 2 ≤ m ∧
    3 ≤ U ∧ 2 ≤ V ∧ U ^ 2 - 2 * V ^ 2 = 1 ∧
    ((silverUnit ^ (-(m : ℤ)) : (ℤ√2)ˣ) : ℤ√2) = ⟨U, -V⟩ ∧
    1 ≤ |α.re| ∧
    2 ≤ α.im ∧
    (k < 0 →
      α ^ d = ⟨U + 2 * V * (y : ℤ), U * (y : ℤ) + V⟩ ∧
      1 ≤ α.re ∧
      81 + (d : ℤ) * α.re * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1) ≤ U + 2 * V * (y : ℤ)) ∧
    (0 < k →
      (-star α) ^ d = ⟨2 * V * (y : ℤ) - U, U * (y : ℤ) - V⟩ ∧
      α.re ≤ -1 ∧
      81 + (d : ℤ) * (-α.re) * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1) ≤ 2 * V * (y : ℤ) - U) ∧
    (d : ℤ) * |α.re| * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1) < (U + 2 * V) * (y : ℤ) ∧
    (d : ℤ) ^ 2 * α.re ^ 2 < (U + 2 * V) ^ 2 * α.im ^ 2 ∧
    (2 * (d : ℤ) ^ 2 - (U + 2 * V) ^ 2) * α.re ^ 2 < (U + 2 * V) ^ 2 * (q : ℤ) ∧
    (|k| = 4 →
      U = 17 ∧ V = 12 ∧
      (d : ℤ) * |α.re| * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1) < 24 * (y : ℤ) ∧
      (d : ℤ) ^ 2 * α.re ^ 2 < 576 * α.im ^ 2 ∧
      ((d : ℤ) ^ 2 - 288) * α.re ^ 2 < 288 * (q : ℤ)) := by
  intro m U V
  have hd3 : 3 ≤ d := by omega
  have hm_cast : (m : ℤ) = |k| := by simp [m]
  have hm_even : Even m := by
    rw [Nat.even_iff]
    have := Int.even_iff.mp hk_even
    omega
  have hm2 : 2 ≤ m := by
    obtain ⟨j, hj⟩ := hm_even
    omega
  obtain ⟨hU3, hV2, hUV_norm, hinv_m⟩ := silverUnit_even_pow_coords hm_even hm2
  have hnorm_if : α.norm = (if Even k then -(q : ℤ) else (q : ℤ)) := by
    rw [ite_eq_left_iff.mpr (fun h => absurd hk_even h), hnorm]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hev⟩ :=
    zsqrtTwo_universal_archimedean_cone hq3 hd_odd hd3 hy_pos hpow hk1 h2k hz hnorm_if
  obtain ⟨_, him1, hneg_re, hpos_re, _, _⟩ := hev hk_even
  have hk_ne0 : k ≠ 0 := by omega
  have hre_abs : 1 ≤ |α.re| := by
    rcases lt_or_gt_of_ne hk_ne0 with hk_neg | hk_pos
    · have := hneg_re hk_neg
      rw [abs_of_nonneg (by omega)]
      exact this
    · have := hpos_re hk_pos
      rw [abs_of_nonpos (by omega)]
      omega
  have him2 : 2 ≤ α.im := by
    have hnorm_eq : 2 * α.im ^ 2 = (q : ℤ) + α.re ^ 2 := by
      have hn : α.norm = α.re ^ 2 - 2 * α.im ^ 2 := by simp [Zsqrtd.norm_def]; ring
      linarith
    have hre_sq : 1 ≤ α.re ^ 2 := by
      rw [← sq_abs α.re]
      nlinarith
    have hq_z : (3 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq3
    have him_sq : 2 ≤ α.im ^ 2 := by linarith
    nlinarith
  have hcoord := (zsqrtTwo_fermat_coordinate_divisibility hd_odd k α hz).1
  have hneg_branch : k < 0 →
      α ^ d = ⟨U + 2 * V * (y : ℤ), U * (y : ℤ) + V⟩ ∧
      1 ≤ α.re ∧
      81 + (d : ℤ) * α.re * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1) ≤ U + 2 * V * (y : ℤ) := by
    intro hk_neg
    have hre1 : 1 ≤ α.re := hneg_re hk_neg
    have hmk : -k = (m : ℤ) := by omega
    have hu_eq : ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2) = ⟨U, V⟩ := by
      rw [hmk, zpow_natCast]
    have hpow_c : α ^ d = ⟨U + 2 * V * (y : ℤ), U * (y : ℤ) + V⟩ := by
      rw [hu_eq] at hcoord
      exact hcoord.trans (by ext <;> simp [add_comm])
    have hlb := zsqrtTwo_pos_coords_lower_bound_pow_re_ge5_sharp hre1 him2 hd_odd hd5
    have hre_eq : (α ^ d).re = U + 2 * V * (y : ℤ) := by rw [hpow_c]
    exact ⟨hpow_c, hre1, by linarith⟩
  have hpos_branch : 0 < k →
      (-star α) ^ d = ⟨2 * V * (y : ℤ) - U, U * (y : ℤ) - V⟩ ∧
      α.re ≤ -1 ∧
      81 + (d : ℤ) * (-α.re) * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1) ≤ 2 * V * (y : ℤ) - U := by
    intro hk_pos
    have hre_le : α.re ≤ -1 := hpos_re hk_pos
    have hmk : -k = -(m : ℤ) := by omega
    have hu_eq : ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2) = ⟨U, -V⟩ := by
      rw [hmk]
      exact hinv_m
    have hpow_c : (-star α) ^ d = ⟨2 * V * (y : ℤ) - U, U * (y : ℤ) - V⟩ := by
      rw [hu_eq] at hcoord
      rw [hd_odd.neg_pow, ← star_pow, hcoord]
      ext <;> simp <;> ring
    set β : ℤ√2 := -star α
    have hbre_eq : β.re = -α.re := by simp [β]
    have hbim_eq : β.im = α.im := by simp [β]
    have hbre : 1 ≤ β.re := by rw [hbre_eq]; omega
    have hbim : 2 ≤ β.im := by rw [hbim_eq]; exact him2
    have hlb := zsqrtTwo_pos_coords_lower_bound_pow_re_ge5_sharp hbre hbim hd_odd hd5
    have hre_eq : (β ^ d).re = 2 * V * (y : ℤ) - U := by rw [hpow_c]
    have hlb' : 81 + (d : ℤ) * (-α.re) * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1) ≤
        2 * V * (y : ℤ) - U := by
      rw [← hbre_eq, ← hbim_eq]
      linarith
    exact ⟨hpow_c, hre_le, hlb'⟩
  have hbd_uv : (d : ℤ) * |α.re| * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1) < (U + 2 * V) * (y : ℤ) := by
    have hy1 : (1 : ℤ) ≤ (y : ℤ) := by exact_mod_cast hy_pos
    have hUy : U ≤ U * (y : ℤ) := by nlinarith
    rcases lt_or_gt_of_ne hk_ne0 with hk_neg | hk_pos
    · obtain ⟨_, hre1, hlb⟩ := hneg_branch hk_neg
      rw [abs_of_nonneg (by omega)]
      linarith
    · obtain ⟨_, hre_le, hlb⟩ := hpos_branch hk_pos
      rw [abs_of_nonpos (by omega)]
      linarith
  have hsq_uv := general_even_k_sq_ineq hd_odd hd5 hpow hnorm hre_abs him2 (by omega) hbd_uv
  refine ⟨hm_even, hm2, hU3, hV2, hUV_norm, hinv_m, hre_abs, him2,
    hneg_branch, hpos_branch, hbd_uv, hsq_uv.1, hsq_uv.2, ?_⟩
  intro hk4
  have hm4 : m = 4 := by omega
  have hsu4 : ((silverUnit ^ m : (ℤ√2)ˣ) : ℤ√2) = ⟨17, 12⟩ := by
    rw [hm4]
    simpa using silverUnit_zpow_four_val
  have hU17 : U = 17 := by
    change ((silverUnit ^ m : (ℤ√2)ˣ) : ℤ√2).re = 17
    rw [hsu4]
  have hV12 : V = 12 := by
    change ((silverUnit ^ m : (ℤ√2)ˣ) : ℤ√2).im = 12
    rw [hsu4]
  have hbd_24 : (d : ℤ) * |α.re| * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1) < 24 * (y : ℤ) := by
    rcases lt_or_gt_of_ne hk_ne0 with hk_neg | hk_pos
    · obtain ⟨_, hre1, hlb⟩ := hneg_branch hk_neg
      rw [hU17, hV12] at hlb
      rw [abs_of_nonneg (by omega)]
      linarith
    · obtain ⟨_, hre_le, hlb⟩ := hpos_branch hk_pos
      rw [hU17, hV12] at hlb
      rw [abs_of_nonpos (by omega)]
      linarith
  have hsq_24 := general_even_k_sq_ineq hd_odd hd5 hpow hnorm hre_abs him2 (by norm_num) hbd_24
  have h576_im : (d : ℤ) ^ 2 * α.re ^ 2 < 576 * α.im ^ 2 := by
    simpa only [show (24 : ℤ) ^ 2 = 576 by norm_num] using hsq_24.1
  have h288_q : ((d : ℤ) ^ 2 - 288) * α.re ^ 2 < 288 * (q : ℤ) := by
    have h := hsq_24.2
    linarith
  exact ⟨hU17, hV12, hbd_24, h576_im, h288_q⟩

/-! ## 3. Sharp `|k| = 4` Quartic `q`-Floor -/

private lemma zsqrtTwo_quartic_288_from_sq_ineq {q d : ℕ} (hd17 : 17 ≤ d) {α : ℤ√2}
    (hsq : ((d : ℤ) ^ 2 - 288) * α.re ^ 2 < 288 * (q : ℤ))
    {r : ℕ} (hr_le : (r : ℤ) ≤ |α.re|) :
    (d ^ 2 - 288) * r ^ 2 < 288 * q := by
  have hr_sq : (r : ℤ) ^ 2 ≤ α.re ^ 2 := by
    rw [← sq_abs α.re]
    exact sq_le_sq' (by linarith [Int.natCast_nonneg r]) hr_le
  have hd2_nonneg : 0 ≤ (d : ℤ) ^ 2 - 288 := by
    have : (17 : ℤ) ≤ d := by exact_mod_cast hd17
    nlinarith
  have hlt_z : ((d : ℤ) ^ 2 - 288) * (r : ℤ) ^ 2 < 288 * (q : ℤ) :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hr_sq hd2_nonneg) hsq
  have hd2 : 288 ≤ d ^ 2 := by nlinarith
  have hcast : (((d ^ 2 - 288) * r ^ 2 : ℕ) : ℤ) =
      ((d : ℤ) ^ 2 - 288) * (r : ℤ) ^ 2 := by
    rw [Nat.cast_mul, Nat.cast_sub hd2, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]
  exact Int.ofNat_lt.mp (by simpa [hcast] using hlt_z)

/-- Sharp `|k| = 4` Archimedean + congruence obstruction on `q ^ d + 1 = 2 * y ^ 2`. -/
theorem zsqrtTwo_fermat_k_abs_four_obstruction
    {q d y : ℕ} (hq3 : 3 ≤ q) (hd_odd : Odd d) (hd17 : 17 ≤ d) (hy_pos : 0 < y)
    (hpow : q ^ d + 1 = 2 * y ^ 2) {k : ℤ} (hk_abs : |k| = 4) {α : ℤ√2}
    (hz : (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d)
    (hnorm : α.norm = -(q : ℤ)) :
    (k = -4 →
      α ^ d = ⟨17 + 24 * (y : ℤ), 17 * (y : ℤ) + 12⟩ ∧
      1 ≤ α.re ∧ 2 ≤ α.im ∧
      (d : ℤ) * α.re * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1) < 24 * (y : ℤ)) ∧
    (k = 4 →
      (-star α) ^ d = ⟨24 * (y : ℤ) - 17, 17 * (y : ℤ) - 12⟩ ∧
      α.re ≤ -1 ∧ 2 ≤ α.im ∧
      (d : ℤ) * (-α.re) * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1) < 24 * (y : ℤ)) ∧
    1 ≤ |α.re| ∧
    2 ≤ α.im ∧
    (d : ℤ) ^ 2 * α.re ^ 2 < 576 * α.im ^ 2 ∧
    ((d : ℤ) ^ 2 - 288) * α.re ^ 2 < 288 * (q : ℤ) ∧
    (α.re ≡ ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2).re [ZMOD (d : ℤ)] →
      (k = -4 → 17 ≤ α.re) ∧
      (k = 4 → (d : ℤ) - 17 ≤ -α.re) ∧
      (241 ≤ d →
        17 ≤ |α.re| ∧
        (d ^ 2 - 288) * 17 ^ 2 < 288 * q ∧
        (k = 4 → 224 ≤ -α.re ∧ (d ^ 2 - 288) * 224 ^ 2 < 288 * q))) := by
  have hd5 : 5 ≤ d := by omega
  have hk_cases : k = 4 ∨ k = -4 := abs_eq (by norm_num : (0 : ℤ) ≤ 4) |>.mp hk_abs
  have hk_even : Even k := by
    rcases hk_cases with rfl | rfl <;> decide
  have hk1 : 1 ≤ |k| := by omega
  have h2k : 2 * |k| ≤ (d : ℤ) - 1 := by omega
  obtain ⟨_, _, _, _, _, _, hre_abs, him2, hneg_b, hpos_b, _, _, _, hk4_b⟩ :=
    zsqrtTwo_fermat_general_even_k_obstruction hq3 hd_odd hd5 hy_pos hpow hk_even hk1 h2k hz hnorm
  obtain ⟨hU17, hV12, hbd_24, h576_im, h288_q⟩ := hk4_b hk_abs
  have hm4_branch : k = -4 →
      α ^ d = ⟨17 + 24 * (y : ℤ), 17 * (y : ℤ) + 12⟩ ∧
      1 ≤ α.re ∧ 2 ≤ α.im ∧
      (d : ℤ) * α.re * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1) < 24 * (y : ℤ) := by
    rintro rfl
    obtain ⟨hpow_c, hre1, _⟩ := hneg_b (by norm_num)
    rw [hU17, hV12] at hpow_c
    have hpow_c' : α ^ d = ⟨17 + 24 * (y : ℤ), 17 * (y : ℤ) + 12⟩ := by
      simpa [mul_assoc] using hpow_c
    have hbd' : (d : ℤ) * α.re * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1) < 24 * (y : ℤ) := by
      rwa [abs_of_nonneg (by omega)] at hbd_24
    exact ⟨hpow_c', hre1, him2, hbd'⟩
  have hp4_branch : k = 4 →
      (-star α) ^ d = ⟨24 * (y : ℤ) - 17, 17 * (y : ℤ) - 12⟩ ∧
      α.re ≤ -1 ∧ 2 ≤ α.im ∧
      (d : ℤ) * (-α.re) * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1) < 24 * (y : ℤ) := by
    rintro rfl
    obtain ⟨hpow_c, hre_le, _⟩ := hpos_b (by norm_num)
    rw [hU17, hV12] at hpow_c
    have hpow_c' : (-star α) ^ d = ⟨24 * (y : ℤ) - 17, 17 * (y : ℤ) - 12⟩ := by
      simpa [mul_assoc] using hpow_c
    have hbd' : (d : ℤ) * (-α.re) * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1) < 24 * (y : ℤ) := by
      rwa [abs_of_nonpos (by omega)] at hbd_24
    exact ⟨hpow_c', hre_le, him2, hbd'⟩
  refine ⟨hm4_branch, hp4_branch, hre_abs, him2, h576_im, h288_q, ?_⟩
  intro hre_mod
  have hre_mod17 : α.re ≡ 17 [ZMOD (d : ℤ)] := by
    rcases hk_cases with rfl | rfl
    · have hu : ((silverUnit ^ (-(4 : ℤ)) : (ℤ√2)ˣ) : ℤ√2).re = 17 := by
        rw [silverUnit_zpow_neg_four_val]
      rwa [hu] at hre_mod
    · have hu : ((silverUnit ^ (-(-4 : ℤ)) : (ℤ√2)ˣ) : ℤ√2).re = 17 := by
        simpa using congrArg Zsqrtd.re silverUnit_zpow_four_val
      rwa [hu] at hre_mod
  have hm4_cong : k = -4 → 17 ≤ α.re := by
    rintro rfl
    have hre1 : 1 ≤ α.re := (hm4_branch rfl).2.1
    obtain ⟨t, ht⟩ := Int.modEq_iff_add_fac.mp hre_mod17.symm
    have hd_pos : (0 : ℤ) < d := by omega
    have ht_nonneg : 0 ≤ t := by
      by_contra! ht_neg
      have ht_le : t ≤ -1 := by omega
      have hdt : (d : ℤ) * t ≤ -(d : ℤ) := by nlinarith
      linarith
    have hdt_nonneg : 0 ≤ (d : ℤ) * t := mul_nonneg hd_pos.le ht_nonneg
    linarith
  have hp4_cong : k = 4 → (d : ℤ) - 17 ≤ -α.re := by
    rintro rfl
    have hre_le : α.re ≤ -1 := (hp4_branch rfl).2.1
    have hdvd : (d : ℤ) ∣ -α.re + 17 := by
      have h1 : -α.re + 17 ≡ 0 [ZMOD (d : ℤ)] := by
        have := hre_mod17.neg.add_right 17
        simpa using this
      exact Int.modEq_zero_iff_dvd.mp h1
    have hd_le : (d : ℤ) ≤ -α.re + 17 := Int.le_of_dvd (by omega) hdvd
    omega
  refine ⟨hm4_cong, hp4_cong, ?_⟩
  intro hd241
  have h17_abs : 17 ≤ |α.re| := by
    rcases hk_cases with rfl | rfl
    · rw [abs_of_nonpos (by have := (hp4_branch rfl).2.1; omega)]
      have := hp4_cong rfl
      omega
    · rw [abs_of_nonneg (by have := (hm4_branch rfl).2.1; omega)]
      exact hm4_cong rfl
  have hq17 : (d ^ 2 - 288) * 17 ^ 2 < 288 * q :=
    zsqrtTwo_quartic_288_from_sq_ineq hd17 h288_q (by exact_mod_cast h17_abs)
  refine ⟨h17_abs, hq17, ?_⟩
  rintro rfl
  have h224 : 224 ≤ -α.re := by
    have := hp4_cong rfl
    omega
  have h224_abs : ((224 : ℕ) : ℤ) ≤ |α.re| := by
    rw [abs_of_nonpos (by have := (hp4_branch rfl).2.1; omega)]
    exact h224
  exact ⟨h224, zsqrtTwo_quartic_288_from_sq_ineq hd17 h288_q h224_abs⟩

private lemma k4_floor_241 (d : ℕ) (hd241 : 241 ≤ d) :
    57993 * 288 < (d ^ 2 - 288) * 17 ^ 2 := by
  have h1 : 241 ^ 2 - 288 ≤ d ^ 2 - 288 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hd241 2) 288
  have hmul : (241 ^ 2 - 288) * 17 ^ 2 ≤ (d ^ 2 - 288) * 17 ^ 2 :=
    Nat.mul_le_mul_right (17 ^ 2) h1
  calc
    57993 * 288 < (241 ^ 2 - 288) * 17 ^ 2 := by norm_num
    _ ≤ (d ^ 2 - 288) * 17 ^ 2 := hmul

private lemma k4_floor_241_pos (d : ℕ) (hd241 : 241 ≤ d) :
    10068824 * 288 < (d ^ 2 - 288) * 224 ^ 2 := by
  have h1 : 241 ^ 2 - 288 ≤ d ^ 2 - 288 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hd241 2) 288
  have hmul : (241 ^ 2 - 288) * 224 ^ 2 ≤ (d ^ 2 - 288) * 224 ^ 2 :=
    Nat.mul_le_mul_right (224 ^ 2) h1
  calc
    10068824 * 288 < (241 ^ 2 - 288) * 224 ^ 2 := by norm_num
    _ ≤ (d ^ 2 - 288) * 224 ^ 2 := hmul

/-- Unconditional `|k| = 4` quartic obstruction on any exceptional Euler-index witness
`sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`):
forces `1 ≤ |α.re|`, `2 ≤ α.im`, `(d : ℤ) ^ 2 * α.re ^ 2 < 576 * α.im ^ 2`,
`((d : ℤ) ^ 2 - 288) * α.re ^ 2 < 288 * (q : ℤ)`, `17 ≤ α.re` (at `k = -4`),
`(d : ℤ) - 17 ≤ -α.re` (at `k = 4`), and when `¬ 3 ∣ N ∧ ¬ 5 ∣ N`:
`241 ≤ d`, `17 ≤ |α.re|`, `(d ^ 2 - 288) * 17 ^ 2 < 288 * q`, and `57993 < q`
(`10068824 < q` when `k = 4`). -/
theorem exceptional_euler_unit_exponent_four_bound
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
      (|k| = 4 →
        1 ≤ |α.re| ∧
        2 ≤ α.im ∧
        (d : ℤ) ^ 2 * α.re ^ 2 < 576 * α.im ^ 2 ∧
        ((d : ℤ) ^ 2 - 288) * α.re ^ 2 < 288 * (q : ℤ) ∧
        (k = -4 → 17 ≤ α.re) ∧
        (k = 4 → (d : ℤ) - 17 ≤ -α.re) ∧
        (¬ 3 ∣ N → ¬ 5 ∣ N →
          241 ≤ d ∧ 17 ≤ |α.re| ∧
          (d ^ 2 - 288) * 17 ^ 2 < 288 * q ∧ 57993 < q ∧
          (k = 4 → 224 ≤ -α.re ∧ (d ^ 2 - 288) * 224 ^ 2 < 288 * q ∧ 10068824 < q))) := by
  intro d
  obtain ⟨_, hd17, hd8, _, _, _, _⟩ :=
    exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hd_odd : Odd d := Nat.odd_iff.mpr (by omega)
  obtain ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, hnorm, _, _, _,
      hre_d, _, _, _, _⟩ :=
    exceptional_euler_zsqrtTwo_mod_eight_d_profile hN ho hq hq4 ha4 ha hqm hform hl hi
  refine ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, hnorm, ?_⟩
  intro hk_abs
  have hk_cases : k = 4 ∨ k = -4 := abs_eq (by norm_num : (0 : ℤ) ≤ 4) |>.mp hk_abs
  have hk_even : Even k := by
    rcases hk_cases with rfl | rfl <;> decide
  have hnorm_neg : α.norm = -(q : ℤ) := by
    rw [hnorm, ite_eq_left_iff.mpr (fun h => absurd hk_even h)]
  obtain ⟨_, _, hre_abs, him2, h576, h288, hcong⟩ :=
    zsqrtTwo_fermat_k_abs_four_obstruction hq3 hd_odd hd17 hy_pos hpow hk_abs hz_eq hnorm_neg
  obtain ⟨hm4_cong, hp4_cong, h241_cong⟩ := hcong hre_d
  refine ⟨hre_abs, him2, h576, h288, hm4_cong, hp4_cong, ?_⟩
  intro h3 h5
  obtain ⟨_, _, _, hd241, _⟩ :=
    exceptional_euler_of_not_three_or_five_dvd hN ho hq hq4 ha4 ha hqm hform hl hi h3 h5
  obtain ⟨h17_abs, hq17, hp4_b⟩ := h241_cong hd241
  have hfl := k4_floor_241 d hd241
  have h57993 : 57993 < q := by omega
  refine ⟨hd241, h17_abs, hq17, h57993, ?_⟩
  intro hk4
  obtain ⟨h224, hq224⟩ := hp4_b hk4
  have hfl_pos := k4_floor_241_pos d hd241
  exact ⟨h224, hq224, by omega⟩

/-! ## 4. Unified `|k| ≤ 4` Quartic `q`-Floor -/

/-- Unified `|k| ≤ 4` quartic `q`-floor on any exceptional Euler-index witness
`sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`):
combines `|k| = 1` (`6690816000 < q`), `|k| = 2` (`6703954379 < q`),
`|k| = 3` (`131924500 < q`), and `|k| = 4` (`57993 < q`) into
`241 ≤ d ∧ 57993 < q` whenever `|k| ≤ 4` and `¬ 3 ∣ N ∧ ¬ 5 ∣ N`. -/
theorem exceptional_euler_k_le_four_unified_floor
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
      (|k| ≤ 4 → ¬ 3 ∣ N → ¬ 5 ∣ N → 241 ≤ d ∧ 57993 < q) := by
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
  intro hkle4 h3 h5
  obtain ⟨_, _, _, hd241, _⟩ :=
    exceptional_euler_of_not_three_or_five_dvd hN ho hq hq4 ha4 ha hqm hform hl hi h3 h5
  refine ⟨hd241, ?_⟩
  have hk_cases : |k| = 1 ∨ |k| = 2 ∨ |k| = 3 ∨ |k| = 4 := by omega
  rcases hk_cases with hk1_eq | hk2_eq | hk3_eq | hk4_eq
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
    have h1 : 241 ^ 2 - 1 ≤ d ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hd241 2) 1
    have h2 : (241 - 1) ^ 2 ≤ (d - 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hmul : 2 * ((241 ^ 2 - 1) * (241 - 1) ^ 2) ≤ 2 * ((d ^ 2 - 1) * (d - 1) ^ 2) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul h1 h2)
    have h241 : 57993 < 2 * ((241 ^ 2 - 1) * (241 - 1) ^ 2) := by norm_num
    have hassoc : 2 * ((d ^ 2 - 1) * (d - 1) ^ 2) = 2 * (d ^ 2 - 1) * (d - 1) ^ 2 := by ring
    omega
  · have hk_pm : k = 2 ∨ k = -2 := abs_eq (by norm_num : (0 : ℤ) ≤ 2) |>.mp hk2_eq
    have hk_even : Even k := by rcases hk_pm with rfl | rfl <;> decide
    have hnorm_neg : α.norm = -(q : ℤ) := by
      rw [hnorm, ite_eq_left_iff.mpr (fun h => absurd hk_even h)]
    obtain ⟨_, _, _, _, _, _, hcong⟩ :=
      zsqrtTwo_fermat_k_abs_two_obstruction hq3 hd_odd hd5 hy_pos hpow hk2_eq hz_eq hnorm_neg
    obtain ⟨_, _, _, _, h8q⟩ := hcong hd8 hq16 hre_d hre8
    have h1 : 241 ^ 2 - 8 ≤ d ^ 2 - 8 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hd241 2) 8
    have h2 : (4 * 241 - 3) ^ 2 ≤ (4 * d - 3) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hmul : (241 ^ 2 - 8) * (4 * 241 - 3) ^ 2 ≤ (d ^ 2 - 8) * (4 * d - 3) ^ 2 :=
      Nat.mul_le_mul h1 h2
    have h241 : 57993 * 8 < (241 ^ 2 - 8) * (4 * 241 - 3) ^ 2 := by norm_num
    omega
  · have hk_pm : k = 3 ∨ k = -3 := abs_eq (by norm_num : (0 : ℤ) ≤ 3) |>.mp hk3_eq
    have hk_odd_val : Odd k := by rcases hk_pm with rfl | rfl <;> decide
    have hnot_even : ¬ Even k := Int.not_even_iff_odd.mpr hk_odd_val
    have hnorm_pos : α.norm = (q : ℤ) := by
      rw [hnorm, ite_eq_right_iff.mpr (fun h => absurd h hnot_even)]
    have hev_im : Even α.im := (hk_odd_prof hk_odd_val).1
    obtain ⟨_, _, _, _, _, _, hcong⟩ :=
      zsqrtTwo_fermat_k_abs_three_obstruction hq3 hd_odd hd7 hy_pos hpow hk3_eq hz_eq hnorm_pos
    obtain ⟨_, _, _, h49q⟩ := hcong hev_im him_d
    have h1 : 241 ^ 2 - 49 ≤ d ^ 2 - 49 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hd241 2) 49
    have h2 : (241 - 5) ^ 2 ≤ (d - 5) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hmul : 2 * ((241 ^ 2 - 49) * (241 - 5) ^ 2) ≤ 2 * ((d ^ 2 - 49) * (d - 5) ^ 2) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul h1 h2)
    have h241 : 57993 * 49 < 2 * ((241 ^ 2 - 49) * (241 - 5) ^ 2) := by norm_num
    have hassoc : 2 * ((d ^ 2 - 49) * (d - 5) ^ 2) = 2 * (d ^ 2 - 49) * (d - 5) ^ 2 := by ring
    omega
  · have hk_pm : k = 4 ∨ k = -4 := abs_eq (by norm_num : (0 : ℤ) ≤ 4) |>.mp hk4_eq
    have hk_even : Even k := by rcases hk_pm with rfl | rfl <;> decide
    have hnorm_neg : α.norm = -(q : ℤ) := by
      rw [hnorm, ite_eq_left_iff.mpr (fun h => absurd hk_even h)]
    obtain ⟨_, _, _, _, _, _, hcong⟩ :=
      zsqrtTwo_fermat_k_abs_four_obstruction hq3 hd_odd hd17 hy_pos hpow hk4_eq hz_eq hnorm_neg
    obtain ⟨_, _, h241_cong⟩ := hcong hre_d
    obtain ⟨_, hq17, _⟩ := h241_cong hd241
    have hfl := k4_floor_241 d hd241
    omega

end OddPerfect
