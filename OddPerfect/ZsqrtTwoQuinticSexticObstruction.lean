module

public import OddPerfect.ZsqrtTwoEvenKAndQuarticObstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quintic (`|k| = 5`) and Sextic (`|k| = 6`) Unit-Exponent Obstructions in `ℤ√2`
(`OddPerfect.ZsqrtTwoQuinticSexticObstruction`)

Extends the `ℤ√2` unit-exponent obstructions on `q ^ d + 1 = 2 * y ^ 2` and exceptional Euler
indices `sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`) to `|k| = 5`, `|k| = 6`, and
the unified `|k| ≤ 6` floor:

1. `zsqrtTwo_fermat_k_abs_five_obstruction`:
   specializes the odd-`k` obstruction to `|k| = 5` (`silverUnit ^ 5 = ⟨41, 29⟩`,
   `silverUnit ^ (-5 : ℤ) = ⟨-41, 29⟩`). Using `y ≥ 30` from `q ^ d + 1 = 2 * y ^ 2` (`3 ≤ q`,
   `17 ≤ d`), sharpens the binomial bound to `< 42 * y`, yielding
   `2 * ((d : ℤ) ^ 2 - 1764) * α.im ^ 2 < 1764 * (q : ℤ)`, hence
   `(2 * (d : ℤ) ^ 2 - 4900) * α.im ^ 2 < 4900 * (q : ℤ)` and
   `((d : ℤ) ^ 2 - 2450) * α.im ^ 2 < 2450 * (q : ℤ)`.
   Under `Even α.im` and `α.im ≡ 29 [ZMOD d]`, pins `(d : ℤ) - 29 ≤ -α.im` for `k = 5`,
   `(d : ℤ) + 29 ≤ α.im` for `k = -5` (`31 ≤ d`), and for `241 ≤ d`:
   `212 ≤ |α.im|`, `(d ^ 2 - 2450) * 212 ^ 2 < 2450 * q`, and `1020522 < q`.
2. `zsqrtTwo_fermat_k_abs_six_obstruction`:
   specializes `zsqrtTwo_fermat_general_even_k_obstruction` to `|k| = 6`
   (`silverUnit ^ 6 = ⟨99, 70⟩`, `U + 2 * V = 239`, `239 ^ 2 = 57121`), yielding
   `(2 * (d : ℤ) ^ 2 - 57121) * α.re ^ 2 < 57121 * (q : ℤ)`.
   Under `α.re ≡ 99 [ZMOD d]` at `241 ≤ d`, pins `99 ≤ α.re` (`k = -6`) and
   `(d : ℤ) - 99 ≤ -α.re` (`142 ≤ -α.re` for `k = 6`), hence `99 ≤ |α.re|`,
   `(2 * d ^ 2 - 57121) * 99 ^ 2 < 57121 * q`, and `10130 < q` (`20841 < q` when `k = 6`).
3. `exceptional_euler_unit_exponent_five_and_six_bounds` and
   `exceptional_euler_k_le_six_unified_floor`:
   on any exceptional Euler-index witness when `¬ 3 ∣ N ∧ ¬ 5 ∣ N`, yields
   `|k| = 5 → 241 ≤ d ∧ 1020522 < q`, `|k| = 6 → 241 ≤ d ∧ 10130 < q`, and
   unifies all `|k| ≤ 6` into `241 ≤ d ∧ 10130 < q`.
-/

public section

namespace OddPerfect

open ArithmeticFunction

/-! ## 1. `silverUnit ^ ±5` & `silverUnit ^ ±6` Coordinates and Helper Inequalities -/

private lemma silverUnit_zpow_five_val :
    ((silverUnit ^ (5 : ℤ) : (ℤ√2)ˣ) : ℤ√2) = ⟨41, 29⟩ := by
  have h5 : (silverUnit ^ (5 : ℤ) : (ℤ√2)ˣ) = silverUnit ^ (5 : ℕ) := rfl
  rw [h5, Units.val_pow_eq_pow_val, silverUnit_val, show (5 : ℕ) = 2 + 2 + 1 by rfl,
    pow_succ, pow_add, pow_two]
  ext <;> simp

private lemma silverUnit_zpow_neg_five_val :
    ((silverUnit ^ (-5 : ℤ) : (ℤ√2)ˣ) : ℤ√2) = ⟨-41, 29⟩ := by
  have h := (silverUnit_odd_pow_coords (m := 5) (by decide) (by omega)).2.2.2
  have h5 : ((silverUnit ^ (5 : ℕ) : (ℤ√2)ˣ) : ℤ√2) = ⟨41, 29⟩ := by
    simpa using silverUnit_zpow_five_val
  simpa [h5] using h

private lemma silverUnit_zpow_six_val :
    ((silverUnit ^ (6 : ℤ) : (ℤ√2)ˣ) : ℤ√2) = ⟨99, 70⟩ := by
  have h6 : (silverUnit ^ (6 : ℤ) : (ℤ√2)ˣ) = silverUnit ^ (6 : ℕ) := rfl
  rw [h6, Units.val_pow_eq_pow_val, silverUnit_val, show (6 : ℕ) = 2 + 2 + 2 by rfl,
    pow_add, pow_add, pow_two]
  ext <;> simp

private lemma silverUnit_zpow_neg_six_val :
    ((silverUnit ^ (-6 : ℤ) : (ℤ√2)ˣ) : ℤ√2) = ⟨99, -70⟩ := by
  have h := (silverUnit_even_pow_coords (m := 6) (by decide) (by omega)).2.2.2
  have h6 : ((silverUnit ^ (6 : ℕ) : (ℤ√2)ˣ) : ℤ√2) = ⟨99, 70⟩ := by
    simpa using silverUnit_zpow_six_val
  simpa [h6] using h

private lemma odd_k_sq_ineq_local {q d y : ℕ} (hd3 : 3 ≤ d)
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

private lemma zsqrtTwo_quartic_2450_from_sq_ineq {q d : ℕ} (hd241 : 241 ≤ d) {α : ℤ√2}
    (hsq : ((d : ℤ) ^ 2 - 2450) * α.im ^ 2 < 2450 * (q : ℤ))
    {r : ℕ} (hr_le : (r : ℤ) ≤ |α.im|) :
    (d ^ 2 - 2450) * r ^ 2 < 2450 * q := by
  have hr_sq : (r : ℤ) ^ 2 ≤ α.im ^ 2 := by
    rw [← sq_abs α.im]
    exact sq_le_sq' (by linarith [Int.natCast_nonneg r]) hr_le
  have hd2_nonneg : 0 ≤ (d : ℤ) ^ 2 - 2450 := by
    have : (241 : ℤ) ≤ d := by exact_mod_cast hd241
    nlinarith
  have hlt_z : ((d : ℤ) ^ 2 - 2450) * (r : ℤ) ^ 2 < 2450 * (q : ℤ) :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hr_sq hd2_nonneg) hsq
  have hd2 : 2450 ≤ d ^ 2 := by nlinarith
  have hcast : (((d ^ 2 - 2450) * r ^ 2 : ℕ) : ℤ) =
      ((d : ℤ) ^ 2 - 2450) * (r : ℤ) ^ 2 := by
    rw [Nat.cast_mul, Nat.cast_sub hd2, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]
  exact Int.ofNat_lt.mp (by simpa [hcast] using hlt_z)

private lemma zsqrtTwo_quartic_57121_from_sq_ineq {q d : ℕ} (hd241 : 241 ≤ d) {α : ℤ√2}
    (hsq : (2 * (d : ℤ) ^ 2 - 57121) * α.re ^ 2 < 57121 * (q : ℤ))
    {r : ℕ} (hr_le : (r : ℤ) ≤ |α.re|) :
    (2 * d ^ 2 - 57121) * r ^ 2 < 57121 * q := by
  have hr_sq : (r : ℤ) ^ 2 ≤ α.re ^ 2 := by
    rw [← sq_abs α.re]
    exact sq_le_sq' (by linarith [Int.natCast_nonneg r]) hr_le
  have hd2_nonneg : 0 ≤ 2 * (d : ℤ) ^ 2 - 57121 := by
    have : (241 : ℤ) ≤ d := by exact_mod_cast hd241
    nlinarith
  have hlt_z : (2 * (d : ℤ) ^ 2 - 57121) * (r : ℤ) ^ 2 < 57121 * (q : ℤ) :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hr_sq hd2_nonneg) hsq
  have hd2 : 57121 ≤ 2 * d ^ 2 := by nlinarith
  have hcast : (((2 * d ^ 2 - 57121) * r ^ 2 : ℕ) : ℤ) =
      (2 * (d : ℤ) ^ 2 - 57121) * (r : ℤ) ^ 2 := by
    rw [Nat.cast_mul, Nat.cast_sub hd2, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
      Nat.cast_pow, Nat.cast_ofNat]
  exact Int.ofNat_lt.mp (by simpa [hcast] using hlt_z)

/-! ## 2. Sharp `|k| = 5` Obstruction -/

/-- Sharp `|k| = 5` Archimedean + congruence obstruction on `q ^ d + 1 = 2 * y ^ 2`. -/
theorem zsqrtTwo_fermat_k_abs_five_obstruction
    {q d y : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) (hd_odd : Odd d) (hd17 : 17 ≤ d) (hy_pos : 0 < y)
    (hpow : q ^ d + 1 = 2 * y ^ 2) {k : ℤ} (hk_abs : |k| = 5) {α : ℤ√2}
    (hz : (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d)
    (hnorm : α.norm = (q : ℤ)) :
    (k = -5 →
      α ^ d = ⟨41 + 58 * (y : ℤ), 41 * (y : ℤ) + 29⟩ ∧
      3 ≤ α.re ∧ 1 ≤ α.im ∧
      (d : ℤ) * α.re ^ (d - 1) * α.im < 42 * (y : ℤ)) ∧
    (k = 5 →
      (star α) ^ d = ⟨58 * (y : ℤ) - 41, 41 * (y : ℤ) - 29⟩ ∧
      3 ≤ α.re ∧ α.im ≤ -1 ∧
      (d : ℤ) * α.re ^ (d - 1) * (-α.im) < 42 * (y : ℤ)) ∧
    3 ≤ α.re ∧
    1 ≤ |α.im| ∧
    2 * (d : ℤ) ^ 2 * α.im ^ 2 < 4900 * α.re ^ 2 ∧
    (2 * (d : ℤ) ^ 2 - 4900) * α.im ^ 2 < 4900 * (q : ℤ) ∧
    ((d : ℤ) ^ 2 - 2450) * α.im ^ 2 < 2450 * (q : ℤ) ∧
    (Even α.im →
      α.im ≡ ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2).im [ZMOD (d : ℤ)] →
      (k = 5 → (d : ℤ) - 29 ≤ -α.im) ∧
      (31 ≤ d → (k = -5 → (d : ℤ) + 29 ≤ α.im)) ∧
      (241 ≤ d →
        212 ≤ |α.im| ∧
        (d ^ 2 - 2450) * 212 ^ 2 < 2450 * q ∧
        1020522 < q)) := by
  have _ := hq.two_le
  have hd3 : 3 ≤ d := by omega
  have hk_cases : k = 5 ∨ k = -5 := abs_eq (by norm_num : (0 : ℤ) ≤ 5) |>.mp hk_abs
  have hk_odd : Odd k := by rcases hk_cases with rfl | rfl <;> decide
  have hk1 : 1 ≤ |k| := by omega
  have h2k : 2 * |k| ≤ (d : ℤ) - 1 := by omega
  obtain ⟨_, _, _, _, _, _, hre1, hre3, him_abs, hneg_b, hpos_b, _, _, _, _⟩ :=
    zsqrtTwo_fermat_general_odd_k_obstruction hq3 hd_odd hd3 hy_pos hpow hk_odd hk1 h2k hz hnorm
  have hm5 : k.natAbs = 5 := by omega
  have hsu5 : ((silverUnit ^ k.natAbs : (ℤ√2)ˣ) : ℤ√2) = ⟨41, 29⟩ := by
    rw [hm5]
    simpa using silverUnit_zpow_five_val
  have hU41 : ((silverUnit ^ k.natAbs : (ℤ√2)ˣ) : ℤ√2).re = 41 := by rw [hsu5]
  have hV29 : ((silverUnit ^ k.natAbs : (ℤ√2)ˣ) : ℤ√2).im = 29 := by rw [hsu5]
  have hy30 : (30 : ℤ) ≤ (y : ℤ) := by
    have hpow_ge : 3 ^ 17 ≤ q ^ d :=
      le_trans (Nat.pow_le_pow_right (by norm_num) hd17) (Nat.pow_le_pow_left hq3 d)
    have h17 : 2 * 30 ^ 2 < 3 ^ 17 + 1 := by norm_num
    have hy2 : 30 ^ 2 < y ^ 2 := by omega
    have hy_nat : 30 < y := by nlinarith
    exact_mod_cast hy_nat.le
  have hbd_42 : (d : ℤ) * α.re ^ (d - 1) * |α.im| < 42 * (y : ℤ) := by
    rcases hk_cases with rfl | rfl
    · obtain ⟨_, him_le, hlb⟩ := hpos_b (by norm_num)
      rw [hU41, hV29] at hlb
      rw [abs_of_nonpos (by omega)]
      linarith
    · obtain ⟨_, him1, hlb⟩ := hneg_b (by norm_num)
      rw [hU41, hV29] at hlb
      rw [abs_of_nonneg (by omega)]
      linarith
  have hm5_branch : k = -5 →
      α ^ d = ⟨41 + 58 * (y : ℤ), 41 * (y : ℤ) + 29⟩ ∧
      3 ≤ α.re ∧ 1 ≤ α.im ∧
      (d : ℤ) * α.re ^ (d - 1) * α.im < 42 * (y : ℤ) := by
    rintro rfl
    obtain ⟨hpow_c, him1, _⟩ := hneg_b (by norm_num)
    rw [hU41, hV29] at hpow_c
    have hpow_c' : α ^ d = ⟨41 + 58 * (y : ℤ), 41 * (y : ℤ) + 29⟩ := by
      simpa [mul_assoc] using hpow_c
    have hbd' : (d : ℤ) * α.re ^ (d - 1) * α.im < 42 * (y : ℤ) := by
      rwa [abs_of_nonneg (by omega)] at hbd_42
    exact ⟨hpow_c', hre3, him1, hbd'⟩
  have hp5_branch : k = 5 →
      (star α) ^ d = ⟨58 * (y : ℤ) - 41, 41 * (y : ℤ) - 29⟩ ∧
      3 ≤ α.re ∧ α.im ≤ -1 ∧
      (d : ℤ) * α.re ^ (d - 1) * (-α.im) < 42 * (y : ℤ) := by
    rintro rfl
    obtain ⟨hpow_c, him_le, _⟩ := hpos_b (by norm_num)
    rw [hU41, hV29] at hpow_c
    have hpow_c' : (star α) ^ d = ⟨58 * (y : ℤ) - 41, 41 * (y : ℤ) - 29⟩ := by
      simpa [mul_assoc] using hpow_c
    have hbd' : (d : ℤ) * α.re ^ (d - 1) * (-α.im) < 42 * (y : ℤ) := by
      rwa [abs_of_nonpos (by omega)] at hbd_42
    exact ⟨hpow_c', hre3, him_le, hbd'⟩
  obtain ⟨hsq_1764_re, hsq_1764_q⟩ :=
    odd_k_sq_ineq_local hd3 hpow hnorm hre1 him_abs (by norm_num) hbd_42
  have hsq_4900_re : 2 * (d : ℤ) ^ 2 * α.im ^ 2 < 4900 * α.re ^ 2 := by
    have hre2_pos : 0 < α.re ^ 2 := by positivity
    nlinarith
  have hsq_4900_q : (2 * (d : ℤ) ^ 2 - 4900) * α.im ^ 2 < 4900 * (q : ℤ) := by
    have him2_nonneg : 0 ≤ α.im ^ 2 := sq_nonneg α.im
    have hq_pos : (0 : ℤ) < (q : ℤ) := by omega
    nlinarith
  have hsq_2450_q : ((d : ℤ) ^ 2 - 2450) * α.im ^ 2 < 2450 * (q : ℤ) := by
    linarith
  refine ⟨hm5_branch, hp5_branch, hre3, him_abs, hsq_4900_re, hsq_4900_q, hsq_2450_q, ?_⟩
  intro hev_im him_mod
  have him_mod29 : α.im ≡ 29 [ZMOD (d : ℤ)] := by
    rcases hk_cases with rfl | rfl
    · have hu : ((silverUnit ^ (-(5 : ℤ)) : (ℤ√2)ˣ) : ℤ√2).im = 29 := by
        rw [silverUnit_zpow_neg_five_val]
      rwa [hu] at him_mod
    · have hu : ((silverUnit ^ (-(-5 : ℤ)) : (ℤ√2)ˣ) : ℤ√2).im = 29 := by
        simpa using congrArg Zsqrtd.im silverUnit_zpow_five_val
      rwa [hu] at him_mod
  have hp5_cong : k = 5 → (d : ℤ) - 29 ≤ -α.im := by
    rintro rfl
    have him_le : α.im ≤ -1 := (hp5_branch rfl).2.2.1
    have hdvd : (d : ℤ) ∣ -α.im + 29 := by
      have h1 : -α.im + 29 ≡ 0 [ZMOD (d : ℤ)] := by
        have := him_mod29.neg.add_right 29
        simpa using this
      exact Int.modEq_zero_iff_dvd.mp h1
    have hd_le : (d : ℤ) ≤ -α.im + 29 := Int.le_of_dvd (by omega) hdvd
    omega
  have hm5_cong : 31 ≤ d → k = -5 → (d : ℤ) + 29 ≤ α.im := by
    intro hd31
    rintro rfl
    have him1 : 1 ≤ α.im := (hm5_branch rfl).2.2.1
    obtain ⟨t, ht⟩ := Int.modEq_iff_add_fac.mp him_mod29.symm
    have hd_pos : (0 : ℤ) < d := by omega
    have ht_pos : 1 ≤ t := by
      by_contra! ht0
      have ht_le : t ≤ 0 := by omega
      rcases lt_or_eq_of_le ht_le with ht_neg | rfl
      · have hdt : (d : ℤ) * t ≤ -(d : ℤ) := by nlinarith
        linarith
      · have him29 : α.im = 29 := by linarith
        rw [him29] at hev_im
        exact (by decide : ¬ Even (29 : ℤ)) hev_im
    have : (d : ℤ) * 1 ≤ (d : ℤ) * t := mul_le_mul_of_nonneg_left ht_pos hd_pos.le
    linarith
  refine ⟨hp5_cong, hm5_cong, ?_⟩
  intro hd241
  have hd31 : 31 ≤ d := by omega
  have h212_abs : 212 ≤ |α.im| := by
    rcases hk_cases with rfl | rfl
    · rw [abs_of_nonpos (by have := (hp5_branch rfl).2.2.1; omega)]
      have := hp5_cong rfl
      omega
    · rw [abs_of_nonneg (by have := (hm5_branch rfl).2.2.1; omega)]
      have := hm5_cong hd31 rfl
      omega
  have hq212 : (d ^ 2 - 2450) * 212 ^ 2 < 2450 * q :=
    zsqrtTwo_quartic_2450_from_sq_ineq hd241 hsq_2450_q (by exact_mod_cast h212_abs)
  have hfloor : 1020522 * 2450 < (d ^ 2 - 2450) * 212 ^ 2 := by
    have h1 : 241 ^ 2 - 2450 ≤ d ^ 2 - 2450 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hd241 2) 2450
    have hmul : (241 ^ 2 - 2450) * 212 ^ 2 ≤ (d ^ 2 - 2450) * 212 ^ 2 :=
      Nat.mul_le_mul_right (212 ^ 2) h1
    calc
      1020522 * 2450 < (241 ^ 2 - 2450) * 212 ^ 2 := by norm_num
      _ ≤ (d ^ 2 - 2450) * 212 ^ 2 := hmul
  exact ⟨h212_abs, hq212, by omega⟩

/-! ## 3. Sharp `|k| = 6` Obstruction -/

/-- Sharp `|k| = 6` Archimedean + congruence obstruction on `q ^ d + 1 = 2 * y ^ 2`. -/
theorem zsqrtTwo_fermat_k_abs_six_obstruction
    {q d y : ℕ} (hq3 : 3 ≤ q) (hd_odd : Odd d) (hd17 : 17 ≤ d) (hy_pos : 0 < y)
    (hpow : q ^ d + 1 = 2 * y ^ 2) {k : ℤ} (hk_abs : |k| = 6) {α : ℤ√2}
    (hz : (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d)
    (hnorm : α.norm = -(q : ℤ)) :
    (k = -6 →
      α ^ d = ⟨99 + 140 * (y : ℤ), 99 * (y : ℤ) + 70⟩ ∧
      1 ≤ α.re ∧ 2 ≤ α.im ∧
      (d : ℤ) * α.re * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1) < 239 * (y : ℤ)) ∧
    (k = 6 →
      (-star α) ^ d = ⟨140 * (y : ℤ) - 99, 99 * (y : ℤ) - 70⟩ ∧
      α.re ≤ -1 ∧ 2 ≤ α.im ∧
      (d : ℤ) * (-α.re) * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1) < 239 * (y : ℤ)) ∧
    1 ≤ |α.re| ∧
    2 ≤ α.im ∧
    (d : ℤ) ^ 2 * α.re ^ 2 < 57121 * α.im ^ 2 ∧
    (2 * (d : ℤ) ^ 2 - 57121) * α.re ^ 2 < 57121 * (q : ℤ) ∧
    (α.re ≡ ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2).re [ZMOD (d : ℤ)] →
      (k = 6 → (d : ℤ) - 99 ≤ -α.re) ∧
      (241 ≤ d →
        (k = -6 → 99 ≤ α.re) ∧
        (k = 6 → 142 ≤ -α.re) ∧
        99 ≤ |α.re| ∧
        (2 * d ^ 2 - 57121) * 99 ^ 2 < 57121 * q ∧
        10130 < q ∧
        (k = 6 → (2 * d ^ 2 - 57121) * 142 ^ 2 < 57121 * q ∧ 20841 < q))) := by
  have hd5 : 5 ≤ d := by omega
  have hk_cases : k = 6 ∨ k = -6 := abs_eq (by norm_num : (0 : ℤ) ≤ 6) |>.mp hk_abs
  have hk_even : Even k := by rcases hk_cases with rfl | rfl <;> decide
  have hk1 : 1 ≤ |k| := by omega
  have h2k : 2 * |k| ≤ (d : ℤ) - 1 := by omega
  obtain ⟨_, _, _, _, _, _, hre_abs, him2, hneg_b, hpos_b, hbd_uv, hsq_re, hsq_q, _⟩ :=
    zsqrtTwo_fermat_general_even_k_obstruction hq3 hd_odd hd5 hy_pos hpow hk_even hk1 h2k hz hnorm
  have hm6 : k.natAbs = 6 := by omega
  have hsu6 : ((silverUnit ^ k.natAbs : (ℤ√2)ˣ) : ℤ√2) = ⟨99, 70⟩ := by
    rw [hm6]
    simpa using silverUnit_zpow_six_val
  have hU99 : ((silverUnit ^ k.natAbs : (ℤ√2)ˣ) : ℤ√2).re = 99 := by rw [hsu6]
  have hV70 : ((silverUnit ^ k.natAbs : (ℤ√2)ˣ) : ℤ√2).im = 70 := by rw [hsu6]
  have hUV : ((silverUnit ^ k.natAbs : (ℤ√2)ˣ) : ℤ√2).re +
      2 * ((silverUnit ^ k.natAbs : (ℤ√2)ˣ) : ℤ√2).im = 239 := by
    rw [hU99, hV70]
    norm_num
  have hbd_239 : (d : ℤ) * |α.re| * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1) < 239 * (y : ℤ) := by
    rwa [hUV] at hbd_uv
  have hsq_57121_im : (d : ℤ) ^ 2 * α.re ^ 2 < 57121 * α.im ^ 2 := by
    rw [hUV] at hsq_re
    simpa only [show (239 : ℤ) ^ 2 = 57121 by norm_num] using hsq_re
  have hsq_57121_q : (2 * (d : ℤ) ^ 2 - 57121) * α.re ^ 2 < 57121 * (q : ℤ) := by
    rw [hUV] at hsq_q
    simpa only [show (239 : ℤ) ^ 2 = 57121 by norm_num] using hsq_q
  have hm6_branch : k = -6 →
      α ^ d = ⟨99 + 140 * (y : ℤ), 99 * (y : ℤ) + 70⟩ ∧
      1 ≤ α.re ∧ 2 ≤ α.im ∧
      (d : ℤ) * α.re * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1) < 239 * (y : ℤ) := by
    rintro rfl
    obtain ⟨hpow_c, hre1, _⟩ := hneg_b (by norm_num)
    rw [hU99, hV70] at hpow_c
    have hpow_c' : α ^ d = ⟨99 + 140 * (y : ℤ), 99 * (y : ℤ) + 70⟩ := by
      simpa [mul_assoc] using hpow_c
    have hbd' : (d : ℤ) * α.re * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1) < 239 * (y : ℤ) := by
      rwa [abs_of_nonneg (by omega)] at hbd_239
    exact ⟨hpow_c', hre1, him2, hbd'⟩
  have hp6_branch : k = 6 →
      (-star α) ^ d = ⟨140 * (y : ℤ) - 99, 99 * (y : ℤ) - 70⟩ ∧
      α.re ≤ -1 ∧ 2 ≤ α.im ∧
      (d : ℤ) * (-α.re) * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1) < 239 * (y : ℤ) := by
    rintro rfl
    obtain ⟨hpow_c, hre_le, _⟩ := hpos_b (by norm_num)
    rw [hU99, hV70] at hpow_c
    have hpow_c' : (-star α) ^ d = ⟨140 * (y : ℤ) - 99, 99 * (y : ℤ) - 70⟩ := by
      simpa [mul_assoc] using hpow_c
    have hbd' : (d : ℤ) * (-α.re) * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1) < 239 * (y : ℤ) := by
      rwa [abs_of_nonpos (by omega)] at hbd_239
    exact ⟨hpow_c', hre_le, him2, hbd'⟩
  refine ⟨hm6_branch, hp6_branch, hre_abs, him2, hsq_57121_im, hsq_57121_q, ?_⟩
  intro hre_mod
  have hre_mod99 : α.re ≡ 99 [ZMOD (d : ℤ)] := by
    rcases hk_cases with rfl | rfl
    · have hu : ((silverUnit ^ (-(6 : ℤ)) : (ℤ√2)ˣ) : ℤ√2).re = 99 := by
        rw [silverUnit_zpow_neg_six_val]
      rwa [hu] at hre_mod
    · have hu : ((silverUnit ^ (-(-6 : ℤ)) : (ℤ√2)ˣ) : ℤ√2).re = 99 := by
        simpa using congrArg Zsqrtd.re silverUnit_zpow_six_val
      rwa [hu] at hre_mod
  have hp6_cong : k = 6 → (d : ℤ) - 99 ≤ -α.re := by
    rintro rfl
    have hre_le : α.re ≤ -1 := (hp6_branch rfl).2.1
    have hdvd : (d : ℤ) ∣ -α.re + 99 := by
      have h1 : -α.re + 99 ≡ 0 [ZMOD (d : ℤ)] := by
        have := hre_mod99.neg.add_right 99
        simpa using this
      exact Int.modEq_zero_iff_dvd.mp h1
    have hd_le : (d : ℤ) ≤ -α.re + 99 := Int.le_of_dvd (by omega) hdvd
    omega
  refine ⟨hp6_cong, ?_⟩
  intro hd241
  have hm6_cong : k = -6 → 99 ≤ α.re := by
    rintro rfl
    have hre1 : 1 ≤ α.re := (hm6_branch rfl).2.1
    obtain ⟨t, ht⟩ := Int.modEq_iff_add_fac.mp hre_mod99.symm
    have hd_pos : (0 : ℤ) < d := by omega
    have ht_nonneg : 0 ≤ t := by
      by_contra! ht_neg
      have ht_le : t ≤ -1 := by omega
      have hdt : (d : ℤ) * t ≤ -(d : ℤ) := by nlinarith
      linarith
    have hdt_nonneg : 0 ≤ (d : ℤ) * t := mul_nonneg hd_pos.le ht_nonneg
    linarith
  have hp6_142 : k = 6 → 142 ≤ -α.re := by
    intro hk6
    have := hp6_cong hk6
    omega
  have h99_abs : 99 ≤ |α.re| := by
    rcases hk_cases with rfl | rfl
    · rw [abs_of_nonpos (by have := (hp6_branch rfl).2.1; omega)]
      have := hp6_142 rfl
      omega
    · rw [abs_of_nonneg (by have := (hm6_branch rfl).2.1; omega)]
      exact hm6_cong rfl
  have hq99 : (2 * d ^ 2 - 57121) * 99 ^ 2 < 57121 * q :=
    zsqrtTwo_quartic_57121_from_sq_ineq hd241 hsq_57121_q (by exact_mod_cast h99_abs)
  have hfloor99 : 10130 * 57121 < (2 * d ^ 2 - 57121) * 99 ^ 2 := by
    have h1 : 2 * 241 ^ 2 - 57121 ≤ 2 * d ^ 2 - 57121 :=
      Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hd241 2)) 57121
    have hmul : (2 * 241 ^ 2 - 57121) * 99 ^ 2 ≤ (2 * d ^ 2 - 57121) * 99 ^ 2 :=
      Nat.mul_le_mul_right (99 ^ 2) h1
    calc
      10130 * 57121 < (2 * 241 ^ 2 - 57121) * 99 ^ 2 := by norm_num
      _ ≤ (2 * d ^ 2 - 57121) * 99 ^ 2 := hmul
  refine ⟨hm6_cong, hp6_142, h99_abs, hq99, by omega, ?_⟩
  rintro rfl
  have h142 : 142 ≤ -α.re := hp6_142 rfl
  have h142_abs : ((142 : ℕ) : ℤ) ≤ |α.re| := by
    rw [abs_of_nonpos (by have := (hp6_branch rfl).2.1; omega)]
    exact h142
  have hq142 : (2 * d ^ 2 - 57121) * 142 ^ 2 < 57121 * q :=
    zsqrtTwo_quartic_57121_from_sq_ineq hd241 hsq_57121_q h142_abs
  have hfloor142 : 20841 * 57121 < (2 * d ^ 2 - 57121) * 142 ^ 2 := by
    have h1 : 2 * 241 ^ 2 - 57121 ≤ 2 * d ^ 2 - 57121 :=
      Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hd241 2)) 57121
    have hmul : (2 * 241 ^ 2 - 57121) * 142 ^ 2 ≤ (2 * d ^ 2 - 57121) * 142 ^ 2 :=
      Nat.mul_le_mul_right (142 ^ 2) h1
    calc
      20841 * 57121 < (2 * 241 ^ 2 - 57121) * 142 ^ 2 := by norm_num
      _ ≤ (2 * d ^ 2 - 57121) * 142 ^ 2 := hmul
  exact ⟨hq142, by omega⟩

/-! ## 4. Exceptional Euler Bounds (`|k| = 5, 6`) & Unified `|k| ≤ 6` Floor -/

/-- `|k| = 5` and `|k| = 6` obstructions on any exceptional Euler-index witness
`sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`) when `¬ 3 ∣ N ∧ ¬ 5 ∣ N`:
forces `241 ≤ d` and `1020522 < q` (at `|k| = 5`), `10130 < q` (at `|k| = 6`; `20841 < q` at `k = 6`). -/
theorem exceptional_euler_unit_exponent_five_and_six_bounds
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
      (|k| = 5 → ¬ 3 ∣ N → ¬ 5 ∣ N →
        241 ≤ d ∧ 212 ≤ |α.im| ∧ (d ^ 2 - 2450) * 212 ^ 2 < 2450 * q ∧ 1020522 < q) ∧
      (|k| = 6 → ¬ 3 ∣ N → ¬ 5 ∣ N →
        241 ≤ d ∧ 99 ≤ |α.re| ∧ (2 * d ^ 2 - 57121) * 99 ^ 2 < 57121 * q ∧ 10130 < q ∧
        (k = 6 → 20841 < q)) := by
  intro d
  obtain ⟨_, hd17, hd8, _, _, _, _⟩ :=
    exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hd_odd : Odd d := Nat.odd_iff.mpr (by omega)
  obtain ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, hnorm, _, _, _,
      hre_d, him_d, _, _, hk_odd_prof⟩ :=
    exceptional_euler_zsqrtTwo_mod_eight_d_profile hN ho hq hq4 ha4 ha hqm hform hl hi
  refine ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, hnorm, ?_, ?_⟩
  · intro hk5 h3 h5
    have hk_pm : k = 5 ∨ k = -5 := abs_eq (by norm_num : (0 : ℤ) ≤ 5) |>.mp hk5
    have hk_odd_val : Odd k := by rcases hk_pm with rfl | rfl <;> decide
    have hnot_even : ¬ Even k := Int.not_even_iff_odd.mpr hk_odd_val
    have hnorm_pos : α.norm = (q : ℤ) := by
      rw [hnorm, ite_eq_right_iff.mpr (fun h => absurd h hnot_even)]
    have hev_im : Even α.im := (hk_odd_prof hk_odd_val).1
    obtain ⟨_, _, _, _, _, _, _, hcong⟩ :=
      zsqrtTwo_fermat_k_abs_five_obstruction hq hq3 hd_odd hd17 hy_pos hpow hk5 hz_eq hnorm_pos
    obtain ⟨_, _, h241_cong⟩ := hcong hev_im him_d
    obtain ⟨_, _, _, hd241, _⟩ :=
      exceptional_euler_of_not_three_or_five_dvd hN ho hq hq4 ha4 ha hqm hform hl hi h3 h5
    obtain ⟨h212, hq212, h1020522⟩ := h241_cong hd241
    exact ⟨hd241, h212, hq212, h1020522⟩
  · intro hk6 h3 h5
    have hk_pm : k = 6 ∨ k = -6 := abs_eq (by norm_num : (0 : ℤ) ≤ 6) |>.mp hk6
    have hk_even : Even k := by rcases hk_pm with rfl | rfl <;> decide
    have hnorm_neg : α.norm = -(q : ℤ) := by
      rw [hnorm, ite_eq_left_iff.mpr (fun h => absurd hk_even h)]
    obtain ⟨_, _, _, _, _, _, hcong⟩ :=
      zsqrtTwo_fermat_k_abs_six_obstruction hq3 hd_odd hd17 hy_pos hpow hk6 hz_eq hnorm_neg
    obtain ⟨_, h241_cong⟩ := hcong hre_d
    obtain ⟨_, _, _, hd241, _⟩ :=
      exceptional_euler_of_not_three_or_five_dvd hN ho hq hq4 ha4 ha hqm hform hl hi h3 h5
    obtain ⟨_, _, h99, hq99, h10130, hk6_extra⟩ := h241_cong hd241
    exact ⟨hd241, h99, hq99, h10130, fun hk6_pos => (hk6_extra hk6_pos).2⟩

/-- Unified `|k| ≤ 6` quartic `q`-floor on any exceptional Euler-index witness
`sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`):
combines `|k| ≤ 4` (`57993 < q`), `|k| = 5` (`1020522 < q`), and `|k| = 6` (`10130 < q`) into
`241 ≤ d ∧ 10130 < q` whenever `|k| ≤ 6` and `¬ 3 ∣ N ∧ ¬ 5 ∣ N`. -/
theorem exceptional_euler_k_le_six_unified_floor
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
      (|k| ≤ 6 → ¬ 3 ∣ N → ¬ 5 ∣ N → 241 ≤ d ∧ 10130 < q) := by
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
  intro hkle6 h3 h5
  obtain ⟨_, _, _, hd241, _⟩ :=
    exceptional_euler_of_not_three_or_five_dvd hN ho hq hq4 ha4 ha hqm hform hl hi h3 h5
  refine ⟨hd241, ?_⟩
  have hk_cases : |k| = 1 ∨ |k| = 2 ∨ |k| = 3 ∨ |k| = 4 ∨ |k| = 5 ∨ |k| = 6 := by omega
  rcases hk_cases with hk1_eq | hk2_eq | hk3_eq | hk4_eq | hk5_eq | hk6_eq
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
    have h241 : 10130 < 2 * ((241 ^ 2 - 1) * (241 - 1) ^ 2) := by norm_num
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
    have h241 : 10130 * 8 < (241 ^ 2 - 8) * (4 * 241 - 3) ^ 2 := by norm_num
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
    have h241 : 10130 * 49 < 2 * ((241 ^ 2 - 49) * (241 - 5) ^ 2) := by norm_num
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
    have h1 : 241 ^ 2 - 288 ≤ d ^ 2 - 288 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hd241 2) 288
    have hmul : (241 ^ 2 - 288) * 17 ^ 2 ≤ (d ^ 2 - 288) * 17 ^ 2 :=
      Nat.mul_le_mul_right (17 ^ 2) h1
    have h241 : 10130 * 288 < (241 ^ 2 - 288) * 17 ^ 2 := by norm_num
    omega
  · have hk_pm : k = 5 ∨ k = -5 := abs_eq (by norm_num : (0 : ℤ) ≤ 5) |>.mp hk5_eq
    have hk_odd_val : Odd k := by rcases hk_pm with rfl | rfl <;> decide
    have hnot_even : ¬ Even k := Int.not_even_iff_odd.mpr hk_odd_val
    have hnorm_pos : α.norm = (q : ℤ) := by
      rw [hnorm, ite_eq_right_iff.mpr (fun h => absurd h hnot_even)]
    have hev_im : Even α.im := (hk_odd_prof hk_odd_val).1
    obtain ⟨_, _, _, _, _, _, _, hcong⟩ :=
      zsqrtTwo_fermat_k_abs_five_obstruction hq hq3 hd_odd hd17 hy_pos hpow hk5_eq hz_eq hnorm_pos
    obtain ⟨_, _, h241_cong⟩ := hcong hev_im him_d
    obtain ⟨_, _, h1020522⟩ := h241_cong hd241
    omega
  · have hk_pm : k = 6 ∨ k = -6 := abs_eq (by norm_num : (0 : ℤ) ≤ 6) |>.mp hk6_eq
    have hk_even : Even k := by rcases hk_pm with rfl | rfl <;> decide
    have hnorm_neg : α.norm = -(q : ℤ) := by
      rw [hnorm, ite_eq_left_iff.mpr (fun h => absurd hk_even h)]
    obtain ⟨_, _, _, _, _, _, hcong⟩ :=
      zsqrtTwo_fermat_k_abs_six_obstruction hq3 hd_odd hd17 hy_pos hpow hk6_eq hz_eq hnorm_neg
    obtain ⟨_, h241_cong⟩ := hcong hre_d
    obtain ⟨_, _, _, _, h10130, _⟩ := h241_cong hd241
    exact h10130

end OddPerfect
