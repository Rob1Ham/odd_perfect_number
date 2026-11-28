module

public import OddPerfect.ZsqrtTwoArchimedeanObstruction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Universal Archimedean Cone & Sharp `|k| = 2` Quartic Floors in `ℤ√2`
(`OddPerfect.ZsqrtTwoUniversalCone`)

Extends `OddPerfect.ZsqrtTwoArchimedeanObstruction` with:

1. `zsqrtTwo_universal_archimedean_cone` (and `exceptional_euler_universal_archimedean_cone`):
   for EVERY `k` with `1 ≤ |k|` and `2 * |k| ≤ d - 1` on `q ^ d + 1 = 2 * y ^ 2`, proves
   the conjugate ratio squeeze `(1 + √2)⁻¹ < u / v < 1 + √2`, sign-resolved strict
   ordering (`0 < k → u < v`, `k < 0 → v < u`), `(u - v) ^ 2 < (2 * √2 - 2) * q < (5 / 6) * q`,
   and the exact integer coordinate inequalities for both `Odd k` and `Even k`.
2. `zsqrtTwo_pos_coords_lower_bound_pow_re_k2`, `zsqrtTwo_fermat_k_abs_two_obstruction`, and
   `exceptional_euler_unit_exponent_two_quartic_bound`:
   proves the sharp odd-power real-part lower bound
   `4 + d * β.re * 2 ^ ((d - 1) / 2) * β.im ^ (d - 1) ≤ (β ^ d).re` for `1 ≤ β.re, 2 ≤ β.im`,
   derives `d ^ 2 * α.re ^ 2 < 16 * α.im ^ 2` and `(d ^ 2 - 8) * α.re ^ 2 < 8 * q` for
   `|k| = 2`, and on the exceptional Euler branch pins `4 * d - 3 ≤ |α.re|` (`4 * d + 3 ≤ α.re`
   for `k = -2`), yielding `(d ^ 2 - 8) * (4 * d - 3) ^ 2 < 8 * q` (`148403 < q` unconditionally,
   `177065 < q` for `k = -2`, and `6703954379 < q` / `6787927937 < q` when `¬ 3 ∣ N ∧ ¬ 5 ∣ N`).
-/

public section

namespace OddPerfect

open ArithmeticFunction

/-! ## 1. Universal Archimedean Cone Across All `1 ≤ |k| ≤ (d - 1) / 2` -/

private lemma abs_star_silverUnit_zpow {k : ℤ} :
    |toReal2 (star ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2))| = (1 + Real.sqrt 2) ^ (-k) := by
  set z : ℤ√2 := ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2)
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
  have hz_real : toReal2 z = (1 + Real.sqrt 2) ^ k := by
    dsimp [z]
    induction k using Int.induction_on with
    | zero => simp
    | succ n ih =>
      rw [zpow_add_one, Units.val_mul, map_mul, ih, hsu_real, zpow_add_one₀ hbase_ne]
    | pred n ih =>
      rw [sub_eq_add_neg, zpow_add, zpow_neg_one, Units.val_mul, map_mul, ih, hsu_inv,
        ← zpow_neg_one, ← zpow_add₀ hbase_ne, ← sub_eq_add_neg]
  have hnorm_unit : IsUnit z.norm :=
    (Zsqrtd.isUnit_iff_norm_isUnit z).mp (silverUnit ^ k : (ℤ√2)ˣ).isUnit
  have hnorm_abs : |(z.norm : ℝ)| = 1 := by
    rcases Int.isUnit_iff.mp hnorm_unit with h1 | hm1
    · rw [h1]; norm_num
    · rw [hm1]; norm_num
  have hprod : |toReal2 z| * |toReal2 (star z)| = 1 := by
    rw [← abs_mul, zsqrtTwo_toReal_mul_star_eq_norm, hnorm_abs]
  have hz_pos : 0 < toReal2 z := by
    rw [hz_real]
    exact zpow_pos hbase_pos k
  rw [abs_of_pos hz_pos, hz_real] at hprod
  calc
    |toReal2 (star z)| = (1 + Real.sqrt 2) ^ (-k) * ((1 + Real.sqrt 2) ^ k * |toReal2 (star z)|) := by
      rw [← mul_assoc, ← zpow_add₀ hbase_ne, neg_add_cancel, zpow_zero, one_mul]
    _ = (1 + Real.sqrt 2) ^ (-k) := by rw [hprod, mul_one]

private lemma y_ge_four_of_fermat {q d y : ℕ} (hq3 : 3 ≤ q) (hd3 : 3 ≤ d)
    (hpow : q ^ d + 1 = 2 * y ^ 2) : 4 ≤ y := by
  have hqd : 27 ≤ q ^ d := by
    have h1 : 3 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq3 3
    have h2 : q ^ 3 ≤ q ^ d := Nat.pow_le_pow_right (by omega) hd3
    omega
  nlinarith

private lemma conjugate_ratio_sq_bound {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hu_lt : u < (1 + Real.sqrt 2) * v) (hv_lt : v < (1 + Real.sqrt 2) * u) :
    (u - v) ^ 2 < (2 * Real.sqrt 2 - 2) * (u * v) := by
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  set s : ℝ := 1 + Real.sqrt 2
  have hs_gt1 : 1 < s := by linarith
  have hs_pos : 0 < s := by positivity
  have hs_inv : s⁻¹ = Real.sqrt 2 - 1 := by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hmul : s * (Real.sqrt 2 - 1) = 1 := by
      dsimp [s]
      nlinarith
    exact (eq_inv_of_mul_eq_one_right hmul).symm
  have hsum_s : s + s⁻¹ - 2 = 2 * Real.sqrt 2 - 2 := by
    rw [hs_inv]
    dsimp [s]
    ring
  have hratio_bound : ∀ {t : ℝ}, 1 ≤ t → t < s → t + t⁻¹ < s + s⁻¹ := by
    intro t ht1 hts
    have ht_pos : 0 < t := by linarith
    have hst1 : 1 < s * t := by nlinarith
    have hdiff : (s + s⁻¹) - (t + t⁻¹) = (s - t) * (s * t - 1) / (s * t) := by
      field_simp
      ring
    have hnum_pos : 0 < (s - t) * (s * t - 1) := mul_pos (by linarith) (by linarith)
    have hden_pos : 0 < s * t := mul_pos hs_pos ht_pos
    have hpos : 0 < (s + s⁻¹) - (t + t⁻¹) := by
      rw [hdiff]
      exact div_pos hnum_pos hden_pos
    linarith
  have hlt_main : u / v + v / u < s + s⁻¹ := by
    rcases le_total v u with hvu | huv
    · have ht1 : 1 ≤ u / v := (one_le_div hv).mpr hvu
      have hts : u / v < s := (div_lt_iff₀ hv).mpr hu_lt
      have hinv : (u / v)⁻¹ = v / u := inv_div u v
      simpa [hinv] using hratio_bound ht1 hts
    · have ht1 : 1 ≤ v / u := (one_le_div hu).mpr huv
      have hts : v / u < s := (div_lt_iff₀ hu).mpr hv_lt
      have hinv : (v / u)⁻¹ = u / v := inv_div v u
      rw [add_comm (u / v) (v / u)]
      simpa [hinv] using hratio_bound ht1 hts
  have hid : (u - v) ^ 2 = (u / v + v / u - 2) * (u * v) := by
    field_simp
    ring
  rw [hid, ← hsum_s]
  exact mul_lt_mul_of_pos_right (by linarith) (mul_pos hu hv)

/-- Universal Archimedean cone across ALL `1 ≤ |k| ≤ (d - 1) / 2` on `q ^ d + 1 = 2 * y ^ 2`. -/
theorem zsqrtTwo_universal_archimedean_cone
    {q d y : ℕ} (hq3 : 3 ≤ q) (hd_odd : Odd d) (hd3 : 3 ≤ d) (_hy_pos : 0 < y)
    (hpow : q ^ d + 1 = 2 * y ^ 2) {k : ℤ} {α : ℤ√2}
    (_hk1 : 1 ≤ |k|) (h2k : 2 * |k| ≤ (d : ℤ) - 1)
    (hz : (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d)
    (hnorm : α.norm = (if Even k then -(q : ℤ) else (q : ℤ))) :
    let u := toReal2 α
    let v := |toReal2 (star α)|
    0 < u ∧
    0 < v ∧
    u * v = (q : ℝ) ∧
    u < (1 + Real.sqrt 2) * v ∧
    v < (1 + Real.sqrt 2) * u ∧
    (0 < k → u < v) ∧
    (k < 0 → v < u) ∧
    (u - v) ^ 2 < (2 * Real.sqrt 2 - 2) * (q : ℝ) ∧
    (u - v) ^ 2 < (5 / 6 : ℝ) * (q : ℝ) ∧
    (Odd k →
      toReal2 (star α) = v ∧
      1 ≤ α.re ∧
      (k < 0 → 1 ≤ α.im) ∧
      (0 < k → α.im ≤ -1) ∧
      48 * α.im ^ 2 < 5 * (q : ℤ) ∧
      9 * α.im ^ 2 < (q : ℤ)) ∧
    (Even k →
      toReal2 (star α) = -v ∧
      1 ≤ α.im ∧
      (k < 0 → 1 ≤ α.re) ∧
      (0 < k → α.re ≤ -1) ∧
      24 * α.re ^ 2 < 5 * (q : ℤ) ∧
      4 * α.re ^ 2 < (q : ℤ)) := by
  intro u v
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt2_lt2 : Real.sqrt 2 < 2 := by nlinarith
  have hy4 : 4 ≤ y := y_ge_four_of_fermat hq3 hd3 hpow
  have hy4_real : (4 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy4
  have hq_pos_real : (0 : ℝ) < (q : ℝ) := by
    have : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
    linarith
  obtain ⟨huk_eq, _, hu_pos, _⟩ := zsqrtTwo_fermat_toReal_pos hd_odd k α hz
  change 0 < u at hu_pos
  have huv_signed : u * toReal2 (star α) = (α.norm : ℝ) := zsqrtTwo_toReal_mul_star_eq_norm α
  have hnorm_abs : |(α.norm : ℝ)| = (q : ℝ) := by
    rw [hnorm]
    split_ifs
    · push_cast
      rw [abs_neg, abs_of_pos hq_pos_real]
    · push_cast
      exact abs_of_pos hq_pos_real
  have huv_prod : u * v = (q : ℝ) := by
    have h := congrArg abs huv_signed
    rw [abs_mul, abs_of_pos hu_pos, hnorm_abs] at h
    exact h
  have hv_pos : 0 < v := pos_of_mul_pos_right (huv_prod.symm ▸ hq_pos_real) hu_pos.le
  have hy_sqrt2_gt1 : 1 < (y : ℝ) * Real.sqrt 2 := by
    have : 1 < Real.sqrt 2 := by nlinarith
    nlinarith
  have hden_pos : 0 < (y : ℝ) * Real.sqrt 2 - 1 := by linarith
  have hz_star : star (⟨1, (y : ℤ)⟩ : ℤ√2) =
      (star α) ^ d * star ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) := by
    have h := congrArg star hz
    rw [star_mul, star_pow] at h
    exact h
  have hstar_1y : |toReal2 (star (⟨1, (y : ℤ)⟩ : ℤ√2))| = (y : ℝ) * Real.sqrt 2 - 1 := by
    rw [(zsqrtTwo_toReal_add_and_sub_star ⟨1, (y : ℤ)⟩).2.1]
    simp only [Int.cast_one, Int.cast_natCast]
    rw [← abs_neg, abs_of_pos (by linarith)]
    ring
  have hv_pow_eq : (y : ℝ) * Real.sqrt 2 - 1 = v ^ d * (1 + Real.sqrt 2) ^ (-k) := by
    have h := congrArg (fun x => |toReal2 x|) hz_star
    rw [hstar_1y, map_mul, map_pow, abs_mul, abs_pow, abs_star_silverUnit_zpow] at h
    exact h
  have hu_pow_eq : 1 + (y : ℝ) * Real.sqrt 2 = (1 + Real.sqrt 2) ^ k * u ^ d := by
    have h := congrArg toReal2 hz
    rw [map_mul, map_pow, huk_eq, (zsqrtTwo_toReal_add_and_sub_star ⟨1, (y : ℤ)⟩).1] at h
    simpa using h
  set s : ℝ := 1 + Real.sqrt 2
  have hs_gt1 : 1 < s := by dsimp [s]; linarith
  have hs_pos : 0 < s := by positivity
  have hs_ne : s ≠ 0 := hs_pos.ne'
  set R : ℝ := (1 + (y : ℝ) * Real.sqrt 2) / ((y : ℝ) * Real.sqrt 2 - 1)
  have hR_gt1 : 1 < R := by
    rw [one_lt_div hden_pos]
    linarith
  have hR_lt_s : R < s := by
    rw [div_lt_iff₀ hden_pos]
    have hdiff : s * ((y : ℝ) * Real.sqrt 2 - 1) - (1 + (y : ℝ) * Real.sqrt 2) =
        2 * (y : ℝ) - 2 - Real.sqrt 2 := by
      dsimp [s]
      nlinarith
    have hpos : 0 < 2 * (y : ℝ) - 2 - Real.sqrt 2 := by linarith
    linarith
  have hratio_pow : (u / v) ^ d = s ^ (-2 * k) * R := by
    have hvd_ne : v ^ d ≠ 0 := (pow_pos hv_pos d).ne'
    have h1 : u ^ d = (1 + (y : ℝ) * Real.sqrt 2) * s ^ (-k) := by
      calc
        u ^ d = s ^ (-k) * (s ^ k * u ^ d) := by
          rw [← mul_assoc, ← zpow_add₀ hs_ne, neg_add_cancel, zpow_zero, one_mul]
        _ = (1 + (y : ℝ) * Real.sqrt 2) * s ^ (-k) := by
          rw [← hu_pow_eq, mul_comm]
    have h2 : v ^ d = ((y : ℝ) * Real.sqrt 2 - 1) * s ^ k := by
      calc
        v ^ d = (v ^ d * s ^ (-k)) * s ^ k := by
          rw [mul_assoc, ← zpow_add₀ hs_ne, neg_add_cancel, zpow_zero, mul_one]
        _ = ((y : ℝ) * Real.sqrt 2 - 1) * s ^ k := by
          rw [← hv_pow_eq]
    rw [div_pow, h1, h2]
    calc
      (1 + (y : ℝ) * Real.sqrt 2) * s ^ (-k) / (((y : ℝ) * Real.sqrt 2 - 1) * s ^ k)
          = ((1 + (y : ℝ) * Real.sqrt 2) / ((y : ℝ) * Real.sqrt 2 - 1)) * (s ^ (-k) / s ^ k) :=
        mul_div_mul_comm _ _ _ _
      _ = s ^ (-2 * k) * R := by
        rw [mul_comm, ← zpow_sub₀ hs_ne, show (-k) - k = -2 * k by ring]
  have hd_ne : d ≠ 0 := by omega
  have huv_pos : 0 < u / v := div_pos hu_pos hv_pos
  have hu_lt : u < (1 + Real.sqrt 2) * v := by
    have hle_exp : -2 * k ≤ (d : ℤ) - 1 := by
      have : -k ≤ |k| := neg_le_abs k
      omega
    have hpow_le : s ^ (-2 * k) ≤ s ^ ((d : ℤ) - 1) :=
      zpow_le_zpow_right₀ hs_gt1.le hle_exp
    have hpow_lt : (u / v) ^ d < s ^ d := by
      calc
        (u / v) ^ d = s ^ (-2 * k) * R := hratio_pow
        _ < s ^ ((d : ℤ) - 1) * s := by
          exact mul_lt_mul' hpow_le hR_lt_s (by positivity) (zpow_pos hs_pos _)
        _ = s ^ ((d : ℤ) - 1 + 1) := by
          rw [← zpow_add_one₀ hs_ne]
        _ = s ^ d := by
          rw [sub_add_cancel, zpow_natCast]
    have hdiv_lt : u / v < s :=
      (pow_lt_pow_iff_left₀ huv_pos.le hs_pos.le hd_ne).mp hpow_lt
    exact (div_lt_iff₀ hv_pos).mp hdiv_lt
  have hv_lt : v < (1 + Real.sqrt 2) * u := by
    have hle_exp : -((d : ℤ) - 1) ≤ -2 * k := by
      have : k ≤ |k| := le_abs_self k
      omega
    have hpow_gt : s ^ (-(d : ℤ)) < s ^ (-2 * k) := by
      have h1 : (-(d : ℤ)) < -((d : ℤ) - 1) := by omega
      exact lt_of_lt_of_le (zpow_lt_zpow_right₀ hs_gt1 h1) (zpow_le_zpow_right₀ hs_gt1.le hle_exp)
    have hpow_gt' : (s⁻¹) ^ d < (u / v) ^ d := by
      calc
        (s⁻¹) ^ d = s ^ (-(d : ℤ)) * 1 := by
          rw [zpow_neg, zpow_natCast, inv_pow, mul_one]
        _ < s ^ (-2 * k) * R := by
          exact mul_lt_mul'' hpow_gt hR_gt1 (zpow_pos hs_pos _).le (by norm_num)
        _ = (u / v) ^ d := hratio_pow.symm
    have hdiv_gt : s⁻¹ < u / v :=
      (pow_lt_pow_iff_left₀ (inv_pos.mpr hs_pos).le huv_pos.le hd_ne).mp hpow_gt'
    have h1 : 1 < s * (u / v) := by
      calc
        1 = s * s⁻¹ := (mul_inv_cancel₀ hs_ne).symm
        _ < s * (u / v) := mul_lt_mul_of_pos_left hdiv_gt hs_pos
    have h2 : v < s * u := by
      have : s * (u / v) = (s * u) / v := by ring
      rw [this, one_lt_div hv_pos] at h1
      exact h1
    exact h2
  have hpos_k_lt : 0 < k → u < v := by
    intro hk_pos
    have hle : -2 * k ≤ -2 := by omega
    have hpow_le : s ^ (-2 * k) ≤ s ^ (-2 : ℤ) := zpow_le_zpow_right₀ hs_gt1.le hle
    have hpow_lt : (u / v) ^ d < 1 ^ d := by
      calc
        (u / v) ^ d = s ^ (-2 * k) * R := hratio_pow
        _ < s ^ (-2 : ℤ) * s := by
          exact mul_lt_mul' hpow_le hR_lt_s (by positivity) (zpow_pos hs_pos _)
        _ = s ^ (-1 : ℤ) := by
          rw [← zpow_add_one₀ hs_ne]
          norm_num
        _ < s ^ (0 : ℤ) := zpow_lt_zpow_right₀ hs_gt1 (by norm_num)
        _ = 1 ^ d := by simp
    have hdiv_lt : u / v < 1 :=
      (pow_lt_pow_iff_left₀ huv_pos.le zero_le_one hd_ne).mp hpow_lt
    exact (div_lt_one hv_pos).mp hdiv_lt
  have hneg_k_lt : k < 0 → v < u := by
    intro hk_neg
    have hle : (2 : ℤ) ≤ -2 * k := by omega
    have hpow_le : s ^ (2 : ℤ) ≤ s ^ (-2 * k) := zpow_le_zpow_right₀ hs_gt1.le hle
    have hpow_gt : 1 ^ d < (u / v) ^ d := by
      calc
        1 ^ d = s ^ (0 : ℤ) * 1 := by simp
        _ < s ^ (2 : ℤ) * 1 := by
          exact mul_lt_mul_of_pos_right (zpow_lt_zpow_right₀ hs_gt1 (by norm_num)) zero_lt_one
        _ < s ^ (-2 * k) * R := by
          exact mul_lt_mul' hpow_le hR_gt1 zero_le_one (zpow_pos hs_pos _)
        _ = (u / v) ^ d := hratio_pow.symm
    have hdiv_gt : 1 < u / v :=
      (pow_lt_pow_iff_left₀ zero_le_one huv_pos.le hd_ne).mp hpow_gt
    exact (one_lt_div hv_pos).mp hdiv_gt
  have hsq_2sqrt : (u - v) ^ 2 < (2 * Real.sqrt 2 - 2) * (q : ℝ) := by
    rw [← huv_prod]
    exact conjugate_ratio_sq_bound hu_pos hv_pos hu_lt hv_lt
  have hsqrt_five_sixths : 2 * Real.sqrt 2 - 2 < (5 / 6 : ℝ) := by
    have hlt : 2 * Real.sqrt 2 < (17 / 6 : ℝ) := by nlinarith
    linarith
  have hsq_five_sixths : (u - v) ^ 2 < (5 / 6 : ℝ) * (q : ℝ) := by
    have h1 : (2 * Real.sqrt 2 - 2) * (q : ℝ) < (5 / 6 : ℝ) * (q : ℝ) :=
      mul_lt_mul_of_pos_right hsqrt_five_sixths hq_pos_real
    exact lt_trans hsq_2sqrt h1
  obtain ⟨_, _, hadd, hsub⟩ := zsqrtTwo_toReal_add_and_sub_star α
  change u + toReal2 (star α) = 2 * (α.re : ℝ) at hadd
  change u - toReal2 (star α) = 2 * (α.im : ℝ) * Real.sqrt 2 at hsub
  have hodd_branch : Odd k →
      toReal2 (star α) = v ∧
      1 ≤ α.re ∧
      (k < 0 → 1 ≤ α.im) ∧
      (0 < k → α.im ≤ -1) ∧
      48 * α.im ^ 2 < 5 * (q : ℤ) ∧
      9 * α.im ^ 2 < (q : ℤ) := by
    intro hk_odd
    have hnot_ev : ¬ Even k := Int.not_even_iff_odd.mpr hk_odd
    have hnorm_pos : α.norm = (q : ℤ) := by
      rw [hnorm, ite_eq_right_iff.mpr (fun h => absurd h hnot_ev)]
    have huv_eq : u * toReal2 (star α) = (q : ℝ) := by
      rw [huv_signed, hnorm_pos]
      simp
    have hstar_pos : 0 < toReal2 (star α) :=
      pos_of_mul_pos_right (huv_eq.symm ▸ hq_pos_real) hu_pos.le
    have hv_eq : toReal2 (star α) = v := (abs_of_pos hstar_pos).symm
    have hre_pos_r : (0 : ℝ) < (α.re : ℝ) := by linarith only [hadd, hv_eq, hu_pos, hv_pos]
    have hre_pos_z : 0 < α.re := Int.cast_pos.mp hre_pos_r
    have hre_ge1 : 1 ≤ α.re := by omega
    have hneg_im : k < 0 → 1 ≤ α.im := by
      intro hk_neg
      have hvu : v < u := hneg_k_lt hk_neg
      have him_pos_r : (0 : ℝ) < (α.im : ℝ) * Real.sqrt 2 := by
        linarith only [hsub, hv_eq, hvu]
      have him_pos_r' : (0 : ℝ) < (α.im : ℝ) := pos_of_mul_pos_left him_pos_r hsqrt2_pos.le
      have him_pos_z : 0 < α.im := Int.cast_pos.mp him_pos_r'
      omega
    have hpos_im : 0 < k → α.im ≤ -1 := by
      intro hk_pos
      have huv : u < v := hpos_k_lt hk_pos
      have him_neg_r : (α.im : ℝ) * Real.sqrt 2 < 0 := by
        linarith only [hsub, hv_eq, huv]
      have him_neg_r' : (α.im : ℝ) < 0 := by nlinarith only [him_neg_r, hsqrt2_pos]
      have him_neg_z : α.im < 0 := Int.cast_lt_zero.mp him_neg_r'
      omega
    have him_sq_real : 8 * (α.im : ℝ) ^ 2 < (5 / 6 : ℝ) * (q : ℝ) := by
      have hsq_id : (u - v) ^ 2 = 8 * (α.im : ℝ) ^ 2 := by
        have hdiff : u - v = 2 * (α.im : ℝ) * Real.sqrt 2 := by linarith only [hsub, hv_eq]
        rw [hdiff]
        calc
          (2 * (α.im : ℝ) * Real.sqrt 2) ^ 2 = 4 * (α.im : ℝ) ^ 2 * Real.sqrt 2 ^ 2 := by ring
          _ = 8 * (α.im : ℝ) ^ 2 := by rw [hsqrt2_sq]; ring
      rwa [← hsq_id]
    have h48_real : 48 * (α.im : ℝ) ^ 2 < 5 * (q : ℝ) := by linarith only [him_sq_real]
    have h48_int : 48 * α.im ^ 2 < 5 * (q : ℤ) := by exact_mod_cast h48_real
    have h9_int : 9 * α.im ^ 2 < (q : ℤ) := by
      have hnonneg : 0 ≤ α.im ^ 2 := sq_nonneg α.im
      omega
    exact ⟨hv_eq, hre_ge1, hneg_im, hpos_im, h48_int, h9_int⟩
  have heven_branch : Even k →
      toReal2 (star α) = -v ∧
      1 ≤ α.im ∧
      (k < 0 → 1 ≤ α.re) ∧
      (0 < k → α.re ≤ -1) ∧
      24 * α.re ^ 2 < 5 * (q : ℤ) ∧
      4 * α.re ^ 2 < (q : ℤ) := by
    intro hk_even
    have hnorm_neg : α.norm = -(q : ℤ) := by
      rw [hnorm, ite_eq_left_iff.mpr (fun h => absurd hk_even h)]
    have huv_eq : u * toReal2 (star α) = -(q : ℝ) := by
      rw [huv_signed, hnorm_neg]
      simp
    have hstar_neg : toReal2 (star α) < 0 := by
      by_contra! hnonneg
      have hmul_nonneg : 0 ≤ u * toReal2 (star α) := mul_nonneg hu_pos.le hnonneg
      linarith only [hmul_nonneg, huv_eq, hq_pos_real]
    have hv_eq : toReal2 (star α) = -v := by
      dsimp [v]
      rw [abs_of_neg hstar_neg, neg_neg]
    have him_pos_r : (0 : ℝ) < (α.im : ℝ) * Real.sqrt 2 := by
      linarith only [hsub, hv_eq, hu_pos, hv_pos]
    have him_pos_r' : (0 : ℝ) < (α.im : ℝ) := pos_of_mul_pos_left him_pos_r hsqrt2_pos.le
    have him_pos_z : 0 < α.im := Int.cast_pos.mp him_pos_r'
    have him_ge1 : 1 ≤ α.im := by omega
    have hneg_re : k < 0 → 1 ≤ α.re := by
      intro hk_neg
      have hvu : v < u := hneg_k_lt hk_neg
      have hre_pos_r : (0 : ℝ) < (α.re : ℝ) := by linarith only [hadd, hv_eq, hvu]
      have hre_pos_z : 0 < α.re := Int.cast_pos.mp hre_pos_r
      omega
    have hpos_re : 0 < k → α.re ≤ -1 := by
      intro hk_pos
      have huv : u < v := hpos_k_lt hk_pos
      have hre_neg_r : (α.re : ℝ) < 0 := by linarith only [hadd, hv_eq, huv]
      have hre_neg_z : α.re < 0 := Int.cast_lt_zero.mp hre_neg_r
      omega
    have hre_sq_real : 4 * (α.re : ℝ) ^ 2 < (5 / 6 : ℝ) * (q : ℝ) := by
      have hsq_id : (u - v) ^ 2 = 4 * (α.re : ℝ) ^ 2 := by
        have hdiff : u - v = 2 * (α.re : ℝ) := by linarith only [hadd, hv_eq]
        rw [hdiff]
        ring
      rwa [← hsq_id]
    have h24_real : 24 * (α.re : ℝ) ^ 2 < 5 * (q : ℝ) := by linarith only [hre_sq_real]
    have h24_int : 24 * α.re ^ 2 < 5 * (q : ℤ) := by exact_mod_cast h24_real
    have h4_int : 4 * α.re ^ 2 < (q : ℤ) := by
      have hnonneg : 0 ≤ α.re ^ 2 := sq_nonneg α.re
      omega
    exact ⟨hv_eq, him_ge1, hneg_re, hpos_re, h24_int, h4_int⟩
  exact ⟨hu_pos, hv_pos, huv_prod, hu_lt, hv_lt, hpos_k_lt, hneg_k_lt,
    hsq_2sqrt, hsq_five_sixths, hodd_branch, heven_branch⟩

/-- Exceptional Euler-index specialization of `zsqrtTwo_universal_archimedean_cone`. -/
theorem exceptional_euler_universal_archimedean_cone
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
      let u := toReal2 α
      let v := |toReal2 (star α)|
      0 < u ∧ 0 < v ∧ u * v = (q : ℝ) ∧
      u < (1 + Real.sqrt 2) * v ∧ v < (1 + Real.sqrt 2) * u ∧
      (0 < k → u < v) ∧ (k < 0 → v < u) ∧
      (u - v) ^ 2 < (2 * Real.sqrt 2 - 2) * (q : ℝ) ∧
      (u - v) ^ 2 < (5 / 6 : ℝ) * (q : ℝ) ∧
      (Odd k →
        toReal2 (star α) = v ∧ 1 ≤ α.re ∧
        (k < 0 → 1 ≤ α.im) ∧ (0 < k → α.im ≤ -1) ∧
        48 * α.im ^ 2 < 5 * (q : ℤ) ∧ 9 * α.im ^ 2 < (q : ℤ)) ∧
      (Even k →
        toReal2 (star α) = -v ∧ 1 ≤ α.im ∧
        (k < 0 → 1 ≤ α.re) ∧ (0 < k → α.re ≤ -1) ∧
        24 * α.re ^ 2 < 5 * (q : ℤ) ∧ 4 * α.re ^ 2 < (q : ℤ)) := by
  intro d
  obtain ⟨_, hd17, hd8, _, _, _, _⟩ :=
    exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hd_odd : Odd d := Nat.odd_iff.mpr (by omega)
  have hd3 : 3 ≤ d := by omega
  obtain ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, hnorm, _⟩ :=
    exceptional_euler_zsqrtTwo_mod_eight_d_profile hN ho hq hq4 ha4 ha hqm hform hl hi
  exact ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, hnorm,
    zsqrtTwo_universal_archimedean_cone hq3 hd_odd hd3 hy_pos hpow hk1 h2k hz_eq hnorm⟩

/-! ## 2. Sharp `|k| = 2` Quartic `q`-Floor -/

/-- For `β : ℤ√2` with `1 ≤ β.re` and `2 ≤ β.im`, every odd `m` satisfies
`2 ^ ((m - 1) / 2) * β.im ^ m ≤ (β ^ m).im`, and every odd `d ≥ 5` satisfies
`4 + (d : ℤ) * β.re * 2 ^ ((d - 1) / 2) * β.im ^ (d - 1) ≤ (β ^ d).re`. -/
theorem zsqrtTwo_pos_coords_lower_bound_pow_re_k2 {β : ℤ√2}
    (hre : 1 ≤ β.re) (him : 2 ≤ β.im) {d : ℕ} (hd_odd : Odd d) (hd5 : 5 ≤ d) :
    (∀ m : ℕ, Odd m → 2 ^ ((m - 1) / 2) * β.im ^ m ≤ (β ^ m).im) ∧
    4 + (d : ℤ) * β.re * 2 ^ ((d - 1) / 2) * β.im ^ (d - 1) ≤ (β ^ d).re := by
  have him1 : 1 ≤ β.im := by omega
  have hpos := (zsqrtTwo_pos_coords_pow_bounds hre him1).1
  have him_pow_j : ∀ j : ℕ, 2 ^ j * β.im ^ (2 * j + 1) ≤ (β ^ (2 * j + 1)).im := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      set m0 : ℕ := 2 * j + 1
      have hstep : β ^ (2 * (j + 1) + 1) = β ^ m0 * β ^ 2 := by
        rw [show 2 * (j + 1) + 1 = m0 + 2 by omega, pow_add]
      have hre2 : (β ^ 2).re = β.re ^ 2 + 2 * β.im ^ 2 := by
        rw [pow_two, Zsqrtd.re_mul]; ring
      have him2 : (β ^ 2).im = 2 * β.re * β.im := by
        rw [pow_two, Zsqrtd.im_mul]; ring
      have hm0_re_nonneg : 0 ≤ (β ^ m0).re := by
        have := (hpos m0 (by omega)).1
        linarith
      have hmul_nonneg : 0 ≤ (β ^ m0).re * (2 * β.re * β.im) := by positivity
      have hm0_im_bound : 2 ^ j * β.im ^ m0 ≤ (β ^ m0).im := ih
      have him_nonneg : 0 ≤ (2 : ℤ) ^ j * β.im ^ m0 := by positivity
      have hsq_le : 2 * β.im ^ 2 ≤ β.re ^ 2 + 2 * β.im ^ 2 := by
        nlinarith [sq_nonneg β.re]
      have hmul_le : (2 : ℤ) ^ j * β.im ^ m0 * (2 * β.im ^ 2) ≤
          (β ^ m0).im * (β.re ^ 2 + 2 * β.im ^ 2) := by
        calc
          (2 : ℤ) ^ j * β.im ^ m0 * (2 * β.im ^ 2)
              ≤ (β ^ m0).im * (2 * β.im ^ 2) := mul_le_mul_of_nonneg_right hm0_im_bound (by positivity)
          _ ≤ (β ^ m0).im * (β.re ^ 2 + 2 * β.im ^ 2) :=
            mul_le_mul_of_nonneg_left hsq_le (le_trans him_nonneg hm0_im_bound)
      rw [hstep, Zsqrtd.im_mul, hre2, him2]
      calc
        (2 : ℤ) ^ (j + 1) * β.im ^ (2 * (j + 1) + 1)
            = (2 : ℤ) ^ j * β.im ^ m0 * (2 * β.im ^ 2) := by
          rw [show 2 * (j + 1) + 1 = m0 + 2 by omega, pow_succ, pow_add, pow_two]
          ring
        _ ≤ (β ^ m0).re * (2 * β.re * β.im) + (β ^ m0).im * (β.re ^ 2 + 2 * β.im ^ 2) := by
          linarith
  have him_pow : ∀ m : ℕ, Odd m → 2 ^ ((m - 1) / 2) * β.im ^ m ≤ (β ^ m).im := by
    intro m hm
    obtain ⟨j, rfl⟩ := hm
    have hidx : (2 * j + 1 - 1) / 2 = j := by omega
    rw [hidx]
    exact him_pow_j j
  refine ⟨him_pow, ?_⟩
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
    have hterm2 : 4 ≤ 20 * β.re ^ 3 * β.im ^ 2 := by
      have h1 : 1 ≤ β.re ^ 3 := one_le_pow₀ hre
      have h2 : 4 ≤ β.im ^ 2 := by nlinarith
      nlinarith
    rw [hpow5]
    norm_num
    linarith
  | succ j hj ih =>
    set m : ℕ := 2 * j + 1
    have hm_odd : Odd m := ⟨j, rfl⟩
    have ih' : 4 + (m : ℤ) * β.re * 2 ^ ((m - 1) / 2) * β.im ^ (m - 1) ≤ (β ^ m).re :=
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
    have h1 : (4 + (m : ℤ) * β.re * 2 ^ ((m - 1) / 2) * β.im ^ (m - 1)) * (2 * β.im ^ 2) ≤
        (β ^ m).re * (β.re ^ 2 + 2 * β.im ^ 2) := by
      calc
        (4 + (m : ℤ) * β.re * 2 ^ ((m - 1) / 2) * β.im ^ (m - 1)) * (2 * β.im ^ 2)
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
        (4 + (m : ℤ) * β.re * 2 ^ j * β.im ^ (m - 1)) * (2 * β.im ^ 2) +
          2 * (2 ^ j * β.im ^ m) * (2 * β.re * β.im) =
        8 * β.im ^ 2 + ((m : ℤ) + 2) * β.re * 2 ^ (j + 1) * β.im ^ ((m - 1) + 2) := by
      have hp1 : β.im ^ ((m - 1) + 2) = β.im ^ (m - 1) * β.im ^ 2 := by rw [pow_add]
      have hp2 : β.im ^ ((m - 1) + 2) = β.im ^ m * β.im := by rw [← hm_eq, pow_succ]
      rw [pow_succ (2 : ℤ) j]
      calc
        (4 + (m : ℤ) * β.re * 2 ^ j * β.im ^ (m - 1)) * (2 * β.im ^ 2) +
            2 * (2 ^ j * β.im ^ m) * (2 * β.re * β.im)
            = 8 * β.im ^ 2 + (m : ℤ) * β.re * (2 ^ j * 2) * (β.im ^ (m - 1) * β.im ^ 2) +
              2 * β.re * (2 ^ j * 2) * (β.im ^ m * β.im) := by ring
        _ = 8 * β.im ^ 2 + ((m : ℤ) + 2) * β.re * (2 ^ j * 2) * β.im ^ ((m - 1) + 2) := by
          rw [← hp1, ← hp2]
          ring
    have hcast : ((2 * (j + 1) + 1 : ℕ) : ℤ) = (m : ℤ) + 2 := by
      dsimp [m]; omega
    rw [hcast]
    linarith

private lemma silverUnit_zpow_two_val :
    ((silverUnit ^ (2 : ℤ) : (ℤ√2)ˣ) : ℤ√2) = ⟨3, 2⟩ := by
  have hsu : (silverUnit : ℤ√2) = ⟨1, 1⟩ := silverUnit_val
  have h2 : (silverUnit ^ (2 : ℤ) : (ℤ√2)ˣ) = silverUnit ^ (2 : ℕ) := rfl
  rw [h2, Units.val_pow_eq_pow_val, hsu, pow_two]
  ext <;> simp

private lemma silverUnit_zpow_neg_two_val :
    ((silverUnit ^ (-2 : ℤ) : (ℤ√2)ˣ) : ℤ√2) = ⟨3, -2⟩ := by
  have hinv : ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2) = ⟨-1, 1⟩ := silverUnit_inv_val
  have hm2 : (silverUnit ^ (-2 : ℤ) : (ℤ√2)ˣ) = (silverUnit⁻¹) ^ (2 : ℕ) := by
    rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) by decide, zpow_neg, zpow_natCast, inv_pow]
  rw [hm2, Units.val_pow_eq_pow_val, hinv, pow_two]
  ext <;> simp

private lemma k_abs_two_sq_ineq {q d y : ℕ} (hd_odd : Odd d) (hd5 : 5 ≤ d)
    (hpow : q ^ d + 1 = 2 * y ^ 2) {β : ℤ√2}
    (hre : 1 ≤ β.re) (him : 2 ≤ β.im) (hnorm : β.norm = -(q : ℤ))
    (hbd : (d : ℤ) * β.re * 2 ^ ((d - 1) / 2) * β.im ^ (d - 1) < 4 * (y : ℤ)) :
    (d : ℤ) ^ 2 * β.re ^ 2 < 16 * β.im ^ 2 ∧
    ((d : ℤ) ^ 2 - 8) * β.re ^ 2 < 8 * (q : ℤ) := by
  have hd_pos : (0 : ℤ) < d := by omega
  have hre_pos : (0 : ℤ) < β.re := by omega
  have him_pos : (0 : ℤ) < β.im := by omega
  have hlhs_pos : 0 < (d : ℤ) * β.re * 2 ^ ((d - 1) / 2) * β.im ^ (d - 1) := by positivity
  have hsq_lt : ((d : ℤ) * β.re * 2 ^ ((d - 1) / 2) * β.im ^ (d - 1)) ^ 2 < 16 * (y : ℤ) ^ 2 := by
    nlinarith
  have hpow_z : (q : ℤ) ^ d + 1 = 2 * (y : ℤ) ^ 2 := by exact_mod_cast hpow
  have hnorm_eq : (q : ℤ) = 2 * β.im ^ 2 - β.re ^ 2 := by
    have hn : β.norm = β.re ^ 2 - 2 * β.im ^ 2 := by simp [Zsqrtd.norm_def]; ring
    linarith
  have hq_nonneg : (0 : ℤ) ≤ (q : ℤ) := Int.natCast_nonneg q
  have hq_lt_2im2 : (q : ℤ) < 2 * β.im ^ 2 := by
    have : 1 ≤ β.re ^ 2 := by nlinarith
    linarith
  have hqd_lt : (q : ℤ) ^ d < (2 * β.im ^ 2) ^ d :=
    pow_lt_pow_left₀ hq_lt_2im2 hq_nonneg (by omega)
  have hqd1_le : (q : ℤ) ^ d + 1 ≤ (2 * β.im ^ 2) ^ d := by omega
  have hd_sub_even : (d - 1) / 2 * 2 = d - 1 := by
    obtain ⟨j, rfl⟩ := hd_odd
    omega
  have hexp_lhs : ((d : ℤ) * β.re * 2 ^ ((d - 1) / 2) * β.im ^ (d - 1)) ^ 2 =
      (2 ^ (d - 1) * β.im ^ (2 * d - 2)) * ((d : ℤ) ^ 2 * β.re ^ 2) := by
    rw [mul_pow, mul_pow, mul_pow, ← pow_mul (2 : ℤ), ← pow_mul β.im, hd_sub_even,
      show (d - 1) * 2 = 2 * d - 2 by omega]
    ring
  have hexp_rhs : 8 * (2 * β.im ^ 2) ^ d =
      (2 ^ (d - 1) * β.im ^ (2 * d - 2)) * (16 * β.im ^ 2) := by
    rw [mul_pow, ← pow_mul β.im]
    have hp2 : (2 : ℤ) ^ d = 2 ^ (d - 1) * 2 := by
      rw [← pow_succ, show d - 1 + 1 = d by omega]
    have hpim : β.im ^ (2 * d) = β.im ^ (2 * d - 2) * β.im ^ 2 := by
      rw [← pow_add, show 2 * d - 2 + 2 = 2 * d by omega]
    rw [hp2, hpim]
    ring
  have hmul_lt : (2 ^ (d - 1) * β.im ^ (2 * d - 2)) * ((d : ℤ) ^ 2 * β.re ^ 2) <
      (2 ^ (d - 1) * β.im ^ (2 * d - 2)) * (16 * β.im ^ 2) := by
    calc
      (2 ^ (d - 1) * β.im ^ (2 * d - 2)) * ((d : ℤ) ^ 2 * β.re ^ 2)
          = ((d : ℤ) * β.re * 2 ^ ((d - 1) / 2) * β.im ^ (d - 1)) ^ 2 := hexp_lhs.symm
      _ < 16 * (y : ℤ) ^ 2 := hsq_lt
      _ = 8 * ((q : ℤ) ^ d + 1) := by linarith
      _ ≤ 8 * (2 * β.im ^ 2) ^ d := by linarith
      _ = (2 ^ (d - 1) * β.im ^ (2 * d - 2)) * (16 * β.im ^ 2) := hexp_rhs
  have hfac_pos : 0 < (2 : ℤ) ^ (d - 1) * β.im ^ (2 * d - 2) := by positivity
  have h1 : (d : ℤ) ^ 2 * β.re ^ 2 < 16 * β.im ^ 2 := lt_of_mul_lt_mul_left hmul_lt hfac_pos.le
  have h2 : ((d : ℤ) ^ 2 - 8) * β.re ^ 2 < 8 * (q : ℤ) := by
    linarith
  exact ⟨h1, h2⟩

/-- Sharp `|k| = 2` Archimedean + congruence obstruction on `q ^ d + 1 = 2 * y ^ 2`. -/
theorem zsqrtTwo_fermat_k_abs_two_obstruction
    {q d y : ℕ} (hq3 : 3 ≤ q) (hd_odd : Odd d) (hd5 : 5 ≤ d) (hy_pos : 0 < y)
    (hpow : q ^ d + 1 = 2 * y ^ 2) {k : ℤ} (hk_abs : |k| = 2) {α : ℤ√2}
    (hz : (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d)
    (hnorm : α.norm = -(q : ℤ)) :
    (k = -2 →
      α ^ d = ⟨4 * (y : ℤ) + 3, 3 * (y : ℤ) + 2⟩ ∧
      1 ≤ α.re ∧ 2 ≤ α.im ∧
      (d : ℤ) * α.re * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1) < 4 * (y : ℤ)) ∧
    (k = 2 →
      (-star α) ^ d = ⟨4 * (y : ℤ) - 3, 3 * (y : ℤ) - 2⟩ ∧
      α.re ≤ -1 ∧ 2 ≤ α.im ∧
      (d : ℤ) * (-α.re) * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1) < 4 * (y : ℤ)) ∧
    1 ≤ |α.re| ∧
    2 ≤ α.im ∧
    (d : ℤ) ^ 2 * α.re ^ 2 < 16 * α.im ^ 2 ∧
    ((d : ℤ) ^ 2 - 8) * α.re ^ 2 < 8 * (q : ℤ) ∧
    (d % 8 = 1 → q % 16 = 1 →
      α.re ≡ ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2).re [ZMOD (d : ℤ)] →
      α.re ≡ ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2).re +
        2 * ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2).im * (y : ℤ) [ZMOD 8] →
      Odd y ∧
      (k = -2 → 4 * (d : ℤ) + 3 ≤ α.re ∧ (d ^ 2 - 8) * (4 * d + 3) ^ 2 < 8 * q) ∧
      (k = 2 → 4 * (d : ℤ) - 3 ≤ -α.re) ∧
      4 * (d : ℤ) - 3 ≤ |α.re| ∧
      (d ^ 2 - 8) * (4 * d - 3) ^ 2 < 8 * q) := by
  have hd3 : 3 ≤ d := by omega
  have hk1 : 1 ≤ |k| := by omega
  have h2k : 2 * |k| ≤ (d : ℤ) - 1 := by omega
  have hk_cases : k = 2 ∨ k = -2 := abs_eq (by norm_num : (0 : ℤ) ≤ 2) |>.mp hk_abs
  have hk_even : Even k := by
    rcases hk_cases with rfl | rfl <;> decide
  have hnorm_if : α.norm = (if Even k then -(q : ℤ) else (q : ℤ)) := by
    rw [ite_eq_left_iff.mpr (fun h => absurd hk_even h), hnorm]
  have hcone := zsqrtTwo_universal_archimedean_cone hq3 hd_odd hd3 hy_pos hpow hk1 h2k hz hnorm_if
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hev⟩ := hcone
  obtain ⟨_, him1, hneg_re, hpos_re, _, _⟩ := hev hk_even
  have him2 : 2 ≤ α.im := by
    have hnorm_eq : α.re ^ 2 - 2 * α.im ^ 2 = -(q : ℤ) := by
      have hn : α.norm = α.re ^ 2 - 2 * α.im ^ 2 := by
        simp [Zsqrtd.norm_def]
        ring
      linarith
    have hre1 : 1 ≤ α.re ^ 2 := by
      rcases hk_cases with rfl | rfl
      · have := hpos_re (by norm_num); nlinarith
      · have := hneg_re (by norm_num); nlinarith
    have him_sq : 2 ≤ α.im ^ 2 := by linarith
    nlinarith
  have hcoord := (zsqrtTwo_fermat_coordinate_divisibility hd_odd k α hz).1
  have hm2_branch : k = -2 →
      α ^ d = ⟨4 * (y : ℤ) + 3, 3 * (y : ℤ) + 2⟩ ∧
      1 ≤ α.re ∧ 2 ≤ α.im ∧
      (d : ℤ) * α.re * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1) < 4 * (y : ℤ) := by
    rintro rfl
    have hre1 : 1 ≤ α.re := hneg_re (by norm_num)
    have hpow_c : α ^ d = ⟨4 * (y : ℤ) + 3, 3 * (y : ℤ) + 2⟩ := by
      have hc := (zsqrtTwo_fermat_coordinate_divisibility hd_odd (-2) α hz).1
      dsimp at hc
      rw [silverUnit_zpow_two_val] at hc
      exact hc.trans (by ext <;> simp [add_comm])
    have hlb := (zsqrtTwo_pos_coords_lower_bound_pow_re_k2 hre1 him2 hd_odd hd5).2
    have hpow_re : (α ^ d).re = 4 * (y : ℤ) + 3 := by rw [hpow_c]
    exact ⟨hpow_c, hre1, him2, by linarith⟩
  have hp2_branch : k = 2 →
      (-star α) ^ d = ⟨4 * (y : ℤ) - 3, 3 * (y : ℤ) - 2⟩ ∧
      α.re ≤ -1 ∧ 2 ≤ α.im ∧
      (d : ℤ) * (-α.re) * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1) < 4 * (y : ℤ) := by
    rintro rfl
    have hre_neg1 : α.re ≤ -1 := hpos_re (by norm_num)
    have hpow_c : (-star α) ^ d = ⟨4 * (y : ℤ) - 3, 3 * (y : ℤ) - 2⟩ := by
      have hc := (zsqrtTwo_fermat_coordinate_divisibility hd_odd 2 α hz).1
      rw [silverUnit_zpow_neg_two_val] at hc
      rw [hd_odd.neg_pow, ← star_pow, hc]
      ext <;> simp <;> ring
    set β : ℤ√2 := -star α
    have hbre_eq : β.re = -α.re := by simp [β]
    have hbim_eq : β.im = α.im := by simp [β]
    have hbre : 1 ≤ β.re := by rw [hbre_eq]; omega
    have hbim : 2 ≤ β.im := by rw [hbim_eq]; exact him2
    have hlb := (zsqrtTwo_pos_coords_lower_bound_pow_re_k2 hbre hbim hd_odd hd5).2
    have hpow_re : (β ^ d).re = 4 * (y : ℤ) - 3 := by rw [hpow_c]
    have hlt : (d : ℤ) * (-α.re) * 2 ^ ((d - 1) / 2) * α.im ^ (d - 1) < 4 * (y : ℤ) := by
      rw [← hbre_eq, ← hbim_eq]
      linarith
    exact ⟨hpow_c, hre_neg1, him2, hlt⟩
  have hre_abs : 1 ≤ |α.re| := by
    rcases hk_cases with rfl | rfl
    · have := (hp2_branch rfl).2.1
      rw [abs_of_nonpos (by omega)]
      omega
    · have := (hm2_branch rfl).2.1
      rw [abs_of_nonneg (by omega)]
      exact this
  have hsq_both : (d : ℤ) ^ 2 * α.re ^ 2 < 16 * α.im ^ 2 ∧
      ((d : ℤ) ^ 2 - 8) * α.re ^ 2 < 8 * (q : ℤ) := by
    rcases hk_cases with rfl | rfl
    · obtain ⟨_, hre_neg1, _, hlt⟩ := hp2_branch rfl
      set β : ℤ√2 := -star α
      have hbre_eq : β.re = -α.re := by simp [β]
      have hbim_eq : β.im = α.im := by simp [β]
      have hbre : 1 ≤ β.re := by rw [hbre_eq]; omega
      have hbim : 2 ≤ β.im := by rw [hbim_eq]; exact him2
      have hbnorm : β.norm = -(q : ℤ) := by
        dsimp [β]
        rw [Zsqrtd.norm_neg, Zsqrtd.norm_conj, hnorm]
      have hlt' : (d : ℤ) * β.re * 2 ^ ((d - 1) / 2) * β.im ^ (d - 1) < 4 * (y : ℤ) := by
        rwa [hbre_eq, hbim_eq]
      have hsq := k_abs_two_sq_ineq hd_odd hd5 hpow hbre hbim hbnorm hlt'
      simpa [hbre_eq, hbim_eq] using hsq
    · obtain ⟨_, hre1, _, hlt⟩ := hm2_branch rfl
      exact k_abs_two_sq_ineq hd_odd hd5 hpow hre1 him2 hnorm hlt
  refine ⟨hm2_branch, hp2_branch, hre_abs, him2, hsq_both.1, hsq_both.2, ?_⟩
  intro hd8 hq16 hmod_d hmod_8
  have hy_odd : Odd y := by
    have hqd_mod16 : q ^ d % 16 = 1 := by
      rw [Nat.pow_mod, hq16]
      simp
    have hy2_mod8 : y ^ 2 % 8 = 1 := by omega
    rw [Nat.odd_iff]
    by_contra hy_even
    have hy0 : y % 2 = 0 := by omega
    have hy4 : y % 4 = 0 ∨ y % 4 = 2 := by omega
    rcases hy4 with h | h
    · have : y ^ 2 % 8 = 0 := by
        have hy8 : y % 8 = 0 ∨ y % 8 = 4 := by omega
        rcases hy8 with h' | h' <;> simp [sq, Nat.mul_mod, h']
      omega
    · have : y ^ 2 % 8 = 4 := by
        have hy8 : y % 8 = 2 ∨ y % 8 = 6 := by omega
        rcases hy8 with h' | h' <;> simp [sq, Nat.mul_mod, h']
      omega
  have hy_z_odd : (y : ℤ) % 2 = 1 := by
    have := Nat.odd_iff.mp hy_odd
    omega
  have hd_z8 : (d : ℤ) % 8 = 1 := by exact_mod_cast hd8
  have h8q_bound : ∀ {m : ℕ}, (m : ℤ) ≤ |α.re| → (d ^ 2 - 8) * m ^ 2 < 8 * q := by
    intro m hm_le
    have hm_sq : (m : ℤ) ^ 2 ≤ α.re ^ 2 := by
      have habs : |α.re| ^ 2 = α.re ^ 2 := sq_abs α.re
      rw [← habs]
      exact sq_le_sq' (by linarith [Int.natCast_nonneg m]) hm_le
    have hd2_nonneg : 0 ≤ (d : ℤ) ^ 2 - 8 := by
      have : (5 : ℤ) ≤ d := by exact_mod_cast hd5
      nlinarith
    have hlt_z : ((d : ℤ) ^ 2 - 8) * (m : ℤ) ^ 2 < 8 * (q : ℤ) :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left hm_sq hd2_nonneg) hsq_both.2
    have hd2 : 8 ≤ d ^ 2 := by nlinarith
    have hcast : (((d ^ 2 - 8) * m ^ 2 : ℕ) : ℤ) = ((d : ℤ) ^ 2 - 8) * (m : ℤ) ^ 2 := by
      rw [Nat.cast_mul, Nat.cast_sub hd2, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]
    have hlt_nat : (d ^ 2 - 8) * m ^ 2 < 8 * q := by
      exact Int.ofNat_lt.mp (by simpa [hcast] using hlt_z)
    exact hlt_nat
  have hm2_cong : k = -2 → 4 * (d : ℤ) + 3 ≤ α.re ∧ (d ^ 2 - 8) * (4 * d + 3) ^ 2 < 8 * q := by
    rintro rfl
    have hre1 : 1 ≤ α.re := (hm2_branch rfl).2.1
    have hu : ((silverUnit ^ (-(-2 : ℤ)) : (ℤ√2)ˣ) : ℤ√2) = ⟨3, 2⟩ := by
      simpa using silverUnit_zpow_two_val
    rw [hu] at hmod_d hmod_8
    obtain ⟨t, ht⟩ := Int.modEq_iff_add_fac.mp hmod_d.symm
    have hre_mod8 : α.re % 8 = 7 := by
      have h1 : α.re % 8 = (3 + 4 * (y : ℤ)) % 8 := by
        simpa [Int.ModEq] using hmod_8
      omega
    have ht_nonneg : 0 ≤ t := by
      by_contra! ht_neg
      have hdt : (d : ℤ) * t ≤ -(d : ℤ) := by nlinarith
      linarith
    have ht_mod8 : t % 8 = 4 := by
      have : α.re % 8 = (3 + (d : ℤ) * t) % 8 := by rw [ht]
      rw [hre_mod8, Int.add_emod, Int.mul_emod, hd_z8] at this
      omega
    have ht4 : 4 ≤ t := by omega
    have hre_lb : 4 * (d : ℤ) + 3 ≤ α.re := by
      have : 4 * (d : ℤ) ≤ (d : ℤ) * t := by nlinarith
      linarith
    have habs_le : ((4 * d + 3 : ℕ) : ℤ) ≤ |α.re| := by
      rw [abs_of_nonneg (by omega)]
      push_cast
      exact hre_lb
    exact ⟨hre_lb, h8q_bound habs_le⟩
  have hp2_cong : k = 2 → 4 * (d : ℤ) - 3 ≤ -α.re := by
    rintro rfl
    have hre_neg1 : α.re ≤ -1 := (hp2_branch rfl).2.1
    have hu : ((silverUnit ^ (-(2 : ℤ)) : (ℤ√2)ˣ) : ℤ√2) = ⟨3, -2⟩ := silverUnit_zpow_neg_two_val
    rw [hu] at hmod_d hmod_8
    obtain ⟨t, ht⟩ := Int.modEq_iff_add_fac.mp hmod_d.symm
    have hre_mod8 : α.re % 8 = 7 := by
      have h1 : α.re % 8 = (3 + 2 * (-2 : ℤ) * (y : ℤ)) % 8 := by
        simpa [Int.ModEq] using hmod_8
      omega
    have ht_le : t ≤ -1 := by
      by_contra! ht0
      have ht_nonneg : 0 ≤ t := by omega
      have hdt : 0 ≤ (d : ℤ) * t := mul_nonneg (by positivity) ht_nonneg
      linarith
    have ht_mod8 : t % 8 = 4 := by
      have : α.re % 8 = (3 + (d : ℤ) * t) % 8 := by rw [ht]
      rw [hre_mod8, Int.add_emod, Int.mul_emod, hd_z8] at this
      omega
    have ht_le_m4 : t ≤ -4 := by omega
    have hdt_le : (d : ℤ) * t ≤ -(4 * (d : ℤ)) := by nlinarith
    linarith
  have hre_abs_lb : 4 * (d : ℤ) - 3 ≤ |α.re| := by
    rcases hk_cases with rfl | rfl
    · rw [abs_of_nonpos (by have := (hp2_branch rfl).2.1; omega)]
      exact hp2_cong rfl
    · rw [abs_of_nonneg (by have := (hm2_branch rfl).2.1; omega)]
      have := (hm2_branch rfl).2.1
      have := (hm2_cong rfl).1
      omega
  have habs_nat_le : ((4 * d - 3 : ℕ) : ℤ) ≤ |α.re| := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_ofNat]
    exact hre_abs_lb
  exact ⟨hy_odd, hm2_cong, hp2_cong, hre_abs_lb, h8q_bound habs_nat_le⟩

private lemma k2_floor_17 (d : ℕ) (hd17 : 17 ≤ d) :
    148403 * 8 < (d ^ 2 - 8) * (4 * d - 3) ^ 2 := by
  have h1 : 17 ^ 2 - 8 ≤ d ^ 2 - 8 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hd17 2) 8
  have h2 : (4 * 17 - 3) ^ 2 ≤ (4 * d - 3) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hmul : (17 ^ 2 - 8) * (4 * 17 - 3) ^ 2 ≤ (d ^ 2 - 8) * (4 * d - 3) ^ 2 :=
    Nat.mul_le_mul h1 h2
  have h17 : 148403 * 8 < (17 ^ 2 - 8) * (4 * 17 - 3) ^ 2 := by norm_num
  omega

private lemma k2_floor_17_plus (d : ℕ) (hd17 : 17 ≤ d) :
    177065 * 8 < (d ^ 2 - 8) * (4 * d + 3) ^ 2 := by
  have h1 : 17 ^ 2 - 8 ≤ d ^ 2 - 8 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hd17 2) 8
  have h2 : (4 * 17 + 3) ^ 2 ≤ (4 * d + 3) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hmul : (17 ^ 2 - 8) * (4 * 17 + 3) ^ 2 ≤ (d ^ 2 - 8) * (4 * d + 3) ^ 2 :=
    Nat.mul_le_mul h1 h2
  have h17 : 177065 * 8 < (17 ^ 2 - 8) * (4 * 17 + 3) ^ 2 := by norm_num
  omega

private lemma k2_floor_241 (d : ℕ) (hd241 : 241 ≤ d) :
    6703954379 * 8 < (d ^ 2 - 8) * (4 * d - 3) ^ 2 := by
  have h1 : 241 ^ 2 - 8 ≤ d ^ 2 - 8 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hd241 2) 8
  have h2 : (4 * 241 - 3) ^ 2 ≤ (4 * d - 3) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hmul : (241 ^ 2 - 8) * (4 * 241 - 3) ^ 2 ≤ (d ^ 2 - 8) * (4 * d - 3) ^ 2 :=
    Nat.mul_le_mul h1 h2
  have h241 : 6703954379 * 8 < (241 ^ 2 - 8) * (4 * 241 - 3) ^ 2 := by norm_num
  omega

private lemma k2_floor_241_plus (d : ℕ) (hd241 : 241 ≤ d) :
    6787927937 * 8 < (d ^ 2 - 8) * (4 * d + 3) ^ 2 := by
  have h1 : 241 ^ 2 - 8 ≤ d ^ 2 - 8 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hd241 2) 8
  have h2 : (4 * 241 + 3) ^ 2 ≤ (4 * d + 3) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hmul : (241 ^ 2 - 8) * (4 * 241 + 3) ^ 2 ≤ (d ^ 2 - 8) * (4 * d + 3) ^ 2 :=
    Nat.mul_le_mul h1 h2
  have h241 : 6787927937 * 8 < (241 ^ 2 - 8) * (4 * 241 + 3) ^ 2 := by norm_num
  omega

/-- Unconditional `|k| = 2` quartic obstruction on any exceptional Euler-index witness
`sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`):
forces `1 ≤ |α.re|`, `2 ≤ α.im`, `4 * (d : ℤ) - 3 ≤ |α.re|`,
`(d : ℤ) ^ 2 * α.re ^ 2 < 16 * α.im ^ 2`, `(d ^ 2 - 8) * (4 * d - 3) ^ 2 < 8 * q`,
`148403 < q` (`177065 < q` when `k = -2`), and `6703954379 < q` (`6787927937 < q` when `k = -2`)
when `¬ 3 ∣ N ∧ ¬ 5 ∣ N`. -/
theorem exceptional_euler_unit_exponent_two_quartic_bound
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
      (|k| = 2 →
        Odd y ∧
        1 ≤ |α.re| ∧
        2 ≤ α.im ∧
        4 * (d : ℤ) - 3 ≤ |α.re| ∧
        (d : ℤ) ^ 2 * α.re ^ 2 < 16 * α.im ^ 2 ∧
        (d ^ 2 - 8) * (4 * d - 3) ^ 2 < 8 * q ∧
        148403 < q ∧
        (k = -2 → 4 * (d : ℤ) + 3 ≤ α.re ∧ (d ^ 2 - 8) * (4 * d + 3) ^ 2 < 8 * q ∧ 177065 < q) ∧
        (¬ 3 ∣ N → ¬ 5 ∣ N →
          241 ≤ d ∧ 6703954379 < q ∧ (k = -2 → 6787927937 < q))) := by
  intro d
  obtain ⟨hd, hd17, hd8, hq16, _, _, _⟩ :=
    exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hd_odd : Odd d := Nat.odd_iff.mpr (by omega)
  have hd5 : 5 ≤ d := by omega
  obtain ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, hnorm, _, _, _,
      hre_d, _, hre8, _, _⟩ :=
    exceptional_euler_zsqrtTwo_mod_eight_d_profile hN ho hq hq4 ha4 ha hqm hform hl hi
  refine ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, hnorm, ?_⟩
  intro hk_abs
  have hk_cases : k = 2 ∨ k = -2 := abs_eq (by norm_num : (0 : ℤ) ≤ 2) |>.mp hk_abs
  have hk_even : Even k := by
    rcases hk_cases with rfl | rfl <;> decide
  have hnorm_neg : α.norm = -(q : ℤ) := by
    rw [hnorm, ite_eq_left_iff.mpr (fun h => absurd hk_even h)]
  obtain ⟨_, _, hre_abs, him2, hsq, _, hcong⟩ :=
    zsqrtTwo_fermat_k_abs_two_obstruction hq3 hd_odd hd5 hy_pos hpow hk_abs hz_eq hnorm_neg
  obtain ⟨hy_odd, hm2_cong, _, hre_lb, h8q_lt⟩ := hcong hd8 hq16 hre_d hre8
  have h148 : 148403 < q := by
    have hfl := k2_floor_17 d hd17
    omega
  have hm2_full : k = -2 →
      4 * (d : ℤ) + 3 ≤ α.re ∧ (d ^ 2 - 8) * (4 * d + 3) ^ 2 < 8 * q ∧ 177065 < q := by
    intro hkm2
    obtain ⟨hre_p, hq_p⟩ := hm2_cong hkm2
    have hfl := k2_floor_17_plus d hd17
    exact ⟨hre_p, hq_p, by omega⟩
  have h241_branch : ¬ 3 ∣ N → ¬ 5 ∣ N →
      241 ≤ d ∧ 6703954379 < q ∧ (k = -2 → 6787927937 < q) := by
    intro h3 h5
    obtain ⟨_, _, _, hd241, _⟩ :=
      exceptional_euler_of_not_three_or_five_dvd hN ho hq hq4 ha4 ha hqm hform hl hi h3 h5
    have hfl := k2_floor_241 d hd241
    refine ⟨hd241, by omega, ?_⟩
    intro hkm2
    obtain ⟨_, hq_p⟩ := hm2_cong hkm2
    have hfl_p := k2_floor_241_plus d hd241
    omega
  exact ⟨hy_odd, hre_abs, him2, hre_lb, hsq, h8q_lt, h148, hm2_full, h241_branch⟩

end OddPerfect
