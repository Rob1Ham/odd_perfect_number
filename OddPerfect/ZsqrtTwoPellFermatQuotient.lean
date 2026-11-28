module

public import OddPerfect.ZsqrtTwoQuinticSexticObstruction
public import OddPerfect.ExceptionalBlockSquare
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# All-`k` Mod-`d ^ 2` Pell–Fermat Quotient Law in `ℤ√2` (`OddPerfect.ZsqrtTwoPellFermatQuotient`)

Formalizes the mod-`d ^ 2` Pell–Fermat quotient law on `q ^ d + 1 = 2 * y ^ 2`
(`d.Prime`, `d % 8 = 1`, `d ∣ y`) and on exceptional Euler indices
`sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`):

1. `pellFermatQuotient`: `((silverUnit ^ (d - 1) : (ℤ√2)ˣ) : ℤ√2).im / d`.
2. `silverUnit_pow_pred_mod_sq`: proves `(d : ℤ) ^ 2 ∣ (silverUnit ^ (d - 1)).re - 1`,
   `(d : ℤ) ∣ (silverUnit ^ (d - 1)).im`, and for ALL `k : ℤ`,
   `silverUnit ^ (k * (d - 1)) ≡ ⟨1, k * d * pellFermatQuotient d⟩ [ZMOD d ^ 2]`.
3. `zsqrtTwo_pow_mul_pred_mod_sq`: for `¬ (d : ℤ) ∣ α.norm`,
   `α ^ (d * (d - 1)) ≡ 1 [ZMOD d ^ 2]` coordinatewise.
4. `zsqrtTwo_fermat_pell_quotient_all_k_congruence`: for EVERY `k`,
   `k * pellFermatQuotient d ≡ -(y / d) [ZMOD d]`, and when `¬ d ∣ pellFermatQuotient d`
   with `1 ≤ |k| ≤ (d - 1) / 2`, rules out `d ^ 2 ∣ y`.
5. `exceptional_euler_pell_fermat_quotient_profile`: specializes to exceptional Euler-index
   witnesses, establishing `q + 1 ≡ 2 * d * (k * pellFermatQuotient d) ^ 2 [ZMOD d ^ 2]`
   and unconditionally ruling out `d ^ 2 ∣ y` and `d ^ 2 ∣ q + 1` for
   `d ∈ {17, 41, 73, 89, 97, 113, 137, 193, 233, 241}`.
-/

public section

namespace OddPerfect

open ArithmeticFunction

/-- The Pell–Fermat quotient of `1 + √2` modulo prime `d ≡ 1 [MOD 8]`:
`((silverUnit ^ (d - 1)).im) / d`. -/
@[expose] def pellFermatQuotient (d : ℕ) : ℤ :=
  (((silverUnit ^ (d - 1) : (ℤ√2)ˣ) : ℤ√2).im) / (d : ℤ)

private lemma silverUnit_pow_norm (n : ℕ) :
    ((silverUnit ^ n : (ℤ√2)ˣ) : ℤ√2).norm = (-1 : ℤ) ^ n := by
  have hsu : (silverUnit : ℤ√2).norm = -1 := by
    simp [silverUnit_val, Zsqrtd.norm_def]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Units.val_mul, Zsqrtd.norm_mul, ih, hsu, pow_succ]

private lemma zsqrtTwo_unit_inv_eq_star {u : (ℤ√2)ˣ} (hu : (u : ℤ√2).norm = 1) :
    ((u⁻¹ : (ℤ√2)ˣ) : ℤ√2) = star (u : ℤ√2) := by
  have hmul : (u : ℤ√2) * star (u : ℤ√2) = 1 := by
    rw [← Zsqrtd.norm_eq_mul_conj, hu]
    rfl
  calc
    ((u⁻¹ : (ℤ√2)ˣ) : ℤ√2)
        = ((u⁻¹ : (ℤ√2)ˣ) : ℤ√2) * ((u : ℤ√2) * star (u : ℤ√2)) := by
      rw [hmul, mul_one]
    _ = (((u⁻¹ * u : (ℤ√2)ˣ) : ℤ√2)) * star (u : ℤ√2) := by
      rw [Units.val_mul, mul_assoc]
    _ = star (u : ℤ√2) := by simp

/-- Mod-`d ^ 2` Pell–Fermat congruence for `silverUnit ^ (k * (d - 1))` for every `k : ℤ`. -/
theorem silverUnit_pow_pred_mod_sq {d : ℕ} (hd : d.Prime) (hd8 : d % 8 = 1) :
    ((d : ℤ) ^ 2 ∣ (((silverUnit ^ (d - 1) : (ℤ√2)ˣ) : ℤ√2).re - 1)) ∧
    ((d : ℤ) ∣ (((silverUnit ^ (d - 1) : (ℤ√2)ˣ) : ℤ√2).im)) ∧
    (d : ℤ) * pellFermatQuotient d = (((silverUnit ^ (d - 1) : (ℤ√2)ˣ) : ℤ√2).im) ∧
    ∀ k : ℤ,
      ((d : ℤ) ^ 2 ∣ (((silverUnit ^ (k * ((d : ℕ) - 1 : ℤ)) : (ℤ√2)ˣ) : ℤ√2).re - 1)) ∧
      ((d : ℤ) ^ 2 ∣ ((((silverUnit ^ (k * ((d : ℕ) - 1 : ℤ)) : (ℤ√2)ˣ) : ℤ√2).im) -
        k * (d : ℤ) * pellFermatQuotient d)) := by
  have hd_pos : 0 < d := hd.pos
  have hd_ne : (d : ℤ) ≠ 0 := by positivity
  have hd_odd : Odd d := Nat.odd_iff.mpr (by omega)
  have hdeven : Even (d - 1) := by
    obtain ⟨m, hm⟩ := hd_odd
    exact ⟨m, by omega⟩
  set w : (ℤ√2)ˣ := silverUnit ^ (d - 1)
  set u : ℤ√2 := (w : ℤ√2)
  have hpow_d : (silverUnit : ℤ√2) ^ d = u * (silverUnit : ℤ√2) := by
    have h1 : d = (d - 1) + 1 := by omega
    conv_lhs => rw [h1, pow_succ]
    simp [u, w]
  have hu_eq : u = (silverUnit : ℤ√2) ^ d * ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2) := by
    calc
      u = u * (((silverUnit * silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2)) := by simp
      _ = (u * (silverUnit : ℤ√2)) * ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2) := by
        rw [Units.val_mul, mul_assoc]
      _ = (silverUnit : ℤ√2) ^ d * ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2) := by rw [← hpow_d]
  obtain ⟨hfrob_re, hfrob_im⟩ :=
    zsqrtTwo_pow_modEq_self_of_prime_mod_eight_eq_one hd hd8 (silverUnit : ℤ√2)
  have hsu_re : (silverUnit : ℤ√2).re = 1 := rfl
  have hsu_im : (silverUnit : ℤ√2).im = 1 := rfl
  rw [hsu_re] at hfrob_re
  rw [hsu_im] at hfrob_im
  have hu_re_expr : u.re = -((silverUnit : ℤ√2) ^ d).re + 2 * ((silverUnit : ℤ√2) ^ d).im := by
    rw [hu_eq, Zsqrtd.re_mul, silverUnit_inv_val]
    simp
  have hu_im_expr : u.im = ((silverUnit : ℤ√2) ^ d).re - ((silverUnit : ℤ√2) ^ d).im := by
    rw [hu_eq, Zsqrtd.im_mul, silverUnit_inv_val]
    simp
    ring
  have hu_re_mod : u.re ≡ 1 [ZMOD (d : ℤ)] := by
    rw [hu_re_expr]
    have h1 := (hfrob_re.neg).add (hfrob_im.mul_left 2)
    simpa using h1
  have hu_im_mod : u.im ≡ 0 [ZMOD (d : ℤ)] := by
    rw [hu_im_expr]
    have h1 := hfrob_re.sub hfrob_im
    simpa using h1
  have hd_dvd_re1 : (d : ℤ) ∣ u.re - 1 := by
    exact Int.modEq_iff_dvd.mp hu_re_mod.symm
  have hd_dvd_im : (d : ℤ) ∣ u.im := by
    exact Int.modEq_zero_iff_dvd.mp hu_im_mod
  obtain ⟨A, hA⟩ := hd_dvd_re1
  obtain ⟨B, hB⟩ := hd_dvd_im
  have hu_norm : u.norm = 1 := by
    change ((silverUnit ^ (d - 1) : (ℤ√2)ˣ) : ℤ√2).norm = 1
    rw [silverUnit_pow_norm, hdeven.neg_one_pow]
  have hu_re_val : u.re = 1 + (d : ℤ) * A := by linarith
  have hnorm_expand : (1 + (d : ℤ) * A) ^ 2 - 2 * ((d : ℤ) * B) ^ 2 = 1 := by
    rw [← hu_re_val, ← hB, ← hu_norm, Zsqrtd.norm_def]
    ring
  have hzero : (d : ℤ) * (2 * A + (d : ℤ) * (A ^ 2 - 2 * B ^ 2)) = 0 := by
    linarith
  have hlin : 2 * A + (d : ℤ) * (A ^ 2 - 2 * B ^ 2) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hd_ne
  have hd_dvd_2A : (d : ℤ) ∣ 2 * A := ⟨-(A ^ 2 - 2 * B ^ 2), by linarith⟩
  have hcop_d2 : IsCoprime (d : ℤ) 2 := by
    have hg : Int.gcd (d : ℤ) 2 = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, Int.gcd_natCast_natCast]
      exact hd_odd.coprime_two_right
    exact Int.isCoprime_iff_gcd_eq_one.mpr hg
  have hd_dvd_A : (d : ℤ) ∣ A := hcop_d2.dvd_of_dvd_mul_left hd_dvd_2A
  obtain ⟨a, ha⟩ := hd_dvd_A
  have hd2_dvd_re1 : (d : ℤ) ^ 2 ∣ u.re - 1 := ⟨a, by rw [hA, ha]; ring⟩
  have hd_dvd_im' : (d : ℤ) ∣ u.im := ⟨B, hB⟩
  have hQ_eq : (d : ℤ) * pellFermatQuotient d = u.im :=
    Int.mul_ediv_cancel' hd_dvd_im'
  refine ⟨hd2_dvd_re1, hd_dvd_im', hQ_eq, ?_⟩
  set Q : ℤ := pellFermatQuotient d
  have hnat : ∀ n : ℕ,
      ((d : ℤ) ^ 2 ∣ (((w ^ n : (ℤ√2)ˣ) : ℤ√2).re - 1)) ∧
      ((d : ℤ) ^ 2 ∣ ((((w ^ n : (ℤ√2)ˣ) : ℤ√2).im) - (n : ℤ) * (d : ℤ) * Q)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      obtain ⟨⟨r, hr⟩, ⟨s, hs⟩⟩ := ih
      have hre_n : ((w ^ n : (ℤ√2)ˣ) : ℤ√2).re = 1 + (d : ℤ) ^ 2 * r := by linarith
      have him_n : ((w ^ n : (ℤ√2)ˣ) : ℤ√2).im = (n : ℤ) * (d : ℤ) * Q + (d : ℤ) ^ 2 * s := by
        linarith
      have hu_re' : u.re = 1 + (d : ℤ) ^ 2 * a := by
        rw [hu_re_val, ha]
        ring
      have hu_im' : u.im = (d : ℤ) * Q := hQ_eq.symm
      have hmul_val : ((w ^ (n + 1) : (ℤ√2)ˣ) : ℤ√2) = ((w ^ n : (ℤ√2)ˣ) : ℤ√2) * u := by
        rw [pow_succ, Units.val_mul]
      rw [hmul_val]
      constructor
      · refine ⟨a + r + (d : ℤ) ^ 2 * r * a + 2 * (n : ℤ) * Q ^ 2 + 2 * (d : ℤ) * s * Q, ?_⟩
        rw [Zsqrtd.re_mul, hre_n, him_n, hu_re', hu_im']
        ring
      · refine ⟨(d : ℤ) * r * Q + s + (n : ℤ) * (d : ℤ) * Q * a + (d : ℤ) ^ 2 * s * a, ?_⟩
        rw [Zsqrtd.im_mul, hre_n, him_n, hu_re', hu_im']
        push_cast
        ring
  intro k
  have hk_exp : (silverUnit ^ (k * ((d : ℕ) - 1 : ℤ)) : (ℤ√2)ˣ) = w ^ k := by
    have hw_zpow : (w : (ℤ√2)ˣ) = silverUnit ^ ((d : ℕ) - 1 : ℤ) := by
      have h1 : ((d - 1 : ℕ) : ℤ) = ((d : ℕ) - 1 : ℤ) := by omega
      rw [← h1, zpow_natCast]
    rw [hw_zpow, ← zpow_mul, mul_comm k]
  rw [hk_exp]
  cases k with
  | ofNat n =>
    simpa [Int.ofNat_eq_natCast] using hnat n
  | negSucc m =>
    set n : ℕ := m + 1
    have hk_eq : Int.negSucc m = -(n : ℤ) := rfl
    rw [hk_eq, zpow_neg, zpow_natCast]
    have hnorm_wn : ((w ^ n : (ℤ√2)ˣ) : ℤ√2).norm = 1 := by
      induction n with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, Units.val_mul, Zsqrtd.norm_mul, ih, show (w : ℤ√2).norm = 1 from hu_norm,
          mul_one]
    have hinv_star : (((w ^ n)⁻¹ : (ℤ√2)ˣ) : ℤ√2) = star ((w ^ n : (ℤ√2)ˣ) : ℤ√2) :=
      zsqrtTwo_unit_inv_eq_star hnorm_wn
    obtain ⟨hr, hs⟩ := hnat n
    rw [hinv_star]
    constructor
    · change (d : ℤ) ^ 2 ∣ ((w ^ n : (ℤ√2)ˣ) : ℤ√2).re - 1
      exact hr
    · obtain ⟨s, hs_eq⟩ := hs
      refine ⟨-s, ?_⟩
      change -((w ^ n : (ℤ√2)ˣ) : ℤ√2).im - -(n : ℤ) * (d : ℤ) * Q = (d : ℤ) ^ 2 * -s
      linarith

/-- For any `α : ℤ√2` whose norm is coprime to `d` (`d.Prime`, `d % 8 = 1`),
`α ^ (d * (d - 1)) ≡ 1 [ZMOD d ^ 2]` coordinatewise. -/
theorem zsqrtTwo_pow_mul_pred_mod_sq {d : ℕ} (hd : d.Prime) (hd8 : d % 8 = 1)
    {α : ℤ√2} (hcop : ¬ (d : ℤ) ∣ α.norm) :
    ((d : ℤ) ^ 2 ∣ (α ^ (d * (d - 1))).re - 1) ∧
    ((d : ℤ) ^ 2 ∣ (α ^ (d * (d - 1))).im) := by
  have hd_pos : 0 < d := hd.pos
  obtain ⟨hfrob_re, hfrob_im⟩ :=
    zsqrtTwo_pow_modEq_self_of_prime_mod_eight_eq_one hd hd8 α
  have hd_re : (d : ℤ) ∣ (α ^ d - α).re := by
    simpa [Zsqrtd.re_sub] using Int.modEq_iff_dvd.mp hfrob_re.symm
  have hd_im : (d : ℤ) ∣ (α ^ d - α).im := by
    simpa [Zsqrtd.im_sub] using Int.modEq_iff_dvd.mp hfrob_im.symm
  obtain ⟨x, hx⟩ := hd_re
  obtain ⟨y, hy⟩ := hd_im
  let β : ℤ√2 := ⟨x, y⟩
  have hdiff : α ^ d - α = (d : ℤ√2) * β := by
    ext
    · simpa [β] using hx
    · simpa [β] using hy
  have hmul_conj : (α ^ (d - 1) - 1) * (α.norm : ℤ√2) = (d : ℤ√2) * (β * star α) := by
    calc
      (α ^ (d - 1) - 1) * (α.norm : ℤ√2)
          = (α ^ (d - 1) - 1) * (α * star α) := by rw [Zsqrtd.norm_eq_mul_conj]
      _ = ((α ^ (d - 1) - 1) * α) * star α := by ring
      _ = (α ^ (d - 1 + 1) - α) * star α := by rw [sub_mul, one_mul, pow_succ]
      _ = (α ^ d - α) * star α := by rw [Nat.sub_add_cancel hd_pos]
      _ = ((d : ℤ√2) * β) * star α := by rw [hdiff]
      _ = (d : ℤ√2) * (β * star α) := by ring
  have hre_div : (d : ℤ) ∣ (α ^ (d - 1) - 1).re * α.norm := by
    have hre := congrArg Zsqrtd.re hmul_conj
    simp only [Zsqrtd.re_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast, mul_zero, add_zero,
      Zsqrtd.re_natCast, Zsqrtd.im_natCast, zero_mul] at hre
    exact ⟨(β * star α).re, hre⟩
  have him_div : (d : ℤ) ∣ (α ^ (d - 1) - 1).im * α.norm := by
    have him := congrArg Zsqrtd.im hmul_conj
    simp only [Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast, mul_zero, zero_add,
      Zsqrtd.re_natCast, Zsqrtd.im_natCast, zero_mul, add_zero] at him
    exact ⟨(β * star α).im, him⟩
  have hd_int_prime : Prime (d : ℤ) :=
    Int.prime_iff_natAbs_prime.mpr (by simpa using hd)
  have hd_re1 : (d : ℤ) ∣ (α ^ (d - 1) - 1).re :=
    (hd_int_prime.dvd_or_dvd hre_div).resolve_right hcop
  have hd_im1 : (d : ℤ) ∣ (α ^ (d - 1) - 1).im :=
    (hd_int_prime.dvd_or_dvd him_div).resolve_right hcop
  obtain ⟨u, hu⟩ := hd_re1
  obtain ⟨v, hv⟩ := hd_im1
  let γ : ℤ√2 := ⟨u, v⟩
  have hpred : α ^ (d - 1) = (d : ℤ√2) * γ + 1 := by
    apply sub_eq_iff_eq_add.mp
    ext
    · simpa [γ] using hu
    · simpa [γ] using hv
  have hpow : α ^ (d * (d - 1)) = ((d : ℤ√2) * γ + 1) ^ d := by
    rw [mul_comm, pow_mul, hpred]
  let f : ℕ → ℤ√2 := fun j => ((d : ℤ√2) * γ) ^ j * 1 ^ (d - j) * (d.choose j : ℤ√2)
  have hbin : α ^ (d * (d - 1)) = ∑ j ∈ Finset.range (d + 1), f j := by
    rw [hpow, add_pow]
  have hsplit : (∑ j ∈ Finset.range (d + 1), f j) =
      (∑ j ∈ Finset.range d, f (j + 1)) + f 0 :=
    Finset.sum_range_succ' f d
  have hf0 : f 0 = 1 := by simp [f]
  have hd_sub : d = (d - 1) + 1 := by omega
  have hsplit2 : (∑ j ∈ Finset.range d, f (j + 1)) =
      (∑ j ∈ Finset.range (d - 1), f (j + 2)) + f 1 := by
    conv_lhs => rw [hd_sub]
    exact Finset.sum_range_succ' (fun j => f (j + 1)) (d - 1)
  let D2 : ℤ := (d : ℤ) ^ 2
  have hf1 : f 1 = (D2 : ℤ√2) * γ := by
    dsimp [f, D2]
    rw [pow_one, one_pow, mul_one, Nat.choose_one_right]
    push_cast
    ring
  have hdvd_tail : (D2 : ℤ√2) ∣ ∑ j ∈ Finset.range (d - 1), f (j + 2) := by
    apply Finset.dvd_sum
    intro j _
    dsimp [f, D2]
    refine ⟨γ ^ (j + 2) * (d : ℤ√2) ^ j * (d.choose (j + 2) : ℤ√2), ?_⟩
    push_cast
    ring
  obtain ⟨K, hK⟩ := hdvd_tail
  have hfinal : α ^ (d * (d - 1)) - 1 = (D2 : ℤ√2) * (γ + K) := by
    rw [hbin, hsplit, hf0, add_sub_cancel_right, hsplit2, hf1, hK]
    ring
  constructor
  · refine ⟨(γ + K).re, ?_⟩
    have hre := congrArg Zsqrtd.re hfinal
    simp only [Zsqrtd.re_sub, Zsqrtd.re_one, Zsqrtd.re_mul, Zsqrtd.re_intCast,
      Zsqrtd.im_intCast, mul_zero, zero_mul, add_zero] at hre
    exact hre
  · refine ⟨(γ + K).im, ?_⟩
    have him := congrArg Zsqrtd.im hfinal
    simp only [Zsqrtd.im_sub, Zsqrtd.im_one, sub_zero, Zsqrtd.im_mul, Zsqrtd.re_intCast,
      Zsqrtd.im_intCast, zero_mul, add_zero] at him
    exact him

/-- All-`k` mod-`d` Pell–Fermat quotient congruence on `q ^ d + 1 = 2 * y ^ 2`:
for every `k` (`1 ≤ |k| ≤ (d - 1) / 2`), `k * pellFermatQuotient d ≡ -(y / d) [ZMOD d]`,
and `¬ d ∣ pellFermatQuotient d` forces `¬ d ^ 2 ∣ y`. -/
theorem zsqrtTwo_fermat_pell_quotient_all_k_congruence {q d y : ℕ}
    (hq : q.Prime) (hd : d.Prime) (hd8 : d % 8 = 1) (hdy : d ∣ y)
    (hpow : q ^ d + 1 = 2 * y ^ 2) {k : ℤ} {α : ℤ√2}
    (hz : (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d)
    (hnorm : α.norm = (if Even k then -(q : ℤ) else (q : ℤ))) :
    k * pellFermatQuotient d ≡ -((y / d : ℕ) : ℤ) [ZMOD (d : ℤ)] ∧
    (1 ≤ |k| → 2 * |k| ≤ (d : ℤ) - 1 → ¬ (d : ℤ) ∣ pellFermatQuotient d → ¬ d ^ 2 ∣ y) := by
  have hd_pos : 0 < d := hd.pos
  have hd3 : 3 ≤ d := by have := hd.two_le; omega
  have hd_ne : (d : ℤ) ≠ 0 := by positivity
  have hqd_ne : q ≠ d := by
    intro hqd
    subst hqd
    have h1 : q ∣ q ^ q := dvd_pow_self q hd_pos.ne'
    have h2 : q ∣ 2 * y ^ 2 := dvd_mul_of_dvd_right (hdy.trans (dvd_pow_self y (by decide : 2 ≠ 0))) 2
    have h3 : q ∣ q ^ q + 1 := hpow ▸ h2
    have h4 : q ∣ 1 := (Nat.dvd_add_right h1).mp h3
    exact hd.not_dvd_one h4
  have hcop : ¬ (d : ℤ) ∣ α.norm := by
    intro hdv
    have hd_dvd_q : (d : ℤ) ∣ (q : ℤ) := by
      rw [hnorm] at hdv
      split_ifs at hdv
      · exact dvd_neg.mp hdv
      · exact hdv
    have hd_q : d ∣ q := Int.natCast_dvd_natCast.mp hd_dvd_q
    exact hqd_ne ((Nat.prime_dvd_prime_iff_eq hd hq).mp hd_q).symm
  obtain ⟨hα_re, hα_im⟩ := zsqrtTwo_pow_mul_pred_mod_sq hd hd8 hcop
  obtain ⟨_, _, _, hk_su⟩ := silverUnit_pow_pred_mod_sq hd hd8
  obtain ⟨hsu_re, hsu_im⟩ := hk_su k
  set Q : ℤ := pellFermatQuotient d
  set Y : ℕ := y / d
  have hy_eq : y = d * Y := (Nat.mul_div_cancel' hdy).symm
  have hy_z : (y : ℤ) = (d : ℤ) * (Y : ℤ) := by exact_mod_cast hy_eq
  have hlhs_pow : ((⟨1, (y : ℤ)⟩ : ℤ√2) ^ (d - 1)).im ≡
      ((d : ℤ) - 1) * (y : ℤ) [ZMOD (d : ℤ) ^ 2] := by
    have hsplit : (⟨1, (y : ℤ)⟩ : ℤ√2) = ⟨0, (y : ℤ)⟩ + 1 := by ext <;> simp
    let g : ℕ → ℤ√2 := fun j => (⟨0, (y : ℤ)⟩ : ℤ√2) ^ j * 1 ^ (d - 1 - j) * ((d - 1).choose j : ℤ√2)
    have hbin : (⟨1, (y : ℤ)⟩ : ℤ√2) ^ (d - 1) = ∑ j ∈ Finset.range d, g j := by
      rw [hsplit, add_pow, Nat.sub_add_cancel hd_pos]
    have hsplit1 : (∑ j ∈ Finset.range d, g j) =
        (∑ j ∈ Finset.range (d - 1), g (j + 1)) + g 0 := by
      have hd_sub : d = (d - 1) + 1 := by omega
      conv_lhs => rw [hd_sub]
      exact Finset.sum_range_succ' g (d - 1)
    have hg0 : g 0 = 1 := by simp [g]
    have hsplit2 : (∑ j ∈ Finset.range (d - 1), g (j + 1)) =
        (∑ j ∈ Finset.range (d - 2), g (j + 2)) + g 1 := by
      have hd_sub : d - 1 = (d - 2) + 1 := by omega
      conv_lhs => rw [hd_sub]
      exact Finset.sum_range_succ' (fun j => g (j + 1)) (d - 2)
    have hg1 : g 1 = ⟨0, ((d : ℤ) - 1) * (y : ℤ)⟩ := by
      dsimp [g]
      rw [pow_one, one_pow, mul_one, Nat.choose_one_right]
      have hdm1 : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
      ext
      · simp
      · simp [hdm1, mul_comm]
    have hdvd_tail : (((d : ℤ) ^ 2 : ℤ) : ℤ√2) ∣ ∑ j ∈ Finset.range (d - 2), g (j + 2) := by
      apply Finset.dvd_sum
      intro j _
      dsimp [g]
      have hsq_dvd : (((d : ℤ) ^ 2 : ℤ) : ℤ√2) ∣ (⟨0, (y : ℤ)⟩ : ℤ√2) ^ 2 := by
        refine ⟨⟨2 * (Y : ℤ) ^ 2, 0⟩, ?_⟩
        ext
        · simp [pow_two, hy_z]
          ring
        · simp [pow_two]
      rw [pow_add]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hsq_dvd _) _) _
    obtain ⟨M, hM⟩ := hdvd_tail
    have hsum_eq : (⟨1, (y : ℤ)⟩ : ℤ√2) ^ (d - 1) =
        (((d : ℤ) ^ 2 : ℤ) : ℤ√2) * M + ⟨1, ((d : ℤ) - 1) * (y : ℤ)⟩ := by
      rw [hbin, hsplit1, hsplit2, hM, hg0, hg1]
      ext <;> simp
    have him := congrArg Zsqrtd.im hsum_eq
    simp only [Zsqrtd.im_add, Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast,
      zero_mul, add_zero] at him
    rw [him]
    exact Int.modEq_iff_dvd.mpr ⟨-M.im, by ring⟩
  have hrhs_eq : (((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d) ^ (d - 1) =
      ((silverUnit ^ (k * ((d : ℕ) - 1 : ℤ)) : (ℤ√2)ˣ) : ℤ√2) * α ^ (d * (d - 1)) := by
    rw [mul_pow, ← pow_mul, ← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul]
    congr 2
    have h1 : ((d - 1 : ℕ) : ℤ) = ((d : ℕ) - 1 : ℤ) := by omega
    rw [h1]
  have hrhs_im : ((((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d) ^ (d - 1)).im ≡
      k * (d : ℤ) * Q [ZMOD (d : ℤ) ^ 2] := by
    rw [hrhs_eq]
    obtain ⟨a, ha⟩ := hsu_re
    obtain ⟨b, hb⟩ := hsu_im
    obtain ⟨c, hc⟩ := hα_re
    obtain ⟨e, he⟩ := hα_im
    set u := ((silverUnit ^ (k * ((d : ℕ) - 1 : ℤ)) : (ℤ√2)ˣ) : ℤ√2)
    set v := α ^ (d * (d - 1))
    have hu_re : u.re = 1 + (d : ℤ) ^ 2 * a := by linarith
    have hu_im : u.im = k * (d : ℤ) * Q + (d : ℤ) ^ 2 * b := by linarith
    have hv_re : v.re = 1 + (d : ℤ) ^ 2 * c := by linarith
    have hv_im : v.im = (d : ℤ) ^ 2 * e := by linarith
    refine Int.modEq_iff_dvd.mpr
      ⟨-(e + (d : ℤ) ^ 2 * a * e + k * (d : ℤ) * Q * c + b + (d : ℤ) ^ 2 * b * c), ?_⟩
    rw [Zsqrtd.im_mul, hu_re, hu_im, hv_re, hv_im]
    ring
  have hpow_eq := congrArg (fun z : ℤ√2 => (z ^ (d - 1)).im) hz
  have him_mod : ((d : ℤ) - 1) * (y : ℤ) ≡ k * (d : ℤ) * Q [ZMOD (d : ℤ) ^ 2] :=
    hlhs_pow.symm.trans (hpow_eq ▸ hrhs_im)
  have hd2_dvd : (d : ℤ) ^ 2 ∣ k * (d : ℤ) * Q - ((d : ℤ) - 1) * (y : ℤ) :=
    Int.modEq_iff_dvd.mp him_mod
  obtain ⟨m, hm⟩ := hd2_dvd
  have hm_eq : (d : ℤ) * (k * Q + (Y : ℤ)) = (d : ℤ) * ((d : ℤ) * (m + (Y : ℤ))) := by
    rw [hy_z] at hm
    linarith
  have hcancel : k * Q + (Y : ℤ) = (d : ℤ) * (m + (Y : ℤ)) :=
    mul_left_cancel₀ hd_ne hm_eq
  have hcong : k * Q ≡ -(Y : ℤ) [ZMOD (d : ℤ)] :=
    Int.modEq_iff_dvd.mpr ⟨-(m + (Y : ℤ)), by linarith⟩
  refine ⟨hcong, ?_⟩
  intro hk1 h2k hndvd hd2_y
  have hd_dvd_Y : d ∣ Y := by
    obtain ⟨t, ht⟩ := hd2_y
    refine ⟨t, ?_⟩
    apply Nat.eq_of_mul_eq_mul_left hd_pos
    calc
      d * Y = y := hy_eq.symm
      _ = d ^ 2 * t := ht
      _ = d * (d * t) := by ring
  have hY_mod : (Y : ℤ) ≡ 0 [ZMOD (d : ℤ)] :=
    Int.modEq_zero_iff_dvd.mpr (Int.natCast_dvd_natCast.mpr hd_dvd_Y)
  have hkQ_dvd : (d : ℤ) ∣ k * Q :=
    Int.modEq_zero_iff_dvd.mp (hcong.trans hY_mod.neg)
  have hd_int_prime : Prime (d : ℤ) :=
    Int.prime_iff_natAbs_prime.mpr (by simpa using hd)
  have hd_dvd_k : (d : ℤ) ∣ k := (hd_int_prime.dvd_or_dvd hkQ_dvd).resolve_right hndvd
  have hd_dvd_abs : (d : ℤ) ∣ |k| := by
    rcases abs_choice k with h | h <;> rw [h]
    · exact hd_dvd_k
    · exact hd_dvd_k.neg_right
  have hd_le_abs : (d : ℤ) ≤ |k| := Int.le_of_dvd (by omega) hd_dvd_abs
  omega

private def mulZsqrtTwoMod (a b : ℤ × ℤ) (m : ℤ) : ℤ × ℤ :=
  ((a.1 * b.1 + 2 * a.2 * b.2) % m, (a.1 * b.2 + a.2 * b.1) % m)

private def powZsqrtTwoModAux : ℕ → ℤ × ℤ → ℕ → ℤ → ℤ × ℤ
  | 0, _, _, m => (1 % m, 0)
  | fuel + 1, a, n, m =>
    if n = 0 then (1 % m, 0)
    else
      let half := powZsqrtTwoModAux fuel a (n / 2) m
      let sq := mulZsqrtTwoMod half half m
      if n % 2 = 0 then sq else mulZsqrtTwoMod sq a m

private lemma mulZsqrtTwoMod_spec (x y : ℤ√2) (px py : ℤ × ℤ) (m : ℤ)
    (hx1 : x.re % m = px.1 % m) (hx2 : x.im % m = px.2 % m)
    (hy1 : y.re % m = py.1 % m) (hy2 : y.im % m = py.2 % m) :
    (x * y).re % m = (mulZsqrtTwoMod px py m).1 % m ∧
    (x * y).im % m = (mulZsqrtTwoMod px py m).2 % m := by
  have hx1' : x.re ≡ px.1 [ZMOD m] := hx1
  have hx2' : x.im ≡ px.2 [ZMOD m] := hx2
  have hy1' : y.re ≡ py.1 [ZMOD m] := hy1
  have hy2' : y.im ≡ py.2 [ZMOD m] := hy2
  constructor
  · change (x * y).re ≡ (px.1 * py.1 + 2 * px.2 * py.2) % m [ZMOD m]
    rw [Zsqrtd.re_mul]
    have h := (hx1'.mul hy1').add ((hx2'.mul_left 2).mul hy2')
    simpa [mul_assoc, Int.ModEq, Int.emod_emod] using h
  · change (x * y).im ≡ (px.1 * py.2 + px.2 * py.1) % m [ZMOD m]
    rw [Zsqrtd.im_mul]
    have h := (hx1'.mul hy2').add (hx2'.mul hy1')
    simpa [Int.ModEq, Int.emod_emod] using h

private lemma powZsqrtTwoModAux_spec (a : ℤ√2) (fuel n : ℕ) (m : ℤ) (hn : n < 2 ^ fuel) :
    (a ^ n).re % m = (powZsqrtTwoModAux fuel (a.re, a.im) n m).1 % m ∧
    (a ^ n).im % m = (powZsqrtTwoModAux fuel (a.re, a.im) n m).2 % m := by
  induction fuel generalizing n with
  | zero =>
    have hn0 : n = 0 := by simpa using hn
    subst hn0
    simp [powZsqrtTwoModAux]
  | succ fuel ih =>
    unfold powZsqrtTwoModAux
    split_ifs with hn0 hn2
    · subst hn0
      simp
    · have hlt : n / 2 < 2 ^ fuel := by
        rw [pow_succ'] at hn
        omega
      obtain ⟨ih1, ih2⟩ := ih (n / 2) hlt
      have hpow : a ^ n = a ^ (n / 2) * a ^ (n / 2) := by
        conv_lhs => rw [show n = 2 * (n / 2) by omega]
        rw [two_mul, pow_add]
      rw [hpow]
      exact mulZsqrtTwoMod_spec (a ^ (n / 2)) (a ^ (n / 2)) _ _ m ih1 ih2 ih1 ih2
    · have hlt : n / 2 < 2 ^ fuel := by
        rw [pow_succ'] at hn
        omega
      obtain ⟨ih1, ih2⟩ := ih (n / 2) hlt
      have hpow : a ^ n = (a ^ (n / 2) * a ^ (n / 2)) * a := by
        conv_lhs => rw [show n = 2 * (n / 2) + 1 by omega]
        rw [two_mul, pow_add, pow_add, pow_one]
      obtain ⟨hsq1, hsq2⟩ :=
        mulZsqrtTwoMod_spec (a ^ (n / 2)) (a ^ (n / 2)) _ _ m ih1 ih2 ih1 ih2
      rw [hpow]
      exact mulZsqrtTwoMod_spec (a ^ (n / 2) * a ^ (n / 2)) a _ (a.re, a.im) m hsq1 hsq2 rfl rfl

private lemma pellFermatQuotient_not_dvd_of_concrete {d : ℕ}
    (hd : d.Prime) (hd8 : d % 8 = 1) (hd_lt : d - 1 < 2 ^ 10)
    (hpow_ne : (powZsqrtTwoModAux 10 (1, 1) (d - 1) ((d : ℤ) ^ 2)).2 % ((d : ℤ) ^ 2) ≠ 0) :
    ¬ (d : ℤ) ∣ pellFermatQuotient d := by
  intro hd_dvd
  obtain ⟨_, _, hQ_eq, _⟩ := silverUnit_pow_pred_mod_sq hd hd8
  have hd2_dvd : (d : ℤ) ^ 2 ∣ (((silverUnit ^ (d - 1) : (ℤ√2)ˣ) : ℤ√2).im) := by
    rw [← hQ_eq]
    obtain ⟨t, ht⟩ := hd_dvd
    refine ⟨t, ?_⟩
    rw [ht]
    ring
  have him_zero : (((silverUnit ^ (d - 1) : (ℤ√2)ˣ) : ℤ√2).im) % ((d : ℤ) ^ 2) = 0 :=
    Int.emod_eq_zero_of_dvd hd2_dvd
  have hspec := (powZsqrtTwoModAux_spec (silverUnit : ℤ√2) 10 (d - 1) ((d : ℤ) ^ 2) hd_lt).2
  rw [← Units.val_pow_eq_pow_val] at hspec
  rw [him_zero, silverUnit_val] at hspec
  exact hpow_ne hspec.symm

private lemma pellFermatQuotient_not_dvd_finset {d : ℕ}
    (hd : d.Prime) (hd8 : d % 8 = 1)
    (hd_mem : d ∈ ({17, 41, 73, 89, 97, 113, 137, 193, 233, 241} : Finset ℕ)) :
    ¬ (d : ℤ) ∣ pellFermatQuotient d := by
  have hd_lt : d - 1 < 2 ^ 10 := by fin_cases hd_mem <;> decide
  have hpow_ne : (powZsqrtTwoModAux 10 (1, 1) (d - 1) ((d : ℤ) ^ 2)).2 % ((d : ℤ) ^ 2) ≠ 0 := by
    fin_cases hd_mem <;> decide
  exact pellFermatQuotient_not_dvd_of_concrete hd hd8 hd_lt hpow_ne

private lemma second_block_z_sq_mod_d {q d w z : ℕ}
    (hd : d.Prime) (hd8 : d % 8 = 1)
    (hq1 : q + 1 = 2 * d * w ^ 2) (hqd1 : q ^ d + 1 = 2 * (d * w * z) ^ 2) :
    (z : ℤ) ^ 2 ≡ 1 [ZMOD (d : ℤ)] := by
  have hd_pos : 0 < d := hd.pos
  have hd_odd : Odd d := Nat.odd_iff.mpr (by omega)
  have hd3 : 3 ≤ d := by have := hd.two_le; omega
  have hw_pos : 0 < w := by
    rcases eq_or_ne w 0 with rfl | hw0
    · simp at hq1
    · exact Nat.pos_of_ne_zero hw0
  let E : ℤ := ((q + 1 : ℕ) : ℤ)
  have hE_eq : E = 2 * (d : ℤ) * (w : ℤ) ^ 2 := by
    dsimp [E]
    exact_mod_cast hq1
  have hE_ne : E ≠ 0 := by
    rw [hE_eq]
    positivity
  have hd_ne : (d : ℤ) ≠ 0 := by positivity
  have hq_eq : (q : ℤ) = E + (-1) := by dsimp [E]; ring
  let f : ℕ → ℤ := fun j => E ^ j * (-1) ^ (d - j) * (d.choose j : ℤ)
  have hbin : ((q ^ d + 1 : ℕ) : ℤ) = (∑ j ∈ Finset.range (d + 1), f j) + 1 := by
    push_cast
    rw [hq_eq, add_pow]
  have hsplit1 : (∑ j ∈ Finset.range (d + 1), f j) =
      (∑ j ∈ Finset.range d, f (j + 1)) + f 0 :=
    Finset.sum_range_succ' f d
  have hf0 : f 0 + 1 = 0 := by simp [f, hd_odd.neg_one_pow]
  have hd_sub : d = (d - 1) + 1 := by omega
  have hsplit2 : (∑ j ∈ Finset.range d, f (j + 1)) =
      (∑ j ∈ Finset.range (d - 1), f (j + 2)) + f 1 := by
    conv_lhs => rw [hd_sub]
    exact Finset.sum_range_succ' (fun j => f (j + 1)) (d - 1)
  have hf1 : f 1 = E * (d : ℤ) := by
    dsimp [f]
    have hdeven : Even (d - 1) := by obtain ⟨m, hm⟩ := hd_odd; exact ⟨m, by omega⟩
    rw [pow_one, Nat.choose_one_right, hdeven.neg_one_pow, mul_one]
  have hdvd_tail : E * (d : ℤ) ^ 2 ∣ ∑ j ∈ Finset.range (d - 1), f (j + 2) := by
    apply Finset.dvd_sum
    intro j _
    dsimp [f]
    by_cases hj0 : j = 0
    · subst hj0
      simp only [zero_add]
      have hd_choose : (d : ℤ) ∣ (d.choose 2 : ℤ) := by
        obtain ⟨m, hm⟩ := hd_odd
        have hch : d.choose 2 = d * m := by
          rw [Nat.choose_two_right, show d - 1 = 2 * m by omega, ← mul_assoc,
            Nat.mul_comm d 2, mul_assoc, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
        exact_mod_cast (⟨m, hch⟩ : d ∣ d.choose 2)
      obtain ⟨c, hc⟩ := hd_choose
      refine ⟨2 * (w : ℤ) ^ 2 * (-1) ^ (d - 2) * c, ?_⟩
      rw [pow_two, hc]
      conv_lhs => lhs; lhs; rhs; rw [hE_eq]
      ring
    · have hj1 : 1 ≤ j := Nat.pos_of_ne_zero hj0
      have hpow : E ^ (j + 2) = E * E ^ 2 * E ^ (j - 1) := by
        rw [show j + 2 = 1 + 2 + (j - 1) by omega, pow_add, pow_add, pow_one]
      have hE2 : E ^ 2 = (d : ℤ) ^ 2 * (4 * (w : ℤ) ^ 4) := by
        rw [hE_eq]
        ring
      refine ⟨4 * (w : ℤ) ^ 4 * E ^ (j - 1) * (-1) ^ (d - (j + 2)) * (d.choose (j + 2) : ℤ), ?_⟩
      rw [hpow, hE2]
      ring
  obtain ⟨K, hK⟩ := hdvd_tail
  have hqd1_z : ((q ^ d + 1 : ℕ) : ℤ) = E * (d : ℤ) * (z : ℤ) ^ 2 := by
    have hz_eq : ((q ^ d + 1 : ℕ) : ℤ) = 2 * ((d : ℤ) * (w : ℤ) * (z : ℤ)) ^ 2 := by
      exact_mod_cast hqd1
    rw [hz_eq, hE_eq]
    ring
  have h_sum_eq : E * (d : ℤ) * (z : ℤ) ^ 2 = E * (d : ℤ) * (1 + (d : ℤ) * K) := by
    rw [← hqd1_z, hbin, hsplit1, add_assoc, hf0, add_zero, hsplit2, hf1, hK]
    ring
  have hz2_eq : (z : ℤ) ^ 2 = 1 + (d : ℤ) * K :=
    mul_left_cancel₀ (mul_ne_zero hE_ne hd_ne) h_sum_eq
  exact Int.modEq_iff_dvd.mpr ⟨-K, by linarith⟩

/-- Exceptional Euler-index Pell–Fermat quotient profile on `sigma 1 (m ^ 2) / q ^ a = l * t ^ 2`
(`a > 1`, `l.Prime`): establishes the all-`k` congruence `k * pellFermatQuotient d ≡ -(y / d) [ZMOD d]`,
the mod-`d ^ 2` identity `q + 1 ≡ 2 * d * (k * pellFermatQuotient d) ^ 2 [ZMOD d ^ 2]`, and rules out
`d ^ 2 ∣ y` and `d ^ 2 ∣ q + 1` for all ten primes `d ∈ {17, 41, 73, 89, 97, 113, 137, 193, 233, 241}`. -/
theorem exceptional_euler_pell_fermat_quotient_profile
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
      k * pellFermatQuotient d ≡ -((y / d : ℕ) : ℤ) [ZMOD (d : ℤ)] ∧
      ((q + 1 : ℕ) : ℤ) ≡ 2 * (d : ℤ) * (k * pellFermatQuotient d) ^ 2 [ZMOD (d : ℤ) ^ 2] ∧
      (d ∈ ({17, 41, 73, 89, 97, 113, 137, 193, 233, 241} : Finset ℕ) →
        ¬ d ^ 2 ∣ y ∧ ¬ d ^ 2 ∣ q + 1) := by
  intro d
  obtain ⟨hd, _, hd8, _, _, _, _⟩ :=
    exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
  change d.Prime at hd
  change d % 8 = 1 at hd8
  obtain ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, hnorm, _, _, _, _, _, _, _, _⟩ :=
    exceptional_euler_zsqrtTwo_mod_eight_d_profile hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨w, z, _, _, _, _, hq1, _, hqd1, _, _, _, _⟩ :=
    exceptional_euler_second_block_exact_square hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨hk_cong, hk_ndvd⟩ :=
    zsqrtTwo_fermat_pell_quotient_all_k_congruence hq hd hd8 hdy hpow hz_eq hnorm
  have hy_dwz : y = d * w * z := by
    have h2 : 2 * y ^ 2 = 2 * (d * w * z) ^ 2 := hpow.symm.trans hqd1
    have hsq : y ^ 2 = (d * w * z) ^ 2 := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h2
    exact (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp hsq
  have hy_div_d : y / d = w * z := by
    rw [hy_dwz, mul_assoc, Nat.mul_div_cancel_left _ hd.pos]
  have hz2_mod : (z : ℤ) ^ 2 ≡ 1 [ZMOD (d : ℤ)] :=
    second_block_z_sq_mod_d hd hd8 hq1 hqd1
  have hkq_sq : (k * pellFermatQuotient d) ^ 2 ≡ (w : ℤ) ^ 2 [ZMOD (d : ℤ)] := by
    have hsq := hk_cong.pow 2
    have hneg_sq : (-((y / d : ℕ) : ℤ)) ^ 2 = (w : ℤ) ^ 2 * (z : ℤ) ^ 2 := by
      rw [hy_div_d]
      push_cast
      ring
    rw [hneg_sq] at hsq
    have hwz : (w : ℤ) ^ 2 * (z : ℤ) ^ 2 ≡ (w : ℤ) ^ 2 * 1 [ZMOD (d : ℤ)] :=
      hz2_mod.mul_left ((w : ℤ) ^ 2)
    simpa only [mul_one] using hsq.trans hwz
  have hq1_mod : ((q + 1 : ℕ) : ℤ) ≡ 2 * (d : ℤ) * (k * pellFermatQuotient d) ^ 2 [ZMOD (d : ℤ) ^ 2] := by
    have hq1_z : ((q + 1 : ℕ) : ℤ) = 2 * (d : ℤ) * (w : ℤ) ^ 2 := by exact_mod_cast hq1
    rw [hq1_z]
    obtain ⟨c, hc⟩ := Int.modEq_iff_dvd.mp hkq_sq.symm
    refine Int.modEq_iff_dvd.mpr ⟨2 * c, ?_⟩
    calc
      2 * (d : ℤ) * (k * pellFermatQuotient d) ^ 2 - 2 * (d : ℤ) * (w : ℤ) ^ 2
          = 2 * (d : ℤ) * ((k * pellFermatQuotient d) ^ 2 - (w : ℤ) ^ 2) := by ring
      _ = 2 * (d : ℤ) * ((d : ℤ) * c) := by rw [hc]
      _ = (d : ℤ) ^ 2 * (2 * c) := by ring
  refine ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, hnorm, hk_cong, hq1_mod, ?_⟩
  intro hd_mem
  have hndvd_Q : ¬ (d : ℤ) ∣ pellFermatQuotient d :=
    pellFermatQuotient_not_dvd_finset hd hd8 hd_mem
  have hndvd_y : ¬ d ^ 2 ∣ y := hk_ndvd hk1 h2k hndvd_Q
  have hndvd_q1 : ¬ d ^ 2 ∣ q + 1 := by
    intro hd2_q1
    have hd2_z : (d : ℤ) ^ 2 ∣ ((q + 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hd2_q1
    have h0 : ((q + 1 : ℕ) : ℤ) ≡ 0 [ZMOD (d : ℤ) ^ 2] := Int.modEq_zero_iff_dvd.mpr hd2_z
    have hd2_rhs : (d : ℤ) ^ 2 ∣ 2 * (d : ℤ) * (k * pellFermatQuotient d) ^ 2 :=
      Int.modEq_zero_iff_dvd.mp (hq1_mod.symm.trans h0)
    obtain ⟨c, hc⟩ := hd2_rhs
    have hd_ne : (d : ℤ) ≠ 0 := by positivity
    have hd_dvd_2sq : (d : ℤ) ∣ 2 * (k * pellFermatQuotient d) ^ 2 := by
      refine ⟨c, ?_⟩
      apply mul_left_cancel₀ hd_ne
      calc
        (d : ℤ) * (2 * (k * pellFermatQuotient d) ^ 2)
            = 2 * (d : ℤ) * (k * pellFermatQuotient d) ^ 2 := by ring
        _ = (d : ℤ) ^ 2 * c := hc
        _ = (d : ℤ) * ((d : ℤ) * c) := by ring
    have hd_int_prime : Prime (d : ℤ) :=
      Int.prime_iff_natAbs_prime.mpr (by simpa using hd)
    have hndvd_2 : ¬ (d : ℤ) ∣ (2 : ℤ) := by
      intro h2
      have h2nat : d ∣ 2 := Int.natCast_dvd_natCast.mp h2
      have := Nat.le_of_dvd (by decide) h2nat
      have := hd.two_le
      omega
    have hd_dvd_sq : (d : ℤ) ∣ (k * pellFermatQuotient d) ^ 2 :=
      (hd_int_prime.dvd_or_dvd hd_dvd_2sq).resolve_left hndvd_2
    have hd_dvd_prod : (d : ℤ) ∣ k * pellFermatQuotient d :=
      hd_int_prime.dvd_of_dvd_pow hd_dvd_sq
    have hd_dvd_k : (d : ℤ) ∣ k :=
      (hd_int_prime.dvd_or_dvd hd_dvd_prod).resolve_right hndvd_Q
    have hd_dvd_abs : (d : ℤ) ∣ |k| := by
      rcases abs_choice k with h | h <;> rw [h]
      · exact hd_dvd_k
      · exact hd_dvd_k.neg_right
    have hd_le_abs : (d : ℤ) ≤ |k| := Int.le_of_dvd (by omega) hd_dvd_abs
    omega
  exact ⟨hndvd_y, hndvd_q1⟩

end OddPerfect
