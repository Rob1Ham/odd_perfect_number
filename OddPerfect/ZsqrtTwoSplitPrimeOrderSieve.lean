module

public import OddPerfect.ZsqrtTwoPellFermatQuotient
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# All-`k` Split-Prime `d`-th Power Residue Sieve in `ℤ√2` (`OddPerfect.ZsqrtTwoSplitPrimeOrderSieve`)

Formalizes the split-prime (`r % 8 = 1 ∨ r % 8 = 7`, `d ∣ r - 1`) `d`-th power residue sieve
in `ℤ√2` on `q ^ d + 1 = 2 * y ^ 2` and on exceptional Euler indices
`sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`):

1. `zsqrtTwo_pow_modEq_self_of_prime_mod_eight_one_or_seven`: for any prime `r ≡ 1, 7 [MOD 8]`
   and `α : ℤ√2`, `α ^ r ≡ α [ZMOD r]` coordinatewise.
2. `zsqrtTwo_pow_pred_modEq_one_of_split_prime`: if moreover `¬ (r : ℤ) ∣ α.norm`, then
   `α ^ (r - 1) ≡ 1 [ZMOD r]` coordinatewise.
3. `silverUnit_zpow_not_modEq_one_of_order_d`: if `d ∣ r - 1` (`d.Prime`, `Odd d`) and
   `silverUnit ^ ((r - 1) / d) ≢ 1 [ZMOD r]`, then `silverUnit ^ (k * ((r - 1) / d)) ≢ 1 [ZMOD r]`
   for all `1 ≤ |k| < d`.
4. `zsqrtTwo_fermat_split_prime_order_obstruction`: rules out `r ∣ y` for every such split prime.
5. `exceptional_euler_split_prime_y_sieve`: specializes to exceptional Euler-index witnesses,
   including concrete 8-prime sieves for `d = 17`, `d = 73`, and `d = 241`.
-/

public section

namespace OddPerfect

open ArithmeticFunction

private def zsqrtTwoReHom : ℤ√2 →+ ℤ where
  toFun := Zsqrtd.re
  map_zero' := rfl
  map_add' := fun _ _ => rfl

private def zsqrtTwoImHom : ℤ√2 →+ ℤ where
  toFun := Zsqrtd.im
  map_zero' := rfl
  map_add' := fun _ _ => rfl

private lemma sqrtd_two_even (j : ℕ) :
    (Zsqrtd.sqrtd : ℤ√2) ^ (2 * j) = ((2 ^ j : ℤ) : ℤ√2) := by
  rw [pow_mul, pow_two, Zsqrtd.dmuld, Int.cast_pow]

private lemma sqrtd_two_odd (j : ℕ) :
    (Zsqrtd.sqrtd : ℤ√2) ^ (2 * j + 1) = ⟨0, (2 : ℤ) ^ j⟩ := by
  rw [pow_succ, sqrtd_two_even, show (Zsqrtd.sqrtd : ℤ√2) = ⟨0, 1⟩ from rfl, Zsqrtd.smul_val]
  simp

/-- For any prime `r ≡ 1, 7 [MOD 8]` and `α : ℤ√2`, `α ^ r ≡ α [ZMOD r]` coordinatewise. -/
theorem zsqrtTwo_pow_modEq_self_of_prime_mod_eight_one_or_seven {r : ℕ}
    (hr_prime : r.Prime) (hr8 : r % 8 = 1 ∨ r % 8 = 7) (α : ℤ√2) :
    (α ^ r).re ≡ α.re [ZMOD (r : ℤ)] ∧ (α ^ r).im ≡ α.im [ZMOD (r : ℤ)] := by
  have : Fact r.Prime := ⟨hr_prime⟩
  have hr_odd : Odd r := Nat.odd_iff.mpr (by omega)
  rcases α with ⟨a, b⟩
  have hsplit : (⟨a, b⟩ : ℤ√2) = (b : ℤ√2) * Zsqrtd.sqrtd + (a : ℤ√2) := by
    ext <;> simp
  let term (i : ℕ) : ℤ√2 :=
    ((b : ℤ√2) * Zsqrtd.sqrtd) ^ i * (a : ℤ√2) ^ (r - i) * (r.choose i : ℤ√2)
  have hexp : (⟨a, b⟩ : ℤ√2) ^ r = ∑ i ∈ Finset.range (r + 1), term i := by
    rw [hsplit, add_pow]
  have hre_term : ∀ i ∈ Finset.range (r + 1),
      (term i).re ≡ (if i = 0 then a ^ r else 0) [ZMOD (r : ℤ)] := by
    intro i hi
    have hir_le : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases hi0 : i = 0
    · rw [hi0]
      simp only [↓reduceIte, term, pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right,
        Nat.cast_one, mul_one, ← Int.cast_pow, Zsqrtd.re_intCast]
      rfl
    · by_cases hir : i = r
      · obtain ⟨j, hj⟩ := hr_odd
        have ht : term r = ⟨0, b ^ (2 * j + 1) * 2 ^ j⟩ := by
          dsimp [term]
          rw [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, mul_one,
            hj, mul_pow, ← Int.cast_pow, sqrtd_two_odd, Zsqrtd.smul_val]
          simp
        rw [hir, ht]
        simp [hr_prime.ne_zero]
      · have hir_lt : i < r := lt_of_le_of_ne hir_le hir
        have hdvd_nat : r ∣ r.choose i := Nat.Prime.dvd_choose_self hr_prime hi0 hir_lt
        have hdvd_int : (r : ℤ) ∣ (r.choose i : ℤ) := Int.natCast_dvd_natCast.mpr hdvd_nat
        have hdvd_zsqrt : ((r : ℤ) : ℤ√2) ∣ term i := by
          dsimp [term]
          refine dvd_mul_of_dvd_right ?_ _
          rw [← Int.cast_natCast (r.choose i)]
          exact (Zsqrtd.intCast_dvd_intCast (r : ℤ) (r.choose i : ℤ)).mpr hdvd_int
        have hdvd_re : (r : ℤ) ∣ (term i).re := (Zsqrtd.intCast_dvd (r : ℤ) (term i)).mp hdvd_zsqrt |>.1
        simp only [hi0, ↓reduceIte]
        exact Int.modEq_zero_iff_dvd.mpr hdvd_re
  have him_term : ∀ i ∈ Finset.range (r + 1),
      (term i).im ≡ (if i = r then b ^ r * 2 ^ ((r - 1) / 2) else 0) [ZMOD (r : ℤ)] := by
    intro i hi
    have hir_le : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases hir : i = r
    · obtain ⟨j, hj⟩ := hr_odd
      have hj_eq : j = (r - 1) / 2 := by omega
      have ht : term r = ⟨0, b ^ r * 2 ^ ((r - 1) / 2)⟩ := by
        dsimp [term]
        rw [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, mul_one,
          mul_pow, ← Int.cast_pow]
        conv_lhs => rhs; rw [hj, sqrtd_two_odd, hj_eq]
        rw [Zsqrtd.smul_val]
        simp
      rw [hir, ht]
      simp
    · by_cases hi0 : i = 0
      · have hr_ne0 : 0 ≠ r := hr_prime.ne_zero.symm
        simp only [hr_ne0, ↓reduceIte, term, hi0, pow_zero, one_mul, Nat.sub_zero,
          Nat.choose_zero_right, Nat.cast_one, mul_one, ← Int.cast_pow, Zsqrtd.im_intCast]
        rfl
      · have hir_lt : i < r := lt_of_le_of_ne hir_le hir
        have hdvd_nat : r ∣ r.choose i := Nat.Prime.dvd_choose_self hr_prime hi0 hir_lt
        have hdvd_int : (r : ℤ) ∣ (r.choose i : ℤ) := Int.natCast_dvd_natCast.mpr hdvd_nat
        have hdvd_zsqrt : ((r : ℤ) : ℤ√2) ∣ term i := by
          dsimp [term]
          refine dvd_mul_of_dvd_right ?_ _
          rw [← Int.cast_natCast (r.choose i)]
          exact (Zsqrtd.intCast_dvd_intCast (r : ℤ) (r.choose i : ℤ)).mpr hdvd_int
        have hdvd_im : (r : ℤ) ∣ (term i).im := (Zsqrtd.intCast_dvd (r : ℤ) (term i)).mp hdvd_zsqrt |>.2
        simp only [hir, ↓reduceIte]
        exact Int.modEq_zero_iff_dvd.mpr hdvd_im
  have ha_fermat : a ^ r ≡ a [ZMOD (r : ℤ)] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    exact ZMod.pow_card (a : ZMod r)
  have hb_fermat : b ^ r ≡ b [ZMOD (r : ℤ)] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    exact ZMod.pow_card (b : ZMod r)
  have h2_euler : (2 : ℤ) ^ ((r - 1) / 2) ≡ 1 [ZMOD (r : ℤ)] := by
    have hr_two : 2 ≤ r := hr_prime.two_le
    have hr_ne2 : r ≠ 2 := by rcases hr8 with h | h <;> omega
    have hsq : IsSquare (2 : ZMod r) := (ZMod.exists_sq_eq_two_iff hr_ne2).mpr hr8
    have h2_ne : (2 : ZMod r) ≠ 0 := by
      intro h0
      have hdvd : r ∣ 2 := (ZMod.natCast_eq_zero_iff 2 r).mp h0
      have := Nat.le_of_dvd (by decide) hdvd
      omega
    have heul : (2 : ZMod r) ^ (r / 2) = 1 := (ZMod.euler_criterion r h2_ne).mp hsq
    have hdiv : r / 2 = (r - 1) / 2 := by omega
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    rw [← hdiv]
    exact heul
  have hre_sum : (⟨a, b⟩ ^ r : ℤ√2).re ≡ a ^ r [ZMOD (r : ℤ)] := by
    change zsqrtTwoReHom (⟨a, b⟩ ^ r) ≡ _ [ZMOD (r : ℤ)]
    rw [hexp, map_sum]
    have hcongr : ∑ x ∈ Finset.range (r + 1), zsqrtTwoReHom (term x) =
        ∑ x ∈ Finset.range (r + 1), (term x).re := rfl
    rw [hcongr]
    have hs := Int.ModEq.sum (s := Finset.range (r + 1)) hre_term
    have h0_mem : 0 ∈ Finset.range (r + 1) := Finset.mem_range.mpr (by omega)
    simpa [h0_mem] using hs
  have him_sum : (⟨a, b⟩ ^ r : ℤ√2).im ≡ b ^ r * 2 ^ ((r - 1) / 2) [ZMOD (r : ℤ)] := by
    change zsqrtTwoImHom (⟨a, b⟩ ^ r) ≡ _ [ZMOD (r : ℤ)]
    rw [hexp, map_sum]
    have hcongr : ∑ x ∈ Finset.range (r + 1), zsqrtTwoImHom (term x) =
        ∑ x ∈ Finset.range (r + 1), (term x).im := rfl
    rw [hcongr]
    have hs := Int.ModEq.sum (s := Finset.range (r + 1)) him_term
    have hr_mem : r ∈ Finset.range (r + 1) := Finset.mem_range.mpr (by omega)
    simpa [hr_mem] using hs
  refine ⟨hre_sum.trans ha_fermat, him_sum.trans ?_⟩
  simpa using hb_fermat.mul h2_euler

/-- For any prime `r ≡ 1, 7 [MOD 8]` and `α : ℤ√2` with `¬ (r : ℤ) ∣ α.norm`,
`α ^ (r - 1) ≡ 1 [ZMOD r]` coordinatewise. -/
theorem zsqrtTwo_pow_pred_modEq_one_of_split_prime {r : ℕ}
    (hr_prime : r.Prime) (hr8 : r % 8 = 1 ∨ r % 8 = 7) {α : ℤ√2}
    (hcop : ¬ (r : ℤ) ∣ α.norm) :
    (α ^ (r - 1)).re ≡ 1 [ZMOD (r : ℤ)] ∧ (α ^ (r - 1)).im ≡ 0 [ZMOD (r : ℤ)] := by
  have hr_pos : 0 < r := hr_prime.pos
  obtain ⟨hfrob_re, hfrob_im⟩ :=
    zsqrtTwo_pow_modEq_self_of_prime_mod_eight_one_or_seven hr_prime hr8 α
  have hr_re : (r : ℤ) ∣ (α ^ r - α).re := by
    simpa [Zsqrtd.re_sub] using Int.modEq_iff_dvd.mp hfrob_re.symm
  have hr_im : (r : ℤ) ∣ (α ^ r - α).im := by
    simpa [Zsqrtd.im_sub] using Int.modEq_iff_dvd.mp hfrob_im.symm
  obtain ⟨x, hx⟩ := hr_re
  obtain ⟨y, hy⟩ := hr_im
  let β : ℤ√2 := ⟨x, y⟩
  have hdiff : α ^ r - α = (r : ℤ√2) * β := by
    ext
    · simpa [β] using hx
    · simpa [β] using hy
  have hmul_conj : (α ^ (r - 1) - 1) * (α.norm : ℤ√2) = (r : ℤ√2) * (β * star α) := by
    calc
      (α ^ (r - 1) - 1) * (α.norm : ℤ√2)
          = (α ^ (r - 1) - 1) * (α * star α) := by rw [Zsqrtd.norm_eq_mul_conj]
      _ = ((α ^ (r - 1) - 1) * α) * star α := by ring
      _ = (α ^ (r - 1 + 1) - α) * star α := by rw [sub_mul, one_mul, pow_succ]
      _ = (α ^ r - α) * star α := by rw [Nat.sub_add_cancel hr_pos]
      _ = ((r : ℤ√2) * β) * star α := by rw [hdiff]
      _ = (r : ℤ√2) * (β * star α) := by ring
  have hre_div : (r : ℤ) ∣ (α ^ (r - 1) - 1).re * α.norm := by
    have hre := congrArg Zsqrtd.re hmul_conj
    simp only [Zsqrtd.re_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast, mul_zero, add_zero,
      Zsqrtd.re_natCast, Zsqrtd.im_natCast, zero_mul] at hre
    exact ⟨(β * star α).re, hre⟩
  have him_div : (r : ℤ) ∣ (α ^ (r - 1) - 1).im * α.norm := by
    have him := congrArg Zsqrtd.im hmul_conj
    simp only [Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast, mul_zero, zero_add,
      Zsqrtd.re_natCast, Zsqrtd.im_natCast, zero_mul, add_zero] at him
    exact ⟨(β * star α).im, him⟩
  have hr_int_prime : Prime (r : ℤ) :=
    Int.prime_iff_natAbs_prime.mpr (by simpa using hr_prime)
  have hr_re1 : (r : ℤ) ∣ (α ^ (r - 1) - 1).re :=
    (hr_int_prime.dvd_or_dvd hre_div).resolve_right hcop
  have hr_im1 : (r : ℤ) ∣ (α ^ (r - 1) - 1).im :=
    (hr_int_prime.dvd_or_dvd him_div).resolve_right hcop
  constructor
  · rw [Zsqrtd.re_sub, Zsqrtd.re_one] at hr_re1
    exact (Int.modEq_iff_dvd.mpr hr_re1).symm
  · rw [Zsqrtd.im_sub, Zsqrtd.im_one, sub_zero] at hr_im1
    exact Int.modEq_zero_iff_dvd.mpr hr_im1

private lemma silverUnit_pow_norm' (n : ℕ) :
    ((silverUnit ^ n : (ℤ√2)ˣ) : ℤ√2).norm = (-1 : ℤ) ^ n := by
  have hsu : (silverUnit : ℤ√2).norm = -1 := by
    simp [silverUnit_val, Zsqrtd.norm_def]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Units.val_mul, Zsqrtd.norm_mul, ih, hsu, pow_succ]

private lemma zsqrtTwo_unit_inv_eq_star' {u : (ℤ√2)ˣ} (hu : (u : ℤ√2).norm = 1) :
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

private lemma zsqrtTwo_modEq_one_mul {m : ℤ} {x y : ℤ√2}
    (hx : m ∣ x.re - 1 ∧ m ∣ x.im) (hy : m ∣ y.re - 1 ∧ m ∣ y.im) :
    m ∣ (x * y).re - 1 ∧ m ∣ (x * y).im := by
  obtain ⟨a, ha⟩ := hx.1
  obtain ⟨b, hb⟩ := hx.2
  obtain ⟨c, hc⟩ := hy.1
  obtain ⟨f, hf⟩ := hy.2
  have hxre : x.re = 1 + m * a := by linarith
  have hyre : y.re = 1 + m * c := by linarith
  constructor
  · refine ⟨a + c + m * a * c + 2 * m * b * f, ?_⟩
    rw [Zsqrtd.re_mul, hxre, hb, hyre, hf]
    ring
  · refine ⟨f + m * a * f + b + m * b * c, ?_⟩
    rw [Zsqrtd.im_mul, hxre, hb, hyre, hf]
    ring

private lemma zsqrtTwo_modEq_one_pow {m : ℤ} {x : ℤ√2}
    (hx : m ∣ x.re - 1 ∧ m ∣ x.im) (n : ℕ) :
    m ∣ (x ^ n).re - 1 ∧ m ∣ (x ^ n).im := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    exact zsqrtTwo_modEq_one_mul ih hx

private lemma zsqrtTwo_unit_pow_norm_one {u : (ℤ√2)ˣ} (hu : (u : ℤ√2).norm = 1) (n : ℕ) :
    ((u ^ n : (ℤ√2)ˣ) : ℤ√2).norm = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Units.val_mul, Zsqrtd.norm_mul, ih, hu, mul_one]

private lemma zsqrtTwo_unit_zpow_norm_one {u : (ℤ√2)ˣ} (hu : (u : ℤ√2).norm = 1) (z : ℤ) :
    ((u ^ z : (ℤ√2)ˣ) : ℤ√2).norm = 1 := by
  cases z with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact zsqrtTwo_unit_pow_norm_one hu n
  | negSucc m =>
    set n : ℕ := m + 1
    have hz_eq : Int.negSucc m = -(n : ℤ) := rfl
    rw [hz_eq, zpow_neg, zpow_natCast,
      zsqrtTwo_unit_inv_eq_star' (zsqrtTwo_unit_pow_norm_one hu n), Zsqrtd.norm_conj]
    exact zsqrtTwo_unit_pow_norm_one hu n

private lemma zsqrtTwo_unit_modEq_one_zpow {m : ℤ} {u : (ℤ√2)ˣ}
    (hunorm : (u : ℤ√2).norm = 1)
    (hu : m ∣ (u : ℤ√2).re - 1 ∧ m ∣ (u : ℤ√2).im) (z : ℤ) :
    m ∣ ((u ^ z : (ℤ√2)ˣ) : ℤ√2).re - 1 ∧ m ∣ ((u ^ z : (ℤ√2)ˣ) : ℤ√2).im := by
  have hnat_mod : ∀ n : ℕ,
      m ∣ ((u ^ n : (ℤ√2)ˣ) : ℤ√2).re - 1 ∧ m ∣ ((u ^ n : (ℤ√2)ˣ) : ℤ√2).im := by
    intro n
    rw [Units.val_pow_eq_pow_val]
    exact zsqrtTwo_modEq_one_pow hu n
  cases z with
  | ofNat n =>
    simpa [Int.ofNat_eq_natCast] using hnat_mod n
  | negSucc k =>
    set n : ℕ := k + 1
    have hz_eq : Int.negSucc k = -(n : ℤ) := rfl
    rw [hz_eq, zpow_neg, zpow_natCast,
      zsqrtTwo_unit_inv_eq_star' (zsqrtTwo_unit_pow_norm_one hunorm n)]
    obtain ⟨hre, him⟩ := hnat_mod n
    exact ⟨hre, dvd_neg.mpr him⟩

/-- If `d ∣ r - 1` (`d.Prime`, `Odd d`) and `silverUnit ^ ((r - 1) / d) ≢ 1 [ZMOD r]`,
then `silverUnit ^ (k * ((r - 1) / d)) ≢ 1 [ZMOD r]` for every `1 ≤ |k| < d`. -/
theorem silverUnit_zpow_not_modEq_one_of_order_d {r d : ℕ}
    (hr_prime : r.Prime) (hr8 : r % 8 = 1 ∨ r % 8 = 7)
    (hd_prime : d.Prime) (hd_odd : Odd d) (hdr : d ∣ r - 1)
    (hne1 : ¬ ((r : ℤ) ∣ (((silverUnit ^ ((r - 1) / d) : (ℤ√2)ˣ) : ℤ√2).re - 1) ∧
               (r : ℤ) ∣ (((silverUnit ^ ((r - 1) / d) : (ℤ√2)ˣ) : ℤ√2).im)))
    {k : ℤ} (hk1 : 1 ≤ |k|) (hk_lt : |k| < (d : ℤ)) :
    ¬ ((r : ℤ) ∣ (((silverUnit ^ (k * (((r - 1) / d : ℕ) : ℤ)) : (ℤ√2)ˣ) : ℤ√2).re - 1) ∧
       (r : ℤ) ∣ (((silverUnit ^ (k * (((r - 1) / d : ℕ) : ℤ)) : (ℤ√2)ˣ) : ℤ√2).im)) := by
  intro hk_mod
  set e : ℕ := (r - 1) / d
  set ζ : (ℤ√2)ˣ := silverUnit ^ e
  have hde : d * e = r - 1 := Nat.mul_div_cancel' hdr
  have hr_even_pred : Even (r - 1) := by
    have hr_odd : Odd r := Nat.odd_iff.mpr (by omega)
    obtain ⟨m, hm⟩ := hr_odd
    exact ⟨m, by omega⟩
  have he_even : Even e := by
    rw [← hde, Nat.even_mul] at hr_even_pred
    exact hr_even_pred.resolve_left (Nat.not_even_iff_odd.mpr hd_odd)
  have hζ_norm : (ζ : ℤ√2).norm = 1 := by
    change ((silverUnit ^ e : (ℤ√2)ˣ) : ℤ√2).norm = 1
    rw [silverUnit_pow_norm', he_even.neg_one_pow]
  have hζd_eq : (ζ ^ (d : ℤ) : (ℤ√2)ˣ) = silverUnit ^ (r - 1) := by
    dsimp [ζ]
    rw [zpow_natCast, ← pow_mul, mul_comm e d, hde]
  have hsu_cop : ¬ (r : ℤ) ∣ (silverUnit : ℤ√2).norm := by
    have hnorm : (silverUnit : ℤ√2).norm = -1 := by
      simp [silverUnit_val, Zsqrtd.norm_def]
    rw [hnorm]
    intro hdv
    have hr1 : (r : ℤ) ∣ 1 := dvd_neg.mp hdv
    exact hr_prime.not_dvd_one (Int.natCast_dvd_natCast.mp hr1)
  have hζd_mod : (r : ℤ) ∣ ((ζ ^ (d : ℤ) : (ℤ√2)ˣ) : ℤ√2).re - 1 ∧
      (r : ℤ) ∣ ((ζ ^ (d : ℤ) : (ℤ√2)ˣ) : ℤ√2).im := by
    rw [hζd_eq, Units.val_pow_eq_pow_val]
    obtain ⟨hre, him⟩ := zsqrtTwo_pow_pred_modEq_one_of_split_prime hr_prime hr8 hsu_cop
    exact ⟨Int.modEq_iff_dvd.mp hre.symm, Int.modEq_zero_iff_dvd.mp him⟩
  have hζk_eq : (silverUnit ^ (k * (e : ℤ)) : (ℤ√2)ˣ) = ζ ^ k := by
    dsimp [ζ]
    rw [mul_comm k (e : ℤ), zpow_mul, zpow_natCast]
  have hζk_mod : (r : ℤ) ∣ ((ζ ^ k : (ℤ√2)ˣ) : ℤ√2).re - 1 ∧
      (r : ℤ) ∣ ((ζ ^ k : (ℤ√2)ˣ) : ℤ√2).im := by
    simpa [hζk_eq] using hk_mod
  have hndvd_abs : ¬ d ∣ k.natAbs := by
    intro hdvd
    have hpos : 0 < k.natAbs := Int.natAbs_pos.mpr (abs_pos.mp (by omega))
    have hle : d ≤ k.natAbs := Nat.le_of_dvd hpos hdvd
    have hcast : (k.natAbs : ℤ) = |k| := Int.natCast_natAbs k
    omega
  have hcop_nat : Nat.Coprime k.natAbs d :=
    (hd_prime.coprime_iff_not_dvd.mpr hndvd_abs).symm
  have hcop_int : IsCoprime k (d : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd] using hcop_nat
  obtain ⟨a, b, hab⟩ := hcop_int
  have hζ_factor : ζ = (ζ ^ k) ^ a * (ζ ^ (d : ℤ)) ^ b := by
    calc
      ζ = ζ ^ (1 : ℤ) := (zpow_one ζ).symm
      _ = ζ ^ (a * k + b * (d : ℤ)) := by rw [hab]
      _ = ζ ^ (a * k) * ζ ^ (b * (d : ℤ)) := zpow_add ζ (a * k) (b * (d : ℤ))
      _ = (ζ ^ k) ^ a * (ζ ^ (d : ℤ)) ^ b := by
        rw [mul_comm a k, zpow_mul, mul_comm b (d : ℤ), zpow_mul]
  have hζk_norm : ((ζ ^ k : (ℤ√2)ˣ) : ℤ√2).norm = 1 :=
    zsqrtTwo_unit_zpow_norm_one hζ_norm k
  have hζd_norm : ((ζ ^ (d : ℤ) : (ℤ√2)ˣ) : ℤ√2).norm = 1 :=
    zsqrtTwo_unit_zpow_norm_one hζ_norm (d : ℤ)
  have hζka_mod := zsqrtTwo_unit_modEq_one_zpow hζk_norm hζk_mod a
  have hζdb_mod := zsqrtTwo_unit_modEq_one_zpow hζd_norm hζd_mod b
  have hζ_mod : (r : ℤ) ∣ (ζ : ℤ√2).re - 1 ∧ (r : ℤ) ∣ (ζ : ℤ√2).im := by
    rw [hζ_factor, Units.val_mul]
    exact zsqrtTwo_modEq_one_mul hζka_mod hζdb_mod
  exact hne1 hζ_mod

/-- Split-prime order obstruction on `q ^ d + 1 = 2 * y ^ 2`: if `r ≡ 1, 7 [MOD 8]` is prime,
`d ∣ r - 1`, and `silverUnit ^ ((r - 1) / d) ≢ 1 [ZMOD r]`, then `¬ r ∣ y`. -/
theorem zsqrtTwo_fermat_split_prime_order_obstruction {q d y r : ℕ}
    (hq : q.Prime) (hd : d.Prime) (hd8 : d % 8 = 1)
    (hpow : q ^ d + 1 = 2 * y ^ 2) {k : ℤ} {α : ℤ√2}
    (hk1 : 1 ≤ |k|) (h2k : 2 * |k| ≤ (d : ℤ) - 1)
    (hz : (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d)
    (hnorm : α.norm = (if Even k then -(q : ℤ) else (q : ℤ)))
    (hr_prime : r.Prime) (hr8 : r % 8 = 1 ∨ r % 8 = 7) (hdr : d ∣ r - 1)
    (hne1 : ¬ ((r : ℤ) ∣ (((silverUnit ^ ((r - 1) / d) : (ℤ√2)ˣ) : ℤ√2).re - 1) ∧
               (r : ℤ) ∣ (((silverUnit ^ ((r - 1) / d) : (ℤ√2)ˣ) : ℤ√2).im))) :
    ¬ r ∣ y := by
  intro hry
  have _ : 0 < q := hq.pos
  have hnrq : ¬ r ∣ q := by
    intro hrq
    have h1 : r ∣ q ^ d := dvd_pow hrq hd.pos.ne'
    have h2 : r ∣ 2 * y ^ 2 :=
      dvd_mul_of_dvd_right (hry.trans (dvd_pow_self y (by decide : 2 ≠ 0))) 2
    have h3 : r ∣ q ^ d + 1 := hpow ▸ h2
    exact hr_prime.not_dvd_one ((Nat.dvd_add_right h1).mp h3)
  have hcop : ¬ (r : ℤ) ∣ α.norm := by
    intro hdv
    have hrq_z : (r : ℤ) ∣ (q : ℤ) := by
      rw [hnorm] at hdv
      split_ifs at hdv
      · exact dvd_neg.mp hdv
      · exact hdv
    exact hnrq (Int.natCast_dvd_natCast.mp hrq_z)
  set e : ℕ := (r - 1) / d
  have hde : d * e = r - 1 := Nat.mul_div_cancel' hdr
  have hlhs_base : (r : ℤ) ∣ (⟨1, (y : ℤ)⟩ : ℤ√2).re - 1 ∧
      (r : ℤ) ∣ (⟨1, (y : ℤ)⟩ : ℤ√2).im := by
    simp [Int.natCast_dvd_natCast.mpr hry]
  have hlhs_pow := zsqrtTwo_modEq_one_pow hlhs_base e
  have hrhs_eq : (⟨1, (y : ℤ)⟩ : ℤ√2) ^ e =
      ((silverUnit ^ (k * (e : ℤ)) : (ℤ√2)ˣ) : ℤ√2) * α ^ (r - 1) := by
    rw [hz, mul_pow, ← pow_mul, hde, ← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul]
  rw [hrhs_eq] at hlhs_pow
  set U : ℤ√2 := ((silverUnit ^ (k * (e : ℤ)) : (ℤ√2)ˣ) : ℤ√2)
  set V : ℤ√2 := α ^ (r - 1)
  obtain ⟨hVre_mod, hVim_mod⟩ := zsqrtTwo_pow_pred_modEq_one_of_split_prime hr_prime hr8 hcop
  obtain ⟨c, hc⟩ := Int.modEq_iff_dvd.mp hVre_mod.symm
  obtain ⟨f, hf⟩ := Int.modEq_zero_iff_dvd.mp hVim_mod
  have hVre : V.re = 1 + (r : ℤ) * c := by linarith
  have hU_re : (r : ℤ) ∣ U.re - 1 := by
    obtain ⟨s, hs⟩ := hlhs_pow.1
    refine ⟨s - (U.re * c + 2 * U.im * f), ?_⟩
    have hmul_re : (U * V).re - 1 = U.re - 1 + (r : ℤ) * (U.re * c + 2 * U.im * f) := by
      rw [Zsqrtd.re_mul, hVre, hf]
      ring
    linarith
  have hU_im : (r : ℤ) ∣ U.im := by
    obtain ⟨s, hs⟩ := hlhs_pow.2
    refine ⟨s - (U.re * f + U.im * c), ?_⟩
    have hmul_im : (U * V).im = U.im + (r : ℤ) * (U.re * f + U.im * c) := by
      rw [Zsqrtd.im_mul, hVre, hf]
      ring
    linarith
  have hd_odd : Odd d := Nat.odd_iff.mpr (by omega)
  have hk_lt : |k| < (d : ℤ) := by omega
  exact silverUnit_zpow_not_modEq_one_of_order_d hr_prime hr8 hd hd_odd hdr hne1 hk1 hk_lt
    ⟨hU_re, hU_im⟩

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

private lemma silverUnit_pow_div_not_modEq_one_of_concrete {r d : ℕ}
    (hlt : (r - 1) / d < 2 ^ 10)
    (hne : (powZsqrtTwoModAux 10 (1, 1) ((r - 1) / d) (r : ℤ)).1 % (r : ℤ) ≠ 1 % (r : ℤ) ∨
           (powZsqrtTwoModAux 10 (1, 1) ((r - 1) / d) (r : ℤ)).2 % (r : ℤ) ≠ 0) :
    ¬ ((r : ℤ) ∣ (((silverUnit ^ ((r - 1) / d) : (ℤ√2)ˣ) : ℤ√2).re - 1) ∧
       (r : ℤ) ∣ (((silverUnit ^ ((r - 1) / d) : (ℤ√2)ˣ) : ℤ√2).im)) := by
  intro ⟨hre, him⟩
  obtain ⟨hspec1, hspec2⟩ :=
    powZsqrtTwoModAux_spec (silverUnit : ℤ√2) 10 ((r - 1) / d) (r : ℤ) hlt
  rw [← Units.val_pow_eq_pow_val, silverUnit_val] at hspec1 hspec2
  have hre_mod : (((silverUnit ^ ((r - 1) / d) : (ℤ√2)ˣ) : ℤ√2).re) % (r : ℤ) = 1 % (r : ℤ) :=
    (Int.modEq_iff_dvd.mpr hre).symm
  have him_mod : (((silverUnit ^ ((r - 1) / d) : (ℤ√2)ˣ) : ℤ√2).im) % (r : ℤ) = 0 :=
    Int.emod_eq_zero_of_dvd him
  rcases hne with hne1 | hne2
  · exact hne1 (hspec1.symm.trans hre_mod)
  · exact hne2 (hspec2.symm.trans him_mod)

/-- Exceptional Euler-index split-prime `d`-th power residue sieve on
`sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`):
rules out `r ∣ y`, `r ∣ w`, and `r ∣ z` for every split prime `r ≡ 1, 7 [MOD 8]` with `d ∣ r - 1`
for which `silverUnit ^ ((r - 1) / d) ≢ 1 [ZMOD r]`, and specializes to 8 concrete primes each for
`d = 17`, `d = 73`, and `d = 241`. -/
theorem exceptional_euler_split_prime_y_sieve
    {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    let d := (a + 1) / 2
    ∃ y w z : ℕ,
      0 < y ∧ 0 < w ∧ 0 < z ∧
      y = d * w * z ∧ q + 1 = 2 * d * w ^ 2 ∧ q ^ d + 1 = 2 * y ^ 2 ∧
      (∀ r : ℕ, r.Prime → (r % 8 = 1 ∨ r % 8 = 7) → d ∣ r - 1 →
        ¬ ((r : ℤ) ∣ (((silverUnit ^ ((r - 1) / d) : (ℤ√2)ˣ) : ℤ√2).re - 1) ∧
           (r : ℤ) ∣ (((silverUnit ^ ((r - 1) / d) : (ℤ√2)ˣ) : ℤ√2).im)) →
        ¬ r ∣ y ∧ ¬ r ∣ w ∧ ¬ r ∣ z) ∧
      (d = 17 → ∀ r ∈ ({103, 137, 409, 647, 919, 953, 1327, 1361} : Finset ℕ),
        ¬ r ∣ y ∧ ¬ r ∣ w ∧ ¬ r ∣ z) ∧
      (d = 73 → ∀ r ∈ ({439, 1607, 1753, 3359, 3943, 4673, 6863, 8761} : Finset ℕ),
        ¬ r ∣ y ∧ ¬ r ∣ w ∧ ¬ r ∣ z) ∧
      (d = 241 → ∀ r ∈ ({1447, 5303, 11087, 16871, 26993, 28439, 28921, 30367} : Finset ℕ),
        ¬ r ∣ y ∧ ¬ r ∣ w ∧ ¬ r ∣ z) := by
  intro d
  obtain ⟨hd, _, hd8, _, _, _, _⟩ :=
    exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
  change d.Prime at hd
  change d % 8 = 1 at hd8
  obtain ⟨y, k, α, hy_pos, _, hpow, hk1, h2k, hz_eq, hnorm, _, _, _⟩ :=
    exceptional_euler_pell_fermat_quotient_profile hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨w, z, _, _, hz_odd, _, hq1, _, hqd1, _, _, _, _⟩ :=
    exceptional_euler_second_block_exact_square hN ho hq hq4 ha4 ha hqm hform hl hi
  have hw_pos : 0 < w := by
    rcases eq_or_ne w 0 with rfl | hw0
    · simp at hq1
    · exact Nat.pos_of_ne_zero hw0
  have hz_pos : 0 < z := by
    rcases eq_or_ne z 0 with rfl | hz0
    · simp at hqd1
    · exact Nat.pos_of_ne_zero hz0
  have hy_dwz : y = d * w * z := by
    have h2 : 2 * y ^ 2 = 2 * (d * w * z) ^ 2 := hpow.symm.trans hqd1
    have hsq : y ^ 2 = (d * w * z) ^ 2 := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h2
    exact (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp hsq
  have hsieve : ∀ r : ℕ, r.Prime → (r % 8 = 1 ∨ r % 8 = 7) → d ∣ r - 1 →
      ¬ ((r : ℤ) ∣ (((silverUnit ^ ((r - 1) / d) : (ℤ√2)ˣ) : ℤ√2).re - 1) ∧
         (r : ℤ) ∣ (((silverUnit ^ ((r - 1) / d) : (ℤ√2)ˣ) : ℤ√2).im)) →
      ¬ r ∣ y ∧ ¬ r ∣ w ∧ ¬ r ∣ z := by
    intro r hr_prime hr8 hdr hne1
    have hny : ¬ r ∣ y :=
      zsqrtTwo_fermat_split_prime_order_obstruction hq hd hd8 hpow hk1 h2k hz_eq hnorm
        hr_prime hr8 hdr hne1
    refine ⟨hny, ?_, ?_⟩
    · intro hrw
      exact hny (hy_dwz ▸ Nat.dvd_trans hrw (dvd_mul_of_dvd_left (dvd_mul_left w d) z))
    · intro hrz
      exact hny (hy_dwz ▸ Nat.dvd_trans hrz (dvd_mul_left z (d * w)))
  refine ⟨y, w, z, hy_pos, hw_pos, hz_pos, hy_dwz, hq1, hpow, hsieve, ?_, ?_, ?_⟩
  · intro hd17 r hr
    rw [hd17] at hsieve
    apply hsieve r
    · fin_cases hr <;> norm_num
    · fin_cases hr <;> decide
    · fin_cases hr <;> decide
    · apply silverUnit_pow_div_not_modEq_one_of_concrete
      · fin_cases hr <;> decide
      · fin_cases hr <;> decide
  · intro hd73 r hr
    rw [hd73] at hsieve
    apply hsieve r
    · fin_cases hr <;> norm_num
    · fin_cases hr <;> decide
    · fin_cases hr <;> decide
    · apply silverUnit_pow_div_not_modEq_one_of_concrete
      · fin_cases hr <;> decide
      · fin_cases hr <;> decide
  · intro hd241 r hr
    rw [hd241] at hsieve
    apply hsieve r
    · fin_cases hr <;> norm_num
    · fin_cases hr <;> decide
    · fin_cases hr <;> decide
    · apply silverUnit_pow_div_not_modEq_one_of_concrete
      · fin_cases hr <;> decide
      · fin_cases hr <;> decide

end OddPerfect
