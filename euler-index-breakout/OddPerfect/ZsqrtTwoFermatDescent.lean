module

public import OddPerfect.ExceptionalFermatReduction
public import OddPerfect.ExceptionalFermatHigherSieve
public import Mathlib.NumberTheory.Zsqrtd.Basic
public import Mathlib.NumberTheory.Pell
import Mathlib.Algebra.Order.Round
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# `ℤ√2` Euclidean Descent & Frobenius Obstruction (`OddPerfect.ZsqrtTwoFermatDescent`)

Develops the algebraic number theory of `ℤ√2` required to analyze the generalized Fermat
equation `q ^ d + 1 = 2 * y ^ 2` arising on the exceptional Euler-index branch
`sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`, `d := (a + 1) / 2`):

1. `instEuclideanDomainZsqrtTwo` and `zsqrtTwo_norm_eq_zero_iff`: constructs a
   `EuclideanDomain (ℤ√2)` instance via rational rounding in `ℚ` and proves `z.norm = 0 ↔ z = 0`.
2. `silverUnit`, `pell_two_fundamental`, and `zsqrtTwo_unit_eq_silverUnit_zpow`: proves that
   `3 + 2√2` is the fundamental Pell solution for `d = 2`, hence every unit of `ℤ√2` is
   `± silverUnit ^ n` (`silverUnit = 1 + √2`).
3. `zsqrtTwo_fermat_reduced_power_descent`: for odd `q, d` with `q ^ d + 1 = 2 * y ^ 2`,
   descends `1 + y√2 = silverUnit ^ k * α ^ d` with reduced exponent `2 * |k| ≤ d - 1` and
   `α.norm = ±q`.
4. `one_add_mul_sqrtd_ne_pow`: unconditionally eliminates the pure `d`-th power case `k = 0`
   for odd `d ≥ 3` and `y ≠ 0`.
5. `zsqrtTwo_pow_modEq_self_of_prime_mod_eight_eq_one` and
   `exceptional_euler_zsqrtTwo_frobenius_descent`: proves the mod-`d` Frobenius identity
   `α ^ d ≡ α [ZMOD d]` for primes `d ≡ 1 [MOD 8]` and combines it with `d ∣ y` to obtain
   `1 ≤ |k|` and `α ≡ silverUnit ^ (-k) [ZMOD d]`.
-/

public section

namespace OddPerfect

open ArithmeticFunction

/-! ## 1. `EuclideanDomain (ℤ√2)` -/

private theorem two_ne_mul_self (n : ℤ) : (2 : ℤ) ≠ n * n := by
  intro hn
  have hmod : (2 : ℤ) % 4 = (n * n) % 4 := congrArg (· % 4) hn
  rw [Int.mul_emod] at hmod
  have hcases : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hcases with h | h | h | h <;> rw [h] at hmod <;> omega

/-- An element of `ℤ√2` has norm zero if and only if it is zero. -/
theorem zsqrtTwo_norm_eq_zero_iff {z : ℤ√2} : z.norm = 0 ↔ z = 0 :=
  Zsqrtd.norm_eq_zero two_ne_mul_self z

def zsqrtTwoDiv (x y : ℤ√2) : ℤ√2 :=
  ⟨round (((x * star y).re : ℚ) / y.norm), round (((x * star y).im : ℚ) / y.norm)⟩

def zsqrtTwoMod (x y : ℤ√2) : ℤ√2 :=
  x - y * zsqrtTwoDiv x y

lemma zsqrtTwoDiv_zero (x : ℤ√2) : zsqrtTwoDiv x 0 = 0 := by
  simp [zsqrtTwoDiv]
  rfl

lemma zsqrtTwoMod_norm_lt (x : ℤ√2) {y : ℤ√2} (hy : y ≠ 0) :
    (zsqrtTwoMod x y).norm.natAbs < y.norm.natAbs := by
  have hyn0 : y.norm ≠ 0 := mt zsqrtTwo_norm_eq_zero_iff.mp hy
  have hynq : (y.norm : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hyn0
  set z : ℤ√2 := x * star y
  set q : ℤ√2 := zsqrtTwoDiv x y
  have hmul : zsqrtTwoMod x y * star y = z - (y.norm : ℤ√2) * q := by
    rw [zsqrtTwoMod, sub_mul, mul_assoc, mul_comm q, ← mul_assoc, ← Zsqrtd.norm_eq_mul_conj]
  have hnorm_eq : (zsqrtTwoMod x y).norm * y.norm =
      (z.re - y.norm * q.re) ^ 2 - 2 * (z.im - y.norm * q.im) ^ 2 := by
    calc
      (zsqrtTwoMod x y).norm * y.norm
          = (zsqrtTwoMod x y).norm * (star y).norm := by rw [Zsqrtd.norm_conj]
      _ = (zsqrtTwoMod x y * star y).norm := (Zsqrtd.norm_mul _ _).symm
      _ = (z - (y.norm : ℤ√2) * q).norm := by rw [hmul]
      _ = (z.re - y.norm * q.re) ^ 2 - 2 * (z.im - y.norm * q.im) ^ 2 := by
        simp [Zsqrtd.norm_def]
        ring
  set α : ℚ := (z.re : ℚ) / y.norm - q.re
  set β : ℚ := (z.im : ℚ) / y.norm - q.im
  have hα : |α| ≤ 1 / 2 := by
    simpa [α, q, zsqrtTwoDiv, z] using abs_sub_round (((x * star y).re : ℚ) / y.norm)
  have hβ : |β| ≤ 1 / 2 := by
    simpa [β, q, zsqrtTwoDiv, z] using abs_sub_round (((x * star y).im : ℚ) / y.norm)
  have hα2 : α ^ 2 ≤ 1 / 4 := by
    have h1 := (abs_le.mp hα).1
    have h2 := (abs_le.mp hα).2
    nlinarith
  have hβ2 : β ^ 2 ≤ 1 / 4 := by
    have h1 := (abs_le.mp hβ).1
    have h2 := (abs_le.mp hβ).2
    nlinarith
  have hbound : |α ^ 2 - 2 * β ^ 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [sq_nonneg α, sq_nonneg β]
  have hqnorm : ((zsqrtTwoMod x y).norm : ℚ) * (y.norm : ℚ) =
      (y.norm : ℚ) ^ 2 * (α ^ 2 - 2 * β ^ 2) := by
    have hcast : (((zsqrtTwoMod x y).norm * y.norm : ℤ) : ℚ) =
        (((z.re - y.norm * q.re) ^ 2 - 2 * (z.im - y.norm * q.im) ^ 2 : ℤ) : ℚ) := by
      exact_mod_cast hnorm_eq
    push_cast at hcast
    rw [hcast]
    dsimp [α, β]
    field_simp [hynq]
  have habs_lt : |((zsqrtTwoMod x y).norm : ℚ)| * |(y.norm : ℚ)| <
      |(y.norm : ℚ)| * |(y.norm : ℚ)| := by
    rw [← abs_mul, hqnorm, abs_mul, sq, abs_mul]
    have hpos : 0 < |(y.norm : ℚ)| * |(y.norm : ℚ)| := mul_pos (abs_pos.mpr hynq) (abs_pos.mpr hynq)
    calc
      |(y.norm : ℚ)| * |(y.norm : ℚ)| * |α ^ 2 - 2 * β ^ 2|
          ≤ |(y.norm : ℚ)| * |(y.norm : ℚ)| * (1 / 2) :=
        mul_le_mul_of_nonneg_left hbound hpos.le
      _ < |(y.norm : ℚ)| * |(y.norm : ℚ)| * 1 := by linarith
      _ = |(y.norm : ℚ)| * |(y.norm : ℚ)| := mul_one _
  have hlt_abs : |((zsqrtTwoMod x y).norm : ℚ)| < |(y.norm : ℚ)| :=
    lt_of_mul_lt_mul_right habs_lt (abs_nonneg _)
  rw [← Int.cast_abs, ← Int.cast_abs, Int.cast_lt] at hlt_abs
  rw [← Int.ofNat_lt, Int.natCast_natAbs, Int.natCast_natAbs]
  exact hlt_abs

lemma zsqrtTwo_mul_left_not_lt (a : ℤ√2) {b : ℤ√2} (hb : b ≠ 0) :
    ¬ (a * b).norm.natAbs < a.norm.natAbs := by
  have hb0 : b.norm ≠ 0 := mt zsqrtTwo_norm_eq_zero_iff.mp hb
  have hbpos : 0 < b.norm.natAbs := Int.natAbs_pos.mpr hb0
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]
  exact not_lt_of_ge (Nat.le_mul_of_pos_right _ hbpos)

/-- Explicit `EuclideanDomain` instance on `ℤ√2`. -/
instance instEuclideanDomainZsqrtTwo : EuclideanDomain (ℤ√2) :=
  { (inferInstance : CommRing (ℤ√2)),
    (inferInstance : Nontrivial (ℤ√2)) with
    quotient := zsqrtTwoDiv
    quotient_zero := zsqrtTwoDiv_zero
    remainder := zsqrtTwoMod
    quotient_mul_add_remainder_eq := fun x y => by dsimp [zsqrtTwoMod]; ring
    r := (measure (Int.natAbs ∘ Zsqrtd.norm)).1
    r_wellFounded := (measure (Int.natAbs ∘ Zsqrtd.norm)).wf
    remainder_lt := zsqrtTwoMod_norm_lt
    mul_left_not_lt := zsqrtTwo_mul_left_not_lt }

/-! ## 2. Fundamental Unit & Unit Group of `ℤ√2` -/

/-- The silver ratio unit `1 + √2 ∈ (ℤ√2)ˣ`. -/
@[expose] def silverUnit : (ℤ√2)ˣ :=
  ⟨⟨1, 1⟩, ⟨-1, 1⟩, by ext <;> simp, by ext <;> simp⟩

/-- Underlying value of `silverUnit` in `ℤ√2`. -/
theorem silverUnit_val : (silverUnit : ℤ√2) = ⟨1, 1⟩ := rfl

/-- Underlying value of `silverUnit⁻¹` in `ℤ√2`. -/
theorem silverUnit_inv_val : ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2) = ⟨-1, 1⟩ := rfl

/-- `3 + 2√2` is the fundamental Pell solution for `d = 2`. -/
theorem pell_two_fundamental :
    Pell.IsFundamental (Pell.Solution₁.mk 3 2 (by norm_num) : Pell.Solution₁ 2) := by
  refine ⟨by norm_num, by norm_num, fun {b} hbx => ?_⟩
  have hprop := b.prop
  change b.x ^ 2 - 2 * b.y ^ 2 = 1 at hprop
  change (3 : ℤ) ≤ b.x
  by_contra! hlt
  have hx2 : b.x = 2 := by omega
  rw [hx2] at hprop
  omega

private lemma silverUnit_sq_eq_pell_fund :
    ((silverUnit ^ 2 : (ℤ√2)ˣ) : ℤ√2) =
      ((Pell.Solution₁.mk 3 2 (by norm_num) : Pell.Solution₁ 2) : ℤ√2) := by
  ext <;> simp [silverUnit, pow_two]

private lemma silverUnit_inv_sq_eq_pell_fund_inv :
    ((silverUnit⁻¹ ^ 2 : (ℤ√2)ˣ) : ℤ√2) =
      (((Pell.Solution₁.mk 3 2 (by norm_num) : Pell.Solution₁ 2)⁻¹ : Pell.Solution₁ 2) : ℤ√2) := by
  ext
  · change ((silverUnit⁻¹ ^ 2 : (ℤ√2)ˣ) : ℤ√2).re =
      ((Pell.Solution₁.mk 3 2 (by norm_num) : Pell.Solution₁ 2)⁻¹).x
    rw [Pell.Solution₁.x_inv]
    simp [silverUnit, pow_two]
  · change ((silverUnit⁻¹ ^ 2 : (ℤ√2)ˣ) : ℤ√2).im =
      ((Pell.Solution₁.mk 3 2 (by norm_num) : Pell.Solution₁ 2)⁻¹).y
    rw [Pell.Solution₁.y_inv]
    simp [silverUnit, pow_two]

private lemma pell_fund_pow_coe (n : ℕ) :
    (((Pell.Solution₁.mk 3 2 (by norm_num) : Pell.Solution₁ 2) ^ n : Pell.Solution₁ 2) : ℤ√2) =
      ((silverUnit ^ (2 * (n : ℤ)) : (ℤ√2)ˣ) : ℤ√2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hmul : ∀ a b : Pell.Solution₁ 2, ((a * b : Pell.Solution₁ 2) : ℤ√2) = (a : ℤ√2) * b :=
      fun _ _ => rfl
    rw [pow_succ, hmul, ih, ← silverUnit_sq_eq_pell_fund, ← Units.val_mul]
    congr 1
    rw [← zpow_natCast silverUnit 2, ← zpow_add]
    congr 1

private lemma pell_fund_zpow_coe (n : ℤ) :
    (((Pell.Solution₁.mk 3 2 (by norm_num) : Pell.Solution₁ 2) ^ n : Pell.Solution₁ 2) : ℤ√2) =
      ((silverUnit ^ (2 * n) : (ℤ√2)ˣ) : ℤ√2) := by
  cases n with
  | ofNat m =>
    simpa [Int.ofNat_eq_natCast] using pell_fund_pow_coe m
  | negSucc m =>
    rw [zpow_negSucc]
    have hpow_inv :
        ((((Pell.Solution₁.mk 3 2 (by norm_num) : Pell.Solution₁ 2) ^ (m + 1))⁻¹ :
          Pell.Solution₁ 2) : ℤ√2) =
          (((Pell.Solution₁.mk 3 2 (by norm_num) : Pell.Solution₁ 2)⁻¹ ^ (m + 1) :
            Pell.Solution₁ 2) : ℤ√2) := by
      rw [inv_pow]
    rw [hpow_inv]
    clear hpow_inv
    induction m with
    | zero =>
      simpa using silverUnit_inv_sq_eq_pell_fund_inv.symm
    | succ m ih =>
      have hmul : ∀ a b : Pell.Solution₁ 2, ((a * b : Pell.Solution₁ 2) : ℤ√2) = (a : ℤ√2) * b :=
        fun _ _ => rfl
      rw [pow_succ, hmul, ih, ← silverUnit_inv_sq_eq_pell_fund_inv, ← Units.val_mul]
      congr 1
      rw [← zpow_natCast (silverUnit⁻¹) 2, inv_zpow, ← zpow_neg, ← zpow_add]
      congr 1

private lemma zsqrtTwo_unit_norm_one {u : (ℤ√2)ˣ} (hu : (u : ℤ√2).norm = 1) :
    ∃ n : ℤ, u = silverUnit ^ n ∨ u = -silverUnit ^ n := by
  let s : Pell.Solution₁ 2 := ⟨(u : ℤ√2), Zsqrtd.norm_eq_one_iff_mem_unitary.mp hu⟩
  obtain ⟨m, hm | hm⟩ := pell_two_fundamental.eq_zpow_or_neg_zpow s
  · refine ⟨2 * m, Or.inl ?_⟩
    apply Units.ext
    have hcoe := congrArg (fun x : Pell.Solution₁ 2 => (x : ℤ√2)) hm
    simpa [s, pell_fund_zpow_coe] using hcoe
  · refine ⟨2 * m, Or.inr ?_⟩
    apply Units.ext
    have hcoe := congrArg (fun x : Pell.Solution₁ 2 => (x : ℤ√2)) hm
    have hneg : ∀ x : Pell.Solution₁ 2, ((-x : Pell.Solution₁ 2) : ℤ√2) = -(x : ℤ√2) :=
      fun _ => rfl
    rw [hneg, pell_fund_zpow_coe] at hcoe
    simpa [s] using hcoe

/-- Every unit of `ℤ√2` is of the form `± silverUnit ^ n`. -/
theorem zsqrtTwo_unit_eq_silverUnit_zpow (u : (ℤ√2)ˣ) :
    ∃ n : ℤ, u = silverUnit ^ n ∨ u = -silverUnit ^ n := by
  have hun : IsUnit (u : ℤ√2).norm := (Zsqrtd.isUnit_iff_norm_isUnit (u : ℤ√2)).mp u.isUnit
  rcases Int.isUnit_iff.mp hun with h1 | hm1
  · exact zsqrtTwo_unit_norm_one h1
  · have hnorm_inv : ((u * silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2).norm = 1 := by
      have hsi : ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2).norm = -1 := by
        simp [silverUnit, Zsqrtd.norm_def]
      rw [Units.val_mul, Zsqrtd.norm_mul, hm1, hsi]
      norm_num
    obtain ⟨m, hm | hm⟩ := zsqrtTwo_unit_norm_one hnorm_inv
    · refine ⟨m + 1, Or.inl ?_⟩
      calc
        u = (u * silverUnit⁻¹) * silverUnit := by simp
        _ = silverUnit ^ m * silverUnit := by rw [hm]
        _ = silverUnit ^ (m + 1) := by rw [zpow_add_one]
    · refine ⟨m + 1, Or.inr ?_⟩
      calc
        u = (u * silverUnit⁻¹) * silverUnit := by simp
        _ = (-silverUnit ^ m) * silverUnit := by rw [hm]
        _ = -silverUnit ^ (m + 1) := by rw [neg_mul, zpow_add_one]

/-! ## 3. Exact Reduced `d`-th Power Descent for `q ^ d + 1 = 2 * y ^ 2` -/

private lemma silverUnit_zpow_norm (k : ℤ) :
    ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2).norm = if Even k then 1 else -1 := by
  have hsu : (silverUnit : ℤ√2).norm = -1 := by simp [silverUnit, Zsqrtd.norm_def]
  have hsi : ((silverUnit⁻¹ : (ℤ√2)ˣ) : ℤ√2).norm = -1 := by
    simp [silverUnit, Zsqrtd.norm_def]
  induction k using Int.induction_on with
  | zero => simp
  | succ m hm =>
    rw [zpow_add, zpow_one, Units.val_mul, Zsqrtd.norm_mul, hm, hsu]
    by_cases h : Even (m : ℤ)
    · have h1 : ¬ Even ((m : ℤ) + 1) := Int.even_add_one.not_left.mpr h
      simp [h, h1]
    · have h1 : Even ((m : ℤ) + 1) := Int.even_add_one.mpr h
      simp [h, h1]
  | pred m hm =>
    rw [sub_eq_add_neg, zpow_add, zpow_neg_one, Units.val_mul, Zsqrtd.norm_mul, hm, hsi]
    have hev : Even (-(m : ℤ)) ↔ ¬ Even (-(m : ℤ) - 1) := by
      have h1 := Int.even_add_one (n := -(m : ℤ) - 1)
      have h2 : -(m : ℤ) - 1 + 1 = -(m : ℤ) := by ring
      rw [h2] at h1
      exact h1
    by_cases h : Even (-(m : ℤ))
    · have h1 : ¬ Even (-(m : ℤ) - 1) := hev.mp h
      simp [h, h1, show -(m : ℤ) + -1 = -(m : ℤ) - 1 by ring]
    · have h1 : Even (-(m : ℤ) - 1) := not_not.mp ((not_congr hev).mp h)
      simp [h, h1, show -(m : ℤ) + -1 = -(m : ℤ) - 1 by ring]

private lemma zsqrtTwo_fermat_reduced_power_descent_aux {q d y : ℕ}
    (hd_odd : Odd d) (heq : q ^ d + 1 = 2 * y ^ 2)
    {n : ℤ} {γ : ℤ√2} (hz1_n : (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ n : (ℤ√2)ˣ) : ℤ√2) * γ ^ d) :
    ∃ (k : ℤ) (α : ℤ√2),
      2 * |k| ≤ (d : ℤ) - 1 ∧
      (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d ∧
      α.norm = (if Even k then -(q : ℤ) else (q : ℤ)) ∧
      ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d +
        star ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * (star α) ^ d = 2 ∧
      ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d -
        star ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * (star α) ^ d = ⟨0, 2 * (y : ℤ)⟩ := by
  let z₁ : ℤ√2 := ⟨1, (y : ℤ)⟩
  let z₂ : ℤ√2 := ⟨1, -(y : ℤ)⟩
  have hd_pos : (0 : ℤ) < d := by exact_mod_cast hd_odd.pos
  let r : ℤ := n % d
  have hr0 : 0 ≤ r := Int.emod_nonneg n hd_pos.ne'
  have hrd : r < d := Int.emod_lt_of_pos n hd_pos
  obtain ⟨k, t, hkt, h2k⟩ : ∃ k t : ℤ, n = k + (d : ℤ) * t ∧ 2 * |k| ≤ (d : ℤ) - 1 := by
    by_cases hr_le : 2 * r ≤ (d : ℤ) - 1
    · refine ⟨r, n / d, ?_, ?_⟩
      · have := Int.mul_ediv_add_emod n d
        omega
      · rw [abs_of_nonneg hr0]
        exact hr_le
    · have hodd_z : (d : ℤ) % 2 = 1 := by exact_mod_cast Nat.odd_iff.mp hd_odd
      have hr_ge : (d : ℤ) + 1 ≤ 2 * r := by omega
      have hf : (d : ℤ) * (n / d + 1) = (d : ℤ) * (n / d) + d := by ring
      have hdiv : (d : ℤ) * (n / d) + r = n := Int.mul_ediv_add_emod n d
      refine ⟨r - d, n / d + 1, ?_, ?_⟩
      · linarith
      · rw [abs_of_nonpos (by omega)]
        omega
  let α : ℤ√2 := ((silverUnit ^ t : (ℤ√2)ˣ) : ℤ√2) * γ
  have hz1_k : z₁ = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d := by
    change z₁ = ((silverUnit ^ n : (ℤ√2)ˣ) : ℤ√2) * γ ^ d at hz1_n
    rw [hz1_n, hkt, zpow_add, Units.val_mul, mul_assoc]
    congr 1
    dsimp [α]
    rw [mul_pow]
    congr 1
    rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul, mul_comm (d : ℤ) t]
  have hnorm_eq : α.norm = if Even k then -(q : ℤ) else (q : ℤ) := by
    have hz1_norm : z₁.norm = -(q : ℤ) ^ d := by
      have heqz : (q : ℤ) ^ d + 1 = 2 * (y : ℤ) ^ 2 := by exact_mod_cast heq
      simp [z₁, Zsqrtd.norm_def]
      linarith
    have hαpow : (α ^ d).norm = α.norm ^ d := Zsqrtd.normMonoidHom.map_pow α d
    have hpow_norm : α.norm ^ d * (if Even k then (1 : ℤ) else -1) = -(q : ℤ) ^ d := by
      have h := congrArg Zsqrtd.norm hz1_k
      rw [Zsqrtd.norm_mul, hαpow, silverUnit_zpow_norm k, hz1_norm] at h
      linarith
    split_ifs with hk
    · simp only [hk, ↓reduceIte, mul_one] at hpow_norm
      have hpow_neg : α.norm ^ d = (-(q : ℤ)) ^ d := by
        rw [hd_odd.neg_pow]
        exact hpow_norm
      exact hd_odd.pow_inj.mp hpow_neg
    · simp only [hk, ↓reduceIte, mul_neg_one, neg_inj] at hpow_norm
      exact hd_odd.pow_inj.mp hpow_norm
  have hstar : star (((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d) = z₂ := by
    rw [← hz1_k]
    ext <;> simp [z₁, z₂]
  rw [star_mul, star_pow, mul_comm (star α ^ d)] at hstar
  refine ⟨k, α, h2k, hz1_k, hnorm_eq, ?_, ?_⟩
  · rw [← hz1_k, hstar]
    ext <;> simp [z₁, z₂]
  · rw [← hz1_k, hstar]
    ext <;> simp [z₁, z₂]; ring

/-- Exact reduced `d`-th power descent in `ℤ√2` for `q ^ d + 1 = 2 * y ^ 2` with `q, d` odd. -/
theorem zsqrtTwo_fermat_reduced_power_descent {q d y : ℕ}
    (hq_odd : Odd q) (hd_odd : Odd d) (heq : q ^ d + 1 = 2 * y ^ 2) :
    ∃ (k : ℤ) (α : ℤ√2),
      2 * |k| ≤ (d : ℤ) - 1 ∧
      (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d ∧
      α.norm = (if Even k then -(q : ℤ) else (q : ℤ)) ∧
      ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d +
        star ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * (star α) ^ d = 2 ∧
      ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d -
        star ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * (star α) ^ d = ⟨0, 2 * (y : ℤ)⟩ := by
  let z₁ : ℤ√2 := ⟨1, (y : ℤ)⟩
  let z₂ : ℤ√2 := ⟨1, -(y : ℤ)⟩
  have hprod : z₁ * z₂ = (-(q : ℤ√2)) ^ d := by
    have heqz : (q : ℤ) ^ d + 1 = 2 * (y : ℤ) ^ 2 := by exact_mod_cast heq
    rw [hd_odd.neg_pow, ← Nat.cast_pow, Zsqrtd.natCast_val]
    ext <;> simp [z₁, z₂]
    linarith
  have hrel : IsRelPrime z₁ z₂ := by
    intro u hu1 hu2
    have hu_sum : u ∣ z₁ + z₂ := dvd_add hu1 hu2
    have hsum_eq : z₁ + z₂ = (2 : ℤ√2) := by ext <;> simp [z₁, z₂]
    rw [hsum_eq] at hu_sum
    have hnorm4 : u.norm ∣ (4 : ℤ) := by
      obtain ⟨v, hv⟩ := hu_sum
      have h := congrArg Zsqrtd.norm hv
      rw [Zsqrtd.norm_mul] at h
      have h2 : (2 : ℤ√2).norm = 4 := by
        simp [Zsqrtd.norm_def]
      rw [h2] at h
      exact ⟨v.norm, h⟩
    have hu_prod : u ∣ (-(q : ℤ√2)) ^ d := by
      rw [← hprod]
      exact hu1.mul_right z₂
    have hnormq : u.norm ∣ (q : ℤ) ^ (2 * d) := by
      obtain ⟨v, hv⟩ := hu_prod
      have h := congrArg Zsqrtd.norm hv
      rw [Zsqrtd.norm_mul] at h
      have hnq : ((-(q : ℤ√2)) ^ d).norm = (q : ℤ) ^ (2 * d) := by
        rw [hd_odd.neg_pow, Zsqrtd.norm_neg, ← Nat.cast_pow, Zsqrtd.norm_natCast]
        push_cast
        ring
      rw [hnq] at h
      exact ⟨v.norm, h⟩
    have hcop_2q : IsCoprime (2 : ℤ) (q : ℤ) := by
      obtain ⟨m, hm⟩ := hq_odd
      refine ⟨-(m : ℤ), 1, ?_⟩
      have hmz : (q : ℤ) = 2 * m + 1 := by exact_mod_cast hm
      linarith
    have hcop_4q : IsCoprime (4 : ℤ) ((q : ℤ) ^ (2 * d)) := by
      have h4 : IsCoprime ((2 : ℤ) ^ 2) (q : ℤ) := hcop_2q.pow_left
      simpa [show (2 : ℤ) ^ 2 = 4 by norm_num] using h4.pow_right (n := 2 * d)
    exact (Zsqrtd.isUnit_iff_norm_isUnit u).mpr (hcop_4q.isUnit_of_dvd' hnorm4 hnormq)
  have hcop : IsCoprime z₁ z₂ := isRelPrime_iff_isCoprime.mp hrel
  obtain ⟨β, hassoc⟩ := exists_associated_pow_of_mul_eq_pow' hcop hprod
  obtain ⟨u, hu⟩ := hassoc
  have hz1_eq : z₁ = ((u : (ℤ√2)ˣ) : ℤ√2) * β ^ d := by
    rw [← hu, mul_comm]
  obtain ⟨n, hn | hn⟩ := zsqrtTwo_unit_eq_silverUnit_zpow u
  · have hz1_n : z₁ = ((silverUnit ^ n : (ℤ√2)ˣ) : ℤ√2) * β ^ d := by
      simpa [hn] using hz1_eq
    exact zsqrtTwo_fermat_reduced_power_descent_aux hd_odd heq hz1_n
  · have hz1_n : z₁ = ((silverUnit ^ n : (ℤ√2)ˣ) : ℤ√2) * (-β) ^ d := by
      rw [hd_odd.neg_pow, mul_neg, ← neg_mul]
      simpa [hn] using hz1_eq
    exact zsqrtTwo_fermat_reduced_power_descent_aux hd_odd heq hz1_n

/-! ## 4. Unconditional Elimination of Pure `d`-th Powers (`k = 0`) -/

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

/-- A pure `d`-th power in `ℤ√2` for odd `d ≥ 3` cannot equal `1 + y√2` when `y ≠ 0`. -/
theorem one_add_mul_sqrtd_ne_pow {d : ℕ} {y : ℤ} (hd_odd : Odd d) (hd3 : 3 ≤ d)
    (hy : y ≠ 0) (α : ℤ√2) : (⟨1, y⟩ : ℤ√2) ≠ α ^ d := by
  intro heq
  rcases α with ⟨a, b⟩
  by_cases hb : b = 0
  · have him := congrArg Zsqrtd.im heq
    have hpow : (⟨a, 0⟩ : ℤ√2) ^ d = ((a ^ d : ℤ) : ℤ√2) := by
      rw [← Zsqrtd.intCast_val, ← Int.cast_pow]
    rw [hb, hpow, Zsqrtd.im_intCast] at him
    exact hy him
  · have hsplit : (⟨a, b⟩ : ℤ√2) = (b : ℤ√2) * Zsqrtd.sqrtd + (a : ℤ√2) := by
      ext <;> simp
    have hexp : (⟨a, b⟩ : ℤ√2) ^ d = ∑ i ∈ Finset.range (d + 1),
        ((b : ℤ√2) * Zsqrtd.sqrtd) ^ i * (a : ℤ√2) ^ (d - i) * (d.choose i : ℤ√2) := by
      rw [hsplit, add_pow]
    let T : ℕ → ℤ := fun i =>
      if Even i then
        let j := i / 2
        (a ^ ((d - 1) / 2 - j)) ^ 2 * (b ^ 2) ^ j * (2 : ℤ) ^ j * (d.choose i : ℤ)
      else 0
    have hre_term : ∀ i ∈ Finset.range (d + 1),
        (((b : ℤ√2) * Zsqrtd.sqrtd) ^ i * (a : ℤ√2) ^ (d - i) * (d.choose i : ℤ√2)).re =
          a * T i := by
      intro i hi
      have hid : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have ha_pow : (a : ℤ√2) ^ (d - i) = ((a ^ (d - i) : ℤ) : ℤ√2) := (Int.cast_pow a _).symm
      have hb_pow : ((b : ℤ√2) * Zsqrtd.sqrtd) ^ i =
          ((b ^ i : ℤ) : ℤ√2) * (Zsqrtd.sqrtd : ℤ√2) ^ i := by
        rw [mul_pow, Int.cast_pow]
      rw [ha_pow, hb_pow]
      rcases Nat.even_or_odd i with he | ho
      · have he' := he
        obtain ⟨j, hj⟩ := he
        have hj2 : i = 2 * j := by omega
        have hij : i / 2 = j := by omega
        have hid1 : 2 * j ≤ d - 1 := by
          rcases hd_odd with ⟨m, rfl⟩
          omega
        have hsub : d - i = 1 + 2 * ((d - 1) / 2 - j) := by
          rcases hd_odd with ⟨m, rfl⟩
          omega
        simp only [T, he', ↓reduceIte]
        rw [hij, hj2, sqrtd_two_even]
        have hcast : (((b ^ (2 * j) : ℤ) : ℤ√2) * ((2 ^ j : ℤ) : ℤ√2)) *
            ((a ^ (d - 2 * j) : ℤ) : ℤ√2) * (d.choose (2 * j) : ℤ√2) =
            ((a ^ (d - 2 * j) * b ^ (2 * j) * 2 ^ j * d.choose (2 * j) : ℤ) : ℤ√2) := by
          push_cast
          ring
        rw [hcast, Zsqrtd.re_intCast, ← hj2, hsub, hj2, pow_add, pow_one, pow_mul, pow_mul]
        ring
      · have ho' := Nat.not_even_iff_odd.mpr ho
        obtain ⟨j, hj⟩ := ho
        have hj2 : i = 2 * j + 1 := by omega
        simp only [T, ho', ↓reduceIte]
        rw [hj2, sqrtd_two_odd, Zsqrtd.smul_val, mul_zero, mul_comm (⟨0, _⟩ : ℤ√2) _,
          Zsqrtd.smul_val, mul_zero, ← Int.cast_natCast (d.choose (2 * j + 1)),
          mul_comm (⟨0, _⟩ : ℤ√2) _, Zsqrtd.smul_val, mul_zero, mul_zero]
    have hre_sum : (⟨a, b⟩ ^ d : ℤ√2).re = a * ∑ i ∈ Finset.range (d + 1), T i := by
      change zsqrtTwoReHom (⟨a, b⟩ ^ d) = _
      rw [hexp, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      exact hre_term i hi
    have hT_nonneg : ∀ i ∈ Finset.range (d + 1), 0 ≤ T i := by
      intro i _
      dsimp [T]
      split_ifs
      · positivity
      · exact le_rfl
    have hd1_mem : d - 1 ∈ Finset.range (d + 1) := Finset.mem_range.mpr (by omega)
    have hd1_even : Even (d - 1) := by
      rcases hd_odd with ⟨m, rfl⟩
      exact ⟨m, by omega⟩
    have hd1_val : 6 ≤ T (d - 1) := by
      simp only [T, hd1_even, ↓reduceIte]
      have hj1 : 1 ≤ (d - 1) / 2 := by omega
      have hsub0 : (d - 1) / 2 - (d - 1) / 2 = 0 := Nat.sub_self _
      have hb2 : 1 ≤ b ^ 2 := by
        have := sq_pos_of_ne_zero hb
        omega
      have h2j : (2 : ℤ) ≤ 2 ^ ((d - 1) / 2) := by
        have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hj1
        exact_mod_cast h
      have hch : (3 : ℤ) ≤ (d.choose (d - 1) : ℤ) := by
        have hch_eq : d.choose (d - 1) = d := by
          obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
          simp [Nat.choose_succ_self_right]
        rw [hch_eq]
        exact_mod_cast hd3
      rw [hsub0, pow_zero, one_pow, one_mul]
      have hb2_pow : 1 ≤ (b ^ 2) ^ ((d - 1) / 2) := one_le_pow₀ hb2
      have hmul_ge : (1 : ℤ) * 2 * 3 ≤
          (b ^ 2) ^ ((d - 1) / 2) * 2 ^ ((d - 1) / 2) * (d.choose (d - 1) : ℤ) := by
        gcongr
      linarith
    have hS_ge : 6 ≤ ∑ i ∈ Finset.range (d + 1), T i :=
      hd1_val.trans (Finset.single_le_sum hT_nonneg hd1_mem)
    have h1 : (1 : ℤ) = a * ∑ i ∈ Finset.range (d + 1), T i := by
      have hre := congrArg Zsqrtd.re heq
      simpa [hre_sum] using hre
    have hunit : IsUnit (∑ i ∈ Finset.range (d + 1), T i) :=
      isUnit_iff_dvd_one.mpr ⟨a, by rw [mul_comm, h1]⟩
    rcases Int.isUnit_iff.mp hunit with h | h <;> omega

/-! ## 5. Mod-`d` Frobenius Identity & Exceptional Euler `ℤ√2` Profile -/

/-- For any prime `d ≡ 1 [MOD 8]` and `α : ℤ√2`, `α ^ d ≡ α [ZMOD d]` coordinatewise. -/
theorem zsqrtTwo_pow_modEq_self_of_prime_mod_eight_eq_one {d : ℕ}
    (hd_prime : d.Prime) (hd8 : d % 8 = 1) (α : ℤ√2) :
    (α ^ d).re ≡ α.re [ZMOD d] ∧ (α ^ d).im ≡ α.im [ZMOD d] := by
  have : Fact d.Prime := ⟨hd_prime⟩
  rcases α with ⟨a, b⟩
  have hsplit : (⟨a, b⟩ : ℤ√2) = (b : ℤ√2) * Zsqrtd.sqrtd + (a : ℤ√2) := by
    ext <;> simp
  let term (i : ℕ) : ℤ√2 :=
    ((b : ℤ√2) * Zsqrtd.sqrtd) ^ i * (a : ℤ√2) ^ (d - i) * (d.choose i : ℤ√2)
  have hexp : (⟨a, b⟩ : ℤ√2) ^ d = ∑ i ∈ Finset.range (d + 1), term i := by
    rw [hsplit, add_pow]
  have hre_term : ∀ i ∈ Finset.range (d + 1),
      (term i).re ≡ (if i = 0 then a ^ d else 0) [ZMOD d] := by
    intro i hi
    have hid_le : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases hi0 : i = 0
    · rw [hi0]
      simp only [↓reduceIte, term, pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right,
        Nat.cast_one, mul_one, ← Int.cast_pow, Zsqrtd.re_intCast]
      rfl
    · by_cases hid : i = d
      · have hd_odd : Odd d := Nat.odd_iff.mpr (by omega)
        obtain ⟨j, hj⟩ := hd_odd
        have ht : term d = ⟨0, b ^ (2 * j + 1) * 2 ^ j⟩ := by
          dsimp [term]
          rw [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, mul_one,
            hj, mul_pow, ← Int.cast_pow, sqrtd_two_odd, Zsqrtd.smul_val]
          simp
        rw [hid, ht]
        simp [hd_prime.ne_zero]
      · have hid_lt : i < d := lt_of_le_of_ne hid_le hid
        have hdvd_nat : d ∣ d.choose i := Nat.Prime.dvd_choose_self hd_prime hi0 hid_lt
        have hdvd_int : (d : ℤ) ∣ (d.choose i : ℤ) := Int.natCast_dvd_natCast.mpr hdvd_nat
        have hdvd_zsqrt : ((d : ℤ) : ℤ√2) ∣ term i := by
          dsimp [term]
          refine dvd_mul_of_dvd_right ?_ _
          rw [← Int.cast_natCast (d.choose i)]
          exact (Zsqrtd.intCast_dvd_intCast (d : ℤ) (d.choose i : ℤ)).mpr hdvd_int
        have hdvd_re : (d : ℤ) ∣ (term i).re := (Zsqrtd.intCast_dvd (d : ℤ) (term i)).mp hdvd_zsqrt |>.1
        simp only [hi0, ↓reduceIte]
        exact Int.modEq_zero_iff_dvd.mpr hdvd_re
  have him_term : ∀ i ∈ Finset.range (d + 1),
      (term i).im ≡ (if i = d then b ^ d * 2 ^ ((d - 1) / 2) else 0) [ZMOD d] := by
    intro i hi
    have hid_le : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases hid : i = d
    · have hd_odd : Odd d := Nat.odd_iff.mpr (by omega)
      obtain ⟨j, hj⟩ := hd_odd
      have hj_eq : j = (d - 1) / 2 := by omega
      have ht : term d = ⟨0, b ^ d * 2 ^ ((d - 1) / 2)⟩ := by
        dsimp [term]
        rw [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, mul_one,
          mul_pow, ← Int.cast_pow]
        conv_lhs => rhs; rw [hj, sqrtd_two_odd, hj_eq]
        rw [Zsqrtd.smul_val]
        simp
      rw [hid, ht]
      simp
    · by_cases hi0 : i = 0
      · have hd_ne0 : 0 ≠ d := hd_prime.ne_zero.symm
        simp only [hd_ne0, ↓reduceIte, term, hi0, pow_zero, one_mul, Nat.sub_zero,
          Nat.choose_zero_right, Nat.cast_one, mul_one, ← Int.cast_pow, Zsqrtd.im_intCast]
        rfl
      · have hid_lt : i < d := lt_of_le_of_ne hid_le hid
        have hdvd_nat : d ∣ d.choose i := Nat.Prime.dvd_choose_self hd_prime hi0 hid_lt
        have hdvd_int : (d : ℤ) ∣ (d.choose i : ℤ) := Int.natCast_dvd_natCast.mpr hdvd_nat
        have hdvd_zsqrt : ((d : ℤ) : ℤ√2) ∣ term i := by
          dsimp [term]
          refine dvd_mul_of_dvd_right ?_ _
          rw [← Int.cast_natCast (d.choose i)]
          exact (Zsqrtd.intCast_dvd_intCast (d : ℤ) (d.choose i : ℤ)).mpr hdvd_int
        have hdvd_im : (d : ℤ) ∣ (term i).im := (Zsqrtd.intCast_dvd (d : ℤ) (term i)).mp hdvd_zsqrt |>.2
        simp only [hid, ↓reduceIte]
        exact Int.modEq_zero_iff_dvd.mpr hdvd_im
  have ha_fermat : a ^ d ≡ a [ZMOD d] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    exact ZMod.pow_card (a : ZMod d)
  have hb_fermat : b ^ d ≡ b [ZMOD d] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    exact ZMod.pow_card (b : ZMod d)
  have h2_euler : (2 : ℤ) ^ ((d - 1) / 2) ≡ 1 [ZMOD d] := by
    have hd_two : 2 ≤ d := hd_prime.two_le
    have hd_ne2 : d ≠ 2 := by omega
    have hsq : IsSquare (2 : ZMod d) := (ZMod.exists_sq_eq_two_iff hd_ne2).mpr (Or.inl hd8)
    have h2_ne : (2 : ZMod d) ≠ 0 := by
      intro h0
      have hdvd : d ∣ 2 := (ZMod.natCast_eq_zero_iff 2 d).mp h0
      have := Nat.le_of_dvd (by decide) hdvd
      omega
    have heul : (2 : ZMod d) ^ (d / 2) = 1 := (ZMod.euler_criterion d h2_ne).mp hsq
    have hdiv : d / 2 = (d - 1) / 2 := by omega
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    rw [← hdiv]
    exact heul
  have hre_sum : (⟨a, b⟩ ^ d : ℤ√2).re ≡ a ^ d [ZMOD d] := by
    change zsqrtTwoReHom (⟨a, b⟩ ^ d) ≡ _ [ZMOD d]
    rw [hexp, map_sum]
    have hcongr : ∑ x ∈ Finset.range (d + 1), zsqrtTwoReHom (term x) =
        ∑ x ∈ Finset.range (d + 1), (term x).re := rfl
    rw [hcongr]
    have hs := Int.ModEq.sum (s := Finset.range (d + 1)) hre_term
    have h0_mem : 0 ∈ Finset.range (d + 1) := Finset.mem_range.mpr (by omega)
    simpa [h0_mem] using hs
  have him_sum : (⟨a, b⟩ ^ d : ℤ√2).im ≡ b ^ d * 2 ^ ((d - 1) / 2) [ZMOD d] := by
    change zsqrtTwoImHom (⟨a, b⟩ ^ d) ≡ _ [ZMOD d]
    rw [hexp, map_sum]
    have hcongr : ∑ x ∈ Finset.range (d + 1), zsqrtTwoImHom (term x) =
        ∑ x ∈ Finset.range (d + 1), (term x).im := rfl
    rw [hcongr]
    have hs := Int.ModEq.sum (s := Finset.range (d + 1)) him_term
    have hd_mem : d ∈ Finset.range (d + 1) := Finset.mem_range.mpr (by omega)
    simpa [hd_mem] using hs
  refine ⟨hre_sum.trans ha_fermat, him_sum.trans ?_⟩
  simpa using hb_fermat.mul h2_euler

/-- General Frobenius descent in `ℤ√2` for `q ^ d + 1 = 2 * y ^ 2` when `q` is odd, `d` is prime
with `d % 8 = 1`, `0 < y`, and `d ∣ y`. -/
theorem zsqrtTwo_fermat_frobenius_descent_of_dvd {q d y : ℕ}
    (hq_odd : Odd q) (hd_prime : d.Prime) (hd8 : d % 8 = 1)
    (hy_pos : 0 < y) (hdy : d ∣ y) (heq : q ^ d + 1 = 2 * y ^ 2) :
    ∃ (k : ℤ) (α : ℤ√2),
      1 ≤ |k| ∧
      2 * |k| ≤ (d : ℤ) - 1 ∧
      (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d ∧
      α.norm = (if Even k then -(q : ℤ) else (q : ℤ)) ∧
      α.re ≡ ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2).re [ZMOD (d : ℤ)] ∧
      α.im ≡ ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2).im [ZMOD (d : ℤ)] := by
  have hd_odd : Odd d := Nat.odd_iff.mpr (by omega)
  have hd3 : 3 ≤ d := by
    have := hd_prime.two_le
    omega
  obtain ⟨k, α, h2k, hz_eq, hnorm, _, _⟩ :=
    zsqrtTwo_fermat_reduced_power_descent hq_odd hd_odd heq
  have hk_ne : k ≠ 0 := by
    rintro rfl
    simp only [zpow_zero, Units.val_one, one_mul] at hz_eq
    exact one_add_mul_sqrtd_ne_pow hd_odd hd3 (by exact_mod_cast hy_pos.ne') α hz_eq
  have hk1 : 1 ≤ |k| := Int.one_le_abs hk_ne
  let v : ℤ√2 := ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2)
  have hpow_eq : α ^ d = v * ⟨1, (y : ℤ)⟩ := by
    calc
      α ^ d = ((silverUnit ^ (-k) * silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d := by
        simp
      _ = v * (((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d) := by
        rw [Units.val_mul, mul_assoc]
      _ = v * ⟨1, (y : ℤ)⟩ := by rw [← hz_eq]
  have hy_mod : (y : ℤ) ≡ 0 [ZMOD (d : ℤ)] :=
    Int.modEq_zero_iff_dvd.mpr (Int.natCast_dvd_natCast.mpr hdy)
  have hre_mod : (v * ⟨1, (y : ℤ)⟩).re ≡ v.re [ZMOD (d : ℤ)] := by
    rw [Zsqrtd.re_mul]
    have hmul : 2 * v.im * (y : ℤ) ≡ 0 [ZMOD (d : ℤ)] := by
      simpa using hy_mod.mul_left (2 * v.im)
    simpa using (Int.ModEq.refl (v.re * 1)).add hmul
  have him_mod : (v * ⟨1, (y : ℤ)⟩).im ≡ v.im [ZMOD (d : ℤ)] := by
    rw [Zsqrtd.im_mul]
    have hmul : v.re * (y : ℤ) ≡ 0 [ZMOD (d : ℤ)] := by
      simpa using hy_mod.mul_left v.re
    simpa using hmul.add (Int.ModEq.refl (v.im * 1))
  obtain ⟨hfrob_re, hfrob_im⟩ := zsqrtTwo_pow_modEq_self_of_prime_mod_eight_eq_one hd_prime hd8 α
  refine ⟨k, α, hk1, h2k, hz_eq, hnorm, ?_, ?_⟩
  · exact hfrob_re.symm.trans (hpow_eq ▸ hre_mod)
  · exact hfrob_im.symm.trans (hpow_eq ▸ him_mod)

/-- Exceptional Euler-index `ℤ√2` Frobenius descent on `sigma 1 (m ^ 2) / q ^ a = l * t ^ 2`
(`a > 1`, `l.Prime`): produces `y`, `k`, and `α` with `1 ≤ |k| ≤ (d - 1) / 2`,
`1 + y√2 = silverUnit ^ k * α ^ d`, `α.norm = ±q`, and `α ≡ silverUnit ^ (-k) [ZMOD d]`. -/
theorem exceptional_euler_zsqrtTwo_frobenius_descent {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    let d := (a + 1) / 2
    ∃ (y : ℕ) (k : ℤ) (α : ℤ√2),
      0 < y ∧ d ∣ y ∧ q ^ d + 1 = 2 * y ^ 2 ∧
      1 ≤ |k| ∧ 2 * |k| ≤ (d : ℤ) - 1 ∧
      (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d ∧
      α.norm = (if Even k then -(q : ℤ) else (q : ℤ)) ∧
      α.re ≡ ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2).re [ZMOD (d : ℤ)] ∧
      α.im ≡ ((silverUnit ^ (-k) : (ℤ√2)ˣ) : ℤ√2).im [ZMOD (d : ℤ)] := by
  intro d
  obtain ⟨hd, _, hd8, _, _, _, _⟩ :=
    exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨w, y, _, _, hpow, _, _, _, hdwy, _, _, _⟩ :=
    exceptional_index_cofactor_factorization hN ho hq hq4 ha4 ha hqm hform hl hi
  change d.Prime at hd
  change d % 8 = 1 at hd8
  change q ^ d + 1 = 2 * y ^ 2 at hpow
  change d * w ∣ y at hdwy
  have hy_pos : 0 < y := Nat.pos_of_ne_zero fun h => by simp [h] at hpow
  have hdy : d ∣ y := (dvd_mul_right d w).trans hdwy
  have hq_odd : Odd q := Nat.odd_iff.mpr (by omega)
  obtain ⟨k, α, hk1, h2k, hz_eq, hnorm, hre, him⟩ :=
    zsqrtTwo_fermat_frobenius_descent_of_dvd hq_odd hd hd8 hy_pos hdy hpow
  exact ⟨y, k, α, hy_pos, hdy, hpow, hk1, h2k, hz_eq, hnorm, hre, him⟩

end OddPerfect
