module

public import OddPerfect.ExceptionalBlockSquare
public import OddPerfect.ExceptionalBranchClosure
public import OddPerfect.Hirakawa
public import OddPerfect.AlternatingPell
public import OddPerfect.PellCoordinates
public import Mathlib.NumberTheory.Pell
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Hirakawa Pell Closure (`OddPerfect.HirakawaClosure`)

Develops the Pell-equation fundamental-solution and `ℤ[√(2q)]` descent structure on the
remaining prime-times-square Euler-index branch `I = sigma 1 (m ^ 2) / q ^ a = l * t ^ 2`
(`a > 1`, `l.Prime`, `d := (a + 1) / 2`):

1. `hirakawa_pell_fundamental_neighbor`: `(2 * q + 1, 2)` is the fundamental solution of
   `x ^ 2 - q * (q + 1) * y ^ 2 = 1` for every `0 < q`.
2. `hirakawa_pell_first_block_solution`: when `q + 1 = 2 * d * w ^ 2` with distinct primes
   `q ≠ d` (`q` odd), `2 * d * q` is non-square and `(2 * q + 1, 2 * w)` is a positive
   solution in `Pell.Solution₁ (2 * d * q)`.
3. `hirakawa_pell_second_block_is_fundamental`: on the simultaneous equations
   `q + 1 = 2 * d * w ^ 2` and `q ^ d + 1 = 2 * (d * w * z) ^ 2`, the explicit solution
   `(2 * q ^ d + 1, 2 * d * w * z * q ^ ((d - 1) / 2))` is fundamental in
   `Pell.Solution₁ (2 * q)`.
4. Euler component index consequences:
   - `exceptional_euler_pell_fundamental_profile`
   - `euler_index_ne_prime_mul_square_of_exponent_lt_33` (and `gcd` corollary)
   - `hirakawa_euler_index_ne_prime_mul_square_of_ivorra_bennett_skinner` (and `gcd` corollary)
-/

public section

namespace OddPerfect

open ArithmeticFunction

/-! ## 1. Neighbor Pell Solution `x ^ 2 - q * (q + 1) * y ^ 2 = 1` -/

/-- Explicit Pell solution `(2 * q + 1, 2)` in `Pell.Solution₁ (q * (q + 1))`. -/
@[expose] def hirakawaNeighborPell (q : ℕ) : Pell.Solution₁ ((q : ℤ) * ((q : ℤ) + 1)) :=
  Pell.Solution₁.mk (2 * (q : ℤ) + 1) 2 (by ring)

/-- For every positive natural `q`, `(2 * q + 1, 2)` is the fundamental solution of
`x ^ 2 - q * (q + 1) * y ^ 2 = 1`. -/
theorem hirakawa_pell_fundamental_neighbor {q : ℕ} (hq : 0 < q) :
    Pell.IsFundamental (hirakawaNeighborPell q) := by
  have hq_int : (0 : ℤ) < q := by exact_mod_cast hq
  refine ⟨by change 1 < 2 * (q : ℤ) + 1; omega, by change (0 : ℤ) < 2; decide, ?_⟩
  intro b hb
  change 2 * (q : ℤ) + 1 ≤ b.x
  have hprop := b.prop
  have hy_sq_ne_one : b.y ^ 2 ≠ 1 := by
    intro hysq
    have hbx_sq : b.x ^ 2 = (q : ℤ) * ((q : ℤ) + 1) + 1 := by
      rw [hysq, mul_one] at hprop
      linarith
    have hlo : (q : ℤ) ^ 2 < b.x ^ 2 := by nlinarith
    have hhi : b.x ^ 2 < ((q : ℤ) + 1) ^ 2 := by nlinarith
    rcases le_or_gt b.x (q : ℤ) with hle | hgt
    · have hsq := pow_le_pow_left₀ (by omega : 0 ≤ b.x) hle 2
      linarith
    · have hsq := pow_le_pow_left₀ (by positivity : (0 : ℤ) ≤ (q : ℤ) + 1)
        (by omega : (q : ℤ) + 1 ≤ b.x) 2
      linarith
  have hy0 : b.y ≠ 0 := Pell.Solution₁.y_ne_zero_of_one_lt_x hb
  have hy1 : b.y ≠ 1 := fun h => hy_sq_ne_one (by rw [h, one_pow])
  have hyn1 : b.y ≠ -1 := fun h => hy_sq_ne_one (by rw [h]; norm_num)
  have hy_ge4 : 4 ≤ b.y ^ 2 := by
    rcases (by omega : b.y ≤ -2 ∨ 2 ≤ b.y) with h | h <;> nlinarith
  have hD_nonneg : 0 ≤ (q : ℤ) * ((q : ℤ) + 1) := by positivity
  have hmul : (q : ℤ) * ((q : ℤ) + 1) * 4 ≤ (q : ℤ) * ((q : ℤ) + 1) * b.y ^ 2 :=
    mul_le_mul_of_nonneg_left hy_ge4 hD_nonneg
  have hbx_sq : (2 * (q : ℤ) + 1) ^ 2 ≤ b.x ^ 2 := by
    calc
      (2 * (q : ℤ) + 1) ^ 2 = 1 + (q : ℤ) * ((q : ℤ) + 1) * 4 := by ring
      _ ≤ 1 + (q : ℤ) * ((q : ℤ) + 1) * b.y ^ 2 := by linarith
      _ = b.x ^ 2 := by linarith [hprop]
  by_contra hlt
  have hlt' : b.x < 2 * (q : ℤ) + 1 := not_le.mp hlt
  have hpow_lt : b.x ^ 2 < (2 * (q : ℤ) + 1) ^ 2 :=
    pow_lt_pow_left₀ hlt' (by omega : 0 ≤ b.x) (by decide : 2 ≠ 0)
  linarith

/-! ## 2. First-Block Pell Solution `x ^ 2 - 2 * d * q * y ^ 2 = 1` -/

/-- Explicit Pell solution `(2 * q + 1, 2 * w)` in `Pell.Solution₁ (2 * d * q)`
when `q + 1 = 2 * d * w ^ 2`. -/
@[expose] def hirakawaFirstBlockPell {q d w : ℕ} (hq1 : q + 1 = 2 * d * w ^ 2) :
    Pell.Solution₁ (2 * (d : ℤ) * (q : ℤ)) :=
  Pell.Solution₁.mk (2 * (q : ℤ) + 1) (2 * (w : ℤ)) (by
    have hq1_int : (q : ℤ) + 1 = 2 * (d : ℤ) * (w : ℤ) ^ 2 := by exact_mod_cast hq1
    have hmul : 2 * (d : ℤ) * (q : ℤ) * (2 * (w : ℤ)) ^ 2 =
        4 * (q : ℤ) * (2 * (d : ℤ) * (w : ℤ) ^ 2) := by ring
    rw [hmul, ← hq1_int]
    ring)

/-- When `q + 1 = 2 * d * w ^ 2` with distinct primes `q ≠ d` and `q` odd, the
discriminant `2 * d * q` is positive and non-square, and `hirakawaFirstBlockPell hq1`
provides an explicit positive Pell solution `(2 * q + 1, 2 * w)`. -/
theorem hirakawa_pell_first_block_solution {q d w : ℕ}
    (hq : q.Prime) (hd : d.Prime) (hqd : q ≠ d) (hq_odd : Odd q)
    (hq1 : q + 1 = 2 * d * w ^ 2) :
    0 < 2 * (d : ℤ) * (q : ℤ) ∧
    ¬ IsSquare (2 * (d : ℤ) * (q : ℤ)) ∧
    1 < (hirakawaFirstBlockPell hq1).x ∧
    0 < (hirakawaFirstBlockPell hq1).y := by
  have hd_pos : 0 < d := hd.pos
  have hq_pos : 0 < q := hq.pos
  have hw_pos : 0 < w := by
    by_contra hw0
    have hw_eq : w = 0 := by omega
    rw [hw_eq] at hq1
    simp at hq1
  have hD_pos : 0 < 2 * (d : ℤ) * (q : ℤ) := by positivity
  have hD_nsq : ¬ IsSquare (2 * (d : ℤ) * (q : ℤ)) := by
    rintro ⟨r, hr⟩
    have hnat : 2 * d * q = r.natAbs ^ 2 := by
      have h := congrArg Int.natAbs hr
      have hcast : (2 * (d : ℤ) * (q : ℤ)) = ((2 * d * q : ℕ) : ℤ) := by push_cast; ring
      rw [hcast, Int.natAbs_natCast, Int.natAbs_mul, ← pow_two] at h
      exact h
    have hr_ne : r.natAbs ≠ 0 := by
      intro h0
      rw [h0] at hnat
      simp [hd.ne_zero, hq.ne_zero] at hnat
    have h2q : ¬ q ∣ 2 := fun h => by
      have hq2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h
      exact hq_odd.not_two_dvd_nat (hq2 ▸ dvd_rfl)
    have hdq : ¬ q ∣ d := fun h => hqd ((Nat.prime_dvd_prime_iff_eq hq hd).mp h)
    have hfac := congrArg (fun n : ℕ => n.factorization q) hnat
    rw [Nat.factorization_mul (mul_ne_zero (by decide) hd.ne_zero) hq.ne_zero,
      Nat.factorization_mul (by decide) hd.ne_zero,
      Finsupp.add_apply, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd h2q,
      Nat.factorization_eq_zero_of_not_dvd hdq,
      hq.factorization_self,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hfac
    omega
  refine ⟨hD_pos, hD_nsq, ?_, ?_⟩
  · change 1 < 2 * (q : ℤ) + 1
    omega
  · change 0 < 2 * (w : ℤ)
    omega

/-! ## 3. Fundamental Pell Property for the Second Block `x ^ 2 - 2 * q * y ^ 2 = 1` -/

/-- Explicit Pell solution `(2 * q ^ d + 1, 2 * d * w * z * q ^ ((d - 1) / 2))` in
`Pell.Solution₁ (2 * q)` when `d` is odd and `q ^ d + 1 = 2 * (d * w * z) ^ 2`. -/
@[expose] def hirakawaSecondBlockPell {q d w z : ℕ}
    (hd_odd : Odd d) (hqd1 : q ^ d + 1 = 2 * (d * w * z) ^ 2) :
    Pell.Solution₁ (2 * (q : ℤ)) :=
  Pell.Solution₁.mk (2 * (q : ℤ) ^ d + 1)
    (2 * (d : ℤ) * (w : ℤ) * (z : ℤ) * (q : ℤ) ^ ((d - 1) / 2)) (by
      have hd_eq : 2 * ((d - 1) / 2) + 1 = d := by
        obtain ⟨k, rfl⟩ := hd_odd
        omega
      have hpow : (q : ℤ) * ((q : ℤ) ^ ((d - 1) / 2)) ^ 2 = (q : ℤ) ^ d := by
        calc
          (q : ℤ) * ((q : ℤ) ^ ((d - 1) / 2)) ^ 2
              = (q : ℤ) ^ ((d - 1) / 2 * 2 + 1) := by rw [pow_succ, ← pow_mul]; ring
          _ = (q : ℤ) ^ d := by rw [mul_comm ((d - 1) / 2) 2, hd_eq]
      have hqd1_int : (q : ℤ) ^ d + 1 = 2 * ((d : ℤ) * (w : ℤ) * (z : ℤ)) ^ 2 := by
        exact_mod_cast hqd1
      calc
        (2 * (q : ℤ) ^ d + 1) ^ 2 -
            2 * (q : ℤ) * (2 * (d : ℤ) * (w : ℤ) * (z : ℤ) * (q : ℤ) ^ ((d - 1) / 2)) ^ 2
            = (2 * (q : ℤ) ^ d + 1) ^ 2 -
                4 * (2 * ((d : ℤ) * (w : ℤ) * (z : ℤ)) ^ 2) *
                  ((q : ℤ) * ((q : ℤ) ^ ((d - 1) / 2)) ^ 2) := by ring
        _ = (2 * (q : ℤ) ^ d + 1) ^ 2 - 4 * ((q : ℤ) ^ d + 1) * (q : ℤ) ^ d := by
              rw [hpow, ← hqd1_int]
        _ = 1 := by ring)

private lemma pell_coe_pow {d : ℤ} (a : Pell.Solution₁ d) (n : ℕ) :
    ((a ^ n : Pell.Solution₁ d) : ℤ√d) = (a : ℤ√d) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, ← ih]
    rfl

private lemma not_isSquare_two_mul_prime {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    ¬ IsSquare (2 * (q : ℤ)) := by
  rintro ⟨r, hr⟩
  have hnat : 2 * q = r.natAbs ^ 2 := by
    have h := congrArg Int.natAbs hr
    have hcast : (2 * (q : ℤ)) = ((2 * q : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, Int.natAbs_natCast, Int.natAbs_mul, ← pow_two] at h
    exact h
  have hr_ne : r.natAbs ≠ 0 := by
    intro h0
    rw [h0] at hnat
    simp [hq.ne_zero] at hnat
  have h2q : ¬ 2 ∣ q := fun h => hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp h).symm
  have hfac := congrArg (fun n : ℕ => n.factorization 2) hnat
  rw [Nat.factorization_mul (by decide) hq.ne_zero, Finsupp.add_apply,
    Nat.prime_two.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd h2q,
    Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hfac
  omega

private lemma two_mul_sq_ne_odd_mul_sq {a b c : ℕ} (ha : a ≠ 0) (hc : Odd c) :
    2 * a ^ 2 ≠ c * b ^ 2 := by
  intro heq
  have hb : b ≠ 0 := by
    intro h0
    rw [h0] at heq
    simp [ha] at heq
  have hc0 : c ≠ 0 := hc.pos.ne'
  have hc2 : ¬ 2 ∣ c := hc.not_two_dvd_nat
  have hfac := congrArg (fun n : ℕ => n.factorization 2) heq
  rw [Nat.factorization_mul (by decide) (pow_ne_zero 2 ha), Finsupp.add_apply,
    Nat.prime_two.factorization_self,
    Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    Nat.factorization_mul hc0 (pow_ne_zero 2 hb), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hc2,
    Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hfac
  omega

private lemma isSquare_div_of_coprime_two_prime_sq {X Y q V k : ℕ}
    (hX0 : 0 < X) (hY0 : 0 < Y) (hV0 : 0 < V) (hq : q.Prime) (hq2 : q ≠ 2)
    (hcop : Nat.Coprime X Y) (heq : X * Y = 2 * q * V ^ 2)
    (hk0 : k ≠ 0) (hkX : k ∣ X)
    (hk2 : k.factorization 2 = if 2 ∣ X then 1 else 0)
    (hkq : k.factorization q = if q ∣ X then 1 else 0)
    (hkr : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ q → k.factorization r = 0) :
    IsSquare (X / k) := by
  have hX_eq : X = k * (X / k) := (Nat.mul_div_cancel' hkX).symm
  have hdiv0 : X / k ≠ 0 := fun h => by rw [h, mul_zero] at hX_eq; omega
  apply Nat.isSquare_iff_even_factorization.mpr
  intro r hr
  have hXk := congrArg (fun n : ℕ => n.factorization r) hX_eq
  rw [Nat.factorization_mul hk0 hdiv0, Finsupp.add_apply] at hXk
  have hXY := congrArg (fun n : ℕ => n.factorization r) heq
  rw [Nat.factorization_mul hX0.ne' hY0.ne', Finsupp.add_apply,
    Nat.factorization_mul (mul_ne_zero (by decide) hq.ne_zero) (pow_ne_zero 2 hV0.ne'),
    Nat.factorization_mul (by decide) hq.ne_zero,
    Finsupp.add_apply, Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hXY
  have hdisj : X.factorization r = 0 ∨ Y.factorization r = 0 := by
    by_contra hboth
    have hXA : X.factorization r ≠ 0 := fun h => hboth (Or.inl h)
    have hYB : Y.factorization r ≠ 0 := fun h => hboth (Or.inr h)
    have hrX : r ∣ X := (hr.dvd_iff_one_le_factorization hX0.ne').mpr (Nat.pos_of_ne_zero hXA)
    have hrY : r ∣ Y := (hr.dvd_iff_one_le_factorization hY0.ne').mpr (Nat.pos_of_ne_zero hYB)
    exact hr.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hrX hrY)
  by_cases hr2 : r = 2
  · subst r
    rw [hk2] at hXk
    by_cases h2X : 2 ∣ X
    · have h2Y : ¬ 2 ∣ Y := fun h =>
        Nat.prime_two.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h2X h)
      have hq_not_2 : ¬ 2 ∣ q := fun h =>
        hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp h).symm
      simp only [h2X, ↓reduceIte] at hXk
      rw [Nat.factorization_eq_zero_of_not_dvd h2Y,
        Nat.prime_two.factorization_self,
        Nat.factorization_eq_zero_of_not_dvd hq_not_2] at hXY
      exact Nat.even_iff.mpr (by omega)
    · simp only [h2X, ↓reduceIte] at hXk
      rw [Nat.factorization_eq_zero_of_not_dvd h2X] at hXk
      exact Nat.even_iff.mpr (by omega)
  · by_cases hrq : r = q
    · subst r
      rw [hkq] at hXk
      by_cases hqX : q ∣ X
      · have hqY : ¬ q ∣ Y := fun h =>
          hq.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hqX h)
        have h2_not_q : ¬ q ∣ 2 := fun h =>
          hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h)
        simp only [hqX, ↓reduceIte] at hXk
        rw [Nat.factorization_eq_zero_of_not_dvd hqY,
          Nat.factorization_eq_zero_of_not_dvd h2_not_q,
          hq.factorization_self] at hXY
        exact Nat.even_iff.mpr (by omega)
      · simp only [hqX, ↓reduceIte] at hXk
        rw [Nat.factorization_eq_zero_of_not_dvd hqX] at hXk
        exact Nat.even_iff.mpr (by omega)
    · have hr_not_2 : ¬ r ∣ 2 := fun h =>
        hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h)
      have hr_not_q : ¬ r ∣ q := fun h =>
        hrq ((Nat.prime_dvd_prime_iff_eq hr hq).mp h)
      rw [hkr r hr hr2 hrq, zero_add] at hXk
      rw [Nat.factorization_eq_zero_of_not_dvd hr_not_2,
        Nat.factorization_eq_zero_of_not_dvd hr_not_q,
        zero_add, zero_add] at hXY
      rcases hdisj with h0 | h0
      · rw [h0] at hXk
        exact Nat.even_iff.mpr (by omega)
      · rw [h0, add_zero] at hXY
        exact Nat.even_iff.mpr (by omega)

private lemma coprime_mul_eq_two_prime_sq {A B q V : ℕ}
    (hA0 : 0 < A) (hB0 : 0 < B) (hV0 : 0 < V) (hq : q.Prime) (hq2 : q ≠ 2)
    (hcop : Nat.Coprime A B) (heq : A * B = 2 * q * V ^ 2) :
    (∃ u v : ℕ, 0 < u ∧ 0 < v ∧ A = 2 * q * u ^ 2 ∧ B = v ^ 2) ∨
    (∃ u v : ℕ, 0 < u ∧ 0 < v ∧ A = u ^ 2 ∧ B = 2 * q * v ^ 2) ∨
    (∃ u v : ℕ, 0 < u ∧ 0 < v ∧ A = 2 * u ^ 2 ∧ B = q * v ^ 2) ∨
    (∃ u v : ℕ, 0 < u ∧ 0 < v ∧ A = q * u ^ 2 ∧ B = 2 * v ^ 2) := by
  have heq_sym : B * A = 2 * q * V ^ 2 := by rw [mul_comm, heq]
  have h2_div : 2 ∣ A ∨ 2 ∣ B := Nat.prime_two.dvd_mul.mp (heq ▸ ⟨q * V ^ 2, by ring⟩)
  have hq_div : q ∣ A ∨ q ∣ B := hq.dvd_mul.mp (heq ▸ ⟨2 * V ^ 2, by ring⟩)
  have h2_not_q : ¬ q ∣ 2 := fun h =>
    hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h)
  have hq_not_2 : ¬ 2 ∣ q := fun h =>
    hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp h).symm
  have h2q_cop : Nat.Coprime 2 q := Nat.prime_two.coprime_iff_not_dvd.mpr hq_not_2
  have h2q_fac_2 : (2 * q).factorization 2 = 1 := by
    rw [Nat.factorization_mul (by decide) hq.ne_zero, Finsupp.add_apply,
      Nat.prime_two.factorization_self, Nat.factorization_eq_zero_of_not_dvd hq_not_2, add_zero]
  have h2q_fac_q : (2 * q).factorization q = 1 := by
    rw [Nat.factorization_mul (by decide) hq.ne_zero, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd h2_not_q, hq.factorization_self, zero_add]
  have h2q_fac_r : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ q → (2 * q).factorization r = 0 := by
    intro r hr hr2 hrq
    rw [Nat.factorization_mul (by decide) hq.ne_zero, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (fun h =>
        hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h)),
      Nat.factorization_eq_zero_of_not_dvd (fun h =>
        hrq ((Nat.prime_dvd_prime_iff_eq hr hq).mp h)), add_zero]
  rcases h2_div with h2A | h2B <;> rcases hq_div with hqA | hqB
  · have h2B : ¬ 2 ∣ B := fun h => Nat.prime_two.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h2A h)
    have hqB : ¬ q ∣ B := fun h => hq.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hqA h)
    have h2qA : 2 * q ∣ A := h2q_cop.mul_dvd_of_dvd_of_dvd h2A hqA
    have hA_sq : IsSquare (A / (2 * q)) :=
      isSquare_div_of_coprime_two_prime_sq hA0 hB0 hV0 hq hq2 hcop heq
        (mul_ne_zero (by decide) hq.ne_zero) h2qA
        (by simp [h2A, h2q_fac_2])
        (by simp [hqA, h2q_fac_q])
        h2q_fac_r
    have hB_sq : IsSquare (B / 1) :=
      isSquare_div_of_coprime_two_prime_sq hB0 hA0 hV0 hq hq2 hcop.symm heq_sym
        one_ne_zero (one_dvd B)
        (by simp [h2B])
        (by simp [hqB])
        (fun _ _ _ _ => by simp)
    obtain ⟨u, hu⟩ := hA_sq
    obtain ⟨v, hv⟩ := hB_sq
    rw [Nat.div_one] at hv
    have hAu : A = 2 * q * u ^ 2 := by
      calc A = 2 * q * (A / (2 * q)) := (Nat.mul_div_cancel' h2qA).symm
        _ = 2 * q * u ^ 2 := by rw [hu, pow_two]
    have hBv : B = v ^ 2 := hv.trans (pow_two v).symm
    have hu0 : 0 < u := Nat.pos_of_ne_zero (fun h => by rw [h] at hAu; simp at hAu; omega)
    have hv0 : 0 < v := Nat.pos_of_ne_zero (fun h => by rw [h] at hBv; simp at hBv; omega)
    exact Or.inl ⟨u, v, hu0, hv0, hAu, hBv⟩
  · have h2B : ¬ 2 ∣ B := fun h => Nat.prime_two.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h2A h)
    have hqA : ¬ q ∣ A := fun h => hq.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h hqB)
    have hA_sq : IsSquare (A / 2) :=
      isSquare_div_of_coprime_two_prime_sq hA0 hB0 hV0 hq hq2 hcop heq
        (by decide) h2A
        (by simp [h2A, Nat.prime_two.factorization_self])
        (by simp [hqA, Nat.factorization_eq_zero_of_not_dvd h2_not_q])
        (fun r hr hr2 _ => Nat.factorization_eq_zero_of_not_dvd (fun h =>
          hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h)))
    have hB_sq : IsSquare (B / q) :=
      isSquare_div_of_coprime_two_prime_sq hB0 hA0 hV0 hq hq2 hcop.symm heq_sym
        hq.ne_zero hqB
        (by simp [h2B, Nat.factorization_eq_zero_of_not_dvd hq_not_2])
        (by simp [hqB, hq.factorization_self])
        (fun r hr _ hrq => Nat.factorization_eq_zero_of_not_dvd (fun h =>
          hrq ((Nat.prime_dvd_prime_iff_eq hr hq).mp h)))
    obtain ⟨u, hu⟩ := hA_sq
    obtain ⟨v, hv⟩ := hB_sq
    have hAu : A = 2 * u ^ 2 := by
      calc A = 2 * (A / 2) := (Nat.mul_div_cancel' h2A).symm
        _ = 2 * u ^ 2 := by rw [hu, pow_two]
    have hBv : B = q * v ^ 2 := by
      calc B = q * (B / q) := (Nat.mul_div_cancel' hqB).symm
        _ = q * v ^ 2 := by rw [hv, pow_two]
    have hu0 : 0 < u := Nat.pos_of_ne_zero (fun h => by rw [h] at hAu; simp at hAu; omega)
    have hv0 : 0 < v := Nat.pos_of_ne_zero (fun h => by rw [h] at hBv; simp at hBv; omega)
    exact Or.inr (Or.inr (Or.inl ⟨u, v, hu0, hv0, hAu, hBv⟩))
  · have h2A : ¬ 2 ∣ A := fun h => Nat.prime_two.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h h2B)
    have hqB : ¬ q ∣ B := fun h => hq.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hqA h)
    have hA_sq : IsSquare (A / q) :=
      isSquare_div_of_coprime_two_prime_sq hA0 hB0 hV0 hq hq2 hcop heq
        hq.ne_zero hqA
        (by simp [h2A, Nat.factorization_eq_zero_of_not_dvd hq_not_2])
        (by simp [hqA, hq.factorization_self])
        (fun r hr _ hrq => Nat.factorization_eq_zero_of_not_dvd (fun h =>
          hrq ((Nat.prime_dvd_prime_iff_eq hr hq).mp h)))
    have hB_sq : IsSquare (B / 2) :=
      isSquare_div_of_coprime_two_prime_sq hB0 hA0 hV0 hq hq2 hcop.symm heq_sym
        (by decide) h2B
        (by simp [h2B, Nat.prime_two.factorization_self])
        (by simp [hqB, Nat.factorization_eq_zero_of_not_dvd h2_not_q])
        (fun r hr hr2 _ => Nat.factorization_eq_zero_of_not_dvd (fun h =>
          hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h)))
    obtain ⟨u, hu⟩ := hA_sq
    obtain ⟨v, hv⟩ := hB_sq
    have hAu : A = q * u ^ 2 := by
      calc A = q * (A / q) := (Nat.mul_div_cancel' hqA).symm
        _ = q * u ^ 2 := by rw [hu, pow_two]
    have hBv : B = 2 * v ^ 2 := by
      calc B = 2 * (B / 2) := (Nat.mul_div_cancel' h2B).symm
        _ = 2 * v ^ 2 := by rw [hv, pow_two]
    have hu0 : 0 < u := Nat.pos_of_ne_zero (fun h => by rw [h] at hAu; simp at hAu; omega)
    have hv0 : 0 < v := Nat.pos_of_ne_zero (fun h => by rw [h] at hBv; simp at hBv; omega)
    exact Or.inr (Or.inr (Or.inr ⟨u, v, hu0, hv0, hAu, hBv⟩))
  · have h2A : ¬ 2 ∣ A := fun h => Nat.prime_two.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h h2B)
    have hqA : ¬ q ∣ A := fun h => hq.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h hqB)
    have h2qB : 2 * q ∣ B := h2q_cop.mul_dvd_of_dvd_of_dvd h2B hqB
    have hA_sq : IsSquare (A / 1) :=
      isSquare_div_of_coprime_two_prime_sq hA0 hB0 hV0 hq hq2 hcop heq
        one_ne_zero (one_dvd A)
        (by simp [h2A])
        (by simp [hqA])
        (fun _ _ _ _ => by simp)
    have hB_sq : IsSquare (B / (2 * q)) :=
      isSquare_div_of_coprime_two_prime_sq hB0 hA0 hV0 hq hq2 hcop.symm heq_sym
        (mul_ne_zero (by decide) hq.ne_zero) h2qB
        (by simp [h2B, h2q_fac_2])
        (by simp [hqB, h2q_fac_q])
        h2q_fac_r
    obtain ⟨u, hu⟩ := hA_sq
    obtain ⟨v, hv⟩ := hB_sq
    rw [Nat.div_one] at hu
    have hAu : A = u ^ 2 := hu.trans (pow_two u).symm
    have hBv : B = 2 * q * v ^ 2 := by
      calc B = 2 * q * (B / (2 * q)) := (Nat.mul_div_cancel' h2qB).symm
        _ = 2 * q * v ^ 2 := by rw [hv, pow_two]
    have hu0 : 0 < u := Nat.pos_of_ne_zero (fun h => by rw [h] at hAu; simp at hAu; omega)
    have hv0 : 0 < v := Nat.pos_of_ne_zero (fun h => by rw [h] at hBv; simp at hBv; omega)
    exact Or.inr (Or.inl ⟨u, v, hu0, hv0, hAu, hBv⟩)

private lemma alternating_pell_norm (B₀ : ℤ) (j : ℕ) :
    (B₀ + 1) * (alternatingPellCoordinates B₀ j).1 ^ 2 -
      B₀ * (alternatingPellCoordinates B₀ j).2 ^ 2 = 1 := by
  induction j with
  | zero => simp [alternatingPellCoordinates]
  | succ j ih =>
    simp only [alternatingPellCoordinates]
    linear_combination ih

private lemma alternating_pell_odd_pow_coords {D : ℤ} {a : Pell.Solution₁ D}
    {B₀ : ℤ} (hax : a.x = 2 * B₀ + 1) (j : ℕ) :
    (a ^ (2 * j + 1)).x + 1 = 2 * (B₀ + 1) * (alternatingPellCoordinates B₀ j).1 ^ 2 ∧
    (a ^ (2 * j + 1)).x - 1 = 2 * B₀ * (alternatingPellCoordinates B₀ j).2 ^ 2 ∧
    (a ^ (2 * j + 1)).y =
      a.y * (alternatingPellCoordinates B₀ j).1 * (alternatingPellCoordinates B₀ j).2 := by
  have h_ay : D * a.y ^ 2 = 4 * B₀ * (B₀ + 1) := by
    rw [a.prop_y, hax]
    ring
  induction j with
  | zero =>
    rw [Nat.mul_zero, zero_add, pow_one, hax]
    simp only [alternatingPellCoordinates]
    exact ⟨by ring, by ring, by ring⟩
  | succ j ih =>
    let p := a ^ (2 * j + 1)
    change p.x + 1 = 2 * (B₀ + 1) * (alternatingPellCoordinates B₀ j).1 ^ 2 ∧
      p.x - 1 = 2 * B₀ * (alternatingPellCoordinates B₀ j).2 ^ 2 ∧
      p.y = a.y * (alternatingPellCoordinates B₀ j).1 * (alternatingPellCoordinates B₀ j).2 at ih
    have hp_x : p.x =
        (B₀ + 1) * (alternatingPellCoordinates B₀ j).1 ^ 2 +
          B₀ * (alternatingPellCoordinates B₀ j).2 ^ 2 := by
      linarith [ih.1, ih.2.1]
    have haa_x : (a * a).x = 8 * B₀ ^ 2 + 8 * B₀ + 1 := by
      rw [Pell.Solution₁.x_mul, hax]
      linear_combination h_ay
    have haa_y : (a * a).y = 2 * (2 * B₀ + 1) * a.y := by
      rw [Pell.Solution₁.y_mul, hax]
      ring
    have hcross : D * (p.y * (a * a).y) =
        8 * B₀ * (B₀ + 1) * (2 * B₀ + 1) *
          (alternatingPellCoordinates B₀ j).1 * (alternatingPellCoordinates B₀ j).2 := by
      calc
        D * (p.y * (a * a).y)
            = (D * a.y ^ 2) * (2 * (2 * B₀ + 1) *
                (alternatingPellCoordinates B₀ j).1 * (alternatingPellCoordinates B₀ j).2) := by
              rw [ih.2.2, haa_y]
              ring
        _ = (4 * B₀ * (B₀ + 1)) * (2 * (2 * B₀ + 1) *
              (alternatingPellCoordinates B₀ j).1 * (alternatingPellCoordinates B₀ j).2) := by
              rw [h_ay]
        _ = _ := by ring
    rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by omega, pow_add, pow_two]
    change (p * (a * a)).x + 1 = _ ∧ (p * (a * a)).x - 1 = _ ∧ (p * (a * a)).y = _
    have h1 : (p * (a * a)).x + 1 =
        2 * (B₀ + 1) * (alternatingPellCoordinates B₀ (j + 1)).1 ^ 2 := by
      rw [Pell.Solution₁.x_mul, hp_x, haa_x, hcross]
      simp only [alternatingPellCoordinates]
      linear_combination -(alternating_pell_norm B₀ j)
    have h2 : (p * (a * a)).x - 1 =
        2 * B₀ * (alternatingPellCoordinates B₀ (j + 1)).2 ^ 2 := by
      linear_combination h1 + 2 * alternating_pell_norm B₀ (j + 1)
    have h3 : (p * (a * a)).y =
        a.y * (alternatingPellCoordinates B₀ (j + 1)).1 *
          (alternatingPellCoordinates B₀ (j + 1)).2 := by
      rw [Pell.Solution₁.y_mul, hp_x, haa_x, ih.2.2, haa_y]
      simp only [alternatingPellCoordinates]
      ring
    exact ⟨h1, h2, h3⟩

/-- On the simultaneous block equations `q + 1 = 2 * d * w ^ 2` and
`q ^ d + 1 = 2 * (d * w * z) ^ 2`, the explicit Pell solution
`hirakawaSecondBlockPell hd_odd hqd1` is fundamental in `Pell.Solution₁ (2 * q)`. -/
theorem hirakawa_pell_second_block_is_fundamental {q d w z : ℕ}
    (hq : q.Prime) (hq5 : 5 ≤ q) (hd : d.Prime) (hd_odd : Odd d)
    (hq1 : q + 1 = 2 * d * w ^ 2)
    (hqd1 : q ^ d + 1 = 2 * (d * w * z) ^ 2) :
    Pell.IsFundamental (hirakawaSecondBlockPell hd_odd hqd1) := by
  have hq2 : q ≠ 2 := by omega
  have hq_odd : Odd q := hq.odd_of_ne_two hq2
  have hD_pos : 0 < 2 * (q : ℤ) := by positivity
  have hD_nsq : ¬ IsSquare (2 * (q : ℤ)) := not_isSquare_two_mul_prime hq hq2
  obtain ⟨a₁, ha₁⟩ := Pell.IsFundamental.exists_of_not_isSquare hD_pos hD_nsq
  let sol := hirakawaSecondBlockPell hd_odd hqd1
  have hsol_x : 0 < sol.x := by change 0 < 2 * (q : ℤ) ^ d + 1; positivity
  have hsol_y : 0 ≤ sol.y := by
    change 0 ≤ 2 * (d : ℤ) * (w : ℤ) * (z : ℤ) * (q : ℤ) ^ ((d - 1) / 2)
    positivity
  obtain ⟨n, hsol_pow⟩ := ha₁.eq_pow_of_nonneg hsol_x hsol_y
  have hn0 : n ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hsol_pow
    have hx1 := congrArg Pell.Solution₁.x hsol_pow
    change 2 * (q : ℤ) ^ d + 1 = 1 at hx1
    have hqd_pos : (0 : ℤ) < (q : ℤ) ^ d := by positivity
    linarith
  have hdwz_ne : d * w * z ≠ 0 := by
    intro h0
    rw [h0] at hqd1
    simp at hqd1
  have hw_ne : w ≠ 0 := by
    intro h0
    rw [h0] at hq1
    simp at hq1
  have hn_odd : Odd n := by
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ho
    · exfalso
      have hn2m : n = 2 * m := by omega
      let b := a₁ ^ m
      have hsol_bb : sol = b * b := by
        rw [hsol_pow, hn2m, mul_comm 2 m, pow_mul, pow_two]
      have hsol_x_eq : sol.x = 2 * b.x ^ 2 - 1 := by
        have hx := congrArg Pell.Solution₁.x hsol_bb
        rw [Pell.Solution₁.x_mul] at hx
        have hby := b.prop_y
        linarith
      have hbx_sq : b.x ^ 2 = 2 * ((d : ℤ) * (w : ℤ) * (z : ℤ)) ^ 2 := by
        have hsol_def : sol.x = 2 * (q : ℤ) ^ d + 1 := rfl
        have hqd1_int : (q : ℤ) ^ d + 1 = 2 * ((d : ℤ) * (w : ℤ) * (z : ℤ)) ^ 2 := by
          exact_mod_cast hqd1
        linarith
      have hnat : 2 * (d * w * z) ^ 2 = b.x.natAbs ^ 2 := by
        have h := congrArg Int.natAbs hbx_sq
        have hcast : 2 * ((d : ℤ) * (w : ℤ) * (z : ℤ)) ^ 2 =
            ((2 * (d * w * z) ^ 2 : ℕ) : ℤ) := by
          push_cast; ring
        rw [pow_two, Int.natAbs_mul, ← pow_two, hcast, Int.natAbs_natCast] at h
        exact h.symm
      exact two_mul_sq_ne_odd_mul_sq hdwz_ne odd_one (by simpa [one_mul] using hnat)
    · exact ho
  obtain ⟨k, hk⟩ := hn_odd
  let X := a₁.x.toNat
  have hX_int : (X : ℤ) = a₁.x := Int.toNat_of_nonneg (by linarith [ha₁.1])
  have hX_gt1 : 1 < X := by
    have : (1 : ℤ) < (X : ℤ) := by rw [hX_int]; exact ha₁.1
    exact_mod_cast this
  obtain ⟨A, hX_odd⟩ : ∃ A : ℕ, X = 2 * A + 1 := by
    rcases Nat.even_or_odd X with ⟨u, hu⟩ | ⟨A, hA⟩
    · exfalso
      have hax2 : a₁.x = 2 * (u : ℤ) := by
        rw [← hX_int, hu]
        push_cast; ring
      have hprop := a₁.prop
      rw [hax2] at hprop
      have hdiv : 2 * (2 * (u : ℤ) ^ 2 - (q : ℤ) * a₁.y ^ 2) = 1 := by linarith
      omega
    · exact ⟨A, hA⟩
  let B := A + 1
  have hA_pos : 0 < A := by omega
  have hB_pos : 0 < B := by omega
  have hcopAB : Nat.Coprime A B := by
    apply Nat.coprime_of_dvd
    intro p hp hpA hpB
    exact hp.not_dvd_one ((Nat.dvd_add_right hpA).mp hpB)
  have hax_eq : a₁.x = 2 * (A : ℤ) + 1 := by
    rw [← hX_int, hX_odd]
    push_cast; ring
  let V := a₁.y.natAbs
  have hV_int : (V : ℤ) = a₁.y := Int.natAbs_of_nonneg ha₁.2.1.le
  have hV_pos : 0 < V := by
    have : (0 : ℤ) < (V : ℤ) := by rw [hV_int]; exact ha₁.2.1
    exact_mod_cast this
  have hqV2 : q * V ^ 2 = 2 * A * B := by
    have hprop := a₁.prop_y
    rw [hax_eq, ← hV_int] at hprop
    have hint : (q : ℤ) * (V : ℤ) ^ 2 = 2 * (A : ℤ) * ((A : ℤ) + 1) := by linarith
    have hint' : (q : ℤ) * (V : ℤ) ^ 2 = 2 * (A : ℤ) * (B : ℤ) := by
      have hBA : (B : ℤ) = (A : ℤ) + 1 := Nat.cast_add_one A
      rw [hBA, hint]
    exact_mod_cast hint'
  obtain ⟨V', hV'⟩ : 2 ∣ V := by
    rcases Nat.even_or_odd V with ⟨t, ht⟩ | hV_odd
    · exact ⟨t, by omega⟩
    · exfalso
      have hodd_lhs : Odd (q * V ^ 2) := hq_odd.mul (hV_odd.pow)
      rw [hqV2] at hodd_lhs
      exact (Nat.not_odd_iff_even.mpr ⟨A * B, by ring⟩) hodd_lhs
  have hV'_pos : 0 < V' := by omega
  have hAB_eq : A * B = 2 * q * V' ^ 2 := by
    apply Nat.mul_left_cancel (by decide : 0 < 2)
    calc
      2 * (A * B) = 2 * A * B := by ring
      _ = q * V ^ 2 := hqV2.symm
      _ = q * (2 * V') ^ 2 := by rw [hV']
      _ = 2 * (2 * q * V' ^ 2) := by ring
  rcases coprime_mul_eq_two_prime_sq hA_pos hB_pos hV'_pos hq hq2 hcopAB hAB_eq with
      ⟨u₀, v₀, hu₀, hv₀, hA_eq, hB_eq⟩ |
      ⟨u₀, v₀, hu₀, hv₀, hA_eq, hB_eq⟩ |
      ⟨u₀, v₀, hu₀, hv₀, hA_eq, hB_eq⟩ |
      ⟨X₀, Y₀, hX₀, hY₀, hA_eq, hB_eq⟩
  · -- Case 1: `A = 2 * q * u₀ ^ 2`, `B = v₀ ^ 2` contradicts minimality of `a₁.x`.
    have hb₀_prop : (v₀ : ℤ) ^ 2 - 2 * (q : ℤ) * (u₀ : ℤ) ^ 2 = 1 := by
      have hBA : (B : ℤ) = (A : ℤ) + 1 := Nat.cast_add_one A
      rw [hA_eq, hB_eq] at hBA
      push_cast at hBA
      linarith
    let b₀ : Pell.Solution₁ (2 * (q : ℤ)) := Pell.Solution₁.mk (v₀ : ℤ) (u₀ : ℤ) hb₀_prop
    have hv₀_gt1_nat : 1 < v₀ := by
      by_contra hle
      have hv1 : v₀ = 1 := by omega
      have hB1 : B = 1 := by rw [hB_eq, hv1]; ring
      have hBA_def : B = A + 1 := rfl
      omega
    have hv₀_gt1 : 1 < b₀.x := by
      change 1 < (v₀ : ℤ)
      exact_mod_cast hv₀_gt1_nat
    have hmin : a₁.x ≤ (v₀ : ℤ) := ha₁.2.2 hv₀_gt1
    have hax_v₀ : a₁.x = 2 * (v₀ : ℤ) ^ 2 - 1 := by
      have hB_cast : (B : ℤ) = (v₀ : ℤ) ^ 2 := by rw [hB_eq]; push_cast; ring
      have hBA : (B : ℤ) = (A : ℤ) + 1 := Nat.cast_add_one A
      linarith
    rw [hax_v₀] at hmin
    have hv₀_ge2 : (2 : ℤ) ≤ (v₀ : ℤ) := by exact_mod_cast hv₀_gt1_nat
    have hv₀_sq_ge : 2 * (v₀ : ℤ) ≤ (v₀ : ℤ) ^ 2 := by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right hv₀_ge2 (by omega)
    linarith
  · -- Case 2: `A = u₀ ^ 2`, `B = 2 * q * v₀ ^ 2` yields `sol.x = 2 * c.re ^ 2 + 1`.
    have huv_sq : (u₀ * v₀) ^ 2 = V' ^ 2 := by
      apply Nat.mul_left_cancel (by positivity : 0 < 2 * q)
      calc
        2 * q * (u₀ * v₀) ^ 2 = u₀ ^ 2 * (2 * q * v₀ ^ 2) := by ring
        _ = A * B := by rw [← hA_eq, ← hB_eq]
        _ = 2 * q * V' ^ 2 := hAB_eq
    have huv : u₀ * v₀ = V' := Nat.pow_left_injective (by decide : 2 ≠ 0) huv_sq
    have hy_eq : a₁.y = 2 * (u₀ : ℤ) * (v₀ : ℤ) := by
      rw [← hV_int, hV', ← huv]
      push_cast; ring
    have hx_eq : a₁.x = (u₀ : ℤ) ^ 2 + 2 * (q : ℤ) * (v₀ : ℤ) ^ 2 := by
      have hA_cast : (A : ℤ) = (u₀ : ℤ) ^ 2 := by rw [hA_eq]; push_cast; ring
      have hB_cast : (B : ℤ) = 2 * (q : ℤ) * (v₀ : ℤ) ^ 2 := by rw [hB_eq]; push_cast; ring
      have hBA : (B : ℤ) = (A : ℤ) + 1 := Nat.cast_add_one A
      linarith
    let c₀ : ℤ√(2 * (q : ℤ)) := ⟨(u₀ : ℤ), (v₀ : ℤ)⟩
    have hc₀_sq : c₀ ^ 2 = (a₁ : ℤ√(2 * (q : ℤ))) := by
      rw [pow_two]
      ext
      · rw [Zsqrtd.re_mul]
        change (u₀ : ℤ) * (u₀ : ℤ) + 2 * (q : ℤ) * (v₀ : ℤ) * (v₀ : ℤ) = a₁.x
        rw [hx_eq]; ring
      · rw [Zsqrtd.im_mul]
        change (u₀ : ℤ) * (v₀ : ℤ) + (v₀ : ℤ) * (u₀ : ℤ) = a₁.y
        rw [hy_eq]; ring
    have hc₀_norm : c₀.norm = -1 := by
      rw [Zsqrtd.norm_def]
      change (u₀ : ℤ) * (u₀ : ℤ) - 2 * (q : ℤ) * (v₀ : ℤ) * (v₀ : ℤ) = -1
      have hA_cast : (A : ℤ) = (u₀ : ℤ) ^ 2 := by rw [hA_eq]; push_cast; ring
      have hB_cast : (B : ℤ) = 2 * (q : ℤ) * (v₀ : ℤ) ^ 2 := by rw [hB_eq]; push_cast; ring
      have hBA : (B : ℤ) = (A : ℤ) + 1 := Nat.cast_add_one A
      linarith
    let c : ℤ√(2 * (q : ℤ)) := c₀ ^ (2 * k + 1)
    have hc_norm : c.norm = -1 := by
      change Zsqrtd.normMonoidHom (c₀ ^ (2 * k + 1)) = -1
      rw [map_pow]
      change c₀.norm ^ (2 * k + 1) = -1
      rw [hc₀_norm, (show Odd (2 * k + 1) from ⟨k, rfl⟩).neg_one_pow]
    have hsol_coe : (sol : ℤ√(2 * (q : ℤ))) = c ^ 2 := by
      rw [hsol_pow, pell_coe_pow, hk, ← hc₀_sq, ← pow_mul, mul_comm 2 (2 * k + 1), pow_mul]
    have hsol_x : sol.x = 2 * c.re ^ 2 + 1 := by
      have hre := congrArg Zsqrtd.re hsol_coe
      change sol.x = (c ^ 2).re at hre
      rw [pow_two, Zsqrtd.re_mul] at hre
      have hcn := hc_norm
      rw [Zsqrtd.norm_def] at hcn
      calc
        sol.x = c.re * c.re + 2 * (q : ℤ) * c.im * c.im := hre
        _ = 2 * c.re ^ 2 + 1 - (c.re * c.re - 2 * (q : ℤ) * c.im * c.im + 1) := by ring
        _ = 2 * c.re ^ 2 + 1 := by rw [hcn]; ring
    have hcre_sq : c.re ^ 2 = (q : ℤ) ^ d := by
      have hsol_def : sol.x = 2 * (q : ℤ) ^ d + 1 := rfl
      linarith
    have hnat : c.re.natAbs ^ 2 = q ^ d := by
      have h := congrArg Int.natAbs hcre_sq
      have hcast : (q : ℤ) ^ d = ((q ^ d : ℕ) : ℤ) := by push_cast; ring
      rw [pow_two, Int.natAbs_mul, ← pow_two, hcast, Int.natAbs_natCast] at h
      exact h
    have hc_ne : c.re.natAbs ≠ 0 := by
      intro h0
      rw [h0] at hnat
      exact (pow_ne_zero d hq.ne_zero) hnat.symm
    have hfac := congrArg (fun m : ℕ => m.factorization q) hnat
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hq.factorization_self, mul_one] at hfac
    have hd_even : Even d := ⟨c.re.natAbs.factorization q, by omega⟩
    exact False.elim ((Nat.not_even_iff_odd.mpr hd_odd) hd_even)
  · -- Case 3: `A = 2 * u₀ ^ 2`, `B = q * v₀ ^ 2` gives `2 * (d * w * z) ^ 2 = q * (v₀ * Y_k) ^ 2`.
    let B₀ : ℤ := (A : ℤ)
    have h_coords := alternating_pell_odd_pow_coords (B₀ := B₀) hax_eq k
    rw [← hk, ← hsol_pow] at h_coords
    have hB₀1 : B₀ + 1 = (q : ℤ) * (v₀ : ℤ) ^ 2 := by
      have hBA : (B : ℤ) = (A : ℤ) + 1 := Nat.cast_add_one A
      have hB_cast : (B : ℤ) = (q : ℤ) * (v₀ : ℤ) ^ 2 := by rw [hB_eq]; push_cast; ring
      dsimp [B₀]
      linarith
    have hsol_add : sol.x + 1 = 4 * ((d : ℤ) * (w : ℤ) * (z : ℤ)) ^ 2 := by
      have hsol_def : sol.x = 2 * (q : ℤ) ^ d + 1 := rfl
      have hqd1_int : (q : ℤ) ^ d + 1 = 2 * ((d : ℤ) * (w : ℤ) * (z : ℤ)) ^ 2 := by
        exact_mod_cast hqd1
      linarith
    have h_int_eq : 2 * ((d : ℤ) * (w : ℤ) * (z : ℤ)) ^ 2 =
        (q : ℤ) * ((v₀ : ℤ) * (alternatingPellCoordinates B₀ k).1) ^ 2 := by
      have h1 := h_coords.1
      rw [hB₀1, hsol_add] at h1
      have h2 : 2 * (2 * ((d : ℤ) * (w : ℤ) * (z : ℤ)) ^ 2) =
          2 * ((q : ℤ) * ((v₀ : ℤ) * (alternatingPellCoordinates B₀ k).1) ^ 2) := by
        linear_combination h1
      linarith
    have hnat : 2 * (d * w * z) ^ 2 =
        q * ((v₀ : ℤ) * (alternatingPellCoordinates B₀ k).1).natAbs ^ 2 := by
      let t : ℤ := (v₀ : ℤ) * (alternatingPellCoordinates B₀ k).1
      have ht_sq : (t ^ 2).natAbs = t.natAbs ^ 2 := by
        rw [pow_two, Int.natAbs_mul, ← pow_two]
      have h := congrArg Int.natAbs h_int_eq
      have hcast1 : 2 * ((d : ℤ) * (w : ℤ) * (z : ℤ)) ^ 2 =
          ((2 * (d * w * z) ^ 2 : ℕ) : ℤ) := by push_cast; ring
      rw [hcast1, Int.natAbs_natCast, Int.natAbs_mul, Int.natAbs_natCast] at h
      exact h.trans (congrArg (q * ·) ht_sq)
    exact False.elim (two_mul_sq_ne_odd_mul_sq hdwz_ne hq_odd hnat)
  · -- Case 4: `A = q * X₀ ^ 2`, `B = 2 * Y₀ ^ 2` forces `k = 0`, so `sol = a₁`.
    let B₀ : ℕ := A
    have hB₀_pos : 0 < B₀ := hA_pos
    have hax_B₀ : a₁.x = 2 * (B₀ : ℤ) + 1 := hax_eq
    have h_coords := alternating_pell_odd_pow_coords (B₀ := (B₀ : ℤ)) hax_B₀ k
    rw [← hk, ← hsol_pow] at h_coords
    have hsol_sub : sol.x - 1 = 2 * (q : ℤ) ^ d := by
      have hsol_def : sol.x = 2 * (q : ℤ) ^ d + 1 := rfl
      linarith
    let h := (d - 1) / 2
    have hd_eq : d = 2 * h + 1 := by
      obtain ⟨t, rfl⟩ := hd_odd
      dsimp [h]
      omega
    have hZ_gt := alternatingPellCoordinates_gt_length (x := (B₀ : ℤ))
      (by exact_mod_cast hB₀_pos) k
    let Zk : ℕ := (alternatingPellCoordinates (B₀ : ℤ) k).2.toNat
    have hZk_int : (Zk : ℤ) = (alternatingPellCoordinates (B₀ : ℤ) k).2 :=
      Int.toNat_of_nonneg (by linarith [hZ_gt.1])
    have hXZ_sq_int : ((X₀ : ℤ) * (Zk : ℤ)) ^ 2 = ((q : ℤ) ^ h) ^ 2 := by
      apply mul_left_cancel₀ (by positivity : 2 * (q : ℤ) ≠ 0)
      calc
        2 * (q : ℤ) * ((X₀ : ℤ) * (Zk : ℤ)) ^ 2
            = 2 * (B₀ : ℤ) * (alternatingPellCoordinates (B₀ : ℤ) k).2 ^ 2 := by
              rw [hZk_int]
              dsimp [B₀]
              rw [hA_eq]
              push_cast
              ring
        _ = sol.x - 1 := h_coords.2.1.symm
        _ = 2 * (q : ℤ) ^ d := hsol_sub
        _ = 2 * (q : ℤ) ^ (h * 2 + 1) := by rw [hd_eq, mul_comm 2 h]
        _ = 2 * (q : ℤ) * ((q : ℤ) ^ h) ^ 2 := by
              rw [pow_succ, pow_mul]
              ring
    have hXZ : X₀ * Zk = q ^ h := by
      have hsq_nat : (X₀ * Zk) ^ 2 = (q ^ h) ^ 2 := by exact_mod_cast hXZ_sq_int
      exact Nat.pow_left_injective (by decide : 2 ≠ 0) hsq_nat
    have hX₀_ne1 : X₀ ≠ 1 := by
      intro hX1
      rw [hX1, one_pow, mul_one] at hA_eq
      have hBY : 2 * Y₀ ^ 2 = 2 * d * w ^ 2 := by
        have hBA : B = A + 1 := rfl
        rw [hB_eq, hA_eq, hq1] at hBA
        exact hBA
      have hYw : Y₀ ^ 2 = d * w ^ 2 := by
        apply Nat.mul_left_cancel (by decide : 0 < 2)
        linarith
      have hfac := congrArg (fun m : ℕ => m.factorization d) hYw
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
        Nat.factorization_mul hd.ne_zero (pow_ne_zero 2 hw_ne), Finsupp.add_apply,
        hd.factorization_self, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hfac
      omega
    have hqB₀ : q ∣ B₀ := by
      dsimp [B₀]
      rw [hA_eq]
      exact dvd_mul_right q (X₀ ^ 2)
    have hZk_dvd_qh : Zk ∣ q ^ h := ⟨X₀, by rw [mul_comm, hXZ]⟩
    obtain ⟨m, _, hm_eq⟩ := (Nat.dvd_prime_pow hq).mp hZk_dvd_qh
    have hZk_dvd_len : Zk ∣ 2 * k + 1 := by
      rw [hm_eq]
      apply alternatingPellCoordinates_pow_dvd_length hq hq5 hqB₀ k
      rw [← hZk_int, hm_eq]
      push_cast
      exact dvd_rfl
    have hZk_le : Zk ≤ 2 * k + 1 := Nat.le_of_dvd (by omega) hZk_dvd_len
    have hk_zero : k = 0 := by
      by_contra hk0
      have hlt := hZ_gt.2 (Nat.pos_of_ne_zero hk0)
      rw [← hZk_int] at hlt
      have hlt_nat : 2 * k + 1 < Zk := by exact_mod_cast hlt
      omega
    have hn_one : n = 1 := by rw [hk, hk_zero]; ring
    rw [hn_one, pow_one] at hsol_pow
    change Pell.IsFundamental sol
    rw [hsol_pow]
    exact ha₁

/-- Concrete non-vacuity witness `(q, d, w, z) = (23, 3, 2, 13)` outside Euler's mod-16
class (`23 + 1 = 2 * 3 * 2 ^ 2`, `23 ^ 3 + 1 = 2 * (3 * 2 * 13) ^ 2`), certifying that
`(24335, 3588)` is the fundamental solution of `x ^ 2 - 46 * y ^ 2 = 1`. -/
theorem hirakawa_pell_second_block_witness_23_3 :
    Pell.IsFundamental
      (hirakawaSecondBlockPell (q := 23) (d := 3) (w := 2) (z := 13)
        (by decide) (by norm_num)) :=
  hirakawa_pell_second_block_is_fundamental
    (by norm_num) (by decide) (by norm_num) (by decide) (by norm_num) (by norm_num)

/-! ## 4. Euler Component Index Consequences -/

/-- Full fundamental-Pell and parameter-floor profile on any hypothetical odd perfect
number `N = q ^ a * m ^ 2` in the exceptional prime-times-square Euler-index branch
`sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`). -/
theorem exceptional_euler_pell_fundamental_profile {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    let d := (a + 1) / 2
    d.Prime ∧ 17 ≤ d ∧ d % 8 = 1 ∧ 193 ≤ q ∧ q % 16 = 1 ∧ 10 ^ 740 < N ∧
    Pell.IsFundamental (hirakawaNeighborPell q) ∧
    ∃ w z : ℕ, ∃ hd_odd : Odd d, ∃ hqd1 : q ^ d + 1 = 2 * (d * w * z) ^ 2,
      Odd w ∧ Odd z ∧ q + 1 = 2 * d * w ^ 2 ∧
      Pell.IsFundamental (hirakawaSecondBlockPell hd_odd hqd1) := by
  let d := (a + 1) / 2
  obtain ⟨hd_prime, hd8, hq16, _⟩ :=
    prime_mul_square_index_forces_exceptional_prime_length hN ho hq hq4 ha4 ha hqm hform
      (Or.inr hl) hi
  obtain ⟨hd17, _, hq193, _, _, _⟩ :=
    exceptional_index_parameter_floors hN ho hq hq4 ha4 ha hqm hform hl hi
  have hN740 :=
    exceptional_index_size_gt_ten_pow_740 hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨w, z, _, hw_odd, hz_odd, _, hq1, _, hqd1, _, _, _, _⟩ :=
    exceptional_euler_second_block_exact_square hN ho hq hq4 ha4 ha hqm hform hl hi
  change d.Prime at hd_prime
  change d % 8 = 1 at hd8
  change q % 16 = 1 at hq16
  change q + 1 = 2 * d * w ^ 2 at hq1
  change q ^ d + 1 = 2 * (d * w * z) ^ 2 at hqd1
  have hd_odd : Odd d := Nat.odd_iff.mpr (by omega)
  have hq5 : 5 ≤ q := by omega
  have hfund_neighbor : Pell.IsFundamental (hirakawaNeighborPell q) :=
    hirakawa_pell_fundamental_neighbor hq.pos
  have hfund_second : Pell.IsFundamental (hirakawaSecondBlockPell hd_odd hqd1) :=
    hirakawa_pell_second_block_is_fundamental hq hq5 hd_prime hd_odd hq1 hqd1
  exact ⟨hd_prime, hd17, hd8, hq193, hq16, hN740, hfund_neighbor,
    w, z, hd_odd, hqd1, hw_odd, hz_odd, hq1, hfund_second⟩

/-- Unconditional exclusion of square and prime-times-square Euler component
indices for all Euler exponents `1 < a < 33` (`a % 4 = 1`). -/
theorem euler_index_ne_prime_mul_square_of_exponent_lt_33 {N q a m : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (ha33 : a < 33) (hqm : ¬ q ∣ m)
    (hform : N = q ^ a * m ^ 2) (l t : ℕ) (hl : l = 1 ∨ l.Prime) :
    sigma 1 (m ^ 2) / q ^ a ≠ l * t ^ 2 := by
  intro hi
  rcases hl with rfl | hl
  · exact euler_index_not_square_of_exponent_gt_one hN ho hq hq4 ha4 ha hqm hform
      ⟨t, by simpa [pow_two] using hi⟩
  · obtain ⟨_, ha33_le, _, _, _, _⟩ :=
      exceptional_index_parameter_floors hN ho hq hq4 ha4 ha hqm hform hl hi
    omega

/-- Unconditional exclusion of square and prime-times-square Euler component
indices in the `gcd` convention for all Euler exponents `1 < a < 33` (`a % 4 = 1`). -/
theorem euler_gcd_index_ne_prime_mul_square_of_exponent_lt_33 {N q a m : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (ha33 : a < 33) (hqm : ¬ q ∣ m)
    (hform : N = q ^ a * m ^ 2) (l t : ℕ) (hl : l = 1 ∨ l.Prime) :
    (m ^ 2).gcd (sigma 1 (m ^ 2)) ≠ l * t ^ 2 := by
  rw [← euler_index_eq_gcd hN ho hq hq4 ha4 hqm hform]
  exact euler_index_ne_prime_mul_square_of_exponent_lt_33 hN ho hq hq4 ha4 ha ha33 hqm hform l t hl

/-- Conditional on Hirakawa's Lemma 2.5 generalized-Fermat bound restricted to the
surviving fundamental-Pell regime (`193 ≤ q`, `q % 16 = 1`, `d.Prime`, `17 ≤ d`,
`d % 8 = 1`), no odd perfect number with Euler exponent `a > 1` can have Euler
component index equal to a square or a prime times a square. -/
theorem hirakawa_euler_index_ne_prime_mul_square_of_ivorra_bennett_skinner
    (hFermat : ∀ q d y : ℕ,
      q.Prime → 193 ≤ q → q % 16 = 1 → d.Prime → 17 ≤ d → d % 8 = 1 → q ^ d + 1 ≠ 2 * y ^ 2)
    {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (l t : ℕ) (hl : l = 1 ∨ l.Prime) :
    sigma 1 (m ^ 2) / q ^ a ≠ l * t ^ 2 := by
  intro hi
  rcases hl with rfl | hl
  · exact euler_index_not_square_of_exponent_gt_one hN ho hq hq4 ha4 ha hqm hform
      ⟨t, by simpa [pow_two] using hi⟩
  · obtain ⟨hd_prime, hd17, hd8, hq193, hq16, _, _, w, z, _, hqd1, _⟩ :=
      exceptional_euler_pell_fundamental_profile hN ho hq hq4 ha4 ha hqm hform hl hi
    exact hFermat q ((a + 1) / 2) (((a + 1) / 2) * w * z)
      hq hq193 hq16 hd_prime hd17 hd8 hqd1

/-- `gcd`-convention corollary of
`hirakawa_euler_index_ne_prime_mul_square_of_ivorra_bennett_skinner`. -/
theorem hirakawa_euler_gcd_index_ne_prime_mul_square_of_ivorra_bennett_skinner
    (hFermat : ∀ q d y : ℕ,
      q.Prime → 193 ≤ q → q % 16 = 1 → d.Prime → 17 ≤ d → d % 8 = 1 → q ^ d + 1 ≠ 2 * y ^ 2)
    {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (l t : ℕ) (hl : l = 1 ∨ l.Prime) :
    (m ^ 2).gcd (sigma 1 (m ^ 2)) ≠ l * t ^ 2 := by
  rw [← euler_index_eq_gcd hN ho hq hq4 ha4 hqm hform]
  exact hirakawa_euler_index_ne_prime_mul_square_of_ivorra_bennett_skinner
    hFermat hN ho hq hq4 ha4 ha hqm hform l t hl

end OddPerfect
