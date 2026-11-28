module

public import OddPerfect.PadicPadeExactSqrtTwoRatio
public import OddPerfect.PadicPadeSublinearRepunitBounds
public import OddPerfect.GlobalObstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fifth-Order `47321 / 8119` Pell–Padé Contraction & `(10 ^ 1000) ^ 6` Margin (`OddPerfect.PadicPade8119HigherContraction`)

Formalizes the fifth-order Pell–Padé contraction (`47321 / 8119`, from the `(8119, 5741)` Pell
convergent) for `3 ≤ p` and `5 ≤ u`, sharpened repunit slopes across `r ∈ {5, 7, 11, 13}`, and
the `(10 ^ 1000) ^ 6` (`10 ^ 6000`) global margin on every even prime-power component index
`componentIndex N r₀ = p ^ j`:

1. `padeSeq_sharpened_47321_8119_contraction`:
   For `3 ≤ p` and `5 ≤ u`:
   - `8119 * padeSeqA u p ≤ 5741 * padeSeqB u p`
   - `8119 * padeSeqB (u + 1) p < 47321 * (p : ℤ) * padeSeqB u p`
   - `8119 ^ (u - 5) * padeSeqB u p < 8119 * 47321 ^ (u - 5) * (p : ℤ) ^ u`
2. `sharpened_repunit_slopes_of_47321_8119_cap`:
   Direct `(47321 / 8119)` repunit-length slope bounds across `r ∈ {5, 7, 11, 13}` from
   `8119 ^ (u - 5) * r ^ (l - 1) < 8119 * 47321 ^ (u - 5)`.
3. `even_prime_power_47321_8119_and_ten_pow_6000_profile`:
   Global `componentIndex N r₀ = p ^ j` wrapper yielding `(10 ^ 1000) ^ 6 * p * k_pade.natAbs < 6 ^ u`
   and sharpened trillion-scale repunit gaps across `r ∈ {5, 7, 11, 13}`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma odd_prime_ge_three_8119 {p : ℕ} (hp : p.Prime) (hpo : Odd p) : 3 ≤ p := by
  have h2 : 2 ≤ p := hp.two_le
  rcases eq_or_lt_of_le h2 with rfl | hlt
  · exact absurd hpo (by decide)
  · exact hlt

private lemma eight_thousand_one_hundred_nineteen_mul_padeSeqA_le_5741_mul_padeSeqB
    {p u : ℕ} (hp3 : 3 ≤ p) (hu : 5 ≤ u) :
    8119 * padeSeqA u p ≤ 5741 * padeSeqB u p := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, u = 5 + k := ⟨u - 5, by omega⟩
  have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
  induction k with
  | zero =>
      set t : ℤ := (p : ℤ) - 3
      have ht : 0 ≤ t := by dsimp [t]; linarith
      have hid :
          5741 * padeSeqB (5 + 0) p - 8119 * padeSeqA (5 + 0) p =
            23305584 * t ^ 4 + 150829632 * t ^ 3 + 362096288 * t ^ 2 +
              381742656 * t + 148931440 := by
        dsimp [t, padeSeqA, padeSeqB, padeSeqPair]
        ring
      have hpos :
          0 ≤ 23305584 * t ^ 4 + 150829632 * t ^ 3 + 362096288 * t ^ 2 +
            381742656 * t + 148931440 := by
        positivity
      linarith
  | succ k ih =>
      have hk5 : 5 ≤ 5 + k := by omega
      have ihk := ih hk5
      obtain ⟨ha, hb⟩ := padeSeq_one_le hp3 (5 + k)
      have hid :
          8119 * (5741 * padeSeqB (5 + k + 1) p - 8119 * padeSeqA (5 + k + 1) p) =
            1393 * (p : ℤ) * (5741 * padeSeqB (5 + k) p - 8119 * padeSeqA (5 + k) p) +
              (2 * (p : ℤ) + 77227928) * padeSeqB (5 + k) p + 77227928 * padeSeqA (5 + k) p := by
        simp only [padeSeqA_succ, padeSeqB_succ]
        ring
      have hdiff : 0 ≤ 5741 * padeSeqB (5 + k) p - 8119 * padeSeqA (5 + k) p := by linarith
      have ht1 :
          0 ≤ 1393 * (p : ℤ) * (5741 * padeSeqB (5 + k) p - 8119 * padeSeqA (5 + k) p) :=
        mul_nonneg (by positivity) hdiff
      have ht2 : 0 < (2 * (p : ℤ) + 77227928) * padeSeqB (5 + k) p :=
        mul_pos (by linarith) (by linarith)
      have hpos : 0 < 8119 * (5741 * padeSeqB (5 + k + 1) p - 8119 * padeSeqA (5 + k + 1) p) := by
        linarith
      rw [← Nat.add_assoc]
      linarith

private lemma eight_thousand_one_hundred_nineteen_mul_padeSeqB_succ_lt_47321_mul
    {p u : ℕ} (hp3 : 3 ≤ p) (hu : 5 ≤ u) :
    8119 * padeSeqB (u + 1) p < 47321 * (p : ℤ) * padeSeqB u p := by
  have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
  obtain ⟨_, hb⟩ := padeSeq_one_le hp3 u
  have h8119_5741 :=
    eight_thousand_one_hundred_nineteen_mul_padeSeqA_le_5741_mul_padeSeqB hp3 hu
  have hstep :
      4 * ((p : ℤ) - 1) * (8119 * padeSeqA u p) + 8119 * (3 * (p : ℤ) - 4) * padeSeqB u p ≤
        4 * ((p : ℤ) - 1) * (5741 * padeSeqB u p) +
          8119 * (3 * (p : ℤ) - 4) * padeSeqB u p := by
    have hmul :
        4 * ((p : ℤ) - 1) * (8119 * padeSeqA u p) ≤
          4 * ((p : ℤ) - 1) * (5741 * padeSeqB u p) :=
      mul_le_mul_of_nonneg_left h8119_5741 (by linarith)
    linarith
  have hid1 :
      8119 * padeSeqB (u + 1) p =
        4 * ((p : ℤ) - 1) * (8119 * padeSeqA u p) + 8119 * (3 * (p : ℤ) - 4) * padeSeqB u p := by
    rw [padeSeqB_succ]
    ring
  have hid2 :
      4 * ((p : ℤ) - 1) * (5741 * padeSeqB u p) + 8119 * (3 * (p : ℤ) - 4) * padeSeqB u p =
        47321 * (p : ℤ) * padeSeqB u p - 55440 * padeSeqB u p := by
    ring
  linarith

private lemma eight_thousand_one_hundred_nineteen_pow_mul_padeSeqB_lt_47321_pow
    {p u : ℕ} (hp3 : 3 ≤ p) (hu : 5 ≤ u) :
    8119 ^ (u - 5) * padeSeqB u p < 8119 * 47321 ^ (u - 5) * (p : ℤ) ^ u := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, u = 5 + k := ⟨u - 5, by omega⟩
  have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
  induction k with
  | zero =>
      simp only [Nat.add_zero, Nat.sub_self, pow_zero, one_mul, mul_one]
      set t : ℤ := (p : ℤ) - 3
      have ht : 0 ≤ t := by dsimp [t]; linarith
      have hid :
          8119 * (p : ℤ) ^ 5 - padeSeqB 5 p =
            55032 * t ^ 4 + 513120 * t ^ 3 + 1840912 * t ^ 2 + 3007712 * t + 1884344 := by
        dsimp [t, padeSeqA, padeSeqB, padeSeqPair]
        ring
      have hpos :
          0 < 55032 * t ^ 4 + 513120 * t ^ 3 + 1840912 * t ^ 2 + 3007712 * t + 1884344 := by
        positivity
      linarith
  | succ k ih =>
      have hk5 : 5 ≤ 5 + k := by omega
      have ihk := ih hk5
      have hstep :=
        eight_thousand_one_hundred_nineteen_mul_padeSeqB_succ_lt_47321_mul hp3 hk5
      have h8119_pos : (0 : ℤ) < (8119 : ℤ) ^ (5 + k - 5) := by positivity
      have hp_pos : (0 : ℤ) < (p : ℤ) := by linarith
      have h1 :
          (8119 : ℤ) ^ (5 + k - 5) * (8119 * padeSeqB (5 + k + 1) p) <
            (8119 : ℤ) ^ (5 + k - 5) * (47321 * (p : ℤ) * padeSeqB (5 + k) p) :=
        mul_lt_mul_of_pos_left hstep h8119_pos
      have h2 :
          47321 * (p : ℤ) * ((8119 : ℤ) ^ (5 + k - 5) * padeSeqB (5 + k) p) <
            47321 * (p : ℤ) * (8119 * 47321 ^ (5 + k - 5) * (p : ℤ) ^ (5 + k)) :=
        mul_lt_mul_of_pos_left ihk (by positivity)
      have hrewL :
          (8119 : ℤ) ^ (5 + (k + 1) - 5) * padeSeqB (5 + (k + 1)) p =
            (8119 : ℤ) ^ (5 + k - 5) * (8119 * padeSeqB (5 + k + 1) p) := by
        rw [show 5 + (k + 1) - 5 = (5 + k - 5) + 1 by omega, pow_succ]
        rw [show 5 + (k + 1) = 5 + k + 1 by omega]
        ring
      have hrewM :
          (8119 : ℤ) ^ (5 + k - 5) * (47321 * (p : ℤ) * padeSeqB (5 + k) p) =
            47321 * (p : ℤ) * ((8119 : ℤ) ^ (5 + k - 5) * padeSeqB (5 + k) p) := by
        ring
      have hrewR :
          47321 * (p : ℤ) * (8119 * 47321 ^ (5 + k - 5) * (p : ℤ) ^ (5 + k)) =
            8119 * 47321 ^ (5 + (k + 1) - 5) * (p : ℤ) ^ (5 + (k + 1)) := by
        rw [show 5 + (k + 1) - 5 = (5 + k - 5) + 1 by omega, pow_succ]
        rw [show 5 + (k + 1) = (5 + k) + 1 by omega, pow_succ]
        ring
      linarith

/-- Bundled `47321 / 8119` fifth-order sharpened Pell–Padé contraction for `3 ≤ p` and `5 ≤ u`. -/
theorem padeSeq_sharpened_47321_8119_contraction {p u : ℕ} (hp3 : 3 ≤ p) (hu : 5 ≤ u) :
    (8119 * padeSeqA u p ≤ 5741 * padeSeqB u p) ∧
    (8119 * padeSeqB (u + 1) p < 47321 * (p : ℤ) * padeSeqB u p) ∧
    (8119 ^ (u - 5) * padeSeqB u p < 8119 * 47321 ^ (u - 5) * (p : ℤ) ^ u) :=
  ⟨eight_thousand_one_hundred_nineteen_mul_padeSeqA_le_5741_mul_padeSeqB hp3 hu,
   eight_thousand_one_hundred_nineteen_mul_padeSeqB_succ_lt_47321_mul hp3 hu,
   eight_thousand_one_hundred_nineteen_pow_mul_padeSeqB_lt_47321_pow hp3 hu⟩

private lemma sublinear_repunit_exp_step_8119 {r r_min l u A B C : ℕ}
    (hr_min : 1 < r_min) (hr_le : r_min ≤ r) (_hu : 5 ≤ u) (hA : 0 < A)
    (hcap : 8119 ^ (u - 5) * r ^ (l - 1) < 8119 * 47321 ^ (u - 5))
    (h47321 : 47321 ^ A ≤ 8119 ^ A * r_min ^ B)
    (h8119 : 8119 ^ A < r_min ^ C) :
    A * (l - 1) < C + B * (u - 5) := by
  have hpow_min : 8119 ^ (u - 5) * r_min ^ (l - 1) < 8119 * 47321 ^ (u - 5) :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hr_le (l - 1))) hcap
  have hpowA : (8119 ^ (u - 5) * r_min ^ (l - 1)) ^ A < (8119 * 47321 ^ (u - 5)) ^ A :=
    Nat.pow_lt_pow_left hpow_min hA.ne'
  have h47321_pow :
      (47321 ^ A) ^ (u - 5) ≤ (8119 ^ (u - 5)) ^ A * r_min ^ (B * (u - 5)) := by
    calc
      (47321 ^ A) ^ (u - 5) ≤ (8119 ^ A * r_min ^ B) ^ (u - 5) :=
          Nat.pow_le_pow_left h47321 (u - 5)
      _ = (8119 ^ A) ^ (u - 5) * (r_min ^ B) ^ (u - 5) := by rw [mul_pow]
      _ = (8119 ^ (u - 5)) ^ A * r_min ^ (B * (u - 5)) := by
          rw [pow_right_comm 8119 A (u - 5), ← pow_mul r_min B (u - 5)]
  have hchain :
      (8119 ^ (u - 5)) ^ A * r_min ^ (A * (l - 1)) <
        (8119 ^ (u - 5)) ^ A * r_min ^ (C + B * (u - 5)) := by
    calc
      (8119 ^ (u - 5)) ^ A * r_min ^ (A * (l - 1))
          = (8119 ^ (u - 5) * r_min ^ (l - 1)) ^ A := by
              rw [mul_pow, ← pow_mul r_min (l - 1) A, mul_comm (l - 1) A]
      _ < (8119 * 47321 ^ (u - 5)) ^ A := hpowA
      _ = 8119 ^ A * (47321 ^ A) ^ (u - 5) := by rw [mul_pow, pow_right_comm]
      _ ≤ 8119 ^ A * ((8119 ^ (u - 5)) ^ A * r_min ^ (B * (u - 5))) :=
          Nat.mul_le_mul_left _ h47321_pow
      _ = (8119 ^ (u - 5)) ^ A * (8119 ^ A * r_min ^ (B * (u - 5))) := by ring
      _ < (8119 ^ (u - 5)) ^ A * (r_min ^ C * r_min ^ (B * (u - 5))) := by
          apply Nat.mul_lt_mul_of_pos_left
          · exact Nat.mul_lt_mul_of_pos_right h8119 (by positivity)
          · positivity
      _ = (8119 ^ (u - 5)) ^ A * r_min ^ (C + B * (u - 5)) := by rw [← pow_add]
  have hpow_lt : r_min ^ (A * (l - 1)) < r_min ^ (C + B * (u - 5)) :=
    Nat.lt_of_mul_lt_mul_left hchain
  exact (Nat.pow_lt_pow_iff_right hr_min).mp hpow_lt

/-- Direct `(47321 / 8119)` sharpened repunit-length slope bounds across `r ∈ {5, 7, 11, 13}` from
`8119 ^ (u - 5) * r ^ (l - 1) < 8119 * 47321 ^ (u - 5)` for `1154 ≤ u` and `2 < l`. -/
theorem sharpened_repunit_slopes_of_47321_8119_cap {r l u : ℕ}
    (hu : 1154 ≤ u) (_hl : 2 < l)
    (hcap : 8119 ^ (u - 5) * r ^ (l - 1) < 8119 * 47321 ^ (u - 5)) :
    (r ∈ ({5, 7, 11, 13} : Finset ℕ) → 10 * l ≤ 11 * u + 10) ∧
    (r ∈ ({7, 11, 13} : Finset ℕ) → 32 * l ≤ 29 * u + 35 ∧ l + 107 ≤ u) ∧
    (r ∈ ({11, 13} : Finset ℕ) → 19 * l ≤ 14 * u + 20 ∧ l + 302 ≤ u) ∧
    (r = 13 → 13 * l ≤ 9 * u + 13 ∧ l + 354 ≤ u) := by
  have h5 : r ∈ ({5, 7, 11, 13} : Finset ℕ) → 10 * l ≤ 11 * u + 10 := by
    intro hr5
    have hr_ge : 5 ≤ r := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr5
      rcases hr5 with rfl | rfl | rfl | rfl <;> decide
    have hlt := sublinear_repunit_exp_step_8119 (r_min := 5) (A := 10) (B := 11) (C := 56)
      (by decide) hr_ge (by omega) (by decide) hcap (by norm_num) (by norm_num)
    omega
  have h7 : r ∈ ({7, 11, 13} : Finset ℕ) → 32 * l ≤ 29 * u + 35 ∧ l + 107 ≤ u := by
    intro hr7
    have hr_ge : 7 ≤ r := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr7
      rcases hr7 with rfl | rfl | rfl <;> decide
    have hlt := sublinear_repunit_exp_step_8119 (r_min := 7) (A := 32) (B := 29) (C := 149)
      (by decide) hr_ge (by omega) (by decide) hcap (by norm_num) (by norm_num)
    omega
  have h11 : r ∈ ({11, 13} : Finset ℕ) → 19 * l ≤ 14 * u + 20 ∧ l + 302 ≤ u := by
    intro hr11
    have hr_ge : 11 ≤ r := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr11
      rcases hr11 with rfl | rfl <;> decide
    have hlt := sublinear_repunit_exp_step_8119 (r_min := 11) (A := 19) (B := 14) (C := 72)
      (by decide) hr_ge (by omega) (by decide) hcap (by norm_num) (by norm_num)
    omega
  have h13 : r = 13 → 13 * l ≤ 9 * u + 13 ∧ l + 354 ≤ u := by
    intro hr13
    subst hr13
    have hlt := sublinear_repunit_exp_step_8119 (r_min := 13) (A := 13) (B := 9) (C := 46)
      (by decide) le_rfl (by omega) (by decide) hcap (by norm_num) (by norm_num)
    omega
  exact ⟨h5, h7, h11, h13⟩

private lemma ten_pow_6000_lt_six_pow_of_floor {u : ℕ} (hu : 500005 ≤ u) :
    (10 ^ 1000) ^ 6 * (8119 * 47321 ^ (u - 5)) < 8119 ^ (u - 5) * 6 ^ u := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, u = 500005 + k := ⟨u - 500005, by omega⟩
  induction k with
  | zero =>
      have h48 : 4 * 47321 ^ 48 < 48714 ^ 48 := by norm_num
      have h2400 : 4 ^ 50 * (47321 ^ 48) ^ 50 < (48714 ^ 48) ^ 50 := by
        rw [← mul_pow]
        exact Nat.pow_lt_pow_left h48 (by decide)
      have h492000 :
          (4 ^ 50) ^ 205 * ((47321 ^ 48) ^ 50) ^ 205 < ((48714 ^ 48) ^ 50) ^ 205 := by
        rw [← mul_pow]
        exact Nat.pow_lt_pow_left h2400 (by decide)
      have h8000 : ((47321 ^ 100) ^ 8) ^ 10 ≤ ((48714 ^ 100) ^ 8) ^ 10 := by
        have hle : (47321 : ℕ) ≤ 48714 := by decide
        exact Nat.pow_le_pow_left
          (Nat.pow_le_pow_left (Nat.pow_le_pow_left hle 100) 8) 10
      have hpow_47321 :
          47321 ^ (500005 + 0 - 5) =
            ((47321 ^ 48) ^ 50) ^ 205 * ((47321 ^ 100) ^ 8) ^ 10 := by
        rw [show 500005 + 0 - 5 = (48 * 50) * 205 + (100 * 8) * 10 by omega, pow_add,
          pow_mul, pow_mul, pow_mul, pow_mul]
      have hpow_48714 :
          8119 ^ (500005 + 0 - 5) * 6 ^ (500005 + 0) =
            6 ^ 5 * (((48714 ^ 48) ^ 50) ^ 205 * ((48714 ^ 100) ^ 8) ^ 10) := by
        have h48714 : (48714 : ℕ) = 8119 * 6 := by decide
        have hexp :
            (8119 * 6) ^ (500005 + 0 - 5) =
              ((48714 ^ 48) ^ 50) ^ 205 * ((48714 ^ 100) ^ 8) ^ 10 := by
          rw [← h48714, show 500005 + 0 - 5 = (48 * 50) * 205 + (100 * 8) * 10 by omega,
            pow_add, pow_mul, pow_mul, pow_mul, pow_mul]
        rw [show 500005 + 0 = 5 + (500005 + 0 - 5) by omega, pow_add, mul_left_comm,
          ← mul_pow, hexp]
      have h10_30 : 10 ^ 30 < 4 ^ 50 := by norm_num
      have h10_6000 : (10 ^ 1000) ^ 6 < (4 ^ 50) ^ 200 := by
        calc
          (10 ^ 1000) ^ 6 = (10 ^ 30) ^ 200 := by rw [← pow_mul, ← pow_mul]
          _ < (4 ^ 50) ^ 200 := Nat.pow_lt_pow_left h10_30 (by decide)
      have h8119_lt : 8119 < 6 ^ 5 * (4 ^ 50) ^ 5 := by
        have h1 : 8119 < 6 ^ 5 * 4 := by norm_num
        have h2 : 4 ≤ (4 ^ 50) ^ 5 := by
          calc
            4 = 4 ^ 1 := by decide
            _ ≤ 4 ^ 250 := Nat.pow_le_pow_right (by decide) (by decide)
            _ = (4 ^ 50) ^ 5 := by rw [← pow_mul]
        exact lt_of_lt_of_le h1 (Nat.mul_le_mul_left _ h2)
      have hcoeff : (10 ^ 1000) ^ 6 * 8119 < 6 ^ 5 * (4 ^ 50) ^ 205 := by
        calc
          (10 ^ 1000) ^ 6 * 8119
              < (4 ^ 50) ^ 200 * (6 ^ 5 * (4 ^ 50) ^ 5) :=
                  Nat.mul_lt_mul'' h10_6000 h8119_lt
          _ = 6 ^ 5 * ((4 ^ 50) ^ 200 * (4 ^ 50) ^ 5) := by rw [mul_left_comm]
          _ = 6 ^ 5 * (4 ^ 50) ^ 205 := by rw [← pow_add]
      calc
        (10 ^ 1000) ^ 6 * (8119 * 47321 ^ (500005 + 0 - 5))
            = ((10 ^ 1000) ^ 6 * 8119) *
                (((47321 ^ 48) ^ 50) ^ 205 * ((47321 ^ 100) ^ 8) ^ 10) := by
                rw [hpow_47321, mul_assoc]
        _ < (6 ^ 5 * (4 ^ 50) ^ 205) *
              (((47321 ^ 48) ^ 50) ^ 205 * ((47321 ^ 100) ^ 8) ^ 10) :=
            Nat.mul_lt_mul_of_pos_right hcoeff (by positivity)
        _ = 6 ^ 5 * ((4 ^ 50) ^ 205 * ((47321 ^ 48) ^ 50) ^ 205) *
              ((47321 ^ 100) ^ 8) ^ 10 := by
            simp only [mul_assoc]
        _ < 6 ^ 5 * ((48714 ^ 48) ^ 50) ^ 205 * ((47321 ^ 100) ^ 8) ^ 10 := by
            apply Nat.mul_lt_mul_of_pos_right _ (by positivity)
            exact Nat.mul_lt_mul_of_pos_left h492000 (by decide)
        _ ≤ 6 ^ 5 * ((48714 ^ 48) ^ 50) ^ 205 * ((48714 ^ 100) ^ 8) ^ 10 :=
            Nat.mul_le_mul_left _ h8000
        _ = 6 ^ 5 * (((48714 ^ 48) ^ 50) ^ 205 * ((48714 ^ 100) ^ 8) ^ 10) := by rw [mul_assoc]
        _ = 8119 ^ (500005 + 0 - 5) * 6 ^ (500005 + 0) := hpow_48714.symm
  | succ k ih =>
      have hk : 500005 ≤ 500005 + k := by omega
      have ihk := ih hk
      have hmul :
          47321 * ((10 ^ 1000) ^ 6 * (8119 * 47321 ^ (500005 + k - 5))) <
            47321 * (8119 ^ (500005 + k - 5) * 6 ^ (500005 + k)) :=
        Nat.mul_lt_mul_of_pos_left ihk (by decide)
      have h47321_lt :
          47321 * (8119 ^ (500005 + k - 5) * 6 ^ (500005 + k)) <
            (8119 * 6) * (8119 ^ (500005 + k - 5) * 6 ^ (500005 + k)) := by
        apply Nat.mul_lt_mul_of_pos_right (by decide : 47321 < 8119 * 6)
        positivity
      have hrewL :
          (10 ^ 1000) ^ 6 * (8119 * 47321 ^ (500005 + (k + 1) - 5)) =
            47321 * ((10 ^ 1000) ^ 6 * (8119 * 47321 ^ (500005 + k - 5))) := by
        rw [show 500005 + (k + 1) - 5 = (500005 + k - 5) + 1 by omega, pow_succ' 47321,
          mul_left_comm 8119 47321, mul_left_comm ((10 ^ 1000) ^ 6) 47321]
      have hrewR :
          (8119 * 6) * (8119 ^ (500005 + k - 5) * 6 ^ (500005 + k)) =
            8119 ^ (500005 + (k + 1) - 5) * 6 ^ (500005 + (k + 1)) := by
        rw [show 500005 + (k + 1) - 5 = (500005 + k - 5) + 1 by omega,
          show 500005 + (k + 1) = (500005 + k) + 1 by omega, pow_succ' 8119, pow_succ' 6,
          mul_mul_mul_comm]
      calc
        (10 ^ 1000) ^ 6 * (8119 * 47321 ^ (500005 + (k + 1) - 5))
            = 47321 * ((10 ^ 1000) ^ 6 * (8119 * 47321 ^ (500005 + k - 5))) := hrewL
        _ < 47321 * (8119 ^ (500005 + k - 5) * 6 ^ (500005 + k)) := hmul
        _ < (8119 * 6) * (8119 ^ (500005 + k - 5) * 6 ^ (500005 + k)) := h47321_lt
        _ = 8119 ^ (500005 + (k + 1) - 5) * 6 ^ (500005 + (k + 1)) := hrewR

private lemma gap7_tridecuple_8119 {l u : ℕ} (hu : 6541380665835014 ≤ u)
    (hlin : 32 * l ≤ 29 * u + 35) : l + 613254000000000 ≤ u := by omega

private lemma gap11_tridecuple_8119 {l u : ℕ} (hu : 6541380665835014 ≤ u)
    (hlin : 19 * l ≤ 14 * u + 20) : l + 1721415000000000 ≤ u := by omega

private lemma gap13_tridecuple_8119 {l u : ℕ} (hu : 6541380665835014 ≤ u)
    (hlin : 13 * l ≤ 9 * u + 13) : l + 2012732000000000 ≤ u := by omega

/-- Global `componentIndex N r₀ = p ^ j` profile coupling the tridecuple floor
`6541380665835014 ≤ u` with the fifth-order `47321 / 8119` Padé contraction, yielding
`(10 ^ 1000) ^ 6 * p * k_pade.natAbs < 6 ^ u` and sharpened repunit slopes and trillion-scale
additive gaps across `r ∈ {5, 7, 11, 13}`. -/
theorem even_prime_power_47321_8119_and_ten_pow_6000_profile {N r₀ p j : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hr₀ : r₀ ∈ N.primeFactors)
    (hp : p.Prime) (hj_pos : 0 < j) (hj_even : Even j)
    (hidx : componentIndex N r₀ = p ^ j) :
    ∃ q s u r l : ℕ,
      let k_pade : ℤ := ((s : ℤ) * padeSeqB u p - padeSeqA u p) / (p : ℤ) ^ (2 * u + 1)
      r₀ = q ∧ q.Prime ∧ q % 4 = 1 ∧ N.factorization q = 1 ∧ Odd s ∧
      j = 2 * u ∧ 6541380665835014 ≤ u ∧
      sigma 1 (p ^ (2 * u)) = q ∧ q + 1 = 2 * s ^ 2 ∧ sigma 1 (s ^ 2) = p ^ (2 * u) ∧
      1 ≤ k_pade ∧
      8119 ^ (u - 5) * (p * k_pade.natAbs) < 8119 * 47321 ^ (u - 5) ∧
      (10 ^ 1000) ^ 6 * p * k_pade.natAbs < 6 ^ u ∧
      ((p % 4 = 3 ∨ Even u) → 2 * (10 ^ 1000) ^ 6 * p < 6 ^ u) ∧
      (p ∣ 64 ^ u - 1 → (10 ^ 1000) ^ 6 * p ^ 2 < 6 ^ u) ∧
      ((2 * u + 1) ∣ p - 2 → (10 ^ 1000) ^ 6 * u * p < 6 ^ u) ∧
      r ∈ ({3, 5, 7, 11, 13} : Finset ℕ) ∧ r.Prime ∧ 2 < l ∧ l.Prime ∧
      r ^ 2 ∣ N ∧ geometricBlock r l = p ∧
      (r ∈ ({5, 7, 11, 13} : Finset ℕ) → 10 * l ≤ 11 * u + 10) ∧
      (r ∈ ({7, 11, 13} : Finset ℕ) → 32 * l ≤ 29 * u + 35 ∧ l + 613254000000000 ≤ u) ∧
      (r ∈ ({11, 13} : Finset ℕ) → 19 * l ≤ 14 * u + 20 ∧ l + 1721415000000000 ≤ u) ∧
      (r = 13 → 13 * l ≤ 9 * u + 13 ∧ l + 2012732000000000 ≤ u) := by
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀
  have ha : 0 < N.factorization r₀ :=
    Nat.Prime.factorization_pos_of_dvd hr₀_prime hN.2.ne' (Nat.dvd_of_mem_primeFactors hr₀)
  have hNb : N = r₀ ^ N.factorization r₀ * ordCompl[r₀] N :=
    (Nat.ordProj_mul_ordCompl_eq_self N r₀).symm
  have hr₀b : ¬ r₀ ∣ ordCompl[r₀] N := Nat.not_dvd_ordCompl hr₀_prime hN.2.ne'
  obtain ⟨i, _, hl, hr, _⟩ := exists_component_index hN hr₀_prime hNb hr₀b
  have hci : componentIndex N r₀ = i := by
    rw [componentIndex, hl]
    exact Nat.mul_div_cancel_left i (pow_pos hr₀_prime.pos _)
  obtain ⟨u, hu_eq⟩ := hj_even
  have hj_eq : j = 2 * u := by omega
  have hu : 0 < u := by omega
  have hi : i = p ^ (2 * u) := by rw [← hci, hidx, hj_eq]
  obtain ⟨ha1, hσq⟩ :=
    even_prime_power_index_eq_selected_sigma hN ho hr₀_prime ha hNb hr₀b hl hr hp hu hi
  have hbo := ho.of_dvd_nat (hNb ▸ dvd_mul_left _ _)
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h4 : 4 ∣ 2 * ordCompl[r₀] N :=
      hr ▸ hi ▸ (pow_dvd_pow 2 (by omega : 2 ≤ 2 * u)).trans (dvd_mul_left _ _)
    have := hbo.not_two_dvd_nat
    omega
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := odd_prime_ge_three_8119 hp hpo
  obtain ⟨m, hr₀4, _, _, hm_sq⟩ :=
    euler_form_of_odd_component_index hN ho hr₀_prime ha hNb hr₀b hl hr (hi ▸ hpo.pow)
  have hm_dvd_N : m ∣ N := by
    rw [hNb, hm_sq]
    exact dvd_mul_of_dvd_right (dvd_pow_self m (by decide : 2 ≠ 0)) _
  have hmo : Odd m := ho.of_dvd_nat hm_dvd_N
  have hl' := hl
  have hr' := hr
  rw [hm_sq, ha1, pow_one, hi] at hl' hr'
  obtain ⟨s, hs, _, _, _, hplus, hσs⟩ :=
    even_prime_power_cofactor_split hr₀_prime hp hmo hpo hu hl' hr'
  obtain ⟨hu_ge, _, _, _, r, hr_mem, hr2_N, l, hl_prime, hl_gt2, hgb, _⟩ :=
    even_prime_power_tridecuple_sublinear_repunit_profile
      hN ho hr₀_prime ha hNb hr₀b hl hr hp hu hi
  have hr_prime : r.Prime := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr_mem
    rcases hr_mem with rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨_, hk1, _, _, _⟩ :=
    even_index_pade_quotient_pos_and_quadratic_identity hp hpo hs hu hσq hplus hσs
  obtain ⟨_, hpu1_k, _, _⟩ :=
    even_index_pade_quotient_weighted_contraction hp hpo hs hu hσq hplus hσs
  set k_pade : ℤ := ((s : ℤ) * padeSeqB u p - padeSeqA u p) / (p : ℤ) ^ (2 * u + 1)
  change 1 ≤ k_pade at hk1
  change (p : ℤ) ^ (u + 1) * k_pade < padeSeqB u p at hpu1_k
  have hu5 : 5 ≤ u := by omega
  have hu1154 : 1154 ≤ u := by omega
  have hu500005 : 500005 ≤ u := by omega
  have h8119_B :=
    eight_thousand_one_hundred_nineteen_pow_mul_padeSeqB_lt_47321_pow hp3 hu5
  have h8119_pos : (0 : ℤ) < (8119 : ℤ) ^ (u - 5) := by positivity
  have hpu_pos : (0 : ℤ) < (p : ℤ) ^ u := by positivity
  have h8119_pk : 8119 ^ (u - 5) * (p * k_pade.natAbs) < 8119 * 47321 ^ (u - 5) := by
    have hchain :
        ((8119 : ℤ) ^ (u - 5) * ((p : ℤ) * k_pade)) * (p : ℤ) ^ u <
          (8119 * 47321 ^ (u - 5)) * (p : ℤ) ^ u := by
      calc
        ((8119 : ℤ) ^ (u - 5) * ((p : ℤ) * k_pade)) * (p : ℤ) ^ u
            = (8119 : ℤ) ^ (u - 5) * ((p : ℤ) ^ (u + 1) * k_pade) := by
                rw [pow_succ']
                ring
        _ < (8119 : ℤ) ^ (u - 5) * padeSeqB u p :=
            mul_lt_mul_of_pos_left hpu1_k h8119_pos
        _ < 8119 * 47321 ^ (u - 5) * (p : ℤ) ^ u := h8119_B
    have hltZ : (8119 : ℤ) ^ (u - 5) * ((p : ℤ) * k_pade) < 8119 * 47321 ^ (u - 5) :=
      lt_of_mul_lt_mul_right hchain hpu_pos.le
    have hnat_abs : (k_pade.natAbs : ℤ) = k_pade := Int.natAbs_of_nonneg (by omega)
    rw [← hnat_abs] at hltZ
    exact_mod_cast hltZ
  have hnum := ten_pow_6000_lt_six_pow_of_floor hu500005
  have h6000_pk : (10 ^ 1000) ^ 6 * p * k_pade.natAbs < 6 ^ u := by
    have hmul :
        8119 ^ (u - 5) * ((10 ^ 1000) ^ 6 * p * k_pade.natAbs) < 8119 ^ (u - 5) * 6 ^ u := by
      calc
        8119 ^ (u - 5) * ((10 ^ 1000) ^ 6 * p * k_pade.natAbs)
            = (10 ^ 1000) ^ 6 * (8119 ^ (u - 5) * (p * k_pade.natAbs)) := by
                rw [mul_assoc ((10 ^ 1000) ^ 6) p k_pade.natAbs, mul_left_comm]
        _ < (10 ^ 1000) ^ 6 * (8119 * 47321 ^ (u - 5)) :=
            Nat.mul_lt_mul_of_pos_left h8119_pk (by positivity)
        _ < 8119 ^ (u - 5) * 6 ^ u := hnum
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hpar_cap : p % 4 = 3 ∨ Even u → 2 * (10 ^ 1000) ^ 6 * p < 6 ^ u := by
    intro hcond
    have hk2 : 2 ≤ k_pade :=
      (even_index_pade_quotient_parity_and_doubled_cap hp hpo hs hu hσq hplus hσs).2.2 hcond |>.1
    have hk2_nat : 2 ≤ k_pade.natAbs := by
      have hnat_abs : (k_pade.natAbs : ℤ) = k_pade := Int.natAbs_of_nonneg (by omega)
      omega
    have hle : 2 * (10 ^ 1000) ^ 6 * p ≤ (10 ^ 1000) ^ 6 * p * k_pade.natAbs := by
      calc
        2 * (10 ^ 1000) ^ 6 * p = (10 ^ 1000) ^ 6 * p * 2 := by
            rw [mul_comm 2 ((10 ^ 1000) ^ 6), mul_assoc, mul_comm 2 p, ← mul_assoc]
        _ ≤ (10 ^ 1000) ^ 6 * p * k_pade.natAbs := Nat.mul_le_mul_left _ hk2_nat
    exact lt_of_le_of_lt hle h6000_pk
  have hmodp_cap : p ∣ 64 ^ u - 1 → (10 ^ 1000) ^ 6 * p ^ 2 < 6 ^ u := by
    intro hp64
    have hpk : (p : ℤ) ≤ k_pade :=
      (even_index_pade_quotient_mod_p_and_sub_two hp hpo hs hu hσq hplus hσs).2.1 hp64 |>.1
    have hpk_nat : p ≤ k_pade.natAbs := by
      have hnat_abs : (k_pade.natAbs : ℤ) = k_pade := Int.natAbs_of_nonneg (by omega)
      omega
    have hle : (10 ^ 1000) ^ 6 * p ^ 2 ≤ (10 ^ 1000) ^ 6 * p * k_pade.natAbs := by
      calc
        (10 ^ 1000) ^ 6 * p ^ 2 = (10 ^ 1000) ^ 6 * p * p := by rw [sq p, ← mul_assoc]
        _ ≤ (10 ^ 1000) ^ 6 * p * k_pade.natAbs := Nat.mul_le_mul_left _ hpk_nat
    exact lt_of_le_of_lt hle h6000_pk
  have hdiv_cap : (2 * u + 1) ∣ p - 2 → (10 ^ 1000) ^ 6 * u * p < 6 ^ u := by
    intro hdiv
    have huk : (u : ℤ) ≤ k_pade :=
      (even_index_pade_quotient_mod_two_len_collapse hr₀_prime hp hpo hs hu hσq hplus hσs hdiv).2.1
    have huk_nat : u ≤ k_pade.natAbs := by
      have hnat_abs : (k_pade.natAbs : ℤ) = k_pade := Int.natAbs_of_nonneg (by omega)
      omega
    have hle : (10 ^ 1000) ^ 6 * u * p ≤ (10 ^ 1000) ^ 6 * p * k_pade.natAbs := by
      calc
        (10 ^ 1000) ^ 6 * u * p = (10 ^ 1000) ^ 6 * p * u := by
            rw [mul_assoc, mul_comm u p, ← mul_assoc]
        _ ≤ (10 ^ 1000) ^ 6 * p * k_pade.natAbs := Nat.mul_le_mul_left _ huk_nat
    exact lt_of_le_of_lt hle h6000_pk
  have hpow_lt_p : r ^ (l - 1) < p := by
    have hl1 : 1 ≤ l := by linarith only [hl_gt2]
    have hl_sub_pos : 0 < l - 1 := Nat.sub_pos_of_lt (by linarith only [hl_gt2] : 1 < l)
    have h0_mem : 0 ∈ Finset.range (l - 1) := Finset.mem_range.mpr hl_sub_pos
    have h1_le : 1 ≤ ∑ t ∈ Finset.range (l - 1), r ^ t := by
      have hle := Finset.single_le_sum (f := fun t => r ^ t) (fun _ _ => Nat.zero_le _) h0_mem
      simpa using hle
    have hsum : geometricBlock r l = (∑ t ∈ Finset.range (l - 1), r ^ t) + r ^ (l - 1) := by
      dsimp [geometricBlock]
      conv_lhs => rw [← Nat.sub_add_cancel hl1, Finset.sum_range_succ]
    linarith only [h1_le, hsum, hgb]
  have hk_pos_nat : 1 ≤ k_pade.natAbs := by
    have hnat_abs : (k_pade.natAbs : ℤ) = k_pade := Int.natAbs_of_nonneg (by omega)
    omega
  have h8119_r : 8119 ^ (u - 5) * r ^ (l - 1) < 8119 * 47321 ^ (u - 5) := by
    calc
      8119 ^ (u - 5) * r ^ (l - 1) < 8119 ^ (u - 5) * p :=
          Nat.mul_lt_mul_of_pos_left hpow_lt_p (by positivity)
      _ ≤ 8119 ^ (u - 5) * (p * k_pade.natAbs) :=
          Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right p hk_pos_nat)
      _ < 8119 * 47321 ^ (u - 5) := h8119_pk
  obtain ⟨hs5, hs7, hs11, hs13⟩ :=
    sharpened_repunit_slopes_of_47321_8119_cap hu1154 hl_gt2 h8119_r
  refine ⟨r₀, s, u, r, l, rfl, hr₀_prime, hr₀4, ha1, hs, hj_eq, hu_ge, hσq, hplus, hσs,
    hk1, h8119_pk, h6000_pk, hpar_cap, hmodp_cap, hdiv_cap,
    hr_mem, hr_prime, hl_gt2, hl_prime, hr2_N, hgb, hs5, ?_, ?_, ?_⟩
  · intro hr7
    exact ⟨(hs7 hr7).1, gap7_tridecuple_8119 hu_ge (hs7 hr7).1⟩
  · intro hr11
    exact ⟨(hs11 hr11).1, gap11_tridecuple_8119 hu_ge (hs11 hr11).1⟩
  · intro hr13
    exact ⟨(hs13 hr13).1, gap13_tridecuple_8119 hu_ge (hs13 hr13).1⟩

end OddPerfect
