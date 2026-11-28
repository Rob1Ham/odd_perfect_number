module

public import OddPerfect.PadicPadeModTwoLenObstruction
public import OddPerfect.TridecupleRepunitObstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Sublinear Repunit-Length Bounds & `10 ^ 1200` Padé Sharpening (`OddPerfect.PadicPadeSublinearRepunitBounds`)

Formalizes:
1. `sublinear_repunit_length_of_1393_239_cap`:
   Direct `(1393 / 239)` sublinear repunit-length bounds (`l < u`) from
   `239 ^ (u - 3) * r ^ (l - 1) < 239 * 1393 ^ (u - 3)` without losing the `(6 * 239) / 1393`
   margin:
   - `r ∈ {7, 11, 13} → 11 * l ≤ 10 * u + 11 ∧ l + 103 ≤ u`
   - `r ∈ {11, 13} → 4 * l ≤ 3 * u + 4 ∧ l + 287 ≤ u`
   - `r = 13 → 10 * l ≤ 7 * u + 10 ∧ l + 345 ≤ u`
2. `ten_pow_1200_lt_six_pow_of_tridecuple_floor`:
   For `100003 ≤ u`, `(10 ^ 600) ^ 2 * (239 * 1393 ^ (u - 3)) < 239 ^ (u - 3) * 6 ^ u`.
3. `even_prime_power_tridecuple_sublinear_repunit_profile`:
   Couples `239 ^ (u - 3) * p < 239 * 1393 ^ (u - 3)` with the tridecuple exponent floor
   `6541380665835014 ≤ u` to lift `10 ^ 12 * p < 6 ^ u` to `(10 ^ 600) ^ 2 * p < 6 ^ u`
   (and `(10 ^ 600) ^ 2 * u * p < 6 ^ u` when `(2 * u + 1) ∣ p - 2`) and upgrade the additive
   repunit gaps to `590000000000000`, `1635000000000000`, and `1962000000000000`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma sublinear_repunit_exp_step {r r_min l u A B C : ℕ}
    (hr_min : 1 < r_min) (hr_le : r_min ≤ r) (_hu : 3 ≤ u) (hA : 0 < A)
    (hcap : 239 ^ (u - 3) * r ^ (l - 1) < 239 * 1393 ^ (u - 3))
    (h1393 : 1393 ^ A ≤ 239 ^ A * r_min ^ B)
    (h239 : 239 ^ A < r_min ^ C) :
    A * (l - 1) < C + B * (u - 3) := by
  have hpow_min : 239 ^ (u - 3) * r_min ^ (l - 1) < 239 * 1393 ^ (u - 3) :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hr_le (l - 1))) hcap
  have hpowA : (239 ^ (u - 3) * r_min ^ (l - 1)) ^ A < (239 * 1393 ^ (u - 3)) ^ A :=
    Nat.pow_lt_pow_left hpow_min hA.ne'
  have h1393_pow :
      (1393 ^ A) ^ (u - 3) ≤ (239 ^ (u - 3)) ^ A * r_min ^ (B * (u - 3)) := by
    calc
      (1393 ^ A) ^ (u - 3) ≤ (239 ^ A * r_min ^ B) ^ (u - 3) :=
          Nat.pow_le_pow_left h1393 (u - 3)
      _ = (239 ^ A) ^ (u - 3) * (r_min ^ B) ^ (u - 3) := by rw [mul_pow]
      _ = (239 ^ (u - 3)) ^ A * r_min ^ (B * (u - 3)) := by
          rw [pow_right_comm 239 A (u - 3), ← pow_mul r_min B (u - 3)]
  have hchain :
      (239 ^ (u - 3)) ^ A * r_min ^ (A * (l - 1)) <
        (239 ^ (u - 3)) ^ A * r_min ^ (C + B * (u - 3)) := by
    calc
      (239 ^ (u - 3)) ^ A * r_min ^ (A * (l - 1))
          = (239 ^ (u - 3) * r_min ^ (l - 1)) ^ A := by
              rw [mul_pow, ← pow_mul r_min (l - 1) A, mul_comm (l - 1) A]
      _ < (239 * 1393 ^ (u - 3)) ^ A := hpowA
      _ = 239 ^ A * (1393 ^ A) ^ (u - 3) := by rw [mul_pow, pow_right_comm]
      _ ≤ 239 ^ A * ((239 ^ (u - 3)) ^ A * r_min ^ (B * (u - 3))) :=
          Nat.mul_le_mul_left _ h1393_pow
      _ = (239 ^ (u - 3)) ^ A * (239 ^ A * r_min ^ (B * (u - 3))) := by ring
      _ < (239 ^ (u - 3)) ^ A * (r_min ^ C * r_min ^ (B * (u - 3))) := by
          apply Nat.mul_lt_mul_of_pos_left
          · exact Nat.mul_lt_mul_of_pos_right h239 (by positivity)
          · positivity
      _ = (239 ^ (u - 3)) ^ A * r_min ^ (C + B * (u - 3)) := by rw [← pow_add]
  have hpow_lt : r_min ^ (A * (l - 1)) < r_min ^ (C + B * (u - 3)) :=
    Nat.lt_of_mul_lt_mul_left hchain
  exact (Nat.pow_lt_pow_iff_right hr_min).mp hpow_lt

/-- Direct `(1393 / 239)` sublinear repunit-length bounds (`l < u`) across `r ∈ {7, 11, 13}`
without losing the `(6 * 239) / 1393` margin. -/
theorem sublinear_repunit_length_of_1393_239_cap {r l u : ℕ}
    (hu : 1154 ≤ u) (hl : 2 < l)
    (hcap : 239 ^ (u - 3) * r ^ (l - 1) < 239 * 1393 ^ (u - 3)) :
    (r ∈ ({7, 11, 13} : Finset ℕ) → 11 * l ≤ 10 * u + 11 ∧ l + 103 ≤ u) ∧
    (r ∈ ({11, 13} : Finset ℕ) → 4 * l ≤ 3 * u + 4 ∧ l + 287 ≤ u) ∧
    (r = 13 → 10 * l ≤ 7 * u + 10 ∧ l + 345 ≤ u) := by
  have h7 : r ∈ ({7, 11, 13} : Finset ℕ) → 11 * l ≤ 10 * u + 11 ∧ l + 103 ≤ u := by
    intro hr7
    have hr_ge : 7 ≤ r := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr7
      rcases hr7 with rfl | rfl | rfl <;> decide
    have hlt := sublinear_repunit_exp_step (r_min := 7) (A := 11) (B := 10) (C := 31)
      (by decide) hr_ge (by omega) (by decide) hcap (by norm_num) (by norm_num)
    omega
  have h11 : r ∈ ({11, 13} : Finset ℕ) → 4 * l ≤ 3 * u + 4 ∧ l + 287 ≤ u := by
    intro hr11
    have hr_ge : 11 ≤ r := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr11
      rcases hr11 with rfl | rfl <;> decide
    have hlt := sublinear_repunit_exp_step (r_min := 11) (A := 4) (B := 3) (C := 10)
      (by decide) hr_ge (by omega) (by decide) hcap (by norm_num) (by norm_num)
    omega
  have h13 : r = 13 → 10 * l ≤ 7 * u + 10 ∧ l + 345 ≤ u := by
    intro hr13
    subst hr13
    have hlt := sublinear_repunit_exp_step (r_min := 13) (A := 10) (B := 7) (C := 22)
      (by decide) le_rfl (by omega) (by decide) hcap (by norm_num) (by norm_num)
    omega
  exact ⟨h7, h11, h13⟩

/-- Coupling `1393 / 239` with `100003 ≤ u` lifts `10 ^ 12` to `(10 ^ 600) ^ 2 = 10 ^ 1200`. -/
theorem ten_pow_1200_lt_six_pow_of_tridecuple_floor {u : ℕ} (hu : 100003 ≤ u) :
    (10 ^ 600) ^ 2 * (239 * 1393 ^ (u - 3)) < 239 ^ (u - 3) * 6 ^ u := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, u = 100003 + k := ⟨u - 100003, by omega⟩
  induction k with
  | zero =>
      have h48 : 4 * 1393 ^ 48 < 1434 ^ 48 := by norm_num
      have h2400 : 4 ^ 50 * (1393 ^ 48) ^ 50 < (1434 ^ 48) ^ 50 := by
        rw [← mul_pow]
        exact Nat.pow_lt_pow_left h48 (by decide)
      have h98400 : (4 ^ 50) ^ 41 * ((1393 ^ 48) ^ 50) ^ 41 < ((1434 ^ 48) ^ 50) ^ 41 := by
        rw [← mul_pow]
        exact Nat.pow_lt_pow_left h2400 (by decide)
      have h1600 : ((1393 ^ 100) ^ 8) ^ 2 ≤ ((1434 ^ 100) ^ 8) ^ 2 := by
        have h1393_1434 : (1393 : ℕ) ≤ 1434 := by decide
        exact Nat.pow_le_pow_left (Nat.pow_le_pow_left (Nat.pow_le_pow_left h1393_1434 100) 8) 2
      have hpow_1393 :
          1393 ^ (100003 + 0 - 3) = ((1393 ^ 48) ^ 50) ^ 41 * ((1393 ^ 100) ^ 8) ^ 2 := by
        rw [show 100003 + 0 - 3 = (48 * 50) * 41 + (100 * 8) * 2 by omega, pow_add,
          pow_mul, pow_mul, pow_mul, pow_mul]
      have hpow_1434 :
          239 ^ (100003 + 0 - 3) * 6 ^ (100003 + 0) =
            6 ^ 3 * (((1434 ^ 48) ^ 50) ^ 41 * ((1434 ^ 100) ^ 8) ^ 2) := by
        have h1434 : (1434 : ℕ) = 239 * 6 := by decide
        have hexp :
            (239 * 6) ^ (100003 + 0 - 3) =
              ((1434 ^ 48) ^ 50) ^ 41 * ((1434 ^ 100) ^ 8) ^ 2 := by
          rw [← h1434, show 100003 + 0 - 3 = (48 * 50) * 41 + (100 * 8) * 2 by omega, pow_add,
            pow_mul, pow_mul, pow_mul, pow_mul]
        rw [show 100003 + 0 = 3 + (100003 + 0 - 3) by omega, pow_add, mul_left_comm,
          ← mul_pow, hexp]
      have h10_30 : 10 ^ 30 < 4 ^ 50 := by norm_num
      have h10_1200 : (10 ^ 600) ^ 2 < (4 ^ 50) ^ 40 := by
        calc
          (10 ^ 600) ^ 2 = (10 ^ 30) ^ 40 := by rw [← pow_mul, ← pow_mul]
          _ < (4 ^ 50) ^ 40 := Nat.pow_lt_pow_left h10_30 (by decide)
      have h239_lt : 239 < 6 ^ 3 * 4 ^ 50 := by norm_num
      have hcoeff : (10 ^ 600) ^ 2 * 239 < 6 ^ 3 * (4 ^ 50) ^ 41 := by
        calc
          (10 ^ 600) ^ 2 * 239
              < (4 ^ 50) ^ 40 * (6 ^ 3 * 4 ^ 50) := by
                  exact Nat.mul_lt_mul'' h10_1200 h239_lt
          _ = 6 ^ 3 * ((4 ^ 50) ^ 40 * 4 ^ 50) := by rw [mul_left_comm]
          _ = 6 ^ 3 * (4 ^ 50) ^ 41 := by rw [← pow_succ]
      calc
        (10 ^ 600) ^ 2 * (239 * 1393 ^ (100003 + 0 - 3))
            = ((10 ^ 600) ^ 2 * 239) * (((1393 ^ 48) ^ 50) ^ 41 * ((1393 ^ 100) ^ 8) ^ 2) := by
                rw [hpow_1393, mul_assoc]
        _ < (6 ^ 3 * (4 ^ 50) ^ 41) * (((1393 ^ 48) ^ 50) ^ 41 * ((1393 ^ 100) ^ 8) ^ 2) :=
            Nat.mul_lt_mul_of_pos_right hcoeff (by positivity)
        _ = 6 ^ 3 * ((4 ^ 50) ^ 41 * ((1393 ^ 48) ^ 50) ^ 41) * ((1393 ^ 100) ^ 8) ^ 2 := by
            simp only [mul_assoc]
        _ < 6 ^ 3 * ((1434 ^ 48) ^ 50) ^ 41 * ((1393 ^ 100) ^ 8) ^ 2 := by
            apply Nat.mul_lt_mul_of_pos_right _ (by positivity)
            exact Nat.mul_lt_mul_of_pos_left h98400 (by decide)
        _ ≤ 6 ^ 3 * ((1434 ^ 48) ^ 50) ^ 41 * ((1434 ^ 100) ^ 8) ^ 2 :=
            Nat.mul_le_mul_left _ h1600
        _ = 6 ^ 3 * (((1434 ^ 48) ^ 50) ^ 41 * ((1434 ^ 100) ^ 8) ^ 2) := by rw [mul_assoc]
        _ = 239 ^ (100003 + 0 - 3) * 6 ^ (100003 + 0) := hpow_1434.symm
  | succ k ih =>
      have hk : 100003 ≤ 100003 + k := by omega
      have ihk := ih hk
      have hmul :
          1393 * ((10 ^ 600) ^ 2 * (239 * 1393 ^ (100003 + k - 3))) <
            1393 * (239 ^ (100003 + k - 3) * 6 ^ (100003 + k)) :=
        Nat.mul_lt_mul_of_pos_left ihk (by decide)
      have h1393_lt :
          1393 * (239 ^ (100003 + k - 3) * 6 ^ (100003 + k)) <
            (239 * 6) * (239 ^ (100003 + k - 3) * 6 ^ (100003 + k)) := by
        apply Nat.mul_lt_mul_of_pos_right (by decide : 1393 < 239 * 6)
        positivity
      have hrewL :
          (10 ^ 600) ^ 2 * (239 * 1393 ^ (100003 + (k + 1) - 3)) =
            1393 * ((10 ^ 600) ^ 2 * (239 * 1393 ^ (100003 + k - 3))) := by
        rw [show 100003 + (k + 1) - 3 = (100003 + k - 3) + 1 by omega, pow_succ' 1393,
          mul_left_comm 239 1393, mul_left_comm ((10 ^ 600) ^ 2) 1393]
      have hrewR :
          (239 * 6) * (239 ^ (100003 + k - 3) * 6 ^ (100003 + k)) =
            239 ^ (100003 + (k + 1) - 3) * 6 ^ (100003 + (k + 1)) := by
        rw [show 100003 + (k + 1) - 3 = (100003 + k - 3) + 1 by omega,
          show 100003 + (k + 1) = (100003 + k) + 1 by omega, pow_succ' 239, pow_succ' 6,
          mul_mul_mul_comm]
      calc
        (10 ^ 600) ^ 2 * (239 * 1393 ^ (100003 + (k + 1) - 3))
            = 1393 * ((10 ^ 600) ^ 2 * (239 * 1393 ^ (100003 + k - 3))) := hrewL
        _ < 1393 * (239 ^ (100003 + k - 3) * 6 ^ (100003 + k)) := hmul
        _ < (239 * 6) * (239 ^ (100003 + k - 3) * 6 ^ (100003 + k)) := h1393_lt
        _ = 239 ^ (100003 + (k + 1) - 3) * 6 ^ (100003 + (k + 1)) := hrewR

private lemma gap7_of_lin {l u : ℕ} (hu : 6541380665835014 ≤ u)
    (hlin : 11 * l ≤ 10 * u + 11) : l + 590000000000000 ≤ u := by omega

private lemma gap11_of_lin {l u : ℕ} (hu : 6541380665835014 ≤ u)
    (hlin : 4 * l ≤ 3 * u + 4) : l + 1635000000000000 ≤ u := by omega

private lemma gap13_of_lin {l u : ℕ} (hu : 6541380665835014 ≤ u)
    (hlin : 10 * l ≤ 7 * u + 10) : l + 1962000000000000 ≤ u := by omega

/-- Global odd-perfect-number theorem coupling the tridecuple exponent floor
`6541380665835014 ≤ u` with `(1393 / 239)` Padé contraction to obtain
`(10 ^ 600) ^ 2 * p < 6 ^ u` (and `(10 ^ 600) ^ 2 * u * p < 6 ^ u` under `(2 * u + 1) ∣ p - 2`)
and sublinear repunit-length bounds with trillion-scale additive gaps across `r ∈ {7, 11, 13}`. -/
theorem even_prime_power_tridecuple_sublinear_repunit_profile
    {N q a b i p u : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b) (hl : sigma 1 b = q ^ a * i)
    (hr : sigma 1 (q ^ a) * i = 2 * b) (hp : p.Prime) (hu : 0 < u) (hi : i = p ^ (2 * u)) :
    6541380665835014 ≤ u ∧ (2 * u + 1).Prime ∧
    (10 ^ 600) ^ 2 * p < 6 ^ u ∧
    ((2 * u + 1) ∣ p - 2 → (10 ^ 600) ^ 2 * u * p < 6 ^ u) ∧
    ∃ r ∈ ({3, 5, 7, 11, 13} : Finset ℕ),
      r ^ 2 ∣ N ∧
      ∃ l : ℕ, l.Prime ∧ 2 < l ∧ geometricBlock r l = p ∧
        239 ^ (u - 3) * r ^ (l - 1) < 239 * 1393 ^ (u - 3) ∧
        (10 ^ 600) ^ 2 * r ^ (l - 1) < 6 ^ u ∧
        3 * l + 75 ≤ 5 * u ∧
        (r ∈ ({5, 7, 11, 13} : Finset ℕ) → 8 * l + 131 ≤ 9 * u) ∧
        (r ∈ ({7, 11, 13} : Finset ℕ) →
          11 * l ≤ 10 * u + 11 ∧ l + 590000000000000 ≤ u) ∧
        (r ∈ ({11, 13} : Finset ℕ) →
          4 * l ≤ 3 * u + 4 ∧ l + 1635000000000000 ≤ u) ∧
        (r = 13 →
          10 * l ≤ 7 * u + 10 ∧ l + 1962000000000000 ≤ u) := by
  obtain ⟨ha1, hσq⟩ :=
    even_prime_power_index_eq_selected_sigma hN ho hq ha hform hqb hl hr hp hu hi
  have hbo := ho.of_dvd_nat (hform ▸ dvd_mul_left b _)
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h4 : 4 ∣ 2 * b := hr ▸ hi ▸ (pow_dvd_pow 2 (by omega : 2 ≤ 2 * u)).trans (dvd_mul_left _ _)
    have := hbo.not_two_dvd_nat
    omega
  have hpo : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨m, _, _, _, rfl⟩ :=
    euler_form_of_odd_component_index hN ho hq ha hform hqb hl hr (hi ▸ hpo.pow)
  have hmo := ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2 ≠ 0)) _)
  have hform' := hform
  have hl' := hl
  have hr' := hr
  rw [ha1, pow_one] at hform' hl' hr'
  rw [hi] at hl' hr'
  obtain ⟨s, hs, _, _, _, hplus, hσs⟩ := even_prime_power_cofactor_split hq hp hmo hpo hu hl' hr'
  have hlen_prime : (2 * u + 1).Prime := even_index_length_prime hq hp hu hσq
  have hu_ge : 6541380665835014 ≤ u :=
    (even_index_exponent_ge_13082761331670028 hp hpo hs hu hσq hplus hσs).1
  have hu_100003 : 100003 ≤ u := le_trans (by decide) hu_ge
  have hu_1154 : 1154 ≤ u := le_trans (by decide) hu_ge
  have hnum := ten_pow_1200_lt_six_pow_of_tridecuple_floor hu_100003
  obtain ⟨_, h239_p, _, _, _⟩ :=
    even_index_prime_ten_pow_twelve_cap hp hpo hs hu hσq hplus hσs
  have h1200_p : (10 ^ 600) ^ 2 * p < 6 ^ u := by
    have hmul : 239 ^ (u - 3) * ((10 ^ 600) ^ 2 * p) < 239 ^ (u - 3) * 6 ^ u := by
      calc
        239 ^ (u - 3) * ((10 ^ 600) ^ 2 * p)
            = (10 ^ 600) ^ 2 * (239 ^ (u - 3) * p) := by rw [mul_left_comm]
        _ < (10 ^ 600) ^ 2 * (239 * 1393 ^ (u - 3)) :=
            Nat.mul_lt_mul_of_pos_left h239_p (by positivity)
        _ < 239 ^ (u - 3) * 6 ^ u := hnum
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hdiv_cap : (2 * u + 1) ∣ p - 2 → (10 ^ 600) ^ 2 * u * p < 6 ^ u := by
    intro hdiv
    obtain ⟨_, _, _, h239_up, _, _⟩ :=
      even_index_pade_quotient_mod_two_len_collapse hq hp hpo hs hu hσq hplus hσs hdiv
    have hmul : 239 ^ (u - 3) * ((10 ^ 600) ^ 2 * u * p) < 239 ^ (u - 3) * 6 ^ u := by
      calc
        239 ^ (u - 3) * ((10 ^ 600) ^ 2 * u * p)
            = (10 ^ 600) ^ 2 * (239 ^ (u - 3) * (u * p)) := by
                rw [mul_assoc ((10 ^ 600) ^ 2) u p, mul_left_comm]
        _ < (10 ^ 600) ^ 2 * (239 * 1393 ^ (u - 3)) :=
            Nat.mul_lt_mul_of_pos_left h239_up (by positivity)
        _ < 239 ^ (u - 3) * 6 ^ u := hnum
    exact Nat.lt_of_mul_lt_mul_left hmul
  obtain ⟨_, _, _, _, r, hr_mem, hr2_N, l, hl_prime, hl_gt2, hgb, _, h3_bd, h5_bd, _⟩ :=
    even_prime_power_all_primorial_repunit_and_len_div_caps hN ho hq ha hform hqb hl hr hp hu hi
  have hpow_lt_p : r ^ (l - 1) < p := by
    have hl1 : 1 ≤ l := by linarith only [hl_gt2]
    have hl_sub_pos : 0 < l - 1 := Nat.sub_pos_of_lt (by linarith only [hl_gt2] : 1 < l)
    have h0_mem : 0 ∈ Finset.range (l - 1) := Finset.mem_range.mpr hl_sub_pos
    have h1_le : 1 ≤ ∑ j ∈ Finset.range (l - 1), r ^ j := by
      have hle := Finset.single_le_sum (f := fun j => r ^ j) (fun _ _ => Nat.zero_le _) h0_mem
      simpa using hle
    have hsum : geometricBlock r l = (∑ j ∈ Finset.range (l - 1), r ^ j) + r ^ (l - 1) := by
      dsimp [geometricBlock]
      conv_lhs => rw [← Nat.sub_add_cancel hl1, Finset.sum_range_succ]
    linarith only [h1_le, hsum, hgb]
  have h239_r : 239 ^ (u - 3) * r ^ (l - 1) < 239 * 1393 ^ (u - 3) := by
    calc
      239 ^ (u - 3) * r ^ (l - 1) < 239 ^ (u - 3) * p :=
          Nat.mul_lt_mul_of_pos_left hpow_lt_p (by positivity)
      _ < 239 * 1393 ^ (u - 3) := h239_p
  have h1200_r : (10 ^ 600) ^ 2 * r ^ (l - 1) < 6 ^ u := by
    calc
      (10 ^ 600) ^ 2 * r ^ (l - 1) < (10 ^ 600) ^ 2 * p :=
          Nat.mul_lt_mul_of_pos_left hpow_lt_p (by positivity)
      _ < 6 ^ u := h1200_p
  obtain ⟨h7_sub, h11_sub, h13_sub⟩ :=
    sublinear_repunit_length_of_1393_239_cap hu_1154 hl_gt2 h239_r
  have h7_gap :
      r ∈ ({7, 11, 13} : Finset ℕ) →
        11 * l ≤ 10 * u + 11 ∧ l + 590000000000000 ≤ u := by
    intro hr7
    have hlin := (h7_sub hr7).1
    exact ⟨hlin, gap7_of_lin hu_ge hlin⟩
  have h11_gap :
      r ∈ ({11, 13} : Finset ℕ) →
        4 * l ≤ 3 * u + 4 ∧ l + 1635000000000000 ≤ u := by
    intro hr11
    have hlin := (h11_sub hr11).1
    exact ⟨hlin, gap11_of_lin hu_ge hlin⟩
  have h13_gap :
      r = 13 →
        10 * l ≤ 7 * u + 10 ∧ l + 1962000000000000 ≤ u := by
    intro hr13
    have hlin := (h13_sub hr13).1
    exact ⟨hlin, gap13_of_lin hu_ge hlin⟩
  exact ⟨hu_ge, hlen_prime, h1200_p, hdiv_cap,
    ⟨r, hr_mem, hr2_N, l, hl_prime, hl_gt2, hgb, h239_r, h1200_r,
      h3_bd, h5_bd, h7_gap, h11_gap, h13_gap⟩⟩

end OddPerfect
