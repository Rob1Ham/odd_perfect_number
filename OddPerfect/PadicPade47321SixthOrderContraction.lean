module

public import OddPerfect.PadicPade8119HigherContraction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Sixth-Order `275807 / 47321` Pell–Padé Contraction & `(10 ^ 1000) ^ 1000` Margin (`OddPerfect.PadicPade47321SixthOrderContraction`)

Extends `OddPerfect.PadicPade8119HigherContraction` from the fifth-order (`47321 / 8119`)
Pell–Padé contraction to the sixth-order (`275807 / 47321`, from `padeLeadB 6 = 47321` and
`padeLeadB 7 = 275807`) contraction for `3 ≤ p` and `6 ≤ u`, sharpened repunit slopes across
`r ∈ {3, 5, 7, 11, 13}`, and the `(10 ^ 1000) ^ 1000` (`10 ^ 1,000,000`, million-digit) global
margin on every even prime-power component index `componentIndex N r₀ = p ^ j`:

1. `padeSeq_sharpened_275807_47321_contraction`:
   For `3 ≤ p` and `6 ≤ u`:
   - `padeLeadB 6 = 47321` and `padeLeadB 7 = 275807`
   - `47321 * padeSeqA u p ≤ 33461 * padeSeqB u p`
   - `47321 * padeSeqB (u + 1) p < 275807 * (p : ℤ) * padeSeqB u p`
   - `47321 ^ (u - 6) * padeSeqB u p < 47321 * 275807 ^ (u - 6) * (p : ℤ) ^ u`
   - For all `k : ℤ` with `1 ≤ k` and `(p : ℤ) ^ (u + 1) * k < padeSeqB u p`:
     `47321 ^ (u - 6) * (p * k.natAbs) < 47321 * 275807 ^ (u - 6)`.
2. `sharpened_repunit_slopes_of_275807_47321_cap`:
   Direct `(275807 / 47321)` repunit-length slope bounds across `3 ≤ r`, `5 ≤ r`, `7 ≤ r`,
   `11 ≤ r`, `13 ≤ r` from `47321 ^ (u - 6) * r ^ (l - 1) < 47321 * 275807 ^ (u - 6)`.
3. `even_prime_power_275807_47321_and_million_digit_profile`:
   Global `componentIndex N r₀ = p ^ j` wrapper yielding `(10 ^ 1000) ^ 1000 * p * k_pade.natAbs < 6 ^ u`
   and sharpened repunit slopes and additive gaps across `r ∈ {3, 5, 7, 11, 13}`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma odd_prime_ge_three_47321 {p : ℕ} (hp : p.Prime) (hpo : Odd p) : 3 ≤ p := by
  have h2 : 2 ≤ p := hp.two_le
  rcases eq_or_lt_of_le h2 with rfl | hlt
  · exact absurd hpo (by decide)
  · exact hlt

private lemma padeLeadB_six_eq : padeLeadB 6 = 47321 := by
  norm_num [padeLeadB, padeLeadA, padeLeadPair]

private lemma padeLeadB_seven_eq : padeLeadB 7 = 275807 := by
  norm_num [padeLeadB, padeLeadA, padeLeadPair]

private lemma forty_seven_thousand_mul_padeSeqA_le_33461_mul_padeSeqB
    {p u : ℕ} (hp3 : 3 ≤ p) (hu : 6 ≤ u) :
    47321 * padeSeqA u p ≤ 33461 * padeSeqB u p := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, u = 6 + k := ⟨u - 6, by omega⟩
  have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
  induction k with
  | zero =>
      set t : ℤ := (p : ℤ) - 3
      have ht : 0 ≤ t := by dsimp [t]; linarith
      have hid :
          33461 * padeSeqB (6 + 0) p - 47321 * padeSeqA (6 + 0) p =
            791703984 * t ^ 5 + 6379243344 * t ^ 4 + 20377808864 * t ^ 3 +
              32235457440 * t ^ 2 + 25232929648 * t + 7812552720 := by
        dsimp [t, padeSeqA, padeSeqB, padeSeqPair]
        ring
      have hpos :
          0 ≤ 791703984 * t ^ 5 + 6379243344 * t ^ 4 + 20377808864 * t ^ 3 +
            32235457440 * t ^ 2 + 25232929648 * t + 7812552720 := by
        positivity
      linarith
  | succ k ih =>
      have hk6 : 6 ≤ 6 + k := by omega
      have ihk := ih hk6
      obtain ⟨ha, hb⟩ := padeSeq_one_le hp3 (6 + k)
      have hid :
          47321 * (33461 * padeSeqB (6 + k + 1) p - 47321 * padeSeqA (6 + k + 1) p) =
            8119 * (p : ℤ) * (33461 * padeSeqB (6 + k) p - 47321 * padeSeqA (6 + k) p) +
              (2 * (p : ℤ) + 2623476240) * padeSeqB (6 + k) p +
              2623476240 * padeSeqA (6 + k) p := by
        simp only [padeSeqA_succ, padeSeqB_succ]
        ring
      have hdiff : 0 ≤ 33461 * padeSeqB (6 + k) p - 47321 * padeSeqA (6 + k) p := by linarith
      have ht1 :
          0 ≤ 8119 * (p : ℤ) * (33461 * padeSeqB (6 + k) p - 47321 * padeSeqA (6 + k) p) :=
        mul_nonneg (by positivity) hdiff
      have ht2 : 0 < (2 * (p : ℤ) + 2623476240) * padeSeqB (6 + k) p :=
        mul_pos (by linarith) (by linarith)
      have hpos :
          0 < 47321 * (33461 * padeSeqB (6 + k + 1) p - 47321 * padeSeqA (6 + k + 1) p) := by
        linarith
      rw [← Nat.add_assoc]
      linarith

private lemma forty_seven_thousand_mul_padeSeqB_succ_lt_275807_mul
    {p u : ℕ} (hp3 : 3 ≤ p) (hu : 6 ≤ u) :
    47321 * padeSeqB (u + 1) p < 275807 * (p : ℤ) * padeSeqB u p := by
  have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
  obtain ⟨_, hb⟩ := padeSeq_one_le hp3 u
  have h47321_33461 :=
    forty_seven_thousand_mul_padeSeqA_le_33461_mul_padeSeqB hp3 hu
  have hstep :
      4 * ((p : ℤ) - 1) * (47321 * padeSeqA u p) +
          47321 * (3 * (p : ℤ) - 4) * padeSeqB u p ≤
        4 * ((p : ℤ) - 1) * (33461 * padeSeqB u p) +
          47321 * (3 * (p : ℤ) - 4) * padeSeqB u p := by
    have hmul :
        4 * ((p : ℤ) - 1) * (47321 * padeSeqA u p) ≤
          4 * ((p : ℤ) - 1) * (33461 * padeSeqB u p) :=
      mul_le_mul_of_nonneg_left h47321_33461 (by linarith)
    linarith
  have hid1 :
      47321 * padeSeqB (u + 1) p =
        4 * ((p : ℤ) - 1) * (47321 * padeSeqA u p) +
          47321 * (3 * (p : ℤ) - 4) * padeSeqB u p := by
    rw [padeSeqB_succ]
    ring
  have hid2 :
      4 * ((p : ℤ) - 1) * (33461 * padeSeqB u p) +
          47321 * (3 * (p : ℤ) - 4) * padeSeqB u p =
        275807 * (p : ℤ) * padeSeqB u p - 323128 * padeSeqB u p := by
    ring
  linarith

private lemma forty_seven_thousand_pow_mul_padeSeqB_lt_275807_pow
    {p u : ℕ} (hp3 : 3 ≤ p) (hu : 6 ≤ u) :
    47321 ^ (u - 6) * padeSeqB u p < 47321 * 275807 ^ (u - 6) * (p : ℤ) ^ u := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, u = 6 + k := ⟨u - 6, by omega⟩
  have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
  induction k with
  | zero =>
      simp only [Nat.add_zero, Nat.sub_self, pow_zero, one_mul, mul_one]
      set t : ℤ := (p : ℤ) - 3
      have ht : 0 ≤ t := by dsimp [t]; linarith
      have hid :
          47321 * (p : ℤ) ^ 6 - padeSeqB 6 p =
            387672 * t ^ 5 + 4506024 * t ^ 4 + 21514480 * t ^ 3 +
              52662224 * t ^ 2 + 65938232 * t + 33699848 := by
        dsimp [t, padeSeqA, padeSeqB, padeSeqPair]
        ring
      have hpos :
          0 < 387672 * t ^ 5 + 4506024 * t ^ 4 + 21514480 * t ^ 3 +
            52662224 * t ^ 2 + 65938232 * t + 33699848 := by
        positivity
      linarith
  | succ k ih =>
      have hk6 : 6 ≤ 6 + k := by omega
      have ihk := ih hk6
      have hstep :=
        forty_seven_thousand_mul_padeSeqB_succ_lt_275807_mul hp3 hk6
      have h47321_pos : (0 : ℤ) < (47321 : ℤ) ^ (6 + k - 6) := by positivity
      have hp_pos : (0 : ℤ) < (p : ℤ) := by linarith
      have h1 :
          (47321 : ℤ) ^ (6 + k - 6) * (47321 * padeSeqB (6 + k + 1) p) <
            (47321 : ℤ) ^ (6 + k - 6) * (275807 * (p : ℤ) * padeSeqB (6 + k) p) :=
        mul_lt_mul_of_pos_left hstep h47321_pos
      have h2 :
          275807 * (p : ℤ) * ((47321 : ℤ) ^ (6 + k - 6) * padeSeqB (6 + k) p) <
            275807 * (p : ℤ) * (47321 * 275807 ^ (6 + k - 6) * (p : ℤ) ^ (6 + k)) :=
        mul_lt_mul_of_pos_left ihk (by positivity)
      have hrewL :
          (47321 : ℤ) ^ (6 + (k + 1) - 6) * padeSeqB (6 + (k + 1)) p =
            (47321 : ℤ) ^ (6 + k - 6) * (47321 * padeSeqB (6 + k + 1) p) := by
        rw [show 6 + (k + 1) - 6 = (6 + k - 6) + 1 by omega, pow_succ]
        rw [show 6 + (k + 1) = 6 + k + 1 by omega]
        ring
      have hrewM :
          (47321 : ℤ) ^ (6 + k - 6) * (275807 * (p : ℤ) * padeSeqB (6 + k) p) =
            275807 * (p : ℤ) * ((47321 : ℤ) ^ (6 + k - 6) * padeSeqB (6 + k) p) := by
        ring
      have hrewR :
          275807 * (p : ℤ) * (47321 * 275807 ^ (6 + k - 6) * (p : ℤ) ^ (6 + k)) =
            47321 * 275807 ^ (6 + (k + 1) - 6) * (p : ℤ) ^ (6 + (k + 1)) := by
        rw [show 6 + (k + 1) - 6 = (6 + k - 6) + 1 by omega, pow_succ]
        rw [show 6 + (k + 1) = (6 + k) + 1 by omega, pow_succ]
        ring
      linarith

/-- Bundled `275807 / 47321` sixth-order sharpened Pell–Padé contraction for `3 ≤ p` and
`6 ≤ u`, including `padeLeadB 6 = 47321`, `padeLeadB 7 = 275807`, and the `k.natAbs` cap. -/
theorem padeSeq_sharpened_275807_47321_contraction {p u : ℕ} (hp3 : 3 ≤ p) (hu : 6 ≤ u) :
    padeLeadB 6 = 47321 ∧
    padeLeadB 7 = 275807 ∧
    (47321 * padeSeqA u p ≤ 33461 * padeSeqB u p) ∧
    (47321 * padeSeqB (u + 1) p < 275807 * (p : ℤ) * padeSeqB u p) ∧
    (47321 ^ (u - 6) * padeSeqB u p < 47321 * 275807 ^ (u - 6) * (p : ℤ) ^ u) ∧
    (∀ k : ℤ, 1 ≤ k → (p : ℤ) ^ (u + 1) * k < padeSeqB u p →
      47321 ^ (u - 6) * (p * k.natAbs) < 47321 * 275807 ^ (u - 6)) := by
  have hB := forty_seven_thousand_pow_mul_padeSeqB_lt_275807_pow hp3 hu
  refine ⟨padeLeadB_six_eq, padeLeadB_seven_eq,
    forty_seven_thousand_mul_padeSeqA_le_33461_mul_padeSeqB hp3 hu,
    forty_seven_thousand_mul_padeSeqB_succ_lt_275807_mul hp3 hu, hB, ?_⟩
  intro k hk1 hpu1_k
  have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
  have h47321_pos : (0 : ℤ) < (47321 : ℤ) ^ (u - 6) := by positivity
  have hpu_pos : (0 : ℤ) < (p : ℤ) ^ u := by positivity
  have hchain :
      ((47321 : ℤ) ^ (u - 6) * ((p : ℤ) * k)) * (p : ℤ) ^ u <
        (47321 * 275807 ^ (u - 6)) * (p : ℤ) ^ u := by
    calc
      ((47321 : ℤ) ^ (u - 6) * ((p : ℤ) * k)) * (p : ℤ) ^ u
          = (47321 : ℤ) ^ (u - 6) * ((p : ℤ) ^ (u + 1) * k) := by
              rw [pow_succ']
              ring
      _ < (47321 : ℤ) ^ (u - 6) * padeSeqB u p :=
          mul_lt_mul_of_pos_left hpu1_k h47321_pos
      _ < 47321 * 275807 ^ (u - 6) * (p : ℤ) ^ u := hB
  have hltZ : (47321 : ℤ) ^ (u - 6) * ((p : ℤ) * k) < 47321 * 275807 ^ (u - 6) :=
    lt_of_mul_lt_mul_right hchain hpu_pos.le
  have hnat_abs : (k.natAbs : ℤ) = k := Int.natAbs_of_nonneg (by omega)
  rw [← hnat_abs] at hltZ
  exact_mod_cast hltZ

private lemma sublinear_repunit_exp_step_47321 {r r_min l u A B C : ℕ}
    (hr_min : 1 < r_min) (hr_le : r_min ≤ r) (_hu : 6 ≤ u) (hA : 0 < A)
    (hcap : 47321 ^ (u - 6) * r ^ (l - 1) < 47321 * 275807 ^ (u - 6))
    (h275807 : 275807 ^ A < 47321 ^ A * r_min ^ B)
    (h47321 : 47321 ^ A ≤ r_min ^ C) :
    A * (l - 1) < C + B * (u - 6) := by
  have hpow_min : 47321 ^ (u - 6) * r_min ^ (l - 1) < 47321 * 275807 ^ (u - 6) :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hr_le (l - 1))) hcap
  have hpowA : (47321 ^ (u - 6) * r_min ^ (l - 1)) ^ A < (47321 * 275807 ^ (u - 6)) ^ A :=
    Nat.pow_lt_pow_left hpow_min hA.ne'
  have h275807_pow :
      (275807 ^ A) ^ (u - 6) ≤ (47321 ^ (u - 6)) ^ A * r_min ^ (B * (u - 6)) := by
    calc
      (275807 ^ A) ^ (u - 6) ≤ (47321 ^ A * r_min ^ B) ^ (u - 6) :=
          Nat.pow_le_pow_left h275807.le (u - 6)
      _ = (47321 ^ A) ^ (u - 6) * (r_min ^ B) ^ (u - 6) := by rw [mul_pow]
      _ = (47321 ^ (u - 6)) ^ A * r_min ^ (B * (u - 6)) := by
          rw [pow_right_comm 47321 A (u - 6), ← pow_mul r_min B (u - 6)]
  have hchain :
      (47321 ^ (u - 6)) ^ A * r_min ^ (A * (l - 1)) <
        (47321 ^ (u - 6)) ^ A * r_min ^ (C + B * (u - 6)) := by
    calc
      (47321 ^ (u - 6)) ^ A * r_min ^ (A * (l - 1))
          = (47321 ^ (u - 6) * r_min ^ (l - 1)) ^ A := by
              rw [mul_pow, ← pow_mul r_min (l - 1) A, mul_comm (l - 1) A]
      _ < (47321 * 275807 ^ (u - 6)) ^ A := hpowA
      _ = 47321 ^ A * (275807 ^ A) ^ (u - 6) := by rw [mul_pow, pow_right_comm]
      _ ≤ 47321 ^ A * ((47321 ^ (u - 6)) ^ A * r_min ^ (B * (u - 6))) :=
          Nat.mul_le_mul_left _ h275807_pow
      _ = (47321 ^ (u - 6)) ^ A * (47321 ^ A * r_min ^ (B * (u - 6))) := by ring
      _ ≤ (47321 ^ (u - 6)) ^ A * (r_min ^ C * r_min ^ (B * (u - 6))) := by
          apply Nat.mul_le_mul_left
          exact Nat.mul_le_mul_right _ h47321
      _ = (47321 ^ (u - 6)) ^ A * r_min ^ (C + B * (u - 6)) := by rw [← pow_add]
  have hpow_lt : r_min ^ (A * (l - 1)) < r_min ^ (C + B * (u - 6)) :=
    Nat.lt_of_mul_lt_mul_left hchain
  exact (Nat.pow_lt_pow_iff_right hr_min).mp hpow_lt

/-- Direct `(275807 / 47321)` sharpened repunit-length slope bounds across `3 ≤ r`, `5 ≤ r`,
`7 ≤ r`, `11 ≤ r`, `13 ≤ r` from `47321 ^ (u - 6) * r ^ (l - 1) < 47321 * 275807 ^ (u - 6)`
for `6 ≤ u` and `1 ≤ l`. -/
theorem sharpened_repunit_slopes_of_275807_47321_cap {r l u : ℕ}
    (hu : 6 ≤ u) (hl : 1 ≤ l)
    (hcap : 47321 ^ (u - 6) * r ^ (l - 1) < 47321 * 275807 ^ (u - 6)) :
    (3 ≤ r → 43 * l ≤ 69 * u + 50) ∧
    (5 ≤ r → 31 * l ≤ 34 * u + 34) ∧
    (7 ≤ r → 32 * l ≤ 29 * u + 35) ∧
    (11 ≤ r → 34 * l ≤ 25 * u + 36) ∧
    (13 ≤ r → 16 * l ≤ 11 * u + 17) := by
  have h3 : 3 ≤ r → 43 * l ≤ 69 * u + 50 := by
    intro hr3
    have h47321_3 : 47321 ^ 43 ≤ 3 ^ 422 := by
      have h1 : 47321 ^ 21 ≤ 3 ^ 206 := by norm_num
      have h2 : 47321 ^ 22 ≤ 3 ^ 216 := by norm_num
      calc
        47321 ^ 43 = 47321 ^ 21 * 47321 ^ 22 := by rw [← pow_add]
        _ ≤ 3 ^ 206 * 3 ^ 216 := Nat.mul_le_mul h1 h2
        _ = 3 ^ 422 := by rw [← pow_add]
    have hlt := sublinear_repunit_exp_step_47321 (r_min := 3) (A := 43) (B := 69) (C := 422)
      (by decide) hr3 hu (by decide) hcap (by norm_num) h47321_3
    omega
  have h5 : 5 ≤ r → 31 * l ≤ 34 * u + 34 := by
    intro hr5
    have hlt := sublinear_repunit_exp_step_47321 (r_min := 5) (A := 31) (B := 34) (C := 208)
      (by decide) hr5 hu (by decide) hcap (by norm_num) (by norm_num)
    omega
  have h7 : 7 ≤ r → 32 * l ≤ 29 * u + 35 := by
    intro hr7
    have hlt := sublinear_repunit_exp_step_47321 (r_min := 7) (A := 32) (B := 29) (C := 178)
      (by decide) hr7 hu (by decide) hcap (by norm_num) (by norm_num)
    omega
  have h11 : 11 ≤ r → 34 * l ≤ 25 * u + 36 := by
    intro hr11
    have hlt := sublinear_repunit_exp_step_47321 (r_min := 11) (A := 34) (B := 25) (C := 153)
      (by decide) hr11 hu (by decide) hcap (by norm_num) (by norm_num)
    omega
  have h13 : 13 ≤ r → 16 * l ≤ 11 * u + 17 := by
    intro hr13
    have hlt := sublinear_repunit_exp_step_47321 (r_min := 13) (A := 16) (B := 11) (C := 68)
      (by decide) hr13 hu (by decide) hcap (by norm_num) (by norm_num)
    omega
  exact ⟨h3, h5, h7, h11, h13⟩

private lemma exp_margin_of_N (N u : ℕ) (hN : 1 ≤ N) (hu : 90 * N + 7 ≤ u) :
    10 ^ N * (47321 * 275807 ^ (u - 6)) < 47321 ^ (u - 6) * 6 ^ u := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, u = (90 * N + 7) + k := ⟨u - (90 * N + 7), by omega⟩
  induction k with
  | zero =>
      have h45 : 18 * 275807 ^ 45 < 5 * 283926 ^ 45 := by norm_num
      have h90 : 10 * 275807 ^ 90 < 283926 ^ 90 := by
        have hsq : (18 * 275807 ^ 45) ^ 2 < (5 * 283926 ^ 45) ^ 2 :=
          Nat.pow_lt_pow_left h45 (by decide)
        have h25_lt : 25 * (10 * 275807 ^ 90) < 25 * 283926 ^ 90 := by
          have hL : 25 * (10 * 275807 ^ 90) ≤ (18 * 275807 ^ 45) ^ 2 := by
            rw [mul_pow, ← pow_mul, show 45 * 2 = 90 by omega, show 18 ^ 2 = 324 by decide]
            nlinarith
          have hR : (5 * 283926 ^ 45) ^ 2 = 25 * 283926 ^ 90 := by
            rw [mul_pow, ← pow_mul, show 45 * 2 = 90 by omega, show 5 ^ 2 = 25 by decide]
          linarith
        exact Nat.lt_of_mul_lt_mul_left h25_lt
      have hN_pow : 10 ^ N * (275807 ^ 90) ^ N < (283926 ^ 90) ^ N := by
        rw [← mul_pow]
        exact Nat.pow_lt_pow_left h90 (by omega)
      have hrem : 47321 * 275807 < 6 ^ 6 * 283926 := by norm_num
      have hpow_275807 : 275807 ^ (90 * N + 7 + 0 - 6) = (275807 ^ 90) ^ N * 275807 := by
        rw [show 90 * N + 7 + 0 - 6 = 90 * N + 1 by omega, pow_add, pow_one, pow_mul]
      have hpow_283926 :
          47321 ^ (90 * N + 7 + 0 - 6) * 6 ^ (90 * N + 7 + 0) =
            6 ^ 6 * ((283926 ^ 90) ^ N * 283926) := by
        have h283926 : (283926 : ℕ) = 47321 * 6 := by decide
        have hexp : (47321 * 6) ^ (90 * N + 1) = (283926 ^ 90) ^ N * 283926 := by
          rw [← h283926, pow_add, pow_one, pow_mul]
        calc
          47321 ^ (90 * N + 7 + 0 - 6) * 6 ^ (90 * N + 7 + 0)
              = 47321 ^ (90 * N + 1) * 6 ^ (6 + (90 * N + 1)) := by
                  rw [show 90 * N + 7 + 0 - 6 = 90 * N + 1 by omega,
                    show 90 * N + 7 + 0 = 6 + (90 * N + 1) by omega]
          _ = 47321 ^ (90 * N + 1) * (6 ^ 6 * 6 ^ (90 * N + 1)) := by
                rw [pow_add 6 6 (90 * N + 1)]
          _ = 6 ^ 6 * (47321 ^ (90 * N + 1) * 6 ^ (90 * N + 1)) := by ring
          _ = 6 ^ 6 * ((47321 * 6) ^ (90 * N + 1)) := by rw [← mul_pow]
          _ = 6 ^ 6 * ((283926 ^ 90) ^ N * 283926) := by rw [hexp]
      calc
        10 ^ N * (47321 * 275807 ^ (90 * N + 7 + 0 - 6))
            = (10 ^ N * (275807 ^ 90) ^ N) * (47321 * 275807) := by
                rw [hpow_275807]
                ring
        _ < (283926 ^ 90) ^ N * (6 ^ 6 * 283926) := Nat.mul_lt_mul'' hN_pow hrem
        _ = 6 ^ 6 * ((283926 ^ 90) ^ N * 283926) := by ring
        _ = 47321 ^ (90 * N + 7 + 0 - 6) * 6 ^ (90 * N + 7 + 0) := hpow_283926.symm
  | succ k ih =>
      have hk : 90 * N + 7 ≤ 90 * N + 7 + k := by omega
      have ihk := ih hk
      have hmul :
          275807 * (10 ^ N * (47321 * 275807 ^ (90 * N + 7 + k - 6))) <
            275807 * (47321 ^ (90 * N + 7 + k - 6) * 6 ^ (90 * N + 7 + k)) :=
        Nat.mul_lt_mul_of_pos_left ihk (by decide)
      have h275807_lt :
          275807 * (47321 ^ (90 * N + 7 + k - 6) * 6 ^ (90 * N + 7 + k)) <
            (47321 * 6) * (47321 ^ (90 * N + 7 + k - 6) * 6 ^ (90 * N + 7 + k)) := by
        apply Nat.mul_lt_mul_of_pos_right (by decide : 275807 < 47321 * 6)
        positivity
      have hrewL :
          10 ^ N * (47321 * 275807 ^ (90 * N + 7 + (k + 1) - 6)) =
            275807 * (10 ^ N * (47321 * 275807 ^ (90 * N + 7 + k - 6))) := by
        rw [show 90 * N + 7 + (k + 1) - 6 = (90 * N + 7 + k - 6) + 1 by omega, pow_succ' 275807,
          mul_left_comm 47321 275807, mul_left_comm (10 ^ N) 275807]
      have hrewR :
          (47321 * 6) * (47321 ^ (90 * N + 7 + k - 6) * 6 ^ (90 * N + 7 + k)) =
            47321 ^ (90 * N + 7 + (k + 1) - 6) * 6 ^ (90 * N + 7 + (k + 1)) := by
        rw [show 90 * N + 7 + (k + 1) - 6 = (90 * N + 7 + k - 6) + 1 by omega,
          show 90 * N + 7 + (k + 1) = (90 * N + 7 + k) + 1 by omega, pow_succ' 47321, pow_succ' 6,
          mul_mul_mul_comm]
      calc
        10 ^ N * (47321 * 275807 ^ (90 * N + 7 + (k + 1) - 6))
            = 275807 * (10 ^ N * (47321 * 275807 ^ (90 * N + 7 + k - 6))) := hrewL
        _ < 275807 * (47321 ^ (90 * N + 7 + k - 6) * 6 ^ (90 * N + 7 + k)) := hmul
        _ < (47321 * 6) * (47321 ^ (90 * N + 7 + k - 6) * 6 ^ (90 * N + 7 + k)) := h275807_lt
        _ = 47321 ^ (90 * N + 7 + (k + 1) - 6) * 6 ^ (90 * N + 7 + (k + 1)) := hrewR

private lemma million_digit_lt_six_pow_of_floor {u : ℕ} (hu : 90000007 ≤ u) :
    (10 ^ 1000) ^ 1000 * (47321 * 275807 ^ (u - 6)) < 47321 ^ (u - 6) * 6 ^ u := by
  have h := exp_margin_of_N (1000 * 1000) u (by decide) (by omega)
  rwa [pow_mul] at h

private lemma gap7_tridecuple_47321 {l u : ℕ} (hu : 6541380665835014 ≤ u)
    (hlin : 32 * l ≤ 29 * u + 35) : l + 613254437422031 ≤ u := by omega

private lemma gap11_tridecuple_47321 {l u : ℕ} (hu : 6541380665835014 ≤ u)
    (hlin : 34 * l ≤ 25 * u + 36) : l + 1731541940956326 ≤ u := by omega

private lemma gap13_tridecuple_47321 {l u : ℕ} (hu : 6541380665835014 ≤ u)
    (hlin : 16 * l ≤ 11 * u + 17) : l + 2044181458073440 ≤ u := by omega

/-- Global `componentIndex N r₀ = p ^ j` profile coupling the tridecuple floor
`6541380665835014 ≤ u` with the sixth-order `275807 / 47321` Padé contraction, yielding
`(10 ^ 1000) ^ 1000 * p * k_pade.natAbs < 6 ^ u` (`10 ^ 1,000,000` margin) and sharpened repunit
slopes and additive gaps across `r ∈ {3, 5, 7, 11, 13}`. -/
theorem even_prime_power_275807_47321_and_million_digit_profile {N r₀ p j : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hr₀ : r₀ ∈ N.primeFactors)
    (hp : p.Prime) (hj_pos : 0 < j) (hj_even : Even j)
    (hidx : componentIndex N r₀ = p ^ j) :
    ∃ q s u r l : ℕ,
      let k_pade : ℤ := ((s : ℤ) * padeSeqB u p - padeSeqA u p) / (p : ℤ) ^ (2 * u + 1)
      r₀ = q ∧ q.Prime ∧ q % 4 = 1 ∧ N.factorization q = 1 ∧ Odd s ∧
      j = 2 * u ∧ 6541380665835014 ≤ u ∧
      sigma 1 (p ^ (2 * u)) = q ∧ q + 1 = 2 * s ^ 2 ∧ sigma 1 (s ^ 2) = p ^ (2 * u) ∧
      1 ≤ k_pade ∧
      47321 ^ (u - 6) * (p * k_pade.natAbs) < 47321 * 275807 ^ (u - 6) ∧
      (10 ^ 1000) ^ 1000 * p * k_pade.natAbs < 6 ^ u ∧
      ((p % 4 = 3 ∨ Even u) → 2 * (10 ^ 1000) ^ 1000 * p < 6 ^ u) ∧
      (p ∣ 64 ^ u - 1 → (10 ^ 1000) ^ 1000 * p ^ 2 < 6 ^ u) ∧
      ((2 * u + 1) ∣ p - 2 → (10 ^ 1000) ^ 1000 * u * p < 6 ^ u) ∧
      r ∈ ({3, 5, 7, 11, 13} : Finset ℕ) ∧ r.Prime ∧ 2 < l ∧ l.Prime ∧
      r ^ 2 ∣ N ∧ geometricBlock r l = p ∧
      (3 ≤ r → 43 * l ≤ 69 * u + 50) ∧
      (5 ≤ r → 31 * l ≤ 34 * u + 34) ∧
      (7 ≤ r → 32 * l ≤ 29 * u + 35 ∧ l + 613254437422031 ≤ u) ∧
      (11 ≤ r → 34 * l ≤ 25 * u + 36 ∧ l + 1731541940956326 ≤ u) ∧
      (13 ≤ r → 16 * l ≤ 11 * u + 17 ∧ l + 2044181458073440 ≤ u) ∧
      (∀ r' ∈ s.primeFactors,
        let l' : ℕ := 2 * s.factorization r' + 1
        geometricBlock r' l' = p →
          (43 * l' ≤ 69 * u + 50) ∧
          (5 ≤ r' → 31 * l' ≤ 34 * u + 34) ∧
          (7 ≤ r' → 32 * l' ≤ 29 * u + 35 ∧ l' + 613254437422031 ≤ u) ∧
          (11 ≤ r' → 34 * l' ≤ 25 * u + 36 ∧ l' + 1731541940956326 ≤ u) ∧
          (13 ≤ r' → 16 * l' ≤ 11 * u + 17 ∧ l' + 2044181458073440 ≤ u)) := by
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
  have hp3 : 3 ≤ p := odd_prime_ge_three_47321 hp hpo
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
  have hu6 : 6 ≤ u := by omega
  have hu90000007 : 90000007 ≤ u := by omega
  have h47321_pk : 47321 ^ (u - 6) * (p * k_pade.natAbs) < 47321 * 275807 ^ (u - 6) :=
    (padeSeq_sharpened_275807_47321_contraction hp3 hu6).2.2.2.2.2 k_pade hk1 hpu1_k
  have hnum := million_digit_lt_six_pow_of_floor hu90000007
  have hM_pk : (10 ^ 1000) ^ 1000 * p * k_pade.natAbs < 6 ^ u := by
    have hmul :
        47321 ^ (u - 6) * ((10 ^ 1000) ^ 1000 * p * k_pade.natAbs) < 47321 ^ (u - 6) * 6 ^ u := by
      calc
        47321 ^ (u - 6) * ((10 ^ 1000) ^ 1000 * p * k_pade.natAbs)
            = (10 ^ 1000) ^ 1000 * (47321 ^ (u - 6) * (p * k_pade.natAbs)) := by
                rw [mul_assoc ((10 ^ 1000) ^ 1000) p k_pade.natAbs, mul_left_comm]
        _ < (10 ^ 1000) ^ 1000 * (47321 * 275807 ^ (u - 6)) :=
            Nat.mul_lt_mul_of_pos_left h47321_pk (by positivity)
        _ < 47321 ^ (u - 6) * 6 ^ u := hnum
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hpar_cap : p % 4 = 3 ∨ Even u → 2 * (10 ^ 1000) ^ 1000 * p < 6 ^ u := by
    intro hcond
    have hk2 : 2 ≤ k_pade :=
      (even_index_pade_quotient_parity_and_doubled_cap hp hpo hs hu hσq hplus hσs).2.2 hcond |>.1
    have hk2_nat : 2 ≤ k_pade.natAbs := by
      have hnat_abs : (k_pade.natAbs : ℤ) = k_pade := Int.natAbs_of_nonneg (by omega)
      omega
    have hle : 2 * (10 ^ 1000) ^ 1000 * p ≤ (10 ^ 1000) ^ 1000 * p * k_pade.natAbs := by
      calc
        2 * (10 ^ 1000) ^ 1000 * p = (10 ^ 1000) ^ 1000 * p * 2 := by
            rw [mul_comm 2 ((10 ^ 1000) ^ 1000), mul_assoc, mul_comm 2 p, ← mul_assoc]
        _ ≤ (10 ^ 1000) ^ 1000 * p * k_pade.natAbs := Nat.mul_le_mul_left _ hk2_nat
    exact lt_of_le_of_lt hle hM_pk
  have hmodp_cap : p ∣ 64 ^ u - 1 → (10 ^ 1000) ^ 1000 * p ^ 2 < 6 ^ u := by
    intro hp64
    have hpk : (p : ℤ) ≤ k_pade :=
      (even_index_pade_quotient_mod_p_and_sub_two hp hpo hs hu hσq hplus hσs).2.1 hp64 |>.1
    have hpk_nat : p ≤ k_pade.natAbs := by
      have hnat_abs : (k_pade.natAbs : ℤ) = k_pade := Int.natAbs_of_nonneg (by omega)
      omega
    have hle : (10 ^ 1000) ^ 1000 * p ^ 2 ≤ (10 ^ 1000) ^ 1000 * p * k_pade.natAbs := by
      calc
        (10 ^ 1000) ^ 1000 * p ^ 2 = (10 ^ 1000) ^ 1000 * p * p := by rw [sq p, ← mul_assoc]
        _ ≤ (10 ^ 1000) ^ 1000 * p * k_pade.natAbs := Nat.mul_le_mul_left _ hpk_nat
    exact lt_of_le_of_lt hle hM_pk
  have hdiv_cap : (2 * u + 1) ∣ p - 2 → (10 ^ 1000) ^ 1000 * u * p < 6 ^ u := by
    intro hdiv
    have huk : (u : ℤ) ≤ k_pade :=
      (even_index_pade_quotient_mod_two_len_collapse hr₀_prime hp hpo hs hu hσq hplus hσs hdiv).2.1
    have huk_nat : u ≤ k_pade.natAbs := by
      have hnat_abs : (k_pade.natAbs : ℤ) = k_pade := Int.natAbs_of_nonneg (by omega)
      omega
    have hle : (10 ^ 1000) ^ 1000 * u * p ≤ (10 ^ 1000) ^ 1000 * p * k_pade.natAbs := by
      calc
        (10 ^ 1000) ^ 1000 * u * p = (10 ^ 1000) ^ 1000 * p * u := by
            rw [mul_assoc, mul_comm u p, ← mul_assoc]
        _ ≤ (10 ^ 1000) ^ 1000 * p * k_pade.natAbs := Nat.mul_le_mul_left _ huk_nat
    exact lt_of_le_of_lt hle hM_pk
  have hk_pos_nat : 1 ≤ k_pade.natAbs := by
    have hnat_abs : (k_pade.natAbs : ℤ) = k_pade := Int.natAbs_of_nonneg (by omega)
    omega
  have hslopes_of_gb :
      ∀ r' l' : ℕ, 2 ≤ l' → geometricBlock r' l' = p →
        (3 ≤ r' → 43 * l' ≤ 69 * u + 50) ∧
        (5 ≤ r' → 31 * l' ≤ 34 * u + 34) ∧
        (7 ≤ r' → 32 * l' ≤ 29 * u + 35 ∧ l' + 613254437422031 ≤ u) ∧
        (11 ≤ r' → 34 * l' ≤ 25 * u + 36 ∧ l' + 1731541940956326 ≤ u) ∧
        (13 ≤ r' → 16 * l' ≤ 11 * u + 17 ∧ l' + 2044181458073440 ≤ u) := by
    intro r' l' hl'2 hgb'
    have hpow_lt_p : r' ^ (l' - 1) < p := by
      have hl'1 : 1 ≤ l' := by omega
      have hl'_sub_pos : 0 < l' - 1 := by omega
      have h0_mem : 0 ∈ Finset.range (l' - 1) := Finset.mem_range.mpr hl'_sub_pos
      have h1_le : 1 ≤ ∑ t ∈ Finset.range (l' - 1), r' ^ t := by
        have hle := Finset.single_le_sum (f := fun t => r' ^ t) (fun _ _ => Nat.zero_le _) h0_mem
        simpa using hle
      have hsum : geometricBlock r' l' = (∑ t ∈ Finset.range (l' - 1), r' ^ t) + r' ^ (l' - 1) := by
        dsimp [geometricBlock]
        conv_lhs => rw [← Nat.sub_add_cancel hl'1, Finset.sum_range_succ]
      linarith only [h1_le, hsum, hgb']
    have h47321_r' : 47321 ^ (u - 6) * r' ^ (l' - 1) < 47321 * 275807 ^ (u - 6) := by
      calc
        47321 ^ (u - 6) * r' ^ (l' - 1) < 47321 ^ (u - 6) * p :=
            Nat.mul_lt_mul_of_pos_left hpow_lt_p (by positivity)
        _ ≤ 47321 ^ (u - 6) * (p * k_pade.natAbs) :=
            Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right p hk_pos_nat)
        _ < 47321 * 275807 ^ (u - 6) := h47321_pk
    obtain ⟨hs3, hs5, hs7, hs11, hs13⟩ :=
      sharpened_repunit_slopes_of_275807_47321_cap hu6 (by omega) h47321_r'
    refine ⟨hs3, hs5, ?_, ?_, ?_⟩
    · intro hr7
      exact ⟨hs7 hr7, gap7_tridecuple_47321 hu_ge (hs7 hr7)⟩
    · intro hr11
      exact ⟨hs11 hr11, gap11_tridecuple_47321 hu_ge (hs11 hr11)⟩
    · intro hr13
      exact ⟨hs13 hr13, gap13_tridecuple_47321 hu_ge (hs13 hr13)⟩
  obtain ⟨hs3, hs5, hs7, hs11, hs13⟩ := hslopes_of_gb r l (by omega) hgb
  refine ⟨r₀, s, u, r, l, rfl, hr₀_prime, hr₀4, ha1, hs, hj_eq, hu_ge, hσq, hplus, hσs,
    hk1, h47321_pk, hM_pk, hpar_cap, hmodp_cap, hdiv_cap,
    hr_mem, hr_prime, hl_gt2, hl_prime, hr2_N, hgb, hs3, hs5, hs7, hs11, hs13, ?_⟩
  intro r' hr'_mem l' hgb'
  obtain ⟨hr'_prime, hr'_dvd, _⟩ := Nat.mem_primeFactors.mp hr'_mem
  have hr'_odd : Odd r' := hs.of_dvd_nat hr'_dvd
  have hr'_ge3 : 3 ≤ r' := odd_prime_ge_three_47321 hr'_prime hr'_odd
  have he_pos : 1 ≤ s.factorization r' :=
    (hr'_prime.dvd_iff_one_le_factorization hs.pos.ne').mp hr'_dvd
  have hl'_ge2 : 2 ≤ l' := by dsimp [l']; omega
  obtain ⟨hs3', hs5', hs7', hs11', hs13'⟩ := hslopes_of_gb r' l' hl'_ge2 hgb'
  exact ⟨hs3' hr'_ge3, hs5', hs7', hs11', hs13'⟩

end OddPerfect
