module

public import OddPerfect.PadicRungeSubTwoObstruction
public import OddPerfect.EvenIndexExponent256
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# p-adic Diagonal Pell–Padé Approximant Obstruction (`OddPerfect.PadicPadeApproximantObstruction`)

Constructs the explicit diagonal `[u / u]` Pell–Padé approximant tower `(padeSeqA u p, padeSeqB u p)`
for the even-index prime-power component equation `2 * (p - 1) * s ^ 2 - (p - 2) = p ^ (2 * u + 1)`
and sharpens the unconditional exponential base cap from `p < 8 ^ u` to **`p < 6 ^ u`**:

1. `padeSeqA`, `padeSeqB`, and `padeSeq_pell_norm_and_bounds`:
   - Exact Pell–Padé norm identity:
     `2 * ((p : ℤ) - 1) * padeSeqA u p ^ 2 - ((p : ℤ) - 2) * padeSeqB u p ^ 2 = (p : ℤ) ^ (2 * u + 1)`.
   - Mod-`p` congruences: `padeSeqA u p ≡ (-8 : ℤ) ^ u [ZMOD (p : ℤ)]` and
     `padeSeqB u p ≡ (-8 : ℤ) ^ u [ZMOD (p : ℤ)]`.
   - Positivity, linear ratio bounds `4 * padeSeqA u p ≤ 3 * padeSeqB u p` (`1 ≤ u`),
     recurrence contraction `padeSeqB (u + 1) p < 6 * (p : ℤ) * padeSeqB u p` (`1 ≤ u`),
     `padeSeqB u p < 7 * 6 ^ (u - 1) * (p : ℤ) ^ u` (`1 ≤ u`), and via leading coefficients at `u = 7`
     (`275807 < 279936 = 6 ^ 7`), `padeSeqB u p < 6 ^ u * (p : ℤ) ^ u` for all `7 ≤ u`.
2. `even_index_pade_full_precision_divisibility`:
   Full `(2 * u + 1)`-order `p`-adic divisibility
   `((p : ℤ) ^ (2 * u + 1)) ∣ (s : ℤ) * padeSeqB u p - padeSeqA u p`.
3. `even_index_prime_lt_seven_mul_six_pow` (`p < 7 * 6 ^ (u - 1)` for `1 ≤ u`) and
   `even_index_prime_lt_six_pow_of_seven_le` (`p < 6 ^ u` for `7 ≤ u`).
4. `even_prime_power_component_base_lt_six_pow`:
   Combines (3) with `component_prime_power_index_exponent_ge_256` (`128 ≤ u`) to deduce
   `p < 6 ^ u` unconditionally on every even prime-power component index `i = p ^ (2 * u)`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-! ### 1. Diagonal Pell–Padé Approximant Tower -/

/-- Auxiliary paired recurrence generating `(padeSeqA u p, padeSeqB u p)`. -/
@[expose] def padeSeqPair : ℕ → ℕ → ℤ × ℤ
  | 0, _ => (1, 1)
  | u + 1, p =>
      let ab := padeSeqPair u p
      ((3 * (p : ℤ) - 4) * ab.1 + 2 * ((p : ℤ) - 2) * ab.2,
       4 * ((p : ℤ) - 1) * ab.1 + (3 * (p : ℤ) - 4) * ab.2)

/-- Numerator sequence `A_u(p)` of the diagonal `[u / u]` Pell–Padé approximant. -/
@[expose] def padeSeqA (u p : ℕ) : ℤ := (padeSeqPair u p).1

/-- Denominator sequence `B_u(p)` of the diagonal `[u / u]` Pell–Padé approximant. -/
@[expose] def padeSeqB (u p : ℕ) : ℤ := (padeSeqPair u p).2

@[simp] theorem padeSeqA_zero (p : ℕ) : padeSeqA 0 p = 1 := rfl
@[simp] theorem padeSeqB_zero (p : ℕ) : padeSeqB 0 p = 1 := rfl

@[simp] theorem padeSeqA_succ (u p : ℕ) :
    padeSeqA (u + 1) p =
      (3 * (p : ℤ) - 4) * padeSeqA u p + 2 * ((p : ℤ) - 2) * padeSeqB u p := rfl

@[simp] theorem padeSeqB_succ (u p : ℕ) :
    padeSeqB (u + 1) p =
      4 * ((p : ℤ) - 1) * padeSeqA u p + (3 * (p : ℤ) - 4) * padeSeqB u p := rfl

/-- Exact polynomial Pell–Padé norm identity for all `u, p : ℕ`. -/
theorem padeSeq_pell_norm (u p : ℕ) :
    2 * ((p : ℤ) - 1) * padeSeqA u p ^ 2 - ((p : ℤ) - 2) * padeSeqB u p ^ 2 =
      (p : ℤ) ^ (2 * u + 1) := by
  induction u with
  | zero =>
      simp
      ring
  | succ u ih =>
      simp only [padeSeqA_succ, padeSeqB_succ]
      have hid :
          2 * ((p : ℤ) - 1) *
              ((3 * (p : ℤ) - 4) * padeSeqA u p + 2 * ((p : ℤ) - 2) * padeSeqB u p) ^ 2 -
            ((p : ℤ) - 2) *
              (4 * ((p : ℤ) - 1) * padeSeqA u p + (3 * (p : ℤ) - 4) * padeSeqB u p) ^ 2 =
          (p : ℤ) ^ 2 *
            (2 * ((p : ℤ) - 1) * padeSeqA u p ^ 2 - ((p : ℤ) - 2) * padeSeqB u p ^ 2) := by
        ring
      rw [hid, ih, ← pow_add]
      congr 1
      omega

/-- Exact divisibility form of the mod-`p` congruence for `padeSeqA` and `padeSeqB`. -/
theorem padeSeq_sub_neg_eight_pow_dvd (u p : ℕ) :
    (p : ℤ) ∣ padeSeqA u p - (-8 : ℤ) ^ u ∧
    (p : ℤ) ∣ padeSeqB u p - (-8 : ℤ) ^ u := by
  induction u with
  | zero =>
      simp
  | succ u ih =>
      rcases ih with ⟨ha, hb⟩
      constructor
      · have hid :
            padeSeqA (u + 1) p - (-8 : ℤ) ^ (u + 1) =
              (3 * (p : ℤ) - 4) * (padeSeqA u p - (-8 : ℤ) ^ u) +
              2 * ((p : ℤ) - 2) * (padeSeqB u p - (-8 : ℤ) ^ u) +
              (p : ℤ) * (5 * (-8 : ℤ) ^ u) := by
          simp only [padeSeqA_succ, pow_succ]
          ring
        rw [hid]
        exact dvd_add (dvd_add (dvd_mul_of_dvd_right ha _) (dvd_mul_of_dvd_right hb _))
          (dvd_mul_right _ _)
      · have hid :
            padeSeqB (u + 1) p - (-8 : ℤ) ^ (u + 1) =
              4 * ((p : ℤ) - 1) * (padeSeqA u p - (-8 : ℤ) ^ u) +
              (3 * (p : ℤ) - 4) * (padeSeqB u p - (-8 : ℤ) ^ u) +
              (p : ℤ) * (7 * (-8 : ℤ) ^ u) := by
          simp only [padeSeqB_succ, pow_succ]
          ring
        rw [hid]
        exact dvd_add (dvd_add (dvd_mul_of_dvd_right ha _) (dvd_mul_of_dvd_right hb _))
          (dvd_mul_right _ _)

/-- Mod-`p` congruence `padeSeqA u p ≡ (-8) ^ u [ZMOD p]` and `padeSeqB u p ≡ (-8) ^ u [ZMOD p]`. -/
theorem padeSeq_modEq (u p : ℕ) :
    padeSeqA u p ≡ (-8 : ℤ) ^ u [ZMOD (p : ℤ)] ∧
    padeSeqB u p ≡ (-8 : ℤ) ^ u [ZMOD (p : ℤ)] := by
  rcases padeSeq_sub_neg_eight_pow_dvd u p with ⟨ha, hb⟩
  exact ⟨Int.modEq_iff_dvd.mpr (by simpa [dvd_neg] using dvd_neg.mpr ha),
    Int.modEq_iff_dvd.mpr (by simpa [dvd_neg] using dvd_neg.mpr hb)⟩

theorem padeSeq_one_le {p : ℕ} (hp3 : 3 ≤ p) (u : ℕ) :
    1 ≤ padeSeqA u p ∧ 1 ≤ padeSeqB u p := by
  induction u with
  | zero =>
      simp
  | succ u ih =>
      rcases ih with ⟨ha, hb⟩
      have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
      constructor <;> simp only [padeSeqA_succ, padeSeqB_succ] <;> nlinarith

theorem padeSeqB_sub_padeSeqA_succ (u p : ℕ) :
    padeSeqB (u + 1) p - padeSeqA (u + 1) p = (p : ℤ) * (padeSeqA u p + padeSeqB u p) := by
  simp only [padeSeqA_succ, padeSeqB_succ]
  ring

theorem padeSeqA_lt_padeSeqB {p u : ℕ} (hp3 : 3 ≤ p) (hu : 1 ≤ u) :
    padeSeqA u p < padeSeqB u p := by
  cases u with
  | zero => omega
  | succ k =>
      have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
      obtain ⟨ha, hb⟩ := padeSeq_one_le hp3 k
      have hdiff := padeSeqB_sub_padeSeqA_succ k p
      nlinarith

theorem four_mul_padeSeqA_le_three_mul_padeSeqB {p u : ℕ} (hp3 : 3 ≤ p) (hu : 1 ≤ u) :
    4 * padeSeqA u p ≤ 3 * padeSeqB u p := by
  cases u with
  | zero => omega
  | succ k =>
      have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
      obtain ⟨ha, hb⟩ := padeSeq_one_le hp3 k
      have hid :
          3 * padeSeqB (k + 1) p - 4 * padeSeqA (k + 1) p =
            4 * padeSeqA k p + ((p : ℤ) + 4) * padeSeqB k p := by
        simp only [padeSeqA_succ, padeSeqB_succ]
        ring
      nlinarith

theorem padeSeqB_succ_lt_six_mul {p u : ℕ} (hp3 : 3 ≤ p) (hu : 1 ≤ u) :
    padeSeqB (u + 1) p < 6 * (p : ℤ) * padeSeqB u p := by
  have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
  obtain ⟨_, hb⟩ := padeSeq_one_le hp3 u
  have h43 := four_mul_padeSeqA_le_three_mul_padeSeqB hp3 hu
  have hstep :
      4 * ((p : ℤ) - 1) * padeSeqA u p + (3 * (p : ℤ) - 4) * padeSeqB u p ≤
        ((p : ℤ) - 1) * (3 * padeSeqB u p) + (3 * (p : ℤ) - 4) * padeSeqB u p := by
    have hmul : ((p : ℤ) - 1) * (4 * padeSeqA u p) ≤ ((p : ℤ) - 1) * (3 * padeSeqB u p) :=
      mul_le_mul_of_nonneg_left h43 (by linarith)
    linarith
  have hid :
      ((p : ℤ) - 1) * (3 * padeSeqB u p) + (3 * (p : ℤ) - 4) * padeSeqB u p =
        6 * (p : ℤ) * padeSeqB u p - 7 * padeSeqB u p := by
    ring
  rw [padeSeqB_succ]
  linarith

theorem padeSeqB_lt_seven_mul_six_pow {p u : ℕ} (hp3 : 3 ≤ p) (hu : 1 ≤ u) :
    padeSeqB u p < 7 * 6 ^ (u - 1) * (p : ℤ) ^ u := by
  induction u with
  | zero => omega
  | succ k ih =>
      rcases eq_or_lt_of_le (Nat.zero_le k) with rfl | hk
      · simp only [padeSeqB_succ, padeSeqA_zero, padeSeqB_zero, Nat.sub_self, pow_zero,
          zero_add, pow_one]
        have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
        linarith
      · have ihk := ih hk
        have hstep := padeSeqB_succ_lt_six_mul hp3 hk
        have h6pow : 6 * (6 : ℤ) ^ (k - 1) = (6 : ℤ) ^ k := by
          have hk1 : k = (k - 1) + 1 := by omega
          conv_rhs => rw [hk1, pow_succ']
        have hp_pos : (0 : ℤ) < (p : ℤ) := by
          have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
          linarith
        have hbound :
            6 * (p : ℤ) * padeSeqB k p <
              6 * (p : ℤ) * (7 * 6 ^ (k - 1) * (p : ℤ) ^ k) :=
          mul_lt_mul_of_pos_left ihk (by positivity)
        have hrew :
            6 * (p : ℤ) * (7 * 6 ^ (k - 1) * (p : ℤ) ^ k) =
              7 * (6 : ℤ) ^ (k + 1 - 1) * (p : ℤ) ^ (k + 1) := by
          calc
            6 * (p : ℤ) * (7 * 6 ^ (k - 1) * (p : ℤ) ^ k)
                = 7 * (6 * (6 : ℤ) ^ (k - 1)) * ((p : ℤ) * (p : ℤ) ^ k) := by ring
            _ = 7 * (6 : ℤ) ^ k * (p : ℤ) ^ (k + 1) := by rw [h6pow, ← pow_succ']
            _ = 7 * (6 : ℤ) ^ (k + 1 - 1) * (p : ℤ) ^ (k + 1) := by simp
        linarith

/-- Leading-coefficient pair `(a_lead u, b_lead u)` dominating `(padeSeqA u p, padeSeqB u p)` in `p ^ u`. -/
@[expose] def padeLeadPair : ℕ → ℤ × ℤ
  | 0 => (1, 1)
  | u + 1 =>
      let ab := padeLeadPair u
      (3 * ab.1 + 2 * ab.2, 4 * ab.1 + 3 * ab.2)

@[expose] def padeLeadA (u : ℕ) : ℤ := (padeLeadPair u).1
@[expose] def padeLeadB (u : ℕ) : ℤ := (padeLeadPair u).2

@[simp] theorem padeLeadA_zero : padeLeadA 0 = 1 := rfl
@[simp] theorem padeLeadB_zero : padeLeadB 0 = 1 := rfl
@[simp] theorem padeLeadA_succ (u : ℕ) : padeLeadA (u + 1) = 3 * padeLeadA u + 2 * padeLeadB u := rfl
@[simp] theorem padeLeadB_succ (u : ℕ) : padeLeadB (u + 1) = 4 * padeLeadA u + 3 * padeLeadB u := rfl

private theorem padeSeq_le_padeLead_mul_pow {p : ℕ} (hp3 : 3 ≤ p) (u : ℕ) :
    padeSeqA u p ≤ padeLeadA u * (p : ℤ) ^ u ∧
    padeSeqB u p ≤ padeLeadB u * (p : ℤ) ^ u := by
  induction u with
  | zero =>
      simp
  | succ u ih =>
      rcases ih with ⟨iha, ihb⟩
      obtain ⟨ha_pos, hb_pos⟩ := padeSeq_one_le hp3 u
      have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
      have hpow_nn : (0 : ℤ) ≤ (p : ℤ) ^ u := by positivity
      have ha_step : padeSeqA (u + 1) p ≤ padeLeadA (u + 1) * (p : ℤ) ^ (u + 1) := by
        calc
          padeSeqA (u + 1) p
              = (3 * (p : ℤ) - 4) * padeSeqA u p + 2 * ((p : ℤ) - 2) * padeSeqB u p :=
                  padeSeqA_succ u p
          _ ≤ 3 * (p : ℤ) * padeSeqA u p + 2 * (p : ℤ) * padeSeqB u p := by nlinarith
          _ ≤ 3 * (p : ℤ) * (padeLeadA u * (p : ℤ) ^ u) +
                2 * (p : ℤ) * (padeLeadB u * (p : ℤ) ^ u) := by
              have h1 := mul_le_mul_of_nonneg_left iha (by linarith : 0 ≤ 3 * (p : ℤ))
              have h2 := mul_le_mul_of_nonneg_left ihb (by linarith : 0 ≤ 2 * (p : ℤ))
              linarith
          _ = (3 * padeLeadA u + 2 * padeLeadB u) * ((p : ℤ) ^ u * (p : ℤ)) := by ring
          _ = padeLeadA (u + 1) * (p : ℤ) ^ (u + 1) := by rw [← pow_succ, padeLeadA_succ]
      have hb_step : padeSeqB (u + 1) p ≤ padeLeadB (u + 1) * (p : ℤ) ^ (u + 1) := by
        calc
          padeSeqB (u + 1) p
              = 4 * ((p : ℤ) - 1) * padeSeqA u p + (3 * (p : ℤ) - 4) * padeSeqB u p :=
                  padeSeqB_succ u p
          _ ≤ 4 * (p : ℤ) * padeSeqA u p + 3 * (p : ℤ) * padeSeqB u p := by nlinarith
          _ ≤ 4 * (p : ℤ) * (padeLeadA u * (p : ℤ) ^ u) +
                3 * (p : ℤ) * (padeLeadB u * (p : ℤ) ^ u) := by
              have h1 := mul_le_mul_of_nonneg_left iha (by linarith : 0 ≤ 4 * (p : ℤ))
              have h2 := mul_le_mul_of_nonneg_left ihb (by linarith : 0 ≤ 3 * (p : ℤ))
              linarith
          _ = (4 * padeLeadA u + 3 * padeLeadB u) * ((p : ℤ) ^ u * (p : ℤ)) := by ring
          _ = padeLeadB (u + 1) * (p : ℤ) ^ (u + 1) := by rw [← pow_succ, padeLeadB_succ]
      exact ⟨ha_step, hb_step⟩

theorem padeSeqB_lt_six_pow_of_seven_le {p u : ℕ} (hp3 : 3 ≤ p) (hu : 7 ≤ u) :
    padeSeqB u p < 6 ^ u * (p : ℤ) ^ u := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, u = 7 + k := ⟨u - 7, by omega⟩
  induction k with
  | zero =>
      have hb7 := (padeSeq_le_padeLead_mul_pow hp3 7).2
      have hlead7 : padeLeadB 7 = 275807 := by norm_num [padeLeadB, padeLeadA, padeLeadPair]
      have hp7_pos : (0 : ℤ) < (p : ℤ) ^ 7 := by
        have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
        positivity
      rw [Nat.add_zero]
      rw [hlead7] at hb7
      have hcmp : (275807 : ℤ) * (p : ℤ) ^ 7 < (6 : ℤ) ^ 7 * (p : ℤ) ^ 7 := by
        nlinarith
      exact lt_of_le_of_lt hb7 hcmp
  | succ k ih =>
      have hk7 : 7 ≤ 7 + k := by omega
      have ihk := ih hk7
      have hstep := padeSeqB_succ_lt_six_mul hp3 (by omega : 1 ≤ 7 + k)
      have hp_pos : (0 : ℤ) < (p : ℤ) := by
        have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
        linarith
      have hmul : 6 * (p : ℤ) * padeSeqB (7 + k) p <
          6 * (p : ℤ) * (6 ^ (7 + k) * (p : ℤ) ^ (7 + k)) :=
        mul_lt_mul_of_pos_left ihk (by positivity)
      rw [show 7 + (k + 1) = (7 + k) + 1 by omega]
      have hrew :
          6 * (p : ℤ) * (6 ^ (7 + k) * (p : ℤ) ^ (7 + k)) =
            (6 : ℤ) ^ ((7 + k) + 1) * (p : ℤ) ^ ((7 + k) + 1) := by
        rw [pow_succ', pow_succ']
        ring
      linarith

/-- Bundled norm, mod-`p` congruence, positivity, linear ratio, and `6`-base upper bounds
for the diagonal Pell–Padé approximant tower `(padeSeqA u p, padeSeqB u p)`. -/
theorem padeSeq_pell_norm_and_bounds {p : ℕ} (hp3 : 3 ≤ p) (u : ℕ) :
    (2 * ((p : ℤ) - 1) * padeSeqA u p ^ 2 - ((p : ℤ) - 2) * padeSeqB u p ^ 2 =
        (p : ℤ) ^ (2 * u + 1)) ∧
    (padeSeqA u p ≡ (-8 : ℤ) ^ u [ZMOD (p : ℤ)] ∧
        padeSeqB u p ≡ (-8 : ℤ) ^ u [ZMOD (p : ℤ)]) ∧
    (1 ≤ padeSeqA u p ∧ 1 ≤ padeSeqB u p) ∧
    (padeSeqB (u + 1) p - padeSeqA (u + 1) p = (p : ℤ) * (padeSeqA u p + padeSeqB u p)) ∧
    (1 ≤ u → padeSeqA u p < padeSeqB u p) ∧
    (1 ≤ u → 4 * padeSeqA u p ≤ 3 * padeSeqB u p) ∧
    (1 ≤ u → padeSeqB (u + 1) p < 6 * (p : ℤ) * padeSeqB u p) ∧
    (1 ≤ u → padeSeqB u p < 7 * 6 ^ (u - 1) * (p : ℤ) ^ u) ∧
    (7 ≤ u → padeSeqB u p < 6 ^ u * (p : ℤ) ^ u) :=
  ⟨padeSeq_pell_norm u p,
   padeSeq_modEq u p,
   padeSeq_one_le hp3 u,
   padeSeqB_sub_padeSeqA_succ u p,
   padeSeqA_lt_padeSeqB hp3,
   four_mul_padeSeqA_le_three_mul_padeSeqB hp3,
   padeSeqB_succ_lt_six_mul hp3,
   padeSeqB_lt_seven_mul_six_pow hp3,
   padeSeqB_lt_six_pow_of_seven_le hp3⟩

/-! ### 2. Full `(2 * u + 1)`-Order Padé Divisibility -/

private lemma odd_prime_ge_three_pade {p : ℕ} (hp : p.Prime) (hpo : Odd p) : 3 ≤ p := by
  have h2 : 2 ≤ p := hp.two_le
  rcases eq_or_lt_of_le h2 with rfl | hlt
  · exact absurd hpo (by decide)
  · exact hlt

/-- Full `(2 * u + 1)`-order `p`-adic divisibility of `(s : ℤ) * padeSeqB u p - padeSeqA u p`
for every even-index prime-power cofactor triple `(q, p, s, u)`. -/
theorem even_index_pade_full_precision_divisibility {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    ((p : ℤ) ^ (2 * u + 1)) ∣ (s : ℤ) * padeSeqB u p - padeSeqA u p := by
  have hp3 : 3 ≤ p := odd_prime_ge_three_pade hp hpo
  have hs_nat := even_index_twice_pred_mul_cofactor_sq hp hσq hplus
  have hs_int : 2 * ((p : ℤ) - 1) * (s : ℤ) ^ 2 - ((p : ℤ) - 2) = (p : ℤ) ^ (2 * u + 1) := by
    have hcast := congrArg (Nat.cast (R := ℤ)) hs_nat
    push_cast at hcast
    rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_sub (by omega : 2 ≤ p)] at hcast
    push_cast at hcast
    linarith
  have hpade := padeSeq_pell_norm u p
  have hdvd_prod :
      ((p : ℤ) ^ (2 * u + 1)) ∣
        ((s : ℤ) * padeSeqB u p - padeSeqA u p) *
          (2 * ((p : ℤ) - 1) * ((s : ℤ) * padeSeqB u p + padeSeqA u p)) := by
    have hid :
        ((s : ℤ) * padeSeqB u p - padeSeqA u p) *
            (2 * ((p : ℤ) - 1) * ((s : ℤ) * padeSeqB u p + padeSeqA u p)) =
          (2 * ((p : ℤ) - 1) * (s : ℤ) ^ 2 - ((p : ℤ) - 2)) * padeSeqB u p ^ 2 -
            (2 * ((p : ℤ) - 1) * padeSeqA u p ^ 2 - ((p : ℤ) - 2) * padeSeqB u p ^ 2) := by
      ring
    rw [hid, hs_int, hpade]
    exact ⟨padeSeqB u p ^ 2 - 1, by ring⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hnot_dvd_2p1 : ¬ (p : ℤ) ∣ 2 * ((p : ℤ) - 1) := by
    intro hdvd
    rcases hpZ.dvd_or_dvd hdvd with h2 | hp1
    · have h2nat : p ∣ 2 := Int.natCast_dvd_natCast.mp h2
      have h2eq : p = 2 := (Nat.dvd_prime Nat.prime_two).mp h2nat |>.resolve_left hp.ne_one
      subst h2eq
      exact absurd hpo (by decide)
    · have h1 : (p : ℤ) ∣ 1 := by
        have : (p : ℤ) ∣ (p : ℤ) - ((p : ℤ) - 1) := dvd_sub dvd_rfl hp1
        simpa using this
      exact hp.not_dvd_one (Int.natCast_dvd_natCast.mp h1)
  have hpdvd_s1 : p ∣ s - 1 :=
    (even_index_exact_p_dvd_cofactor_pred hp hpo hs.pos hu hσq hplus hσs).1
  have hp_dvd_s1 : (p : ℤ) ∣ (s : ℤ) - 1 := by
    have : ((s - 1 : ℕ) : ℤ) = (s : ℤ) - 1 := by rw [Nat.cast_sub hs.pos, Nat.cast_one]
    rw [← this]
    exact Int.natCast_dvd_natCast.mpr hpdvd_s1
  obtain ⟨hp_dvd_A, hp_dvd_B⟩ := padeSeq_sub_neg_eight_pow_dvd u p
  have hnot_dvd_sum : ¬ (p : ℤ) ∣ (s : ℤ) * padeSeqB u p + padeSeqA u p := by
    intro hdiv
    have hid :
        2 * (-8 : ℤ) ^ u =
          ((s : ℤ) * padeSeqB u p + padeSeqA u p) -
            ((s : ℤ) - 1) * padeSeqB u p -
            (padeSeqB u p - (-8 : ℤ) ^ u) -
            (padeSeqA u p - (-8 : ℤ) ^ u) := by
      ring
    have hd2u : (p : ℤ) ∣ 2 * (-8 : ℤ) ^ u := by
      rw [hid]
      exact dvd_sub (dvd_sub (dvd_sub hdiv (dvd_mul_of_dvd_left hp_dvd_s1 _)) hp_dvd_B) hp_dvd_A
    have hneg_dvd : (p : ℤ) ∣ ((-1 : ℤ) ^ u) * ((2 ^ (3 * u + 1) : ℕ) : ℤ) := by
      have hid2 : ((-1 : ℤ) ^ u) * ((2 ^ (3 * u + 1) : ℕ) : ℤ) = 2 * (-8 : ℤ) ^ u := by
        push_cast
        rw [show (-8 : ℤ) = (-1 : ℤ) * 2 ^ 3 by norm_num, mul_pow, ← pow_mul, pow_succ']
        ring
      rwa [hid2]
    have hpow_dvd : (p : ℤ) ∣ ((2 ^ (3 * u + 1) : ℕ) : ℤ) := by
      have hunit : IsUnit ((-1 : ℤ) ^ u) := (isUnit_one.neg).pow u
      exact hunit.dvd_mul_left.mp hneg_dvd
    have hd2nat : p ∣ 2 ^ (3 * u + 1) := Int.natCast_dvd_natCast.mp hpow_dvd
    have hd2 : p ∣ 2 := hp.dvd_of_dvd_pow hd2nat
    have h2 : p = 2 := (Nat.dvd_prime Nat.prime_two).mp hd2 |>.resolve_left hp.ne_one
    subst h2
    exact absurd hpo (by decide)
  have hnot_dvd_coeff : ¬ (p : ℤ) ∣ 2 * ((p : ℤ) - 1) * ((s : ℤ) * padeSeqB u p + padeSeqA u p) := by
    intro hdiv
    rcases hpZ.dvd_or_dvd hdiv with h2p1 | hsum
    · exact hnot_dvd_2p1 h2p1
    · exact hnot_dvd_sum hsum
  have hcop : IsCoprime ((p : ℤ) ^ (2 * u + 1))
      (2 * ((p : ℤ) - 1) * ((s : ℤ) * padeSeqB u p + padeSeqA u p)) :=
    (hpZ.coprime_iff_not_dvd.mpr hnot_dvd_coeff).pow_left
  exact hcop.dvd_of_dvd_mul_right hdvd_prod

/-! ### 3. Exponential Base Bounds `p < 7 * 6 ^ (u - 1)` and `p < 6 ^ u` (`7 ≤ u`) -/

private lemma even_index_prime_lt_of_padeSeqB_bound {q p s u M : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u))
    (hB : padeSeqB u p < (M : ℤ) * (p : ℤ) ^ u) :
    p < M := by
  by_contra! hge
  have hp3 : 3 ≤ p := odd_prime_ge_three_pade hp hpo
  have hu1 : 1 ≤ u := hu
  obtain ⟨_, _, hsu, _⟩ := even_index_cofactor_archimedean_sandwich hp hpo hu hσq hplus
  have hsuZ : (s : ℤ) < (p : ℤ) ^ u := by exact_mod_cast hsu
  have hs1Z : (1 : ℤ) ≤ (s : ℤ) := by exact_mod_cast hs.pos
  obtain ⟨hA_ge, hB_ge⟩ := padeSeq_one_le hp3 u
  have hA_lt_B : padeSeqA u p < padeSeqB u p := padeSeqA_lt_padeSeqB hp3 hu1
  have hgeZ : (M : ℤ) ≤ (p : ℤ) := by exact_mod_cast hge
  have hp_pos : (0 : ℤ) < (p : ℤ) := by
    have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
    linarith
  have hpu_pos : (0 : ℤ) < (p : ℤ) ^ u := by positivity
  have hB_lt_pu1 : padeSeqB u p < (p : ℤ) ^ (u + 1) := by
    calc
      padeSeqB u p < (M : ℤ) * (p : ℤ) ^ u := hB
      _ ≤ (p : ℤ) * (p : ℤ) ^ u := mul_le_mul_of_nonneg_right hgeZ hpu_pos.le
      _ = (p : ℤ) ^ (u + 1) := by rw [pow_succ']
  have hpu1_le : (p : ℤ) ^ (u + 1) ≤ (p : ℤ) ^ (2 * u + 1) := by
    have hp1Z : (1 : ℤ) ≤ (p : ℤ) := by linarith
    exact_mod_cast Nat.pow_le_pow_right hp.pos (by omega : u + 1 ≤ 2 * u + 1)
  have hA_lt_pow : padeSeqA u p < (p : ℤ) ^ (2 * u + 1) :=
    lt_of_lt_of_le (lt_trans hA_lt_B hB_lt_pu1) hpu1_le
  have hsB_lt_pow : (s : ℤ) * padeSeqB u p < (p : ℤ) ^ (2 * u + 1) := by
    calc
      (s : ℤ) * padeSeqB u p < (p : ℤ) ^ u * padeSeqB u p :=
          mul_lt_mul_of_pos_right hsuZ (by linarith)
      _ < (p : ℤ) ^ u * (p : ℤ) ^ (u + 1) :=
          mul_lt_mul_of_pos_left hB_lt_pu1 hpu_pos
      _ = (p : ℤ) ^ (2 * u + 1) := by
          rw [← pow_add, show u + (u + 1) = 2 * u + 1 by omega]
  have hdvd := even_index_pade_full_precision_divisibility hp hpo hs hu hσq hplus hσs
  have hsB_pos : 0 < (s : ℤ) * padeSeqB u p := by nlinarith
  have heq : (s : ℤ) * padeSeqB u p = padeSeqA u p := by
    have h0 : (s : ℤ) * padeSeqB u p - padeSeqA u p = 0 := by
      rcases le_or_gt 0 ((s : ℤ) * padeSeqB u p - padeSeqA u p) with hnn | hneg
      · exact Int.eq_zero_of_dvd_of_nonneg_of_lt hnn (by linarith) hdvd
      · have hopp := Int.eq_zero_of_dvd_of_nonneg_of_lt (by linarith) (by linarith)
          (dvd_neg.mpr hdvd)
        linarith
    linarith
  nlinarith

/-- Sharp exponential base cap `p < 7 * 6 ^ (u - 1)` for all `1 ≤ u`. -/
theorem even_index_prime_lt_seven_mul_six_pow {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    p < 7 * 6 ^ (u - 1) := by
  have hp3 : 3 ≤ p := odd_prime_ge_three_pade hp hpo
  have hB : padeSeqB u p < ((7 * 6 ^ (u - 1) : ℕ) : ℤ) * (p : ℤ) ^ u := by
    push_cast
    exact padeSeqB_lt_seven_mul_six_pow hp3 hu
  exact even_index_prime_lt_of_padeSeqB_bound hp hpo hs hu hσq hplus hσs hB

/-- Unconditional Padé-sharpened exponential base cap `p < 6 ^ u` for all `7 ≤ u`. -/
theorem even_index_prime_lt_six_pow_of_seven_le {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu7 : 7 ≤ u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    p < 6 ^ u := by
  have hp3 : 3 ≤ p := odd_prime_ge_three_pade hp hpo
  have hB : padeSeqB u p < ((6 ^ u : ℕ) : ℤ) * (p : ℤ) ^ u := by
    push_cast
    exact padeSeqB_lt_six_pow_of_seven_le hp3 hu7
  exact even_index_prime_lt_of_padeSeqB_bound hp hpo hs (by omega) hσq hplus hσs hB

/-! ### 4. Global Even Prime-Power Component Synthesis (`p < 6 ^ u`) -/

/-- On every even prime-power component index `i = p ^ (2 * u)` of an odd perfect number `N`,
`128 ≤ u` and **`p < 6 ^ u`** hold unconditionally. -/
theorem even_prime_power_component_base_lt_six_pow
    {N q a b i p u : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b) (hl : sigma 1 b = q ^ a * i)
    (hr : sigma 1 (q ^ a) * i = 2 * b) (hp : p.Prime) (hu : 0 < u) (hi : i = p ^ (2 * u)) :
    128 ≤ u ∧ p < 6 ^ u := by
  have h256 := component_prime_power_index_exponent_ge_256 hN ho hq ha hform hqb hl hr hp
    (by omega : 0 < 2 * u) hi
  have hu128 : 128 ≤ u := by omega
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
  rw [ha1, pow_one] at hform hl hr
  rw [hi] at hl hr
  obtain ⟨s, hs, _, _, _, hplus, hσs⟩ := even_prime_power_cofactor_split hq hp hmo hpo hu hl hr
  exact ⟨hu128, even_index_prime_lt_six_pow_of_seven_le hp hpo hs (by omega) hσq hplus hσs⟩

end OddPerfect
