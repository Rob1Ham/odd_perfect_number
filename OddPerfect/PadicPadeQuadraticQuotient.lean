module

public import OddPerfect.PadicPadeApproximantObstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# p-adic Diagonal Pell–Padé Quadratic Quotient & `239 / 41` Sharpening (`OddPerfect.PadicPadeQuadraticQuotient`)

Deepens the diagonal `[u / u]` Pell–Padé theory `(padeSeqA u p, padeSeqB u p)` on even
prime-power component indices `i = p ^ (2 * u)`:

1. `padeSeq_mod_pred_and_sub_two`:
   Exact modular evaluations modulo `p - 1` and `p - 2`:
   - `padeSeqB u p ≡ (-1 : ℤ) ^ u [ZMOD (p : ℤ) - 1]`
   - `padeSeqA u p ≡ (-1 : ℤ) ^ u * (2 * (u : ℤ) + 1) [ZMOD (p : ℤ) - 1]`
   - `padeSeqA u p ≡ 2 ^ u [ZMOD (p : ℤ) - 2]`
   - `padeSeqB u p ≡ (2 * (u : ℤ) + 1) * 2 ^ u [ZMOD (p : ℤ) - 2]`
2. `even_index_pade_quotient_pos_and_quadratic_identity`:
   Positivity `1 ≤ k_pade` and exact quadratic Diophantine identity for the `(2 * u + 1)`-order
   Padé quotient `k_pade := ((s : ℤ) * padeSeqB u p - padeSeqA u p) / (p : ℤ) ^ (2 * u + 1)`,
   yielding `2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) < padeSeqB u p ^ 2` and
   `k_pade ∣ (padeSeqB u p ^ 2 - 1) / (2 * ((p : ℤ) - 1))`.
3. `padeSeq_sharpened_239_41_contraction`:
   For `3 ≤ p` and `2 ≤ u`, `41 * padeSeqA u p ≤ 29 * padeSeqB u p`,
   `41 * padeSeqB (u + 1) p < 239 * (p : ℤ) * padeSeqB u p`, and
   `41 ^ (u - 2) * padeSeqB u p < 41 * 239 ^ (u - 2) * (p : ℤ) ^ u`.
4. `even_index_prime_sharpened_239_41_cap` & `even_prime_power_component_sharpened_pade_cap`:
   Deduces `41 ^ (u - 2) * p < 41 * 239 ^ (u - 2)` for all `2 ≤ u`, and on every even
   prime-power component index `i = p ^ (2 * u)` (`128 ≤ u`) proves unconditionally
   `41 ^ (u - 2) * p < 41 * 239 ^ (u - 2)` and **`20 * p < 6 ^ u`**.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma odd_prime_ge_three_pade_quad {p : ℕ} (hp : p.Prime) (hpo : Odd p) : 3 ≤ p := by
  have h2 : 2 ≤ p := hp.two_le
  rcases eq_or_lt_of_le h2 with rfl | hlt
  · exact absurd hpo (by decide)
  · exact hlt

/-! ### 1. Exact Modular Evaluations Modulo `p - 1` and `p - 2` -/

/-- Exact modular evaluations of `(padeSeqA u p, padeSeqB u p)` modulo `p - 1` and `p - 2`. -/
theorem padeSeq_mod_pred_and_sub_two {p : ℕ} (_hp3 : 3 ≤ p) (u : ℕ) :
    (padeSeqB u p ≡ (-1 : ℤ) ^ u [ZMOD (p : ℤ) - 1]) ∧
    (padeSeqA u p ≡ (-1 : ℤ) ^ u * (2 * (u : ℤ) + 1) [ZMOD (p : ℤ) - 1]) ∧
    (padeSeqA u p ≡ 2 ^ u [ZMOD (p : ℤ) - 2]) ∧
    (padeSeqB u p ≡ (2 * (u : ℤ) + 1) * 2 ^ u [ZMOD (p : ℤ) - 2]) := by
  have hdvd :
      ((p : ℤ) - 1 ∣ padeSeqB u p - (-1 : ℤ) ^ u) ∧
      ((p : ℤ) - 1 ∣ padeSeqA u p - (-1 : ℤ) ^ u * (2 * (u : ℤ) + 1)) ∧
      ((p : ℤ) - 2 ∣ padeSeqA u p - 2 ^ u) ∧
      ((p : ℤ) - 2 ∣ padeSeqB u p - (2 * (u : ℤ) + 1) * 2 ^ u) := by
    induction u with
    | zero =>
        simp
    | succ u ih =>
        rcases ih with ⟨hb1, ha1, ha2, hb2⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · have hid :
              padeSeqB (u + 1) p - (-1 : ℤ) ^ (u + 1) =
                ((p : ℤ) - 1) * (4 * padeSeqA u p + 3 * padeSeqB u p) -
                  (padeSeqB u p - (-1 : ℤ) ^ u) := by
            simp only [padeSeqB_succ, pow_succ]
            ring
          rw [hid]
          exact dvd_sub (dvd_mul_right _ _) hb1
        · have hid :
              padeSeqA (u + 1) p - (-1 : ℤ) ^ (u + 1) * (2 * ((u + 1 : ℕ) : ℤ) + 1) =
                ((p : ℤ) - 1) * (3 * padeSeqA u p + 2 * padeSeqB u p) -
                  (padeSeqA u p - (-1 : ℤ) ^ u * (2 * (u : ℤ) + 1)) -
                  2 * (padeSeqB u p - (-1 : ℤ) ^ u) := by
            simp only [padeSeqA_succ, pow_succ, Nat.cast_add, Nat.cast_one]
            ring
          rw [hid]
          exact dvd_sub (dvd_sub (dvd_mul_right _ _) ha1) (dvd_mul_of_dvd_right hb1 2)
        · have hid :
              padeSeqA (u + 1) p - 2 ^ (u + 1) =
                ((p : ℤ) - 2) * (3 * padeSeqA u p + 2 * padeSeqB u p) +
                  2 * (padeSeqA u p - 2 ^ u) := by
            simp only [padeSeqA_succ, pow_succ]
            ring
          rw [hid]
          exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_right ha2 2)
        · have hid :
              padeSeqB (u + 1) p - (2 * ((u + 1 : ℕ) : ℤ) + 1) * 2 ^ (u + 1) =
                ((p : ℤ) - 2) * (4 * padeSeqA u p + 3 * padeSeqB u p) +
                  4 * (padeSeqA u p - 2 ^ u) +
                  2 * (padeSeqB u p - (2 * (u : ℤ) + 1) * 2 ^ u) := by
            simp only [padeSeqB_succ, pow_succ, Nat.cast_add, Nat.cast_one]
            ring
          rw [hid]
          exact dvd_add (dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_right ha2 4))
            (dvd_mul_of_dvd_right hb2 2)
  rcases hdvd with ⟨hb1, ha1, ha2, hb2⟩
  exact
    ⟨Int.modEq_iff_dvd.mpr (by simpa [dvd_neg] using dvd_neg.mpr hb1),
     Int.modEq_iff_dvd.mpr (by simpa [dvd_neg] using dvd_neg.mpr ha1),
     Int.modEq_iff_dvd.mpr (by simpa [dvd_neg] using dvd_neg.mpr ha2),
     Int.modEq_iff_dvd.mpr (by simpa [dvd_neg] using dvd_neg.mpr hb2)⟩

/-! ### 2. Exact Diophantine Quadratic Equation for the Padé Quotient -/

/-- Exact Diophantine quadratic identity, positivity `1 ≤ k_pade`, lower bound
`2 * (p - 1) * p ^ (2 * u + 1) < padeSeqB u p ^ 2`, and divisibility
`k_pade ∣ (padeSeqB u p ^ 2 - 1) / (2 * (p - 1))` for the Padé quotient `k_pade`. -/
theorem even_index_pade_quotient_pos_and_quadratic_identity {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let k_pade : ℤ := ((s : ℤ) * padeSeqB u p - padeSeqA u p) / (p : ℤ) ^ (2 * u + 1)
    ((s : ℤ) * padeSeqB u p - padeSeqA u p = (p : ℤ) ^ (2 * u + 1) * k_pade) ∧
    (1 ≤ k_pade) ∧
    (2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) * k_pade ^ 2 +
        4 * ((p : ℤ) - 1) * padeSeqA u p * k_pade = padeSeqB u p ^ 2 - 1) ∧
    (2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) < padeSeqB u p ^ 2) ∧
    (k_pade ∣ (padeSeqB u p ^ 2 - 1) / (2 * ((p : ℤ) - 1))) := by
  intro k_pade
  have hp3 : 3 ≤ p := odd_prime_ge_three_pade_quad hp hpo
  have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
  have hpow_pos : (0 : ℤ) < (p : ℤ) ^ (2 * u + 1) := by positivity
  have hdvd := even_index_pade_full_precision_divisibility hp hpo hs hu hσq hplus hσs
  have hmul : (s : ℤ) * padeSeqB u p - padeSeqA u p = (p : ℤ) ^ (2 * u + 1) * k_pade :=
    (Int.mul_ediv_cancel' hdvd).symm
  obtain ⟨hp2u_lt, _, _, _⟩ := even_index_cofactor_archimedean_sandwich hp hpo hu hσq hplus
  have hs3 : 3 ≤ s := by
    have h9 : 9 ≤ p ^ (2 * u) := by
      calc
        9 = 3 ^ 2 := by norm_num
        _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
        _ ≤ p ^ (2 * u) := Nat.pow_le_pow_right hp.pos (by omega)
    have h2s2 : 9 < 2 * s ^ 2 := lt_of_le_of_lt h9 hp2u_lt
    by_contra! hs2
    have : 2 * s ^ 2 ≤ 8 := by nlinarith only [hs2]
    omega
  have hs3Z : (3 : ℤ) ≤ (s : ℤ) := by exact_mod_cast hs3
  obtain ⟨hA_ge, hB_ge⟩ := padeSeq_one_le hp3 u
  have hA_lt_B : padeSeqA u p < padeSeqB u p := padeSeqA_lt_padeSeqB hp3 hu
  have hdiff_pos : 0 < (s : ℤ) * padeSeqB u p - padeSeqA u p := by
    have h3B : 3 * padeSeqB u p ≤ (s : ℤ) * padeSeqB u p :=
      mul_le_mul_of_nonneg_right hs3Z (by linarith)
    linarith
  have hk_pos : 0 < k_pade := by
    have hmul_pos : 0 < (p : ℤ) ^ (2 * u + 1) * k_pade := by linarith
    exact (mul_pos_iff_of_pos_left hpow_pos).mp hmul_pos
  have hk1 : 1 ≤ k_pade := hk_pos
  have hs_nat := even_index_twice_pred_mul_cofactor_sq hp hσq hplus
  have hs_int : 2 * ((p : ℤ) - 1) * (s : ℤ) ^ 2 - ((p : ℤ) - 2) = (p : ℤ) ^ (2 * u + 1) := by
    have hcast := congrArg (Nat.cast (R := ℤ)) hs_nat
    push_cast at hcast
    rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_sub (by omega : 2 ≤ p)] at hcast
    push_cast at hcast
    linarith
  have hpade := padeSeq_pell_norm u p
  have hsB_eq : (s : ℤ) * padeSeqB u p = padeSeqA u p + (p : ℤ) ^ (2 * u + 1) * k_pade := by
    linarith
  have hquad_mul :
      (p : ℤ) ^ (2 * u + 1) *
          (2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) * k_pade ^ 2 +
            4 * ((p : ℤ) - 1) * padeSeqA u p * k_pade) =
        (p : ℤ) ^ (2 * u + 1) * (padeSeqB u p ^ 2 - 1) := by
    have h1 :
        2 * ((p : ℤ) - 1) * ((s : ℤ) * padeSeqB u p) ^ 2 - ((p : ℤ) - 2) * padeSeqB u p ^ 2 =
          (p : ℤ) ^ (2 * u + 1) * padeSeqB u p ^ 2 := by
      calc
        2 * ((p : ℤ) - 1) * ((s : ℤ) * padeSeqB u p) ^ 2 - ((p : ℤ) - 2) * padeSeqB u p ^ 2
            = (2 * ((p : ℤ) - 1) * (s : ℤ) ^ 2 - ((p : ℤ) - 2)) * padeSeqB u p ^ 2 := by ring
        _ = (p : ℤ) ^ (2 * u + 1) * padeSeqB u p ^ 2 := by rw [hs_int]
    have h2 :
        (2 * ((p : ℤ) - 1) * ((s : ℤ) * padeSeqB u p) ^ 2 - ((p : ℤ) - 2) * padeSeqB u p ^ 2) -
          (2 * ((p : ℤ) - 1) * padeSeqA u p ^ 2 - ((p : ℤ) - 2) * padeSeqB u p ^ 2) =
            (p : ℤ) ^ (2 * u + 1) * (padeSeqB u p ^ 2 - 1) := by
      rw [h1, hpade]
      ring
    rw [hsB_eq] at h2
    calc
      (p : ℤ) ^ (2 * u + 1) *
          (2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) * k_pade ^ 2 +
            4 * ((p : ℤ) - 1) * padeSeqA u p * k_pade)
          = (2 * ((p : ℤ) - 1) * (padeSeqA u p + (p : ℤ) ^ (2 * u + 1) * k_pade) ^ 2 -
              ((p : ℤ) - 2) * padeSeqB u p ^ 2) -
            (2 * ((p : ℤ) - 1) * padeSeqA u p ^ 2 - ((p : ℤ) - 2) * padeSeqB u p ^ 2) := by
          ring
      _ = (p : ℤ) ^ (2 * u + 1) * (padeSeqB u p ^ 2 - 1) := h2
  have hquad :
      2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) * k_pade ^ 2 +
          4 * ((p : ℤ) - 1) * padeSeqA u p * k_pade =
        padeSeqB u p ^ 2 - 1 :=
    mul_left_cancel₀ hpow_pos.ne' hquad_mul
  have hB2_gt : 2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) < padeSeqB u p ^ 2 := by
    have hk2 : 1 ≤ k_pade ^ 2 := one_le_pow₀ hk1
    have hcoeff_nn : 0 ≤ 2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) :=
      mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hpow_pos.le
    have h1 : 2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) ≤
        2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) * k_pade ^ 2 :=
      le_mul_of_one_le_right hcoeff_nn hk2
    have h4p1 : (8 : ℤ) ≤ 4 * ((p : ℤ) - 1) := by linarith
    have h4p1A : (8 : ℤ) ≤ 4 * ((p : ℤ) - 1) * padeSeqA u p := by
      have := mul_le_mul h4p1 hA_ge (by norm_num) (by linarith)
      linarith
    have h2 : (8 : ℤ) ≤ 4 * ((p : ℤ) - 1) * padeSeqA u p * k_pade := by
      have := mul_le_mul h4p1A hk1 (by norm_num) (by linarith)
      linarith
    linarith
  have hk_dvd : k_pade ∣ (padeSeqB u p ^ 2 - 1) / (2 * ((p : ℤ) - 1)) := by
    have hfac :
        (padeSeqB u p ^ 2 - 1) =
          (2 * ((p : ℤ) - 1)) * (((p : ℤ) ^ (2 * u + 1) * k_pade + 2 * padeSeqA u p) * k_pade) := by
      linarith
    have hdiv_ne : 2 * ((p : ℤ) - 1) ≠ 0 := by linarith
    rw [hfac, Int.mul_ediv_cancel_left _ hdiv_ne]
    exact dvd_mul_left k_pade _
  exact ⟨hmul, hk1, hquad, hB2_gt, hk_dvd⟩

/-! ### 3. Sharpened `239 / 41` Contraction for `2 ≤ u` -/

theorem forty_one_mul_padeSeqA_le_twenty_nine_mul_padeSeqB {p u : ℕ}
    (hp3 : 3 ≤ p) (hu : 2 ≤ u) :
    41 * padeSeqA u p ≤ 29 * padeSeqB u p := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, u = 2 + k := ⟨u - 2, by omega⟩
  have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
  induction k with
  | zero =>
      have hid : 29 * padeSeqB (2 + 0) p - 41 * padeSeqA (2 + 0) p = 592 * (p : ℤ) - 768 := by
        simp only [Nat.add_zero, padeSeqA_succ, padeSeqB_succ, padeSeqA_zero, padeSeqB_zero]
        ring
      linarith
  | succ k ih =>
      have hk2 : 2 ≤ 2 + k := by omega
      have ihk := ih hk2
      obtain ⟨ha, hb⟩ := padeSeq_one_le hp3 (2 + k)
      have hid :
          41 * (29 * padeSeqB (2 + k + 1) p - 41 * padeSeqA (2 + k + 1) p) =
            7 * (p : ℤ) * (29 * padeSeqB (2 + k) p - 41 * padeSeqA (2 + k) p) +
              (2 * (p : ℤ) + 1968) * padeSeqB (2 + k) p + 1968 * padeSeqA (2 + k) p := by
        simp only [padeSeqA_succ, padeSeqB_succ]
        ring
      have hdiff : 0 ≤ 29 * padeSeqB (2 + k) p - 41 * padeSeqA (2 + k) p := by linarith
      have ht1 : 0 ≤ 7 * (p : ℤ) * (29 * padeSeqB (2 + k) p - 41 * padeSeqA (2 + k) p) :=
        mul_nonneg (by positivity) hdiff
      have ht2 : 0 < (2 * (p : ℤ) + 1968) * padeSeqB (2 + k) p :=
        mul_pos (by linarith) (by linarith)
      have hpos : 0 < 41 * (29 * padeSeqB (2 + k + 1) p - 41 * padeSeqA (2 + k + 1) p) := by
        linarith
      rw [← Nat.add_assoc]
      linarith

theorem forty_one_mul_padeSeqB_succ_lt_239_mul {p u : ℕ}
    (hp3 : 3 ≤ p) (hu : 2 ≤ u) :
    41 * padeSeqB (u + 1) p < 239 * (p : ℤ) * padeSeqB u p := by
  have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
  obtain ⟨_, hb⟩ := padeSeq_one_le hp3 u
  have h41_29 := forty_one_mul_padeSeqA_le_twenty_nine_mul_padeSeqB hp3 hu
  have hstep :
      4 * ((p : ℤ) - 1) * (41 * padeSeqA u p) + 41 * (3 * (p : ℤ) - 4) * padeSeqB u p ≤
        4 * ((p : ℤ) - 1) * (29 * padeSeqB u p) + 41 * (3 * (p : ℤ) - 4) * padeSeqB u p := by
    have hmul : 4 * ((p : ℤ) - 1) * (41 * padeSeqA u p) ≤
        4 * ((p : ℤ) - 1) * (29 * padeSeqB u p) :=
      mul_le_mul_of_nonneg_left h41_29 (by linarith)
    linarith
  have hid1 :
      41 * padeSeqB (u + 1) p =
        4 * ((p : ℤ) - 1) * (41 * padeSeqA u p) + 41 * (3 * (p : ℤ) - 4) * padeSeqB u p := by
    rw [padeSeqB_succ]
    ring
  have hid2 :
      4 * ((p : ℤ) - 1) * (29 * padeSeqB u p) + 41 * (3 * (p : ℤ) - 4) * padeSeqB u p =
        239 * (p : ℤ) * padeSeqB u p - 280 * padeSeqB u p := by
    ring
  linarith

theorem forty_one_pow_mul_padeSeqB_lt_239_pow {p u : ℕ}
    (hp3 : 3 ≤ p) (hu : 2 ≤ u) :
    41 ^ (u - 2) * padeSeqB u p < 41 * 239 ^ (u - 2) * (p : ℤ) ^ u := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, u = 2 + k := ⟨u - 2, by omega⟩
  have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
  induction k with
  | zero =>
      simp only [Nat.add_zero, Nat.sub_self, pow_zero, one_mul, mul_one]
      have hid : 41 * (p : ℤ) ^ 2 - padeSeqB 2 p = 104 * (p : ℤ) - 64 := by
        simp only [padeSeqB_succ, padeSeqA_succ, padeSeqA_zero, padeSeqB_zero]
        ring
      linarith
  | succ k ih =>
      have hk2 : 2 ≤ 2 + k := by omega
      have ihk := ih hk2
      have hstep := forty_one_mul_padeSeqB_succ_lt_239_mul hp3 hk2
      have h41_pos : (0 : ℤ) < (41 : ℤ) ^ (2 + k - 2) := by positivity
      have hp_pos : (0 : ℤ) < (p : ℤ) := by linarith
      have h1 :
          (41 : ℤ) ^ (2 + k - 2) * (41 * padeSeqB (2 + k + 1) p) <
            (41 : ℤ) ^ (2 + k - 2) * (239 * (p : ℤ) * padeSeqB (2 + k) p) :=
        mul_lt_mul_of_pos_left hstep h41_pos
      have h2 :
          239 * (p : ℤ) * ((41 : ℤ) ^ (2 + k - 2) * padeSeqB (2 + k) p) <
            239 * (p : ℤ) * (41 * 239 ^ (2 + k - 2) * (p : ℤ) ^ (2 + k)) :=
        mul_lt_mul_of_pos_left ihk (by positivity)
      have hrewL :
          (41 : ℤ) ^ (2 + (k + 1) - 2) * padeSeqB (2 + (k + 1)) p =
            (41 : ℤ) ^ (2 + k - 2) * (41 * padeSeqB (2 + k + 1) p) := by
        rw [show 2 + (k + 1) - 2 = (2 + k - 2) + 1 by omega, pow_succ]
        rw [show 2 + (k + 1) = 2 + k + 1 by omega]
        ring
      have hrewM :
          (41 : ℤ) ^ (2 + k - 2) * (239 * (p : ℤ) * padeSeqB (2 + k) p) =
            239 * (p : ℤ) * ((41 : ℤ) ^ (2 + k - 2) * padeSeqB (2 + k) p) := by
        ring
      have hrewR :
          239 * (p : ℤ) * (41 * 239 ^ (2 + k - 2) * (p : ℤ) ^ (2 + k)) =
            41 * 239 ^ (2 + (k + 1) - 2) * (p : ℤ) ^ (2 + (k + 1)) := by
        rw [show 2 + (k + 1) - 2 = (2 + k - 2) + 1 by omega, pow_succ]
        rw [show 2 + (k + 1) = (2 + k) + 1 by omega, pow_succ]
        ring
      linarith

/-- Bundled `239 / 41` sharpened Padé contraction for `3 ≤ p` and `2 ≤ u`. -/
theorem padeSeq_sharpened_239_41_contraction {p u : ℕ} (hp3 : 3 ≤ p) (hu : 2 ≤ u) :
    (41 * padeSeqA u p ≤ 29 * padeSeqB u p) ∧
    (41 * padeSeqB (u + 1) p < 239 * (p : ℤ) * padeSeqB u p) ∧
    (41 ^ (u - 2) * padeSeqB u p < 41 * 239 ^ (u - 2) * (p : ℤ) ^ u) :=
  ⟨forty_one_mul_padeSeqA_le_twenty_nine_mul_padeSeqB hp3 hu,
   forty_one_mul_padeSeqB_succ_lt_239_mul hp3 hu,
   forty_one_pow_mul_padeSeqB_lt_239_pow hp3 hu⟩

/-! ### 4. Sharpened `239 / 41` Exponential Cap & Unconditional `20 * p < 6 ^ u` -/

/-- Sharpened `239 / 41` exponential base cap `41 ^ (u - 2) * p < 41 * 239 ^ (u - 2)` for `2 ≤ u`. -/
theorem even_index_prime_sharpened_239_41_cap {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu2 : 2 ≤ u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    41 ^ (u - 2) * p < 41 * 239 ^ (u - 2) := by
  have hp3 : 3 ≤ p := odd_prime_ge_three_pade_quad hp hpo
  have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
  have hu : 0 < u := by omega
  obtain ⟨_, _, _, hB2_gt, _⟩ :=
    even_index_pade_quotient_pos_and_quadratic_identity hp hpo hs hu hσq hplus hσs
  obtain ⟨_, hB_ge⟩ := padeSeq_one_le hp3 u
  have hpow_pos : (0 : ℤ) < (p : ℤ) ^ (2 * u + 1) := by positivity
  have hpu_pos : (0 : ℤ) < (p : ℤ) ^ u := by positivity
  have h2p1_gt : (p : ℤ) < 2 * ((p : ℤ) - 1) := by linarith
  have hsq_lt : ((p : ℤ) ^ (u + 1)) ^ 2 < padeSeqB u p ^ 2 := by
    have hsq_eq : ((p : ℤ) ^ (u + 1)) ^ 2 = (p : ℤ) * (p : ℤ) ^ (2 * u + 1) := by
      rw [← pow_mul, ← pow_succ']
      congr 1
      omega
    have hmul : (p : ℤ) * (p : ℤ) ^ (2 * u + 1) < 2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) :=
      mul_lt_mul_of_pos_right h2p1_gt hpow_pos
    linarith
  have hpu1_lt_B : (p : ℤ) ^ (u + 1) < padeSeqB u p := by
    by_contra! hle
    have hsq_le : padeSeqB u p ^ 2 ≤ ((p : ℤ) ^ (u + 1)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hle 2
    linarith
  have h41B := forty_one_pow_mul_padeSeqB_lt_239_pow hp3 hu2
  have h41_pos : (0 : ℤ) < (41 : ℤ) ^ (u - 2) := by positivity
  have hchain :
      (41 : ℤ) ^ (u - 2) * (p : ℤ) * (p : ℤ) ^ u <
        41 * 239 ^ (u - 2) * (p : ℤ) ^ u := by
    calc
      (41 : ℤ) ^ (u - 2) * (p : ℤ) * (p : ℤ) ^ u
          = (41 : ℤ) ^ (u - 2) * (p : ℤ) ^ (u + 1) := by rw [pow_succ']; ring
      _ < (41 : ℤ) ^ (u - 2) * padeSeqB u p := mul_lt_mul_of_pos_left hpu1_lt_B h41_pos
      _ < 41 * 239 ^ (u - 2) * (p : ℤ) ^ u := h41B
  have hltZ : (41 : ℤ) ^ (u - 2) * (p : ℤ) < 41 * 239 ^ (u - 2) :=
    lt_of_mul_lt_mul_right hchain hpu_pos.le
  exact_mod_cast hltZ

private lemma twenty_mul_41_mul_239_pow_lt_41_pow_mul_6_pow {u : ℕ} (hu : 128 ≤ u) :
    20 * (41 * 239 ^ (u - 2)) < 41 ^ (u - 2) * 6 ^ u := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, u = 128 + k := ⟨u - 128, by omega⟩
  induction k with
  | zero =>
      norm_num
  | succ k ih =>
      have hk : 128 ≤ 128 + k := by omega
      have ihk := ih hk
      have hmul :
          239 * (20 * (41 * 239 ^ (128 + k - 2))) <
            239 * (41 ^ (128 + k - 2) * 6 ^ (128 + k)) :=
        Nat.mul_lt_mul_of_pos_left ihk (by decide)
      have h239_lt :
          239 * (41 ^ (128 + k - 2) * 6 ^ (128 + k)) <
            (41 * 6) * (41 ^ (128 + k - 2) * 6 ^ (128 + k)) := by
        apply Nat.mul_lt_mul_of_pos_right (by decide : 239 < 41 * 6)
        positivity
      have hrewL :
          20 * (41 * 239 ^ (128 + (k + 1) - 2)) =
            239 * (20 * (41 * 239 ^ (128 + k - 2))) := by
        rw [show 128 + (k + 1) - 2 = (128 + k - 2) + 1 by omega, pow_succ]
        ring
      have hrewR :
          (41 * 6) * (41 ^ (128 + k - 2) * 6 ^ (128 + k)) =
            41 ^ (128 + (k + 1) - 2) * 6 ^ (128 + (k + 1)) := by
        rw [show 128 + (k + 1) - 2 = (128 + k - 2) + 1 by omega, pow_succ]
        rw [show 128 + (k + 1) = (128 + k) + 1 by omega, pow_succ]
        ring
      linarith

/-- On every even prime-power component index `i = p ^ (2 * u)` of an odd perfect number `N`,
`128 ≤ u`, `41 ^ (u - 2) * p < 41 * 239 ^ (u - 2)`, and **`20 * p < 6 ^ u`** hold unconditionally. -/
theorem even_prime_power_component_sharpened_pade_cap
    {N q a b i p u : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b) (hl : sigma 1 b = q ^ a * i)
    (hr : sigma 1 (q ^ a) * i = 2 * b) (hp : p.Prime) (hu : 0 < u) (hi : i = p ^ (2 * u)) :
    128 ≤ u ∧ 41 ^ (u - 2) * p < 41 * 239 ^ (u - 2) ∧ 20 * p < 6 ^ u := by
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
  have hcap := even_index_prime_sharpened_239_41_cap hp hpo hs (by omega : 2 ≤ u) hσq hplus hσs
  have hnum := twenty_mul_41_mul_239_pow_lt_41_pow_mul_6_pow hu128
  have h41_pos : 0 < 41 ^ (u - 2) := by positivity
  have h20 : 41 ^ (u - 2) * (20 * p) < 41 ^ (u - 2) * 6 ^ u := by
    calc
      41 ^ (u - 2) * (20 * p) = 20 * (41 ^ (u - 2) * p) := by ring
      _ < 20 * (41 * 239 ^ (u - 2)) := Nat.mul_lt_mul_of_pos_left hcap (by decide)
      _ < 41 ^ (u - 2) * 6 ^ u := hnum
  exact ⟨hu128, hcap, Nat.lt_of_mul_lt_mul_left h20⟩

end OddPerfect
