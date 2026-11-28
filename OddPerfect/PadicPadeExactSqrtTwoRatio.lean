module

public import OddPerfect.PadicPadeSublinearRepunitBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact `√2` Pell–Padé Ratio & Weighted Quotient Contraction (`OddPerfect.PadicPadeExactSqrtTwoRatio`)

Formalizes the sharp `√2` upper rational approximation for the diagonal `[u / u]` Pell–Padé
sequences `(padeSeqA u p, padeSeqB u p)` and the weighted contraction of the `(2 * u + 1)`-order
Padé quotient `k_pade := ((s : ℤ) * padeSeqB u p - padeSeqA u p) / (p : ℤ) ^ (2 * u + 1)`:

1. `even_index_pade_sq_lt_half_sq_and_upper_pell`:
   Combines `padeSeq_pell_norm` with `2 * (p - 1) * p ^ (2 * u + 1) < padeSeqB u p ^ 2` to prove
   `2 * padeSeqA u p ^ 2 < padeSeqB u p ^ 2` (so `A_u / B_u < 1 / √2`), together with the uniform
   Pell upper-convergent inequality `P * padeSeqA u p < Q * padeSeqB u p` and
   `P * padeSeqB (u + 1) p < (4 * Q + 3 * P) * p * padeSeqB u p` for every solution
   `2 * Q ^ 2 - P ^ 2 = 1`, instantiated at `(1393, 985)` and `(8119, 5741)`.
2. `even_index_pade_quotient_weighted_contraction`:
   Bounds `2 * (p - 1) * p ^ (2 * u + 1) * k_pade ^ 2 < padeSeqB u p ^ 2`, deducing
   `p ^ (u + 1) * k_pade < padeSeqB u p`,
   `140 * (p - 1) * k_pade * p ^ u < 99 * padeSeqB u p`, and
   `239 ^ (u - 3) * (p * k_pade.natAbs) < 239 * 1393 ^ (u - 3)` for `3 ≤ u`.
3. `even_prime_power_exact_sqrt_two_and_weighted_pade_profile`:
   Unconditional global odd-perfect-number wrapper coupling the tridecuple floor
   `6541380665835014 ≤ u` with the weighted `k_pade` contraction to obtain
   `(10 ^ 600) ^ 2 * p * k_pade.natAbs < 6 ^ u`, `2 * (10 ^ 600) ^ 2 * p < 6 ^ u` when
   `p % 4 = 3 ∨ Even u`, and `(10 ^ 600) ^ 2 * p ^ 2 < 6 ^ u` when `p ∣ 64 ^ u - 1`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma odd_prime_ge_three_sqrt_two {p : ℕ} (hp : p.Prime) (hpo : Odd p) : 3 ≤ p := by
  have h2 : 2 ≤ p := hp.two_le
  rcases eq_or_lt_of_le h2 with rfl | hlt
  · exact absurd hpo (by decide)
  · exact hlt

/-- Exact `A_u / B_u < 1 / √2` inequality (`2 * A_u ^ 2 < B_u ^ 2`), uniform Pell upper-convergent
ratio bounds for all `2 * Q ^ 2 - P ^ 2 = 1`, and instantiations at `(1393, 985)` and
`(8119, 5741)`. -/
theorem even_index_pade_sq_lt_half_sq_and_upper_pell {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    2 * padeSeqA u p ^ 2 < padeSeqB u p ^ 2 ∧
    (∀ P Q : ℤ, 0 < P → 0 < Q → 2 * Q ^ 2 - P ^ 2 = 1 →
      P * padeSeqA u p < Q * padeSeqB u p ∧
      P * padeSeqB (u + 1) p < (4 * Q + 3 * P) * (p : ℤ) * padeSeqB u p) ∧
    1393 * padeSeqA u p < 985 * padeSeqB u p ∧
    8119 * padeSeqA u p < 5741 * padeSeqB u p ∧
    1393 * padeSeqB (u + 1) p < 8119 * (p : ℤ) * padeSeqB u p := by
  have hp3 : 3 ≤ p := odd_prime_ge_three_sqrt_two hp hpo
  have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
  obtain ⟨hA_ge, hB_ge⟩ := padeSeq_one_le hp3 u
  obtain ⟨_, _, _, h2pB2, _⟩ :=
    even_index_pade_quotient_pos_and_quadratic_identity hp hpo hs hu hσq hplus hσs
  have hpell := padeSeq_pell_norm u p
  have h2pA :
      2 * ((p : ℤ) - 1) * padeSeqA u p ^ 2 =
        ((p : ℤ) - 2) * padeSeqB u p ^ 2 + (p : ℤ) ^ (2 * u + 1) := by
    linarith [hpell]
  have h4_eq :
      4 * ((p : ℤ) - 1) ^ 2 * padeSeqA u p ^ 2 =
        2 * ((p : ℤ) - 1) * ((p : ℤ) - 2) * padeSeqB u p ^ 2 +
          2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) := by
    calc
      4 * ((p : ℤ) - 1) ^ 2 * padeSeqA u p ^ 2
          = 2 * ((p : ℤ) - 1) * (2 * ((p : ℤ) - 1) * padeSeqA u p ^ 2) := by ring
      _ = 2 * ((p : ℤ) - 1) * (((p : ℤ) - 2) * padeSeqB u p ^ 2 + (p : ℤ) ^ (2 * u + 1)) := by
          rw [h2pA]
      _ = 2 * ((p : ℤ) - 1) * ((p : ℤ) - 2) * padeSeqB u p ^ 2 +
            2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) := by ring
  have h4_lt :
      4 * ((p : ℤ) - 1) ^ 2 * padeSeqA u p ^ 2 <
        (2 * ((p : ℤ) - 1) ^ 2 - (2 * (p : ℤ) - 3)) * padeSeqB u p ^ 2 := by
    have hrew :
        (2 * ((p : ℤ) - 1) * ((p : ℤ) - 2) + 1) * padeSeqB u p ^ 2 =
          (2 * ((p : ℤ) - 1) ^ 2 - (2 * (p : ℤ) - 3)) * padeSeqB u p ^ 2 := by ring
    linarith [h4_eq, h2pB2, hrew]
  have hB2_pos : 0 < padeSeqB u p ^ 2 := by nlinarith only [hB_ge]
  have h2p3_pos : 0 < (2 * (p : ℤ) - 3) * padeSeqB u p ^ 2 := by nlinarith only [hpZ, hB2_pos]
  have hmul_lt :
      2 * ((p : ℤ) - 1) ^ 2 * (2 * padeSeqA u p ^ 2) <
        2 * ((p : ℤ) - 1) ^ 2 * padeSeqB u p ^ 2 := by
    linarith [h4_lt, h2p3_pos]
  have h2A2_lt_B2 : 2 * padeSeqA u p ^ 2 < padeSeqB u p ^ 2 := by
    have hcoeff_pos : 0 < 2 * ((p : ℤ) - 1) ^ 2 := by nlinarith only [hpZ]
    exact lt_of_mul_lt_mul_left hmul_lt hcoeff_pos.le
  have hpell_all :
      ∀ P Q : ℤ, 0 < P → 0 < Q → 2 * Q ^ 2 - P ^ 2 = 1 →
        P * padeSeqA u p < Q * padeSeqB u p ∧
        P * padeSeqB (u + 1) p < (4 * Q + 3 * P) * (p : ℤ) * padeSeqB u p := by
    intro P Q hP hQ hPQ
    have hsq_diff :
        (Q * padeSeqB u p) ^ 2 - (P * padeSeqA u p) ^ 2 =
          Q ^ 2 * (padeSeqB u p ^ 2 - 2 * padeSeqA u p ^ 2) +
            (2 * Q ^ 2 - P ^ 2) * padeSeqA u p ^ 2 := by ring
    have hsq_pos : 0 < (Q * padeSeqB u p) ^ 2 - (P * padeSeqA u p) ^ 2 := by
      have hQ2_pos : 0 < Q ^ 2 := sq_pos_of_pos hQ
      have hA2_pos : 0 < padeSeqA u p ^ 2 := by nlinarith only [hA_ge]
      have h1 : 0 < Q ^ 2 * (padeSeqB u p ^ 2 - 2 * padeSeqA u p ^ 2) :=
        mul_pos hQ2_pos (by linarith [h2A2_lt_B2])
      rw [hsq_diff, hPQ, one_mul]
      linarith [h1, hA2_pos]
    have hPA_lt_QB : P * padeSeqA u p < Q * padeSeqB u p := by
      have hQB_pos : 0 < Q * padeSeqB u p := mul_pos hQ (by linarith [hB_ge])
      by_contra! hle
      have hsq_le : (Q * padeSeqB u p) ^ 2 ≤ (P * padeSeqA u p) ^ 2 :=
        pow_le_pow_left₀ hQB_pos.le hle 2
      linarith [hsq_pos, hsq_le]
    have hPB_succ : P * padeSeqB (u + 1) p < (4 * Q + 3 * P) * (p : ℤ) * padeSeqB u p := by
      rw [padeSeqB_succ]
      have h1 :
          4 * ((p : ℤ) - 1) * (P * padeSeqA u p) <
            4 * ((p : ℤ) - 1) * (Q * padeSeqB u p) :=
        mul_lt_mul_of_pos_left hPA_lt_QB (by linarith [hpZ])
      have hQB_pos : 0 < Q * padeSeqB u p := mul_pos hQ (by linarith [hB_ge])
      have hPB_pos : 0 < P * padeSeqB u p := mul_pos hP (by linarith [hB_ge])
      have h2 : 4 * ((p : ℤ) - 1) * (Q * padeSeqB u p) < 4 * (p : ℤ) * (Q * padeSeqB u p) := by
        nlinarith only [hQB_pos]
      have h3 : (3 * (p : ℤ) - 4) * (P * padeSeqB u p) < 3 * (p : ℤ) * (P * padeSeqB u p) := by
        nlinarith only [hPB_pos]
      have hrewL :
          P * (4 * ((p : ℤ) - 1) * padeSeqA u p + (3 * (p : ℤ) - 4) * padeSeqB u p) =
            4 * ((p : ℤ) - 1) * (P * padeSeqA u p) + (3 * (p : ℤ) - 4) * (P * padeSeqB u p) := by
        ring
      have hrewR :
          4 * (p : ℤ) * (Q * padeSeqB u p) + 3 * (p : ℤ) * (P * padeSeqB u p) =
            (4 * Q + 3 * P) * (p : ℤ) * padeSeqB u p := by
        ring
      linarith [h1, h2, h3, hrewL, hrewR]
    exact ⟨hPA_lt_QB, hPB_succ⟩
  have h1393 := hpell_all 1393 985 (by norm_num) (by norm_num) (by norm_num)
  have h8119 := hpell_all 8119 5741 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨h2A2_lt_B2, hpell_all, h1393.1, h8119.1, ?_⟩
  simpa [show (4 * (985 : ℤ) + 3 * 1393) = 8119 by norm_num] using h1393.2

/-- Weighted quadratic and linear contraction of the Padé quotient `k_pade` against `padeSeqB u p`
and `(239 / 1393) ^ (u - 3)`. -/
theorem even_index_pade_quotient_weighted_contraction {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let k_pade : ℤ := ((s : ℤ) * padeSeqB u p - padeSeqA u p) / (p : ℤ) ^ (2 * u + 1)
    2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) * k_pade ^ 2 < padeSeqB u p ^ 2 ∧
    (p : ℤ) ^ (u + 1) * k_pade < padeSeqB u p ∧
    140 * ((p : ℤ) - 1) * k_pade * (p : ℤ) ^ u < 99 * padeSeqB u p ∧
    (3 ≤ u → 239 ^ (u - 3) * (p * k_pade.natAbs) < 239 * 1393 ^ (u - 3)) := by
  intro k_pade
  have hp3 : 3 ≤ p := odd_prime_ge_three_sqrt_two hp hpo
  have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
  obtain ⟨_, hk1, hquad, _, _⟩ :=
    even_index_pade_quotient_pos_and_quadratic_identity hp hpo hs hu hσq hplus hσs
  change 1 ≤ k_pade at hk1
  change 2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) * k_pade ^ 2 +
      4 * ((p : ℤ) - 1) * padeSeqA u p * k_pade = padeSeqB u p ^ 2 - 1 at hquad
  obtain ⟨hA_ge, hB_ge⟩ := padeSeq_one_le hp3 u
  have hquad_lt : 2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) * k_pade ^ 2 < padeSeqB u p ^ 2 := by
    have h4p1 : 0 < 4 * ((p : ℤ) - 1) := by linarith
    have h4pA : 0 < 4 * ((p : ℤ) - 1) * padeSeqA u p := by nlinarith only [h4p1, hA_ge]
    have hrem : 0 < 4 * ((p : ℤ) - 1) * padeSeqA u p * k_pade + 1 := by nlinarith only [h4pA, hk1]
    linarith [hquad, hrem]
  have hpow_pos : (0 : ℤ) < (p : ℤ) ^ (2 * u + 1) := by positivity
  have hpu_pos : (0 : ℤ) < (p : ℤ) ^ u := by positivity
  have hp2u_pos : (0 : ℤ) < (p : ℤ) ^ (2 * u) := by positivity
  have hk2_pos : 0 < k_pade ^ 2 := by nlinarith only [hk1]
  have hpu1_k_lt : (p : ℤ) ^ (u + 1) * k_pade < padeSeqB u p := by
    have hsq_eq :
        ((p : ℤ) ^ (u + 1) * k_pade) ^ 2 =
          (p : ℤ) * (p : ℤ) ^ (2 * u + 1) * k_pade ^ 2 := by
      rw [mul_pow, ← pow_mul, show (u + 1) * 2 = 1 + (2 * u + 1) by omega, pow_add, pow_one]
    have hp_lt : (p : ℤ) < 2 * ((p : ℤ) - 1) := by linarith
    have hmul_lt :
        (p : ℤ) * (p : ℤ) ^ (2 * u + 1) * k_pade ^ 2 <
          2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) * k_pade ^ 2 := by
      have hpos : 0 < (p : ℤ) ^ (2 * u + 1) * k_pade ^ 2 := mul_pos hpow_pos hk2_pos
      have := mul_lt_mul_of_pos_right hp_lt hpos
      linarith
    have hsq_lt : ((p : ℤ) ^ (u + 1) * k_pade) ^ 2 < padeSeqB u p ^ 2 := by linarith
    by_contra! hle
    have hsq_le : padeSeqB u p ^ 2 ≤ ((p : ℤ) ^ (u + 1) * k_pade) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hle 2
    linarith
  have h140_lt : 140 * ((p : ℤ) - 1) * k_pade * (p : ℤ) ^ u < 99 * padeSeqB u p := by
    have hsq_eq :
        (140 * ((p : ℤ) - 1) * k_pade * (p : ℤ) ^ u) ^ 2 =
          19600 * ((p : ℤ) - 1) ^ 2 * (p : ℤ) ^ (2 * u) * k_pade ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, ← pow_mul, mul_comm u 2]
      ring
    have h99_eq :
        99 ^ 2 * (2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) * k_pade ^ 2) =
          19602 * ((p : ℤ) - 1) * (p : ℤ) * (p : ℤ) ^ (2 * u) * k_pade ^ 2 := by
      rw [pow_succ (p : ℤ) (2 * u)]
      ring
    have hcoeff_lt :
        19600 * ((p : ℤ) - 1) ^ 2 < 19602 * ((p : ℤ) - 1) * (p : ℤ) := by
      have h1 : ((p : ℤ) - 1) ^ 2 < ((p : ℤ) - 1) * (p : ℤ) := by nlinarith
      have h2 : 0 < ((p : ℤ) - 1) * (p : ℤ) := by nlinarith
      linarith
    have hsq_lt_mid :
        (140 * ((p : ℤ) - 1) * k_pade * (p : ℤ) ^ u) ^ 2 <
          99 ^ 2 * (2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) * k_pade ^ 2) := by
      rw [hsq_eq, h99_eq]
      have hpos : 0 < (p : ℤ) ^ (2 * u) * k_pade ^ 2 := mul_pos hp2u_pos hk2_pos
      have hmul := mul_lt_mul_of_pos_right hcoeff_lt hpos
      linarith
    have hsq_lt :
        (140 * ((p : ℤ) - 1) * k_pade * (p : ℤ) ^ u) ^ 2 < (99 * padeSeqB u p) ^ 2 := by
      have h99_lt :
          99 ^ 2 * (2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) * k_pade ^ 2) <
            99 ^ 2 * padeSeqB u p ^ 2 :=
        mul_lt_mul_of_pos_left hquad_lt (by norm_num)
      have h99_sq : (99 * padeSeqB u p) ^ 2 = 99 ^ 2 * padeSeqB u p ^ 2 := by ring
      linarith
    by_contra! hle
    have hsq_le :
        (99 * padeSeqB u p) ^ 2 ≤ (140 * ((p : ℤ) - 1) * k_pade * (p : ℤ) ^ u) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hle 2
    linarith
  have h239_cap : 3 ≤ u → 239 ^ (u - 3) * (p * k_pade.natAbs) < 239 * 1393 ^ (u - 3) := by
    intro hu3
    have h1393B := (padeSeq_sharpened_1393_239_contraction hp3 hu3).2.2
    have h239_pos : (0 : ℤ) < (239 : ℤ) ^ (u - 3) := by positivity
    have hchain :
        ((239 : ℤ) ^ (u - 3) * ((p : ℤ) * k_pade)) * (p : ℤ) ^ u <
          (239 * 1393 ^ (u - 3)) * (p : ℤ) ^ u := by
      calc
        ((239 : ℤ) ^ (u - 3) * ((p : ℤ) * k_pade)) * (p : ℤ) ^ u
            = (239 : ℤ) ^ (u - 3) * ((p : ℤ) ^ (u + 1) * k_pade) := by rw [pow_succ']; ring
        _ < (239 : ℤ) ^ (u - 3) * padeSeqB u p := mul_lt_mul_of_pos_left hpu1_k_lt h239_pos
        _ < 239 * 1393 ^ (u - 3) * (p : ℤ) ^ u := h1393B
    have hltZ : (239 : ℤ) ^ (u - 3) * ((p : ℤ) * k_pade) < 239 * 1393 ^ (u - 3) :=
      lt_of_mul_lt_mul_right hchain hpu_pos.le
    have hnat_abs : (k_pade.natAbs : ℤ) = k_pade := Int.natAbs_of_nonneg (by omega)
    rw [← hnat_abs] at hltZ
    exact_mod_cast hltZ
  exact ⟨hquad_lt, hpu1_k_lt, h140_lt, h239_cap⟩

/-- Global odd-perfect-number theorem coupling the tridecuple exponent floor `6541380665835014 ≤ u`
with the exact `√2` Pell–Padé upper bounds and weighted `k_pade` contraction. -/
theorem even_prime_power_exact_sqrt_two_and_weighted_pade_profile
    {N q a b i p u : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b) (hl : sigma 1 b = q ^ a * i)
    (hr : sigma 1 (q ^ a) * i = 2 * b) (hp : p.Prime) (hu : 0 < u) (hi : i = p ^ (2 * u)) :
    6541380665835014 ≤ u ∧ (2 * u + 1).Prime ∧
    2 * padeSeqA u p ^ 2 < padeSeqB u p ^ 2 ∧
    (∀ P Q : ℤ, 0 < P → 0 < Q → 2 * Q ^ 2 - P ^ 2 = 1 →
      P * padeSeqA u p < Q * padeSeqB u p ∧
      P * padeSeqB (u + 1) p < (4 * Q + 3 * P) * (p : ℤ) * padeSeqB u p) ∧
    (p % 4 = 3 ∨ Even u → 2 * (10 ^ 600) ^ 2 * p < 6 ^ u) ∧
    (p ∣ 64 ^ u - 1 → (10 ^ 600) ^ 2 * p ^ 2 < 6 ^ u) ∧
    ((2 * u + 1) ∣ p - 2 → (10 ^ 600) ^ 2 * u * p < 6 ^ u) ∧
    ∃ s : ℕ, Odd s ∧
      (let k_pade : ℤ := ((s : ℤ) * padeSeqB u p - padeSeqA u p) / (p : ℤ) ^ (2 * u + 1)
       1 ≤ k_pade ∧
       (p : ℤ) ^ (u + 1) * k_pade < padeSeqB u p ∧
       140 * ((p : ℤ) - 1) * k_pade * (p : ℤ) ^ u < 99 * padeSeqB u p ∧
       239 ^ (u - 3) * (p * k_pade.natAbs) < 239 * 1393 ^ (u - 3) ∧
       (10 ^ 600) ^ 2 * p * k_pade.natAbs < 6 ^ u) := by
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
  obtain ⟨hu_ge, hlen_prime, _, hdiv_cap, _⟩ :=
    even_prime_power_tridecuple_sublinear_repunit_profile
      hN ho hq ha hform hqb hl hr hp hu hi
  obtain ⟨h2A2, hpell_all, _, _, _⟩ :=
    even_index_pade_sq_lt_half_sq_and_upper_pell hp hpo hs hu hσq hplus hσs
  obtain ⟨_, hk1, _, _, _⟩ :=
    even_index_pade_quotient_pos_and_quadratic_identity hp hpo hs hu hσq hplus hσs
  obtain ⟨_, hpu1_k, h140_k, h239_k_fn⟩ :=
    even_index_pade_quotient_weighted_contraction hp hpo hs hu hσq hplus hσs
  have hu3 : 3 ≤ u := by omega
  have hu100003 : 100003 ≤ u := by omega
  have h239_pk := h239_k_fn hu3
  have hnum := ten_pow_1200_lt_six_pow_of_tridecuple_floor hu100003
  set k_pade : ℤ := ((s : ℤ) * padeSeqB u p - padeSeqA u p) / (p : ℤ) ^ (2 * u + 1)
  have h1200_pk : (10 ^ 600) ^ 2 * p * k_pade.natAbs < 6 ^ u := by
    have hmul :
        239 ^ (u - 3) * ((10 ^ 600) ^ 2 * p * k_pade.natAbs) < 239 ^ (u - 3) * 6 ^ u := by
      calc
        239 ^ (u - 3) * ((10 ^ 600) ^ 2 * p * k_pade.natAbs)
            = (10 ^ 600) ^ 2 * (239 ^ (u - 3) * (p * k_pade.natAbs)) := by
                rw [mul_assoc ((10 ^ 600) ^ 2) p k_pade.natAbs, mul_left_comm]
        _ < (10 ^ 600) ^ 2 * (239 * 1393 ^ (u - 3)) :=
            Nat.mul_lt_mul_of_pos_left h239_pk (by positivity)
        _ < 239 ^ (u - 3) * 6 ^ u := hnum
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hpar_cap : p % 4 = 3 ∨ Even u → 2 * (10 ^ 600) ^ 2 * p < 6 ^ u := by
    intro hcond
    have hk2 : 2 ≤ k_pade :=
      (even_index_pade_quotient_parity_and_doubled_cap hp hpo hs hu hσq hplus hσs).2.2 hcond |>.1
    have hk2_nat : 2 ≤ k_pade.natAbs := by
      have hnat_abs : (k_pade.natAbs : ℤ) = k_pade := Int.natAbs_of_nonneg (by omega)
      omega
    have hle : 2 * (10 ^ 600) ^ 2 * p ≤ (10 ^ 600) ^ 2 * p * k_pade.natAbs := by
      calc
        2 * (10 ^ 600) ^ 2 * p = (10 ^ 600) ^ 2 * p * 2 := by
            rw [mul_comm 2 ((10 ^ 600) ^ 2), mul_assoc, mul_comm 2 p, ← mul_assoc]
        _ ≤ (10 ^ 600) ^ 2 * p * k_pade.natAbs := Nat.mul_le_mul_left _ hk2_nat
    exact lt_of_le_of_lt hle h1200_pk
  have hmodp_cap : p ∣ 64 ^ u - 1 → (10 ^ 600) ^ 2 * p ^ 2 < 6 ^ u := by
    intro hp64
    have hpk : (p : ℤ) ≤ k_pade :=
      (even_index_pade_quotient_mod_p_and_sub_two hp hpo hs hu hσq hplus hσs).2.1 hp64 |>.1
    have hpk_nat : p ≤ k_pade.natAbs := by
      have hnat_abs : (k_pade.natAbs : ℤ) = k_pade := Int.natAbs_of_nonneg (by omega)
      omega
    have hle : (10 ^ 600) ^ 2 * p ^ 2 ≤ (10 ^ 600) ^ 2 * p * k_pade.natAbs := by
      calc
        (10 ^ 600) ^ 2 * p ^ 2 = (10 ^ 600) ^ 2 * p * p := by rw [sq p, ← mul_assoc]
        _ ≤ (10 ^ 600) ^ 2 * p * k_pade.natAbs := Nat.mul_le_mul_left _ hpk_nat
    exact lt_of_le_of_lt hle h1200_pk
  exact ⟨hu_ge, hlen_prime, h2A2, hpell_all, hpar_cap, hmodp_cap, hdiv_cap,
    ⟨s, hs, hk1, hpu1_k, h140_k, h239_pk, h1200_pk⟩⟩

end OddPerfect
