module

public import OddPerfect.PadicPadeHigherOrderContraction
public import OddPerfect.PadicThirdOrderObstruction
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Mod-`(2 * u + 1)` Padé Collapse & Primorial Repunit Length Bounds (`OddPerfect.PadicPadeModTwoLenObstruction`)

Formalizes:
1. `prime_two_mul_add_one_pade_congruence`:
   Whenever `L = 2 * u + 1` is prime and `2 ^ (u + 1) * k ≡ -1 [ZMOD L]` with `1 ≤ k`,
   Fermat's Little Theorem yields `2 * k ≡ -(2 : ℤ) ^ u [ZMOD L]`, forcing
   `k ≡ u [ZMOD L] ∨ k ≡ u + 1 [ZMOD L]` and hence `u ≤ k`.
2. `even_index_pade_quotient_mod_two_len_collapse`:
   Whenever `(2 * u + 1) ∣ p - 2` on an even prime-power component equation, the Padé quotient
   `k_pade` collapses modulo `2 * u + 1` to `{u, u + 1}`, forcing `u ≤ k_pade`,
   `u * p ^ (u + 1) < padeSeqB u p`, `10 ^ 12 * u * p < 6 ^ u`, and `10 ^ 15 * p < 6 ^ u`.
3. `repunit_length_all_primorial_bases_linear_bounds`:
   Linear upper bounds on the repunit length `l` in terms of `u` across all five surviving
   primorial bases `r ∈ {3, 5, 7, 11, 13}` from `10 ^ 12 * r ^ (l - 1) < 6 ^ u`.
4. `even_prime_power_all_primorial_repunit_and_len_div_caps`:
   Global odd-perfect-number wrapper combining the `(2 * u + 1) ∣ p - 2` exponential sharpening
   with linear repunit-length caps across all `r ∈ {3, 5, 7, 11, 13}`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma odd_prime_ge_three_mod_two_len {p : ℕ} (hp : p.Prime) (hpo : Odd p) : 3 ≤ p := by
  have h2 : 2 ≤ p := hp.two_le
  rcases eq_or_lt_of_le h2 with rfl | hlt
  · exact absurd hpo (by decide)
  · exact hlt

private lemma ten_pow_12_mul_239_mul_1393_pow_lt_239_pow_mul_6_pow_len {u : ℕ} (hu : 1154 ≤ u) :
    10 ^ 12 * (239 * 1393 ^ (u - 3)) < 239 ^ (u - 3) * 6 ^ u := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, u = 1154 + k := ⟨u - 1154, by omega⟩
  induction k with
  | zero =>
      have h48 : 4 * 1393 ^ 48 < 1434 ^ 48 := by norm_num
      have h1104 : 4 ^ 23 * 1393 ^ 1104 < 1434 ^ 1104 := by
        calc
          4 ^ 23 * 1393 ^ 1104
              = (4 * 1393 ^ 48) ^ 23 := by rw [mul_pow, ← pow_mul]
          _ < (1434 ^ 48) ^ 23 := Nat.pow_lt_pow_left h48 (by decide)
          _ = 1434 ^ 1104 := by rw [← pow_mul]
      have h47 : 1393 ^ 47 ≤ 1434 ^ 47 := Nat.pow_le_pow_left (by decide) 47
      have h1151 : 4 ^ 23 * 1393 ^ 1151 < 1434 ^ 1151 := by
        calc
          4 ^ 23 * 1393 ^ 1151
              = (4 ^ 23 * 1393 ^ 1104) * 1393 ^ 47 := by rw [mul_assoc, ← pow_add]
          _ < 1434 ^ 1104 * 1393 ^ 47 := Nat.mul_lt_mul_of_pos_right h1104 (by positivity)
          _ ≤ 1434 ^ 1104 * 1434 ^ 47 := Nat.mul_le_mul_left _ h47
          _ = 1434 ^ 1151 := by rw [← pow_add]
      have h216 : 10 ^ 12 * 239 < 6 ^ 3 * 4 ^ 23 := by norm_num
      have hmul :
          (10 ^ 12 * 239) * 1393 ^ 1151 < (6 ^ 3 * 4 ^ 23) * 1393 ^ 1151 :=
        Nat.mul_lt_mul_of_pos_right h216 (by positivity)
      have h6_1151 : 6 ^ 3 * (4 ^ 23 * 1393 ^ 1151) < 6 ^ 3 * 1434 ^ 1151 :=
        Nat.mul_lt_mul_of_pos_left h1151 (by decide)
      have hrewR :
          239 ^ (1154 + 0 - 3) * 6 ^ (1154 + 0) = 6 ^ 3 * 1434 ^ 1151 := by
        have h1434 : (1434 : ℕ) = 239 * 6 := by decide
        rw [show 1154 + 0 - 3 = 1151 by omega, show 1154 + 0 = 3 + 1151 by omega,
          pow_add, h1434, mul_pow, mul_left_comm]
      calc
        10 ^ 12 * (239 * 1393 ^ (1154 + 0 - 3))
            = (10 ^ 12 * 239) * 1393 ^ 1151 := by
                rw [show 1154 + 0 - 3 = 1151 by omega, mul_assoc]
        _ < (6 ^ 3 * 4 ^ 23) * 1393 ^ 1151 := hmul
        _ = 6 ^ 3 * (4 ^ 23 * 1393 ^ 1151) := by rw [mul_assoc]
        _ < 6 ^ 3 * 1434 ^ 1151 := h6_1151
        _ = 239 ^ (1154 + 0 - 3) * 6 ^ (1154 + 0) := hrewR.symm
  | succ k ih =>
      have hk : 1154 ≤ 1154 + k := by omega
      have ihk := ih hk
      have hmul :
          1393 * (10 ^ 12 * (239 * 1393 ^ (1154 + k - 3))) <
            1393 * (239 ^ (1154 + k - 3) * 6 ^ (1154 + k)) :=
        Nat.mul_lt_mul_of_pos_left ihk (by decide)
      have h1393_lt :
          1393 * (239 ^ (1154 + k - 3) * 6 ^ (1154 + k)) <
            (239 * 6) * (239 ^ (1154 + k - 3) * 6 ^ (1154 + k)) := by
        apply Nat.mul_lt_mul_of_pos_right (by decide : 1393 < 239 * 6)
        positivity
      have hrewL :
          10 ^ 12 * (239 * 1393 ^ (1154 + (k + 1) - 3)) =
            1393 * (10 ^ 12 * (239 * 1393 ^ (1154 + k - 3))) := by
        rw [show 1154 + (k + 1) - 3 = (1154 + k - 3) + 1 by omega, pow_succ' 1393,
          mul_left_comm 239 1393, mul_left_comm (10 ^ 12) 1393]
      have hrewR :
          (239 * 6) * (239 ^ (1154 + k - 3) * 6 ^ (1154 + k)) =
            239 ^ (1154 + (k + 1) - 3) * 6 ^ (1154 + (k + 1)) := by
        rw [show 1154 + (k + 1) - 3 = (1154 + k - 3) + 1 by omega,
          show 1154 + (k + 1) = (1154 + k) + 1 by omega, pow_succ' 239, pow_succ' 6,
          mul_mul_mul_comm]
      calc
        10 ^ 12 * (239 * 1393 ^ (1154 + (k + 1) - 3))
            = 1393 * (10 ^ 12 * (239 * 1393 ^ (1154 + k - 3))) := hrewL
        _ < 1393 * (239 ^ (1154 + k - 3) * 6 ^ (1154 + k)) := hmul
        _ < (239 * 6) * (239 ^ (1154 + k - 3) * 6 ^ (1154 + k)) := h1393_lt
        _ = 239 ^ (1154 + (k + 1) - 3) * 6 ^ (1154 + (k + 1)) := hrewR

/-- Whenever `2 * u + 1` is prime and `2 ^ (u + 1) * k ≡ -1 [ZMOD 2 * u + 1]` with `1 ≤ k`,
Fermat's Little Theorem collapses `k` modulo `2 * u + 1` to `u` or `u + 1`, forcing `u ≤ k`. -/
theorem prime_two_mul_add_one_pade_congruence {u : ℕ} {k : ℤ}
    (hu : 1 ≤ u) (hprime : (2 * u + 1).Prime) (hk : 1 ≤ k)
    (hcong : (2 : ℤ) ^ (u + 1) * k ≡ -1 [ZMOD (2 * (u : ℤ) + 1)]) :
    2 * k ≡ -(2 : ℤ) ^ u [ZMOD (2 * (u : ℤ) + 1)] ∧
    (k ≡ (u : ℤ) [ZMOD (2 * (u : ℤ) + 1)] ∨ k ≡ (u : ℤ) + 1 [ZMOD (2 * (u : ℤ) + 1)]) ∧
    (u : ℤ) ≤ k := by
  set L : ℕ := 2 * u + 1
  have : Fact L.Prime := ⟨hprime⟩
  have hL_cast : ((L : ℕ) : ℤ) = 2 * (u : ℤ) + 1 := by omega
  have hL_ge3 : 3 ≤ L := by omega
  have h2_ne : (2 : ZMod L) ≠ 0 := by
    intro h0
    have hdvd : L ∣ 2 := (ZMod.natCast_eq_zero_iff 2 L).mp (by simpa using h0)
    have hle : L ≤ 2 := Nat.le_of_dvd (by decide) hdvd
    omega
  have hcongL : (2 : ℤ) ^ (u + 1) * k ≡ -1 [ZMOD (L : ℕ)] := by
    rwa [hL_cast]
  have hZ : (2 : ZMod L) ^ (u + 1) * (k : ZMod L) = -1 := by
    have hcast := (ZMod.intCast_eq_intCast_iff _ _ L).mpr hcongL
    simpa using hcast
  have h2k_Z : (2 : ZMod L) * (k : ZMod L) = -((2 : ZMod L) ^ u) := by
    have hmul := congrArg ((2 : ZMod L) ^ u * ·) hZ
    have hpowL : (2 : ZMod L) ^ u * ((2 : ZMod L) ^ (u + 1) * (k : ZMod L)) =
        (2 : ZMod L) ^ L * (k : ZMod L) := by
      rw [← mul_assoc, ← pow_add, show u + (u + 1) = L by omega]
    rw [hpowL, ZMod.pow_card] at hmul
    simpa [mul_neg_one] using hmul
  have h2k : 2 * k ≡ -(2 : ℤ) ^ u [ZMOD (2 * (u : ℤ) + 1)] := by
    rw [← hL_cast]
    apply (ZMod.intCast_eq_intCast_iff _ _ L).mp
    simpa using h2k_Z
  have hpow_sq : ((2 : ZMod L) ^ u) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm u 2, show 2 * u = L - 1 by omega]
    exact ZMod.pow_card_sub_one_eq_one h2_ne
  have h2u_Z : 2 * (u : ZMod L) + 1 = 0 := by
    have hL0 : ((L : ℕ) : ZMod L) = 0 := ZMod.natCast_self L
    dsimp [L] at hL0
    push_cast at hL0
    exact hL0
  have h2u_neg1 : (2 : ZMod L) * (u : ZMod L) = -1 := eq_neg_of_add_eq_zero_left h2u_Z
  have h2u1_pos1 : (2 : ZMod L) * ((u : ZMod L) + 1) = 1 := by
    calc
      (2 : ZMod L) * ((u : ZMod L) + 1) = 2 * (u : ZMod L) + 2 := by ring
      _ = -1 + 2 := by rw [h2u_neg1]
      _ = 1 := by ring
  have hk_cases :
      k ≡ (u : ℤ) [ZMOD (2 * (u : ℤ) + 1)] ∨ k ≡ (u : ℤ) + 1 [ZMOD (2 * (u : ℤ) + 1)] := by
    rcases sq_eq_one_iff.mp hpow_sq with hpow1 | hpowm1
    · left
      rw [hpow1] at h2k_Z
      have hk_Z : (k : ZMod L) = (u : ZMod L) :=
        mul_left_cancel₀ h2_ne (by rw [h2k_Z, h2u_neg1])
      rw [← hL_cast]
      exact (ZMod.intCast_eq_intCast_iff _ _ L).mp (by simpa using hk_Z)
    · right
      rw [hpowm1, neg_neg] at h2k_Z
      have hk_Z : (k : ZMod L) = (u : ZMod L) + 1 :=
        mul_left_cancel₀ h2_ne (by rw [h2k_Z, h2u1_pos1])
      rw [← hL_cast]
      exact (ZMod.intCast_eq_intCast_iff _ _ L).mp (by simpa using hk_Z)
  have hu_le_k : (u : ℤ) ≤ k := by
    rcases hk_cases with hk_u | hk_u1
    · rw [← hL_cast, Int.modEq_iff_dvd] at hk_u
      rcases hk_u with ⟨t, ht⟩
      by_contra! hlt
      have ht_pos : 0 < t := by nlinarith
      have h1 : (L : ℤ) ≤ (L : ℤ) * t := by nlinarith
      have h2 : (u : ℤ) - k < (L : ℤ) := by
        have : (u : ℤ) < (L : ℤ) := by exact_mod_cast (by omega : u < L)
        linarith
      linarith
    · rw [← hL_cast, Int.modEq_iff_dvd] at hk_u1
      rcases hk_u1 with ⟨t, ht⟩
      by_contra! hlt
      have ht_pos : 0 < t := by nlinarith
      have h1 : (L : ℤ) ≤ (L : ℤ) * t := by nlinarith
      have h2 : (u : ℤ) + 1 - k < (L : ℤ) := by
        have : (u : ℤ) + 1 < (L : ℤ) := by exact_mod_cast (by omega : u + 1 < L)
        linarith
      linarith
  exact ⟨h2k, hk_cases, hu_le_k⟩

/-- Whenever `(2 * u + 1) ∣ p - 2` on an even prime-power component equation, the Padé quotient
`k_pade` collapses modulo `2 * u + 1` to `{u, u + 1}`, forcing `u ≤ k_pade`,
`(u : ℤ) * p ^ (u + 1) < padeSeqB u p`, `10 ^ 12 * u * p < 6 ^ u`, and `10 ^ 15 * p < 6 ^ u`. -/
theorem even_index_pade_quotient_mod_two_len_collapse {q p s u : ℕ}
    (hq : q.Prime) (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u))
    (hdiv : (2 * u + 1) ∣ p - 2) :
    let k_pade : ℤ := ((s : ℤ) * padeSeqB u p - padeSeqA u p) / (p : ℤ) ^ (2 * u + 1)
    (k_pade ≡ (u : ℤ) [ZMOD (2 * (u : ℤ) + 1)] ∨
      k_pade ≡ (u : ℤ) + 1 [ZMOD (2 * (u : ℤ) + 1)]) ∧
    (u : ℤ) ≤ k_pade ∧
    (u : ℤ) * (p : ℤ) ^ (u + 1) < padeSeqB u p ∧
    239 ^ (u - 3) * (u * p) < 239 * 1393 ^ (u - 3) ∧
    10 ^ 12 * u * p < 6 ^ u ∧
    10 ^ 15 * p < 6 ^ u := by
  intro k_pade
  have hp3 : 3 ≤ p := odd_prime_ge_three_mod_two_len hp hpo
  have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
  have hlen_prime : (2 * u + 1).Prime := even_index_length_prime hq hp hu hσq
  obtain ⟨_, hk1, hquad, _, _⟩ :=
    even_index_pade_quotient_pos_and_quadratic_identity hp hpo hs hu hσq hplus hσs
  obtain ⟨_, _, hmod_sub_two⟩ :=
    even_index_pade_quotient_mod_p_and_sub_two hp hpo hs hu hσq hplus hσs
  have hdivZ : (2 * (u : ℤ) + 1) ∣ (p : ℤ) - 2 := by
    have hcast : ((2 * u + 1 : ℕ) : ℤ) ∣ ((p - 2 : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hdiv
    rw [Nat.cast_sub (by omega : 2 ≤ p)] at hcast
    push_cast at hcast
    exact hcast
  have hcong_rhs :
      (2 * (u : ℤ) + 1) * (s : ℤ) - 1 ≡ -1 [ZMOD (2 * (u : ℤ) + 1)] := by
    rw [Int.modEq_iff_dvd]
    exact ⟨-(s : ℤ), by ring⟩
  have hcong : (2 : ℤ) ^ (u + 1) * k_pade ≡ -1 [ZMOD (2 * (u : ℤ) + 1)] :=
    (Int.ModEq.of_dvd hdivZ hmod_sub_two).trans hcong_rhs
  obtain ⟨_, hk_mod, hu_le_k⟩ :=
    prime_two_mul_add_one_pade_congruence hu hlen_prime hk1 hcong
  obtain ⟨hA_ge, hB_ge⟩ := padeSeq_one_le hp3 u
  have huB : (u : ℤ) * (p : ℤ) ^ (u + 1) < padeSeqB u p := by
    have hpow_pos : (0 : ℤ) < (p : ℤ) ^ (2 * u + 1) := by positivity
    have h2p1_gt : (p : ℤ) < 2 * ((p : ℤ) - 1) := by linarith
    have hu_sq_le : (u : ℤ) ^ 2 ≤ k_pade ^ 2 :=
      pow_le_pow_left₀ (by positivity) hu_le_k 2
    have hterm2_pos : 0 < 4 * ((p : ℤ) - 1) * padeSeqA u p * k_pade := by
      have h4p1 : 0 < 4 * ((p : ℤ) - 1) := by linarith
      exact mul_pos (mul_pos h4p1 hA_ge) hk1
    have hsq_eq : ((u : ℤ) * (p : ℤ) ^ (u + 1)) ^ 2 =
        (u : ℤ) ^ 2 * (p : ℤ) * (p : ℤ) ^ (2 * u + 1) := by
      rw [mul_pow, ← pow_mul]
      have hpow_split : (p : ℤ) ^ ((u + 1) * 2) = (p : ℤ) * (p : ℤ) ^ (2 * u + 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [hpow_split]
      ring
    have h2p1_pos : 0 ≤ 2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) :=
      mul_nonneg (by linarith) hpow_pos.le
    have hsq_lt : ((u : ℤ) * (p : ℤ) ^ (u + 1)) ^ 2 < padeSeqB u p ^ 2 := by
      calc
        ((u : ℤ) * (p : ℤ) ^ (u + 1)) ^ 2
            = (u : ℤ) ^ 2 * ((p : ℤ) * (p : ℤ) ^ (2 * u + 1)) := by rw [hsq_eq]; ring
        _ < (u : ℤ) ^ 2 * (2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1)) := by
            apply mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right h2p1_gt hpow_pos)
            positivity
        _ ≤ k_pade ^ 2 * (2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1)) :=
            mul_le_mul_of_nonneg_right hu_sq_le h2p1_pos
        _ = 2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) * k_pade ^ 2 := by ring
        _ < 2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) * k_pade ^ 2 +
              4 * ((p : ℤ) - 1) * padeSeqA u p * k_pade + 1 := by linarith
        _ = padeSeqB u p ^ 2 := by linarith
    by_contra! hle
    have hsq_le : padeSeqB u p ^ 2 ≤ ((u : ℤ) * (p : ℤ) ^ (u + 1)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hle 2
    linarith
  obtain ⟨hu1154, _, _, _, _⟩ :=
    even_index_prime_ten_pow_twelve_cap hp hpo hs hu hσq hplus hσs
  have hu3 : 3 ≤ u := by omega
  have hB_bound : (239 : ℤ) ^ (u - 3) * padeSeqB u p < 239 * 1393 ^ (u - 3) * (p : ℤ) ^ u :=
    (padeSeq_sharpened_1393_239_contraction hp3 hu3).2.2
  have h239_posZ : (0 : ℤ) < (239 : ℤ) ^ (u - 3) := by positivity
  have hpu_posZ : (0 : ℤ) < (p : ℤ) ^ u := by positivity
  have h239_up : 239 ^ (u - 3) * (u * p) < 239 * 1393 ^ (u - 3) := by
    have hchain :
        (239 : ℤ) ^ (u - 3) * ((u : ℤ) * (p : ℤ)) * (p : ℤ) ^ u <
          239 * 1393 ^ (u - 3) * (p : ℤ) ^ u := by
      calc
        (239 : ℤ) ^ (u - 3) * ((u : ℤ) * (p : ℤ)) * (p : ℤ) ^ u
            = (239 : ℤ) ^ (u - 3) * ((u : ℤ) * (p : ℤ) ^ (u + 1)) := by rw [pow_succ']; ring
        _ < (239 : ℤ) ^ (u - 3) * padeSeqB u p := mul_lt_mul_of_pos_left huB h239_posZ
        _ < 239 * 1393 ^ (u - 3) * (p : ℤ) ^ u := hB_bound
    have hltZ : (239 : ℤ) ^ (u - 3) * ((u : ℤ) * (p : ℤ)) < 239 * 1393 ^ (u - 3) :=
      lt_of_mul_lt_mul_right hchain hpu_posZ.le
    exact_mod_cast hltZ
  have hnum := ten_pow_12_mul_239_mul_1393_pow_lt_239_pow_mul_6_pow_len hu1154
  have h10_12_up : 10 ^ 12 * u * p < 6 ^ u := by
    have hmul : 239 ^ (u - 3) * (10 ^ 12 * u * p) < 239 ^ (u - 3) * 6 ^ u := by
      calc
        239 ^ (u - 3) * (10 ^ 12 * u * p)
            = 10 ^ 12 * (239 ^ (u - 3) * (u * p)) := by ring
        _ < 10 ^ 12 * (239 * 1393 ^ (u - 3)) := Nat.mul_lt_mul_of_pos_left h239_up (by positivity)
        _ < 239 ^ (u - 3) * 6 ^ u := hnum
    exact Nat.lt_of_mul_lt_mul_left hmul
  have h10_15_p : 10 ^ 15 * p < 6 ^ u := by
    have hcoef : 10 ^ 15 < 10 ^ 12 * u := by
      have h1000 : 10 ^ 15 < 10 ^ 12 * 1154 := by norm_num
      have hle : 10 ^ 12 * 1154 ≤ 10 ^ 12 * u := Nat.mul_le_mul_left _ hu1154
      omega
    calc
      10 ^ 15 * p < (10 ^ 12 * u) * p := Nat.mul_lt_mul_of_pos_right hcoef hp.pos
      _ = 10 ^ 12 * u * p := rfl
      _ < 6 ^ u := h10_12_up
  exact ⟨hk_mod, hu_le_k, huB, h239_up, h10_12_up, h10_15_p⟩

/-- Linear upper bounds on the repunit length `l` in terms of `u` across all five surviving
primorial bases `r ∈ {3, 5, 7, 11, 13}` from `10 ^ 12 * r ^ (l - 1) < 6 ^ u`. -/
theorem repunit_length_all_primorial_bases_linear_bounds {r l u : ℕ}
    (hr : r ∈ ({3, 5, 7, 11, 13} : Finset ℕ)) (hl : 2 < l)
    (hcap : 10 ^ 12 * r ^ (l - 1) < 6 ^ u) :
    3 * l + 75 ≤ 5 * u ∧
    (r ∈ ({5, 7, 11, 13} : Finset ℕ) → 8 * l + 131 ≤ 9 * u) ∧
    (r ∈ ({7, 11, 13} : Finset ℕ) → l + 15 ≤ u) := by
  have h3_le_r : 3 ≤ r := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  have h3_bound : 3 * l + 75 ≤ 5 * u := by
    have h10_3 : 10 ^ 12 * 3 ^ (l - 1) < 6 ^ u :=
      lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h3_le_r (l - 1))) hcap
    have hpow5 : (10 ^ 12 * 3 ^ (l - 1)) ^ 5 < (6 ^ u) ^ 5 :=
      Nat.pow_lt_pow_left h10_3 (by decide)
    have h6_77 : 6 ^ 77 < (10 ^ 12) ^ 5 := by norm_num
    have h6_3 : 6 ^ 3 ≤ 3 ^ 5 := by norm_num
    have h6_exp : 6 ^ (77 + 3 * (l - 1)) < 6 ^ (5 * u) := by
      calc
        6 ^ (77 + 3 * (l - 1)) = 6 ^ 77 * (6 ^ 3) ^ (l - 1) := by rw [pow_add, pow_mul]
        _ < (10 ^ 12) ^ 5 * (6 ^ 3) ^ (l - 1) :=
            Nat.mul_lt_mul_of_pos_right h6_77 (by positivity)
        _ ≤ (10 ^ 12) ^ 5 * (3 ^ 5) ^ (l - 1) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h6_3 (l - 1))
        _ = (10 ^ 12 * 3 ^ (l - 1)) ^ 5 := by rw [mul_pow, pow_right_comm 3 5 (l - 1)]
        _ < (6 ^ u) ^ 5 := hpow5
        _ = 6 ^ (5 * u) := by rw [← pow_mul, mul_comm u 5]
    have hlt := (Nat.pow_lt_pow_iff_right (by decide : 1 < 6)).mp h6_exp
    omega
  have h5_bound : r ∈ ({5, 7, 11, 13} : Finset ℕ) → 8 * l + 131 ≤ 9 * u := by
    intro hr5
    have h5_le_r : 5 ≤ r := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr5
      rcases hr5 with rfl | rfl | rfl | rfl <;> decide
    have h10_5 : 10 ^ 12 * 5 ^ (l - 1) < 6 ^ u :=
      lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h5_le_r (l - 1))) hcap
    have hpow9 : (10 ^ 12 * 5 ^ (l - 1)) ^ 9 < (6 ^ u) ^ 9 :=
      Nat.pow_lt_pow_left h10_5 (by decide)
    have h6_138 : 6 ^ 138 < (10 ^ 12) ^ 9 := by norm_num
    have h6_8 : 6 ^ 8 ≤ 5 ^ 9 := by norm_num
    have h6_exp : 6 ^ (138 + 8 * (l - 1)) < 6 ^ (9 * u) := by
      calc
        6 ^ (138 + 8 * (l - 1)) = 6 ^ 138 * (6 ^ 8) ^ (l - 1) := by rw [pow_add, pow_mul]
        _ < (10 ^ 12) ^ 9 * (6 ^ 8) ^ (l - 1) :=
            Nat.mul_lt_mul_of_pos_right h6_138 (by positivity)
        _ ≤ (10 ^ 12) ^ 9 * (5 ^ 9) ^ (l - 1) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h6_8 (l - 1))
        _ = (10 ^ 12 * 5 ^ (l - 1)) ^ 9 := by rw [mul_pow, pow_right_comm 5 9 (l - 1)]
        _ < (6 ^ u) ^ 9 := hpow9
        _ = 6 ^ (9 * u) := by rw [← pow_mul, mul_comm u 9]
    have hlt := (Nat.pow_lt_pow_iff_right (by decide : 1 < 6)).mp h6_exp
    omega
  have h7_bound : r ∈ ({7, 11, 13} : Finset ℕ) → l + 15 ≤ u := by
    intro hr7
    have h6_le_r : 6 ≤ r := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr7
      rcases hr7 with rfl | rfl | rfl <;> decide
    have h6_15 : 6 ^ 15 < 10 ^ 12 := by norm_num
    have h6_exp : 6 ^ (15 + (l - 1)) < 6 ^ u := by
      calc
        6 ^ (15 + (l - 1)) = 6 ^ 15 * 6 ^ (l - 1) := by rw [pow_add]
        _ < 10 ^ 12 * 6 ^ (l - 1) := Nat.mul_lt_mul_of_pos_right h6_15 (by positivity)
        _ ≤ 10 ^ 12 * r ^ (l - 1) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h6_le_r (l - 1))
        _ < 6 ^ u := hcap
    have hlt := (Nat.pow_lt_pow_iff_right (by decide : 1 < 6)).mp h6_exp
    omega
  exact ⟨h3_bound, h5_bound, h7_bound⟩

/-- Global odd-perfect-number theorem coupling the `(2 * u + 1) ∣ p - 2` Padé collapse
(`10 ^ 12 * u * p < 6 ^ u` and `10 ^ 15 * p < 6 ^ u`) with complete linear repunit-length
bounds across all surviving primorial bases `r ∈ {3, 5, 7, 11, 13}`. -/
theorem even_prime_power_all_primorial_repunit_and_len_div_caps
    {N q a b i p u : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b) (hl : sigma 1 b = q ^ a * i)
    (hr : sigma 1 (q ^ a) * i = 2 * b) (hp : p.Prime) (hu : 0 < u) (hi : i = p ^ (2 * u)) :
    1154 ≤ u ∧ (2 * u + 1).Prime ∧
    10 ^ 12 * p < 6 ^ u ∧
    ((2 * u + 1) ∣ p - 2 → 10 ^ 12 * u * p < 6 ^ u ∧ 10 ^ 15 * p < 6 ^ u) ∧
    (∃ r ∈ ({3, 5, 7, 11, 13} : Finset ℕ),
      r ^ 2 ∣ N ∧
      ∃ l : ℕ, l.Prime ∧ 2 < l ∧ geometricBlock r l = p ∧
        10 ^ 12 * r ^ (l - 1) < 6 ^ u ∧
        3 * l + 75 ≤ 5 * u ∧
        (r ∈ ({5, 7, 11, 13} : Finset ℕ) → 8 * l + 131 ≤ 9 * u) ∧
        (r ∈ ({7, 11, 13} : Finset ℕ) → l + 15 ≤ u)) := by
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
  obtain ⟨⟨hu1154, h10_p, _, _⟩, ⟨r, hr_mem, hr2_N, l, hl_prime, hl_gt2, hgb, h10_r, _⟩⟩ :=
    even_prime_power_primorial_repunit_length_cap hN ho hq ha hform hqb hl hr hp hu hi
  have hdiv_cap : (2 * u + 1) ∣ p - 2 → 10 ^ 12 * u * p < 6 ^ u ∧ 10 ^ 15 * p < 6 ^ u := by
    intro hdiv
    obtain ⟨_, _, _, _, h10_up, h10_15⟩ :=
      even_index_pade_quotient_mod_two_len_collapse hq hp hpo hs hu hσq hplus hσs hdiv
    exact ⟨h10_up, h10_15⟩
  obtain ⟨h3_bd, h5_bd, h7_bd⟩ :=
    repunit_length_all_primorial_bases_linear_bounds hr_mem hl_gt2 h10_r
  exact ⟨hu1154, hlen_prime, h10_p, hdiv_cap,
    ⟨r, hr_mem, hr2_N, l, hl_prime, hl_gt2, hgb, h10_r, h3_bd, h5_bd, h7_bd⟩⟩

end OddPerfect
