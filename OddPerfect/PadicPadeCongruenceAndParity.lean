module

public import OddPerfect.PadicPadeQuadraticQuotient
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# p-adic Padé Second-Order Congruences, Parity Laws & Doubled Contraction (`OddPerfect.PadicPadeCongruenceAndParity`)

Develops higher-order congruences, exact parity laws, doubled exponential contraction,
mod-`p` square-root base collapse, and mod-`(p - 2)` congruences for the Pell–Padé
approximant tower `(padeSeqA u p, padeSeqB u p)` and quotient `k_pade` on `i = p ^ (2 * u)`:

1. `padeSeqB_mod_pred_sq`:
   Second-order Taylor congruence modulo `(p - 1) ^ 2`:
   `((p : ℤ) - 1) ^ 2 ∣ padeSeqB u p - (-1 : ℤ) ^ u * (1 - (u : ℤ) * (4 * (u : ℤ) + 3) * ((p : ℤ) - 1))`.
2. `padeSeqB_sq_sub_one_div_twice_pred_parity`:
   Exact divisibility and parity laws for `rhs := (padeSeqB u p ^ 2 - 1) / (2 * ((p : ℤ) - 1))`:
   `p % 4 = 3 → Even rhs` and `p % 4 = 1 → (Even rhs ↔ Even u)`.
3. `even_index_pade_quotient_parity_and_doubled_cap`:
   Transfers parity to `k_pade`, proving `2 ≤ k_pade`, `2 * p ^ (u + 1) < padeSeqB u p`,
   `2 * 41 ^ (u - 2) * p < 41 * 239 ^ (u - 2)`, and `40 * p < 6 ^ u` whenever `p % 4 = 3 ∨ Even u`.
4. `even_index_pade_quotient_mod_p_and_sub_two`:
   Proves `(p : ℤ) ∣ k_pade ↔ p ∣ 64 ^ u - 1`, quadratic base collapse `20 * p ^ 2 < 6 ^ u`
   when `p ∣ 64 ^ u - 1`, and the mod-`(p - 2)` congruence
   `2 ^ (u + 1) * k_pade ≡ (2 * (u : ℤ) + 1) * (s : ℤ) - 1 [ZMOD (p : ℤ) - 2]`.
5. `even_prime_power_component_parity_and_order_caps`:
   Global odd-perfect-number wrapper bundling `128 ≤ u`, `20 * p < 6 ^ u`,
   `p % 4 = 3 ∨ Even u → 40 * p < 6 ^ u`, and `p ∣ 64 ^ u - 1 → 20 * p ^ 2 < 6 ^ u`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma odd_prime_ge_three_cong {p : ℕ} (hp : p.Prime) (hpo : Odd p) : 3 ≤ p := by
  have h2 : 2 ≤ p := hp.two_le
  rcases eq_or_lt_of_le h2 with rfl | hlt
  · exact absurd hpo (by decide)
  · exact hlt

private lemma padeSeq_sub_pred_dvd (u p : ℕ) :
    ((p : ℤ) - 1 ∣ padeSeqB u p - (-1 : ℤ) ^ u) ∧
    ((p : ℤ) - 1 ∣ padeSeqA u p - (-1 : ℤ) ^ u * (2 * (u : ℤ) + 1)) := by
  induction u with
  | zero =>
      simp
  | succ u ih =>
      rcases ih with ⟨hb, ha⟩
      constructor
      · have hid :
            padeSeqB (u + 1) p - (-1 : ℤ) ^ (u + 1) =
              ((p : ℤ) - 1) * (4 * padeSeqA u p + 3 * padeSeqB u p) -
                (padeSeqB u p - (-1 : ℤ) ^ u) := by
          simp only [padeSeqB_succ, pow_succ]
          ring
        rw [hid]
        exact dvd_sub (dvd_mul_right _ _) hb
      · have hid :
            padeSeqA (u + 1) p - (-1 : ℤ) ^ (u + 1) * (2 * ((u + 1 : ℕ) : ℤ) + 1) =
              ((p : ℤ) - 1) * (3 * padeSeqA u p + 2 * padeSeqB u p) -
                (padeSeqA u p - (-1 : ℤ) ^ u * (2 * (u : ℤ) + 1)) -
                2 * (padeSeqB u p - (-1 : ℤ) ^ u) := by
          simp only [padeSeqA_succ, pow_succ, Nat.cast_add, Nat.cast_one]
          ring
        rw [hid]
        exact dvd_sub (dvd_sub (dvd_mul_right _ _) ha) (dvd_mul_of_dvd_right hb 2)

private lemma twenty_mul_41_mul_239_pow_lt_41_pow_mul_6_pow_cong {u : ℕ} (hu : 128 ≤ u) :
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

/-! ### 1. Second-Order `(p - 1) ^ 2` Taylor Congruence -/

/-- Second-order Taylor congruence for `padeSeqB u p` modulo `(p - 1) ^ 2`. -/
theorem padeSeqB_mod_pred_sq (u p : ℕ) :
    ((p : ℤ) - 1) ^ 2 ∣
      padeSeqB u p - (-1 : ℤ) ^ u * (1 - (u : ℤ) * (4 * (u : ℤ) + 3) * ((p : ℤ) - 1)) := by
  induction u with
  | zero =>
      simp
  | succ u ih =>
      obtain ⟨hb1, ha1⟩ := padeSeq_sub_pred_dvd u p
      have hA_sq :
          ((p : ℤ) - 1) ^ 2 ∣
            4 * ((p : ℤ) - 1) * (padeSeqA u p - (-1 : ℤ) ^ u * (2 * (u : ℤ) + 1)) := by
        rw [show 4 * ((p : ℤ) - 1) * (padeSeqA u p - (-1 : ℤ) ^ u * (2 * (u : ℤ) + 1)) =
            ((p : ℤ) - 1) * (4 * (padeSeqA u p - (-1 : ℤ) ^ u * (2 * (u : ℤ) + 1))) by ring]
        rw [sq]
        exact mul_dvd_mul_left ((p : ℤ) - 1) (dvd_mul_of_dvd_right ha1 4)
      have hB_sq :
          ((p : ℤ) - 1) ^ 2 ∣
            3 * ((p : ℤ) - 1) * (padeSeqB u p - (-1 : ℤ) ^ u) := by
        rw [show 3 * ((p : ℤ) - 1) * (padeSeqB u p - (-1 : ℤ) ^ u) =
            ((p : ℤ) - 1) * (3 * (padeSeqB u p - (-1 : ℤ) ^ u)) by ring]
        rw [sq]
        exact mul_dvd_mul_left ((p : ℤ) - 1) (dvd_mul_of_dvd_right hb1 3)
      have hid :
          padeSeqB (u + 1) p -
              (-1 : ℤ) ^ (u + 1) *
                (1 - ((u + 1 : ℕ) : ℤ) * (4 * ((u + 1 : ℕ) : ℤ) + 3) * ((p : ℤ) - 1)) =
            4 * ((p : ℤ) - 1) * (padeSeqA u p - (-1 : ℤ) ^ u * (2 * (u : ℤ) + 1)) +
              3 * ((p : ℤ) - 1) * (padeSeqB u p - (-1 : ℤ) ^ u) -
              (padeSeqB u p - (-1 : ℤ) ^ u * (1 - (u : ℤ) * (4 * (u : ℤ) + 3) * ((p : ℤ) - 1))) := by
        simp only [padeSeqB_succ, pow_succ, Nat.cast_add, Nat.cast_one]
        ring
      rw [hid]
      exact dvd_sub (dvd_add hA_sq hB_sq) ih

/-! ### 2. Exact Parity Laws for `(padeSeqB u p ^ 2 - 1) / (2 * (p - 1))` -/

/-- Exact divisibility and parity laws for `rhs := (padeSeqB u p ^ 2 - 1) / (2 * ((p : ℤ) - 1))`. -/
theorem padeSeqB_sq_sub_one_div_twice_pred_parity {p u : ℕ}
    (hp_odd : Odd p) (hp3 : 3 ≤ p) (hu : 1 ≤ u) :
    let rhs : ℤ := (padeSeqB u p ^ 2 - 1) / (2 * ((p : ℤ) - 1))
    (2 * ((p : ℤ) - 1) * rhs = padeSeqB u p ^ 2 - 1) ∧
    (p % 4 = 3 → Even rhs) ∧
    (p % 4 = 1 → (Even rhs ↔ Even u)) := by
  intro rhs
  have _hu := hu
  set E : ℤ := (p : ℤ) - 1
  set c : ℤ := (u : ℤ) * (4 * (u : ℤ) + 3)
  obtain ⟨m, hm⟩ := padeSeqB_mod_pred_sq u p
  have hB : padeSeqB u p = (-1 : ℤ) ^ u * (1 - c * E) + E ^ 2 * m := by
    linarith
  obtain ⟨tN, htN⟩ := hp_odd
  have hp_pos3 : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
  have hE_eq : E = 2 * (tN : ℤ) := by
    have ht_cast : (p : ℤ) = 2 * (tN : ℤ) + 1 := by exact_mod_cast htN
    dsimp [E]
    linarith
  set t : ℤ := (tN : ℤ)
  have hneg_sq : ((-1 : ℤ) ^ u) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    simp
  set q : ℤ :=
    -c + c ^ 2 * t + 2 * ((-1 : ℤ) ^ u * (1 - 2 * c * t) * t * m + 2 * t ^ 3 * m ^ 2)
  have hfac : padeSeqB u p ^ 2 - 1 = 2 * E * q := by
    have hexp :
        padeSeqB u p ^ 2 - 1 =
          (((-1 : ℤ) ^ u) ^ 2 * (1 - c * E) ^ 2 - 1) +
            2 * (-1 : ℤ) ^ u * (1 - c * E) * E ^ 2 * m + E ^ 4 * m ^ 2 := by
      rw [hB]
      ring
    rw [hexp, hneg_sq, hE_eq]
    dsimp [q]
    ring
  have hdiv_ne : 2 * E ≠ 0 := by
    dsimp [E]
    linarith
  have hrhs_eq : rhs = q := by
    dsimp [rhs]
    rw [hfac, Int.mul_ediv_cancel_left _ hdiv_ne]
  have hmul_eq : 2 * E * rhs = padeSeqB u p ^ 2 - 1 := by
    rw [hrhs_eq, hfac]
  have hrhs_parity : Even rhs ↔ Even (c * (c * t - 1)) := by
    have hq_rew :
        q = c * (c * t - 1) +
          2 * ((-1 : ℤ) ^ u * (1 - 2 * c * t) * t * m + 2 * t ^ 3 * m ^ 2) := by
      dsimp [q]
      ring
    rw [hrhs_eq, hq_rew, Int.even_add]
    have hev2 : Even (2 * ((-1 : ℤ) ^ u * (1 - 2 * c * t) * t * m + 2 * t ^ 3 * m ^ 2)) :=
      ⟨(-1 : ℤ) ^ u * (1 - 2 * c * t) * t * m + 2 * t ^ 3 * m ^ 2, by ring⟩
    simp [hev2]
  refine ⟨hmul_eq, ?_, ?_⟩
  · intro hmod3
    have htN_odd : tN % 2 = 1 := by omega
    have ht_odd : ¬ Even t := by
      rw [show t = (tN : ℤ) from rfl, Int.even_natCast, Nat.even_iff]
      omega
    rw [hrhs_parity]
    rcases Int.even_or_odd c with hc_even | hc_odd
    · exact hc_even.mul_right _
    · apply Even.mul_left
      rw [Int.even_sub, Int.even_mul]
      have hc_not_even : ¬ Even c := Int.not_even_iff_odd.mpr hc_odd
      simp [hc_not_even, ht_odd]
  · intro hmod1
    have htN_even : tN % 2 = 0 := by omega
    have ht_even : Even t := by
      rw [show t = (tN : ℤ) from rfl, Int.even_natCast, Nat.even_iff]
      exact htN_even
    have hct1_odd : ¬ Even (c * t - 1) := by
      rw [Int.even_sub, Int.even_mul]
      simp [ht_even]
    have hc_even_iff : Even c ↔ Even u := by
      have h4u3_odd : ¬ Even (4 * (u : ℤ) + 3) := by
        rw [show (4 * (u : ℤ) + 3) = 2 * (2 * (u : ℤ) + 1) + 1 by ring, Int.even_add_one]
        have hev : Even (2 * (2 * (u : ℤ) + 1)) := ⟨2 * (u : ℤ) + 1, by ring⟩
        simp [hev]
      dsimp [c]
      rw [Int.even_mul, Int.even_natCast]
      simp [h4u3_odd]
    rw [hrhs_parity, Int.even_mul]
    simp [hct1_odd, hc_even_iff]

/-! ### 3. Padé Quotient Parity & Doubled Exponential Contraction -/

/-- Exact parity characterization of `k_pade` and doubled exponential contraction (`40 * p < 6 ^ u`)
when `p % 4 = 3 ∨ Even u`. -/
theorem even_index_pade_quotient_parity_and_doubled_cap {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let k_pade : ℤ := ((s : ℤ) * padeSeqB u p - padeSeqA u p) / (p : ℤ) ^ (2 * u + 1)
    (p % 4 = 3 → Even k_pade ∧ 2 ≤ k_pade) ∧
    (p % 4 = 1 → (Even k_pade ↔ Even u)) ∧
    (p % 4 = 3 ∨ Even u →
      2 ≤ k_pade ∧
      8 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) < padeSeqB u p ^ 2 ∧
      2 * (p : ℤ) ^ (u + 1) < padeSeqB u p ∧
      (2 ≤ u → 2 * 41 ^ (u - 2) * p < 41 * 239 ^ (u - 2)) ∧
      (128 ≤ u → 40 * p < 6 ^ u)) := by
  intro k_pade
  have hp3 : 3 ≤ p := odd_prime_ge_three_cong hp hpo
  have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
  obtain ⟨_, hk1, hquad, _, _⟩ :=
    even_index_pade_quotient_pos_and_quadratic_identity hp hpo hs hu hσq hplus hσs
  obtain ⟨hmul_rhs, hrhs_mod3, hrhs_mod1⟩ :=
    padeSeqB_sq_sub_one_div_twice_pred_parity hpo hp3 hu
  set rhs : ℤ := (padeSeqB u p ^ 2 - 1) / (2 * ((p : ℤ) - 1))
  have hdiv_ne : 2 * ((p : ℤ) - 1) ≠ 0 := by linarith
  have hlhs_eq : (p : ℤ) ^ (2 * u + 1) * k_pade ^ 2 + 2 * padeSeqA u p * k_pade = rhs := by
    apply mul_left_cancel₀ hdiv_ne
    calc
      2 * ((p : ℤ) - 1) * ((p : ℤ) ^ (2 * u + 1) * k_pade ^ 2 + 2 * padeSeqA u p * k_pade)
          = 2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) * k_pade ^ 2 +
              4 * ((p : ℤ) - 1) * padeSeqA u p * k_pade := by ring
      _ = padeSeqB u p ^ 2 - 1 := hquad
      _ = 2 * ((p : ℤ) - 1) * rhs := hmul_rhs.symm
  have hodd_pZ : ¬ Even (p : ℤ) := by
    rw [Int.even_natCast]
    exact Nat.not_even_iff_odd.mpr hpo
  have hodd_pow : ¬ Even ((p : ℤ) ^ (2 * u + 1)) := by
    rw [Int.even_pow' (by omega)]
    exact hodd_pZ
  have heven_k_iff_rhs : Even k_pade ↔ Even rhs := by
    rw [← hlhs_eq, Int.even_add]
    have hev2 : Even (2 * padeSeqA u p * k_pade) := ⟨padeSeqA u p * k_pade, by ring⟩
    simp [hev2, Int.even_mul, hodd_pow, Int.even_pow' (by decide : 2 ≠ 0)]
  have hge2_of_even : Even k_pade → 2 ≤ k_pade := by
    rintro ⟨m, hm⟩
    have hm1 : 1 ≤ m := by linarith
    linarith
  have hmod3 : p % 4 = 3 → Even k_pade ∧ 2 ≤ k_pade := by
    intro h3
    have hev : Even k_pade := heven_k_iff_rhs.mpr (hrhs_mod3 h3)
    exact ⟨hev, hge2_of_even hev⟩
  have hmod1 : p % 4 = 1 → (Even k_pade ↔ Even u) := by
    intro h1
    exact heven_k_iff_rhs.trans (hrhs_mod1 h1)
  refine ⟨hmod3, hmod1, ?_⟩
  intro hcond
  have hk2 : 2 ≤ k_pade := by
    have hmod13 : p % 4 = 1 ∨ p % 4 = 3 := by
      rcases hpo with ⟨t, rfl⟩
      omega
    rcases hmod13 with h1 | h3
    · rcases hcond with h3' | hu_even
      · omega
      · exact hge2_of_even ((hmod1 h1).mpr hu_even)
    · exact (hmod3 h3).2
  obtain ⟨hA_ge, hB_ge⟩ := padeSeq_one_le hp3 u
  have hpow_pos : (0 : ℤ) < (p : ℤ) ^ (2 * u + 1) := by positivity
  have hpu_pos : (0 : ℤ) < (p : ℤ) ^ u := by positivity
  have h8B2 : 8 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) < padeSeqB u p ^ 2 := by
    have hk_sq : 4 ≤ k_pade ^ 2 := by nlinarith
    have hcoeff_nn : 0 ≤ 2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) :=
      mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hpow_pos.le
    have hmul_sq :
        8 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) ≤
          2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) * k_pade ^ 2 := by
      calc
        8 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1)
            = 2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) * 4 := by ring
        _ ≤ 2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) * k_pade ^ 2 :=
            mul_le_mul_of_nonneg_left hk_sq hcoeff_nn
    have hrem_pos : 0 < 4 * ((p : ℤ) - 1) * padeSeqA u p * k_pade + 1 := by
      have h4 : (8 : ℤ) ≤ 4 * ((p : ℤ) - 1) := by linarith
      have h4A : (8 : ℤ) ≤ 4 * ((p : ℤ) - 1) * padeSeqA u p := by
        nlinarith
      nlinarith
    linarith
  have h2pu1_lt_B : 2 * (p : ℤ) ^ (u + 1) < padeSeqB u p := by
    have h4p_lt : 4 * (p : ℤ) < 8 * ((p : ℤ) - 1) := by linarith
    have hsq_eq : (2 * (p : ℤ) ^ (u + 1)) ^ 2 = 4 * (p : ℤ) * (p : ℤ) ^ (2 * u + 1) := by
      rw [mul_pow, ← pow_mul, show (u + 1) * 2 = 1 + (2 * u + 1) by omega, pow_add, pow_one]
      ring
    have hsq_lt : (2 * (p : ℤ) ^ (u + 1)) ^ 2 < padeSeqB u p ^ 2 := by
      have hmul :
          4 * (p : ℤ) * (p : ℤ) ^ (2 * u + 1) <
            8 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) :=
        mul_lt_mul_of_pos_right h4p_lt hpow_pos
      linarith
    by_contra! hle
    have hsq_le : padeSeqB u p ^ 2 ≤ (2 * (p : ℤ) ^ (u + 1)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hle 2
    linarith
  have h239_cap : 2 ≤ u → 2 * 41 ^ (u - 2) * p < 41 * 239 ^ (u - 2) := by
    intro hu2
    have h41B := forty_one_pow_mul_padeSeqB_lt_239_pow hp3 hu2
    have h41_pos : (0 : ℤ) < (41 : ℤ) ^ (u - 2) := by positivity
    have hchain :
        (2 * (41 : ℤ) ^ (u - 2) * (p : ℤ)) * (p : ℤ) ^ u <
          41 * 239 ^ (u - 2) * (p : ℤ) ^ u := by
      calc
        (2 * (41 : ℤ) ^ (u - 2) * (p : ℤ)) * (p : ℤ) ^ u
            = (41 : ℤ) ^ (u - 2) * (2 * (p : ℤ) ^ (u + 1)) := by rw [pow_succ']; ring
        _ < (41 : ℤ) ^ (u - 2) * padeSeqB u p := mul_lt_mul_of_pos_left h2pu1_lt_B h41_pos
        _ < 41 * 239 ^ (u - 2) * (p : ℤ) ^ u := h41B
    have hltZ : 2 * (41 : ℤ) ^ (u - 2) * (p : ℤ) < 41 * 239 ^ (u - 2) :=
      lt_of_mul_lt_mul_right hchain hpu_pos.le
    exact_mod_cast hltZ
  have h40_cap : 128 ≤ u → 40 * p < 6 ^ u := by
    intro hu128
    have hcap := h239_cap (by omega)
    have hnum := twenty_mul_41_mul_239_pow_lt_41_pow_mul_6_pow_cong hu128
    have h40 : 41 ^ (u - 2) * (40 * p) < 41 ^ (u - 2) * 6 ^ u := by
      calc
        41 ^ (u - 2) * (40 * p) = 20 * (2 * 41 ^ (u - 2) * p) := by ring
        _ < 20 * (41 * 239 ^ (u - 2)) := Nat.mul_lt_mul_of_pos_left hcap (by decide)
        _ < 41 ^ (u - 2) * 6 ^ u := hnum
    exact Nat.lt_of_mul_lt_mul_left h40
  exact ⟨hk2, h8B2, h2pu1_lt_B, h239_cap, h40_cap⟩

/-! ### 4. Mod-`p` Square-Root Collapse & Mod-`(p - 2)` Congruence -/

/-- Mod-`p` divisibility equivalence `(p : ℤ) ∣ k_pade ↔ p ∣ 64 ^ u - 1`, quadratic base collapse
`20 * p ^ 2 < 6 ^ u` when `p ∣ 64 ^ u - 1`, and mod-`(p - 2)` congruence for `k_pade`. -/
theorem even_index_pade_quotient_mod_p_and_sub_two {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let k_pade : ℤ := ((s : ℤ) * padeSeqB u p - padeSeqA u p) / (p : ℤ) ^ (2 * u + 1)
    ((p : ℤ) ∣ k_pade ↔ p ∣ 64 ^ u - 1) ∧
    (p ∣ 64 ^ u - 1 →
      (p : ℤ) ≤ k_pade ∧
      2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 3) < padeSeqB u p ^ 2 ∧
      (p : ℤ) ^ (u + 2) < padeSeqB u p ∧
      (2 ≤ u → 41 ^ (u - 2) * p ^ 2 < 41 * 239 ^ (u - 2)) ∧
      (128 ≤ u → 20 * p ^ 2 < 6 ^ u)) ∧
    (2 ^ (u + 1) * k_pade ≡ (2 * (u : ℤ) + 1) * (s : ℤ) - 1 [ZMOD (p : ℤ) - 2]) := by
  intro k_pade
  have hp3 : 3 ≤ p := odd_prime_ge_three_cong hp hpo
  have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
  obtain ⟨hmul, hk1, hquad, _, _⟩ :=
    even_index_pade_quotient_pos_and_quadratic_identity hp hpo hs hu hσq hplus hσs
  obtain ⟨hp_dvd_A, hp_dvd_B⟩ := padeSeq_sub_neg_eight_pow_dvd u p
  have hp_mod_neg1 : ((p : ℤ) - 1) ≡ -1 [ZMOD (p : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    exact ⟨-1, by ring⟩
  have hmod_p :
      -4 * (-8 : ℤ) ^ u * k_pade ≡ (64 : ℤ) ^ u - 1 [ZMOD (p : ℤ)] := by
    obtain ⟨hA_mod, hB_mod⟩ := padeSeq_modEq u p
    have hpow_mod : (p : ℤ) ^ (2 * u + 1) ≡ 0 [ZMOD (p : ℤ)] := by
      rw [Int.modEq_zero_iff_dvd]
      exact dvd_pow_self (p : ℤ) (by omega : 2 * u + 1 ≠ 0)
    have hlhs_mod :
        2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) * k_pade ^ 2 +
            4 * ((p : ℤ) - 1) * padeSeqA u p * k_pade ≡
          -4 * (-8 : ℤ) ^ u * k_pade [ZMOD (p : ℤ)] := by
      have ht1 : 2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) * k_pade ^ 2 ≡ 0 [ZMOD (p : ℤ)] := by
        have := ((Int.ModEq.refl (2 * ((p : ℤ) - 1))).mul hpow_mod).mul (Int.ModEq.refl (k_pade ^ 2))
        simpa using this
      have ht2 :
          4 * ((p : ℤ) - 1) * padeSeqA u p * k_pade ≡
            4 * (-1) * (-8 : ℤ) ^ u * k_pade [ZMOD (p : ℤ)] :=
        (((Int.ModEq.refl 4).mul hp_mod_neg1).mul hA_mod).mul (Int.ModEq.refl k_pade)
      have hsum := ht1.add ht2
      simpa [show 0 + 4 * (-1) * (-8 : ℤ) ^ u * k_pade = -4 * (-8 : ℤ) ^ u * k_pade by ring] using
        hsum
    have hrhs_mod : padeSeqB u p ^ 2 - 1 ≡ (64 : ℤ) ^ u - 1 [ZMOD (p : ℤ)] := by
      have hsq := hB_mod.pow 2
      have h64 : ((-8 : ℤ) ^ u) ^ 2 = (64 : ℤ) ^ u := by
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num
      rw [h64] at hsq
      exact hsq.sub (Int.ModEq.refl 1)
    rw [hquad] at hlhs_mod
    exact hlhs_mod.symm.trans hrhs_mod
  have hp_dvd_iff : (p : ℤ) ∣ k_pade ↔ p ∣ 64 ^ u - 1 := by
    have h64_cast : ((64 ^ u - 1 : ℕ) : ℤ) = (64 : ℤ) ^ u - 1 := by
      have h1 : 1 ≤ 64 ^ u := Nat.one_le_pow _ _ (by decide)
      rw [Nat.cast_sub h1]
      push_cast
      rfl
    have hdvd_diff : (p : ℤ) ∣ ((64 : ℤ) ^ u - 1) - (-4 * (-8 : ℤ) ^ u * k_pade) :=
      Int.modEq_iff_dvd.mp hmod_p
    have hnot_dvd_coeff : ¬ (p : ℤ) ∣ 4 * (-8 : ℤ) ^ u := by
      intro hd
      have hsign : (4 * (-8 : ℤ) ^ u) = ((-1 : ℤ) ^ u) * ((2 ^ (3 * u + 2) : ℕ) : ℤ) := by
        push_cast
        rw [show (-8 : ℤ) = (-1 : ℤ) * 2 ^ 3 by norm_num, mul_pow, ← pow_mul]
        ring
      rw [hsign] at hd
      have hunit : IsUnit ((-1 : ℤ) ^ u) := (isUnit_one.neg).pow u
      have hd_nat : p ∣ 2 ^ (3 * u + 2) := Int.natCast_dvd_natCast.mp (hunit.dvd_mul_left.mp hd)
      have hp2 : p = 2 := (Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow hd_nat) |>.resolve_left hp.ne_one
      subst hp2
      exact absurd hpo (by decide)
    have hpZ_prime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hdvd_prod_iff : (p : ℤ) ∣ -4 * (-8 : ℤ) ^ u * k_pade ↔ (p : ℤ) ∣ k_pade := by
      constructor
      · intro hmul_dvd
        have hmul_dvd' : (p : ℤ) ∣ -(4 * (-8 : ℤ) ^ u) * k_pade := by
          simpa [mul_assoc] using hmul_dvd
        rcases hpZ_prime.dvd_or_dvd hmul_dvd' with hc | hk
        · exact absurd (dvd_neg.mp hc) hnot_dvd_coeff
        · exact hk
      · intro hk
        exact dvd_mul_of_dvd_right hk _
    have hnat_iff : (p : ℤ) ∣ (64 : ℤ) ^ u - 1 ↔ p ∣ 64 ^ u - 1 := by
      rw [← h64_cast, Int.natCast_dvd_natCast]
    rw [← hnat_iff, ← hdvd_prod_iff]
    constructor
    · intro h1
      have hsum := dvd_add h1 hdvd_diff
      simpa using hsum
    · intro h2
      have hsub := dvd_sub h2 hdvd_diff
      simpa using hsub
  have hcollapse :
      p ∣ 64 ^ u - 1 →
        (p : ℤ) ≤ k_pade ∧
        2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 3) < padeSeqB u p ^ 2 ∧
        (p : ℤ) ^ (u + 2) < padeSeqB u p ∧
        (2 ≤ u → 41 ^ (u - 2) * p ^ 2 < 41 * 239 ^ (u - 2)) ∧
        (128 ≤ u → 20 * p ^ 2 < 6 ^ u) := by
    intro h64
    have hp_dvd_k : (p : ℤ) ∣ k_pade := hp_dvd_iff.mpr h64
    have hp_le_k : (p : ℤ) ≤ k_pade := Int.le_of_dvd (by linarith) hp_dvd_k
    obtain ⟨hA_ge, hB_ge⟩ := padeSeq_one_le hp3 u
    have hpow_pos : (0 : ℤ) < (p : ℤ) ^ (2 * u + 1) := by positivity
    have hpu_pos : (0 : ℤ) < (p : ℤ) ^ u := by positivity
    have hp_sq_le_k_sq : (p : ℤ) ^ 2 ≤ k_pade ^ 2 :=
      pow_le_pow_left₀ (by linarith) hp_le_k 2
    have h2B2 : 2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 3) < padeSeqB u p ^ 2 := by
      have hcoeff_nn : 0 ≤ 2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) :=
        mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hpow_pos.le
      have hmul_sq :
          2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 3) ≤
            2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) * k_pade ^ 2 := by
        calc
          2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 3)
              = 2 * ((p : ℤ) - 1) * ((p : ℤ) ^ (2 * u + 1) * (p : ℤ) ^ 2) := by
                  rw [← pow_add, show (2 * u + 1) + 2 = 2 * u + 3 by omega]
          _ = 2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) * (p : ℤ) ^ 2 := by ring
          _ ≤ 2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) * k_pade ^ 2 :=
              mul_le_mul_of_nonneg_left hp_sq_le_k_sq hcoeff_nn
      have hrem_pos : 0 < 4 * ((p : ℤ) - 1) * padeSeqA u p * k_pade + 1 := by
        have h4 : (8 : ℤ) ≤ 4 * ((p : ℤ) - 1) := by linarith
        have h4A : (8 : ℤ) ≤ 4 * ((p : ℤ) - 1) * padeSeqA u p := by nlinarith
        nlinarith
      linarith
    have hpu2_lt_B : (p : ℤ) ^ (u + 2) < padeSeqB u p := by
      have hp_lt_2p1 : (p : ℤ) < 2 * ((p : ℤ) - 1) := by linarith
      have hpow3_pos : (0 : ℤ) < (p : ℤ) ^ (2 * u + 3) := by positivity
      have hsq_eq : ((p : ℤ) ^ (u + 2)) ^ 2 = (p : ℤ) * (p : ℤ) ^ (2 * u + 3) := by
        rw [← pow_mul, ← pow_succ']
        congr 1
        omega
      have hsq_lt : ((p : ℤ) ^ (u + 2)) ^ 2 < padeSeqB u p ^ 2 := by
        have hmul := mul_lt_mul_of_pos_right hp_lt_2p1 hpow3_pos
        linarith
      by_contra! hle
      have hsq_le : padeSeqB u p ^ 2 ≤ ((p : ℤ) ^ (u + 2)) ^ 2 :=
        pow_le_pow_left₀ (by linarith) hle 2
      linarith
    have h239_sq : 2 ≤ u → 41 ^ (u - 2) * p ^ 2 < 41 * 239 ^ (u - 2) := by
      intro hu2
      have h41B := forty_one_pow_mul_padeSeqB_lt_239_pow hp3 hu2
      have h41_pos : (0 : ℤ) < (41 : ℤ) ^ (u - 2) := by positivity
      have hchain :
          ((41 : ℤ) ^ (u - 2) * (p : ℤ) ^ 2) * (p : ℤ) ^ u <
            41 * 239 ^ (u - 2) * (p : ℤ) ^ u := by
        calc
          ((41 : ℤ) ^ (u - 2) * (p : ℤ) ^ 2) * (p : ℤ) ^ u
              = (41 : ℤ) ^ (u - 2) * (p : ℤ) ^ (u + 2) := by
                  rw [mul_assoc, ← pow_add, show 2 + u = u + 2 by omega]
          _ < (41 : ℤ) ^ (u - 2) * padeSeqB u p := mul_lt_mul_of_pos_left hpu2_lt_B h41_pos
          _ < 41 * 239 ^ (u - 2) * (p : ℤ) ^ u := h41B
      have hltZ : (41 : ℤ) ^ (u - 2) * (p : ℤ) ^ 2 < 41 * 239 ^ (u - 2) :=
        lt_of_mul_lt_mul_right hchain hpu_pos.le
      exact_mod_cast hltZ
    have h20_sq : 128 ≤ u → 20 * p ^ 2 < 6 ^ u := by
      intro hu128
      have hcap := h239_sq (by omega)
      have hnum := twenty_mul_41_mul_239_pow_lt_41_pow_mul_6_pow_cong hu128
      have h20 : 41 ^ (u - 2) * (20 * p ^ 2) < 41 ^ (u - 2) * 6 ^ u := by
        calc
          41 ^ (u - 2) * (20 * p ^ 2) = 20 * (41 ^ (u - 2) * p ^ 2) := by ring
          _ < 20 * (41 * 239 ^ (u - 2)) := Nat.mul_lt_mul_of_pos_left hcap (by decide)
          _ < 41 ^ (u - 2) * 6 ^ u := hnum
      exact Nat.lt_of_mul_lt_mul_left h20
    exact ⟨hp_le_k, h2B2, hpu2_lt_B, h239_sq, h20_sq⟩
  have hmod_sub_two :
      2 ^ (u + 1) * k_pade ≡ (2 * (u : ℤ) + 1) * (s : ℤ) - 1 [ZMOD (p : ℤ) - 2] := by
    obtain ⟨_, _, hA_sub2, hB_sub2⟩ := padeSeq_mod_pred_and_sub_two hp3 u
    have hp_mod2 : (p : ℤ) ≡ 2 [ZMOD (p : ℤ) - 2] := by
      rw [Int.modEq_iff_dvd]
      exact ⟨-1, by ring⟩
    have hpow_mod2 : (p : ℤ) ^ (2 * u + 1) ≡ 2 ^ (2 * u + 1) [ZMOD (p : ℤ) - 2] :=
      hp_mod2.pow (2 * u + 1)
    have hlhs_mod2 :
        (s : ℤ) * padeSeqB u p - padeSeqA u p ≡
          (s : ℤ) * ((2 * (u : ℤ) + 1) * 2 ^ u) - 2 ^ u [ZMOD (p : ℤ) - 2] :=
      ((Int.ModEq.refl (s : ℤ)).mul hB_sub2).sub hA_sub2
    have hrhs_mod2 :
        (p : ℤ) ^ (2 * u + 1) * k_pade ≡ 2 ^ (2 * u + 1) * k_pade [ZMOD (p : ℤ) - 2] :=
      hpow_mod2.mul (Int.ModEq.refl k_pade)
    rw [hmul] at hlhs_mod2
    have hmul_mod2 :
        2 ^ u * (2 ^ (u + 1) * k_pade) ≡
          2 ^ u * ((2 * (u : ℤ) + 1) * (s : ℤ) - 1) [ZMOD (p : ℤ) - 2] := by
      have hrew1 : (2 : ℤ) ^ u * (2 ^ (u + 1) * k_pade) = 2 ^ (2 * u + 1) * k_pade := by
        rw [← mul_assoc, ← pow_add, show u + (u + 1) = 2 * u + 1 by omega]
      have hrew2 :
          (2 : ℤ) ^ u * ((2 * (u : ℤ) + 1) * (s : ℤ) - 1) =
            (s : ℤ) * ((2 * (u : ℤ) + 1) * 2 ^ u) - 2 ^ u := by
        ring
      rw [hrew1, hrew2]
      exact hrhs_mod2.symm.trans hlhs_mod2
    have hdvd_mul :
        (p : ℤ) - 2 ∣
          (2 : ℤ) ^ u * (((2 * (u : ℤ) + 1) * (s : ℤ) - 1) - 2 ^ (u + 1) * k_pade) := by
      have h := Int.modEq_iff_dvd.mp hmul_mod2
      simpa [mul_sub] using h
    have hnot_dvd_2 : ¬ (2 : ℤ) ∣ (p : ℤ) - 2 := by
      intro ⟨k, hk⟩
      have hpe : Even p := by
        rw [← Int.even_natCast]
        exact ⟨k + 1, by linarith⟩
      exact (Nat.not_even_iff_odd.mpr hpo) hpe
    have hcop2 : IsCoprime (2 : ℤ) ((p : ℤ) - 2) :=
      Int.prime_two.coprime_iff_not_dvd.mpr hnot_dvd_2
    have hcop_pow : IsCoprime ((2 : ℤ) ^ u) ((p : ℤ) - 2) :=
      hcop2.pow_left
    have hdvd_cancel :
        (p : ℤ) - 2 ∣ ((2 * (u : ℤ) + 1) * (s : ℤ) - 1) - 2 ^ (u + 1) * k_pade :=
      hcop_pow.symm.dvd_of_dvd_mul_left hdvd_mul
    exact Int.modEq_iff_dvd.mpr hdvd_cancel
  exact ⟨hp_dvd_iff, hcollapse, hmod_sub_two⟩

/-! ### 5. Global Even Prime-Power Component Wrapper -/

/-- On every even prime-power component index `i = p ^ (2 * u)` of an odd perfect number `N`,
`128 ≤ u`, `20 * p < 6 ^ u`, `p % 4 = 3 ∨ Even u → 40 * p < 6 ^ u`, and
`p ∣ 64 ^ u - 1 → 20 * p ^ 2 < 6 ^ u`. -/
theorem even_prime_power_component_parity_and_order_caps
    {N q a b i p u : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b) (hl : sigma 1 b = q ^ a * i)
    (hr : sigma 1 (q ^ a) * i = 2 * b) (hp : p.Prime) (hu : 0 < u) (hi : i = p ^ (2 * u)) :
    128 ≤ u ∧
    20 * p < 6 ^ u ∧
    (p % 4 = 3 ∨ Even u → 40 * p < 6 ^ u) ∧
    (p ∣ 64 ^ u - 1 → 20 * p ^ 2 < 6 ^ u) := by
  obtain ⟨hu128, _, h20⟩ :=
    even_prime_power_component_sharpened_pade_cap hN ho hq ha hform hqb hl hr hp hu hi
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
  have hdoubled :=
    (even_index_pade_quotient_parity_and_doubled_cap hp hpo hs hu hσq hplus hσs).2.2
  have hcollapse :=
    (even_index_pade_quotient_mod_p_and_sub_two hp hpo hs hu hσq hplus hσs).2.1
  refine ⟨hu128, h20, ?_, ?_⟩
  · intro hcond
    exact (hdoubled hcond).2.2.2.2 hu128
  · intro h64
    exact (hcollapse h64).2.2.2.2 hu128

end OddPerfect
