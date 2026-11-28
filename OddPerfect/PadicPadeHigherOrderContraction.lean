module

public import OddPerfect.PadicPadeCongruenceAndParity
public import OddPerfect.PrimePowerExponent2308
public import OddPerfect.EvenIndexPrimorialObstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# p-adic Padé Third-Order `1393 / 239` Contraction & `10 ^ 12` Caps (`OddPerfect.PadicPadeHigherOrderContraction`)

Formalizes the third-order Pell–Padé contraction `(1393 / 239)` for `3 ≤ u` and couples it
with `even_index_exponent_ge_2308_and_base_ge_12207031` (`1154 ≤ u`) and
`even_prime_power_component_forces_small_repunit_base` (`r ∈ {3, 5, 7, 11, 13}`):

1. `padeSeq_sharpened_1393_239_contraction`:
   For `3 ≤ p` and `3 ≤ u`:
   - `239 * padeSeqA u p ≤ 169 * padeSeqB u p`
   - `239 * padeSeqB (u + 1) p < 1393 * (p : ℤ) * padeSeqB u p`
   - `239 ^ (u - 3) * padeSeqB u p < 239 * 1393 ^ (u - 3) * (p : ℤ) ^ u`
2. `even_index_prime_ten_pow_twelve_cap`:
   On any even prime-power component equation `sigma 1 (p ^ (2 * u)) = q`,
   `q + 1 = 2 * s ^ 2`, `sigma 1 (s ^ 2) = p ^ (2 * u)`:
   - `1154 ≤ u`
   - `239 ^ (u - 3) * p < 239 * 1393 ^ (u - 3)`
   - `10 ^ 12 * p < 6 ^ u`
   - `p % 4 = 3 ∨ Even u → 2 * 10 ^ 12 * p < 6 ^ u`
   - `p ∣ 64 ^ u - 1 → 10 ^ 12 * p ^ 2 < 6 ^ u`
3. `even_prime_power_primorial_repunit_length_cap`:
   Global odd-perfect-number wrapper yielding the `10 ^ 12` caps together with
   `r ∈ {3, 5, 7, 11, 13}`, `r ^ 2 ∣ N`, `geometricBlock r l = p`,
   `10 ^ 12 * r ^ (l - 1) < 6 ^ u`, and `r ∈ {7, 11, 13} → l + 15 ≤ u`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma odd_prime_ge_three_1393 {p : ℕ} (hp : p.Prime) (hpo : Odd p) : 3 ≤ p := by
  have h2 : 2 ≤ p := hp.two_le
  rcases eq_or_lt_of_le h2 with rfl | hlt
  · exact absurd hpo (by decide)
  · exact hlt

private lemma two_hundred_thirty_nine_mul_padeSeqA_le_169_mul_padeSeqB {p u : ℕ}
    (hp3 : 3 ≤ p) (hu : 3 ≤ u) :
    239 * padeSeqA u p ≤ 169 * padeSeqB u p := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, u = 3 + k := ⟨u - 3, by omega⟩
  have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
  induction k with
  | zero =>
      set t : ℤ := (p : ℤ) - 3
      have ht : 0 ≤ t := by dsimp [t]; linarith
      have hid :
          169 * padeSeqB (3 + 0) p - 239 * padeSeqA (3 + 0) p =
            20192 * t ^ 2 + 66624 * t + 53984 := by
        dsimp [t, padeSeqA, padeSeqB, padeSeqPair]
        ring
      have hpos : 0 ≤ 20192 * t ^ 2 + 66624 * t + 53984 := by positivity
      linarith
  | succ k ih =>
      have hk3 : 3 ≤ 3 + k := by omega
      have ihk := ih hk3
      obtain ⟨ha, hb⟩ := padeSeq_one_le hp3 (3 + k)
      have hid :
          239 * (169 * padeSeqB (3 + k + 1) p - 239 * padeSeqA (3 + k + 1) p) =
            41 * (p : ℤ) * (169 * padeSeqB (3 + k) p - 239 * padeSeqA (3 + k) p) +
              (2 * (p : ℤ) + 66920) * padeSeqB (3 + k) p + 66920 * padeSeqA (3 + k) p := by
        simp only [padeSeqA_succ, padeSeqB_succ]
        ring
      have hdiff : 0 ≤ 169 * padeSeqB (3 + k) p - 239 * padeSeqA (3 + k) p := by linarith
      have ht1 : 0 ≤ 41 * (p : ℤ) * (169 * padeSeqB (3 + k) p - 239 * padeSeqA (3 + k) p) :=
        mul_nonneg (by positivity) hdiff
      have ht2 : 0 < (2 * (p : ℤ) + 66920) * padeSeqB (3 + k) p :=
        mul_pos (by linarith) (by linarith)
      have hpos : 0 < 239 * (169 * padeSeqB (3 + k + 1) p - 239 * padeSeqA (3 + k + 1) p) := by
        linarith
      rw [← Nat.add_assoc]
      linarith

private lemma two_hundred_thirty_nine_mul_padeSeqB_succ_lt_1393_mul {p u : ℕ}
    (hp3 : 3 ≤ p) (hu : 3 ≤ u) :
    239 * padeSeqB (u + 1) p < 1393 * (p : ℤ) * padeSeqB u p := by
  have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
  obtain ⟨_, hb⟩ := padeSeq_one_le hp3 u
  have h239_169 := two_hundred_thirty_nine_mul_padeSeqA_le_169_mul_padeSeqB hp3 hu
  have hstep :
      4 * ((p : ℤ) - 1) * (239 * padeSeqA u p) + 239 * (3 * (p : ℤ) - 4) * padeSeqB u p ≤
        4 * ((p : ℤ) - 1) * (169 * padeSeqB u p) + 239 * (3 * (p : ℤ) - 4) * padeSeqB u p := by
    have hmul :
        4 * ((p : ℤ) - 1) * (239 * padeSeqA u p) ≤
          4 * ((p : ℤ) - 1) * (169 * padeSeqB u p) :=
      mul_le_mul_of_nonneg_left h239_169 (by linarith)
    linarith
  have hid1 :
      239 * padeSeqB (u + 1) p =
        4 * ((p : ℤ) - 1) * (239 * padeSeqA u p) + 239 * (3 * (p : ℤ) - 4) * padeSeqB u p := by
    rw [padeSeqB_succ]
    ring
  have hid2 :
      4 * ((p : ℤ) - 1) * (169 * padeSeqB u p) + 239 * (3 * (p : ℤ) - 4) * padeSeqB u p =
        1393 * (p : ℤ) * padeSeqB u p - 1632 * padeSeqB u p := by
    ring
  linarith

private lemma two_hundred_thirty_nine_pow_mul_padeSeqB_lt_1393_pow {p u : ℕ}
    (hp3 : 3 ≤ p) (hu : 3 ≤ u) :
    239 ^ (u - 3) * padeSeqB u p < 239 * 1393 ^ (u - 3) * (p : ℤ) ^ u := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, u = 3 + k := ⟨u - 3, by omega⟩
  have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
  induction k with
  | zero =>
      simp only [Nat.add_zero, Nat.sub_self, pow_zero, one_mul, mul_one]
      set t : ℤ := (p : ℤ) - 3
      have ht : 0 ≤ t := by dsimp [t]; linarith
      have hid :
          239 * (p : ℤ) ^ 3 - padeSeqB 3 p =
            944 * t ^ 2 + 4448 * t + 5360 := by
        dsimp [t, padeSeqA, padeSeqB, padeSeqPair]
        ring
      have hpos : 0 < 944 * t ^ 2 + 4448 * t + 5360 := by positivity
      linarith
  | succ k ih =>
      have hk3 : 3 ≤ 3 + k := by omega
      have ihk := ih hk3
      have hstep := two_hundred_thirty_nine_mul_padeSeqB_succ_lt_1393_mul hp3 hk3
      have h239_pos : (0 : ℤ) < (239 : ℤ) ^ (3 + k - 3) := by positivity
      have hp_pos : (0 : ℤ) < (p : ℤ) := by linarith
      have h1 :
          (239 : ℤ) ^ (3 + k - 3) * (239 * padeSeqB (3 + k + 1) p) <
            (239 : ℤ) ^ (3 + k - 3) * (1393 * (p : ℤ) * padeSeqB (3 + k) p) :=
        mul_lt_mul_of_pos_left hstep h239_pos
      have h2 :
          1393 * (p : ℤ) * ((239 : ℤ) ^ (3 + k - 3) * padeSeqB (3 + k) p) <
            1393 * (p : ℤ) * (239 * 1393 ^ (3 + k - 3) * (p : ℤ) ^ (3 + k)) :=
        mul_lt_mul_of_pos_left ihk (by positivity)
      have hrewL :
          (239 : ℤ) ^ (3 + (k + 1) - 3) * padeSeqB (3 + (k + 1)) p =
            (239 : ℤ) ^ (3 + k - 3) * (239 * padeSeqB (3 + k + 1) p) := by
        rw [show 3 + (k + 1) - 3 = (3 + k - 3) + 1 by omega, pow_succ]
        rw [show 3 + (k + 1) = 3 + k + 1 by omega]
        ring
      have hrewM :
          (239 : ℤ) ^ (3 + k - 3) * (1393 * (p : ℤ) * padeSeqB (3 + k) p) =
            1393 * (p : ℤ) * ((239 : ℤ) ^ (3 + k - 3) * padeSeqB (3 + k) p) := by
        ring
      have hrewR :
          1393 * (p : ℤ) * (239 * 1393 ^ (3 + k - 3) * (p : ℤ) ^ (3 + k)) =
            239 * 1393 ^ (3 + (k + 1) - 3) * (p : ℤ) ^ (3 + (k + 1)) := by
        rw [show 3 + (k + 1) - 3 = (3 + k - 3) + 1 by omega, pow_succ]
        rw [show 3 + (k + 1) = (3 + k) + 1 by omega, pow_succ]
        ring
      linarith

/-- Bundled `1393 / 239` third-order sharpened Pell–Padé contraction for `3 ≤ p` and `3 ≤ u`. -/
theorem padeSeq_sharpened_1393_239_contraction {p u : ℕ} (hp3 : 3 ≤ p) (hu : 3 ≤ u) :
    (239 * padeSeqA u p ≤ 169 * padeSeqB u p) ∧
    (239 * padeSeqB (u + 1) p < 1393 * (p : ℤ) * padeSeqB u p) ∧
    (239 ^ (u - 3) * padeSeqB u p < 239 * 1393 ^ (u - 3) * (p : ℤ) ^ u) :=
  ⟨two_hundred_thirty_nine_mul_padeSeqA_le_169_mul_padeSeqB hp3 hu,
   two_hundred_thirty_nine_mul_padeSeqB_succ_lt_1393_mul hp3 hu,
   two_hundred_thirty_nine_pow_mul_padeSeqB_lt_1393_pow hp3 hu⟩

private lemma ten_pow_12_mul_239_mul_1393_pow_lt_239_pow_mul_6_pow {u : ℕ} (hu : 1154 ≤ u) :
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

/-- On any even prime-power component equation `sigma 1 (p ^ (2 * u)) = q`,
`q + 1 = 2 * s ^ 2`, `sigma 1 (s ^ 2) = p ^ (2 * u)`, the `1393 / 239` contraction coupled with
`1154 ≤ u` yields `239 ^ (u - 3) * p < 239 * 1393 ^ (u - 3)`, `10 ^ 12 * p < 6 ^ u`,
`2 * 10 ^ 12 * p < 6 ^ u` when `p % 4 = 3 ∨ Even u`, and `10 ^ 12 * p ^ 2 < 6 ^ u` when
`p ∣ 64 ^ u - 1`. -/
theorem even_index_prime_ten_pow_twelve_cap {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    1154 ≤ u ∧
    239 ^ (u - 3) * p < 239 * 1393 ^ (u - 3) ∧
    10 ^ 12 * p < 6 ^ u ∧
    (p % 4 = 3 ∨ Even u → 2 * 10 ^ 12 * p < 6 ^ u) ∧
    (p ∣ 64 ^ u - 1 → 10 ^ 12 * p ^ 2 < 6 ^ u) := by
  obtain ⟨hu1154, _, _⟩ :=
    even_index_exponent_ge_2308_and_base_ge_12207031 hp hpo hs hu hσq hplus hσs
  have hp3 : 3 ≤ p := odd_prime_ge_three_1393 hp hpo
  have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
  have hu3 : 3 ≤ u := by omega
  have hB_bound : (239 : ℤ) ^ (u - 3) * padeSeqB u p < 239 * 1393 ^ (u - 3) * (p : ℤ) ^ u :=
    two_hundred_thirty_nine_pow_mul_padeSeqB_lt_1393_pow hp3 hu3
  have h239_posZ : (0 : ℤ) < (239 : ℤ) ^ (u - 3) := by positivity
  have hpu_posZ : (0 : ℤ) < (p : ℤ) ^ u := by positivity
  have h239_posN : 0 < 239 ^ (u - 3) := by positivity
  have hnum : 10 ^ 12 * (239 * 1393 ^ (u - 3)) < 239 ^ (u - 3) * 6 ^ u :=
    ten_pow_12_mul_239_mul_1393_pow_lt_239_pow_mul_6_pow hu1154
  obtain ⟨_, _, _, hB2_gt, _⟩ :=
    even_index_pade_quotient_pos_and_quadratic_identity hp hpo hs hu hσq hplus hσs
  obtain ⟨_, hB_ge⟩ := padeSeq_one_le hp3 u
  have hpu1_lt_B : (p : ℤ) ^ (u + 1) < padeSeqB u p := by
    have hpow_pos : (0 : ℤ) < (p : ℤ) ^ (2 * u + 1) := by positivity
    have h2p1_gt : (p : ℤ) < 2 * ((p : ℤ) - 1) := by linarith
    have hsq_eq : ((p : ℤ) ^ (u + 1)) ^ 2 = (p : ℤ) * (p : ℤ) ^ (2 * u + 1) := by
      rw [← pow_mul, ← pow_succ']
      congr 1
      omega
    have hsq_lt : ((p : ℤ) ^ (u + 1)) ^ 2 < padeSeqB u p ^ 2 := by
      have hmul : (p : ℤ) * (p : ℤ) ^ (2 * u + 1) < 2 * ((p : ℤ) - 1) * (p : ℤ) ^ (2 * u + 1) :=
        mul_lt_mul_of_pos_right h2p1_gt hpow_pos
      linarith
    by_contra! hle
    have hsq_le : padeSeqB u p ^ 2 ≤ ((p : ℤ) ^ (u + 1)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hle 2
    linarith
  have h239_p : 239 ^ (u - 3) * p < 239 * 1393 ^ (u - 3) := by
    have hchain :
        (239 : ℤ) ^ (u - 3) * (p : ℤ) * (p : ℤ) ^ u <
          239 * 1393 ^ (u - 3) * (p : ℤ) ^ u := by
      calc
        (239 : ℤ) ^ (u - 3) * (p : ℤ) * (p : ℤ) ^ u
            = (239 : ℤ) ^ (u - 3) * (p : ℤ) ^ (u + 1) := by rw [pow_succ']; ring
        _ < (239 : ℤ) ^ (u - 3) * padeSeqB u p := mul_lt_mul_of_pos_left hpu1_lt_B h239_posZ
        _ < 239 * 1393 ^ (u - 3) * (p : ℤ) ^ u := hB_bound
    have hltZ : (239 : ℤ) ^ (u - 3) * (p : ℤ) < 239 * 1393 ^ (u - 3) :=
      lt_of_mul_lt_mul_right hchain hpu_posZ.le
    exact_mod_cast hltZ
  have h10_p : 10 ^ 12 * p < 6 ^ u := by
    have hmul : 239 ^ (u - 3) * (10 ^ 12 * p) < 239 ^ (u - 3) * 6 ^ u := by
      calc
        239 ^ (u - 3) * (10 ^ 12 * p) = 10 ^ 12 * (239 ^ (u - 3) * p) := by ring
        _ < 10 ^ 12 * (239 * 1393 ^ (u - 3)) := Nat.mul_lt_mul_of_pos_left h239_p (by positivity)
        _ < 239 ^ (u - 3) * 6 ^ u := hnum
    exact Nat.lt_of_mul_lt_mul_left hmul
  have h2_10_p : p % 4 = 3 ∨ Even u → 2 * 10 ^ 12 * p < 6 ^ u := by
    intro hcond
    have h2pu1_lt_B : 2 * (p : ℤ) ^ (u + 1) < padeSeqB u p :=
      ((even_index_pade_quotient_parity_and_doubled_cap hp hpo hs hu hσq hplus hσs).2.2
        hcond).2.2.1
    have hchain :
        (2 * (239 : ℤ) ^ (u - 3) * (p : ℤ)) * (p : ℤ) ^ u <
          239 * 1393 ^ (u - 3) * (p : ℤ) ^ u := by
      calc
        (2 * (239 : ℤ) ^ (u - 3) * (p : ℤ)) * (p : ℤ) ^ u
            = (239 : ℤ) ^ (u - 3) * (2 * (p : ℤ) ^ (u + 1)) := by rw [pow_succ']; ring
        _ < (239 : ℤ) ^ (u - 3) * padeSeqB u p := mul_lt_mul_of_pos_left h2pu1_lt_B h239_posZ
        _ < 239 * 1393 ^ (u - 3) * (p : ℤ) ^ u := hB_bound
    have h2_239 : 2 * 239 ^ (u - 3) * p < 239 * 1393 ^ (u - 3) := by
      exact_mod_cast lt_of_mul_lt_mul_right hchain hpu_posZ.le
    have hmul : 239 ^ (u - 3) * (2 * 10 ^ 12 * p) < 239 ^ (u - 3) * 6 ^ u := by
      calc
        239 ^ (u - 3) * (2 * 10 ^ 12 * p) = 10 ^ 12 * (2 * 239 ^ (u - 3) * p) := by ring
        _ < 10 ^ 12 * (239 * 1393 ^ (u - 3)) := Nat.mul_lt_mul_of_pos_left h2_239 (by positivity)
        _ < 239 ^ (u - 3) * 6 ^ u := hnum
    exact Nat.lt_of_mul_lt_mul_left hmul
  have h10_p2 : p ∣ 64 ^ u - 1 → 10 ^ 12 * p ^ 2 < 6 ^ u := by
    intro h64
    have hpu2_lt_B : (p : ℤ) ^ (u + 2) < padeSeqB u p :=
      ((even_index_pade_quotient_mod_p_and_sub_two hp hpo hs hu hσq hplus hσs).2.1 h64).2.2.1
    have hchain :
        ((239 : ℤ) ^ (u - 3) * (p : ℤ) ^ 2) * (p : ℤ) ^ u <
          239 * 1393 ^ (u - 3) * (p : ℤ) ^ u := by
      calc
        ((239 : ℤ) ^ (u - 3) * (p : ℤ) ^ 2) * (p : ℤ) ^ u
            = (239 : ℤ) ^ (u - 3) * (p : ℤ) ^ (u + 2) := by
                rw [mul_assoc, ← pow_add, show 2 + u = u + 2 by omega]
        _ < (239 : ℤ) ^ (u - 3) * padeSeqB u p := mul_lt_mul_of_pos_left hpu2_lt_B h239_posZ
        _ < 239 * 1393 ^ (u - 3) * (p : ℤ) ^ u := hB_bound
    have h239_p2 : 239 ^ (u - 3) * p ^ 2 < 239 * 1393 ^ (u - 3) := by
      exact_mod_cast lt_of_mul_lt_mul_right hchain hpu_posZ.le
    have hmul : 239 ^ (u - 3) * (10 ^ 12 * p ^ 2) < 239 ^ (u - 3) * 6 ^ u := by
      calc
        239 ^ (u - 3) * (10 ^ 12 * p ^ 2) = 10 ^ 12 * (239 ^ (u - 3) * p ^ 2) := by ring
        _ < 10 ^ 12 * (239 * 1393 ^ (u - 3)) :=
            Nat.mul_lt_mul_of_pos_left h239_p2 (by positivity)
        _ < 239 ^ (u - 3) * 6 ^ u := hnum
    exact Nat.lt_of_mul_lt_mul_left hmul
  exact ⟨hu1154, h239_p, h10_p, h2_10_p, h10_p2⟩

/-- Global odd-perfect-number lift combining `even_index_prime_ten_pow_twelve_cap` (`10 ^ 12 * p < 6 ^ u`)
with `even_prime_power_component_forces_small_repunit_base` (`r ∈ {3, 5, 7, 11, 13}`,
`geometricBlock r l = p`), forcing `10 ^ 12 * r ^ (l - 1) < 6 ^ u` and `l + 15 ≤ u` whenever
`r ∈ {7, 11, 13}`. -/
theorem even_prime_power_primorial_repunit_length_cap
    {N q a b i p u : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b) (hl : sigma 1 b = q ^ a * i)
    (hr : sigma 1 (q ^ a) * i = 2 * b) (hp : p.Prime) (hu : 0 < u) (hi : i = p ^ (2 * u)) :
    (1154 ≤ u ∧ 10 ^ 12 * p < 6 ^ u ∧
      (p % 4 = 3 ∨ Even u → 2 * 10 ^ 12 * p < 6 ^ u) ∧
      (p ∣ 64 ^ u - 1 → 10 ^ 12 * p ^ 2 < 6 ^ u)) ∧
    (∃ r ∈ ({3, 5, 7, 11, 13} : Finset ℕ),
      r ^ 2 ∣ N ∧
      ∃ l : ℕ, l.Prime ∧ 2 < l ∧ geometricBlock r l = p ∧
        10 ^ 12 * r ^ (l - 1) < 6 ^ u ∧
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
  obtain ⟨hu1154, _, h10_p, h2_10_p, h10_p2⟩ :=
    even_index_prime_ten_pow_twelve_cap hp hpo hs hu hσq hplus hσs
  obtain ⟨⟨r, hr_mem, hr2_N, l, hl_prime, hl_gt2, hgb⟩, _⟩ :=
    even_prime_power_component_forces_small_repunit_base hN ho hq ha hform hqb hl hr hp hu hi
  have hpow_lt_p : r ^ (l - 1) < p := by
    have h0_mem : 0 ∈ Finset.range (l - 1) := Finset.mem_range.mpr (by omega)
    have h1_le : 1 ≤ ∑ j ∈ Finset.range (l - 1), r ^ j := by
      have hle := Finset.single_le_sum (f := fun j => r ^ j) (fun _ _ => Nat.zero_le _) h0_mem
      simpa using hle
    have hsum : geometricBlock r l = (∑ j ∈ Finset.range (l - 1), r ^ j) + r ^ (l - 1) := by
      dsimp [geometricBlock]
      conv_lhs => rw [show l = (l - 1) + 1 by omega, Finset.sum_range_succ]
    omega
  have h10_r : 10 ^ 12 * r ^ (l - 1) < 6 ^ u := by
    calc
      10 ^ 12 * r ^ (l - 1) < 10 ^ 12 * p := Nat.mul_lt_mul_of_pos_left hpow_lt_p (by positivity)
      _ < 6 ^ u := h10_p
  have hl_cap : r ∈ ({7, 11, 13} : Finset ℕ) → l + 15 ≤ u := by
    intro hr7
    have hr6 : 6 ≤ r := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr7
      rcases hr7 with rfl | rfl | rfl <;> decide
    have h6_15 : 6 ^ 15 < 10 ^ 12 := by norm_num
    have h6_pow : 6 ^ (l - 1 + 15) < 6 ^ u := by
      calc
        6 ^ (l - 1 + 15) = 6 ^ 15 * 6 ^ (l - 1) := by rw [add_comm, pow_add]
        _ < 10 ^ 12 * 6 ^ (l - 1) := Nat.mul_lt_mul_of_pos_right h6_15 (by positivity)
        _ ≤ 10 ^ 12 * r ^ (l - 1) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hr6 (l - 1))
        _ < 6 ^ u := h10_r
    have hlt_exp : l - 1 + 15 < u := (Nat.pow_lt_pow_iff_right (by decide : 1 < 6)).mp h6_pow
    omega
  exact ⟨⟨hu1154, h10_p, h2_10_p, h10_p2⟩,
    ⟨r, hr_mem, hr2_N, l, hl_prime, hl_gt2, hgb, h10_r, hl_cap⟩⟩

end OddPerfect
