module

public import OddPerfect.PadicThirdOrderObstruction
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# p-adic Runge & Sub-Two Obstructions (`OddPerfect.PadicRungeSubTwoObstruction`)

Develops four structural obstructions for the even-index prime-power component equation
`2 * (p - 1) * s ^ 2 = (p - 2) + p ^ (2 * u + 1)`:
1. The Archimedean sandwich (`p ^ (2 * u) < 2 * s ^ 2 < 2 * p ^ (2 * u)`) and mod-`(p - 2)`
   congruence `s ^ 2 ≡ 4 ^ u [MOD p - 2]`.
2. Purely algebraic exclusion of small exponents `u ∈ {1, 2, 3, 4}`, giving `5 ≤ u` and
   `11 ≤ 2 * u + 1`.
3. Explicit integer power series coefficients `henselScaledCoeff` of
   `g(8y) = (1 - 8y)^(-1/2) * (1 - 4y)^(1/2)` and the polynomial congruence
   `henselScaledPoly_sq_mod_pow`.
4. The unconditional exponential base cap `even_index_prime_lt_eight_pow_u` (`p < 8 ^ u`).
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma odd_prime_ge_three {p : ℕ} (hp : p.Prime) (hpo : Odd p) : 3 ≤ p := by
  have h2 : 2 ≤ p := hp.two_le
  rcases eq_or_lt_of_le h2 with rfl | hlt
  · exact absurd hpo (by decide)
  · exact hlt

/-! ### 1. Archimedean Sandwich & Mod-`(p - 2)` Congruence -/

/-- Archimedean sandwich for the even-index cofactor `s` relative to `p ^ u`. -/
theorem even_index_cofactor_archimedean_sandwich {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2) :
    p ^ (2 * u) < 2 * s ^ 2 ∧ 2 * s ^ 2 < 2 * p ^ (2 * u) ∧ s < p ^ u ∧ p ^ u < 2 * s := by
  have hp3 : 3 ≤ p := odd_prime_ge_three hp hpo
  have hq_ge : p ^ (2 * u) ≤ q := by
    rw [← hσq, sigma_one_apply_prime_pow hp]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_self (2 * u)))
  have hlower : p ^ (2 * u) < 2 * s ^ 2 := by omega
  have hs_nat := even_index_twice_pred_mul_cofactor_sq hp hσq hplus
  have hpow_gt1 : 1 < p ^ (2 * u) := by
    have h9 : 9 ≤ p ^ (2 * u) := calc
      9 = 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
      _ ≤ p ^ (2 * u) := Nat.pow_le_pow_right hp.pos (by omega)
    omega
  have hp2_lt : p - 2 < (p - 2) * p ^ (2 * u) :=
    lt_mul_of_one_lt_right (by omega) hpow_gt1
  have hmul_lt : 2 * (p - 1) * s ^ 2 < 2 * (p - 1) * p ^ (2 * u) := by
    calc
      2 * (p - 1) * s ^ 2 = (p - 2) + p ^ (2 * u + 1) := hs_nat
      _ = (p - 2) + p * p ^ (2 * u) := by rw [pow_succ']
      _ < (p - 2) * p ^ (2 * u) + p * p ^ (2 * u) := by omega
      _ = ((p - 2) + p) * p ^ (2 * u) := by ring
      _ = 2 * (p - 1) * p ^ (2 * u) := by
        congr 1
        omega
  have hs2_lt : s ^ 2 < p ^ (2 * u) :=
    Nat.lt_of_mul_lt_mul_left hmul_lt
  have hupper : 2 * s ^ 2 < 2 * p ^ (2 * u) := by omega
  have hsu : s < p ^ u := by
    have hpow_eq : (p ^ u) ^ 2 = p ^ (2 * u) := by
      rw [← pow_mul, mul_comm u 2]
    exact (Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mp (hpow_eq ▸ hs2_lt)
  have hus : p ^ u < 2 * s := by
    have hsq : (p ^ u) ^ 2 < (2 * s) ^ 2 := by
      calc
        (p ^ u) ^ 2 = p ^ (2 * u) := by rw [← pow_mul, mul_comm]
        _ < 2 * s ^ 2 := hlower
        _ ≤ 4 * s ^ 2 := by omega
        _ = (2 * s) ^ 2 := by ring
    exact (Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mp hsq
  exact ⟨hlower, hupper, hsu, hus⟩

/-- Mod-`(p - 2)` quadratic congruence `s ^ 2 ≡ 4 ^ u [MOD p - 2]` and integer divisibility
`(p - 2) ∣ (s - 2 ^ u) * (s + 2 ^ u)`. -/
theorem even_index_mod_sub_two_congruence {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2) :
    s ^ 2 ≡ 4 ^ u [MOD p - 2] ∧
    ((p : ℤ) - 2) ∣ ((s : ℤ) - 2 ^ u) * ((s : ℤ) + 2 ^ u) := by
  have hp3 : 3 ≤ p := odd_prime_ge_three hp hpo
  have hs_nat := even_index_twice_pred_mul_cofactor_sq hp hσq hplus
  have hs_int : 2 * ((p : ℤ) - 1) * (s : ℤ) ^ 2 = ((p : ℤ) - 2) + (p : ℤ) ^ (2 * u + 1) := by
    have hcast := congrArg (Nat.cast (R := ℤ)) hs_nat
    push_cast at hcast
    rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_sub (by omega : 2 ≤ p)] at hcast
    push_cast at hcast
    exact hcast
  have hdvd_pow : ((p : ℤ) - 2) ∣ (p : ℤ) ^ (2 * u + 1) - (2 : ℤ) ^ (2 * u + 1) :=
    sub_dvd_pow_sub_pow (p : ℤ) 2 (2 * u + 1)
  have hdvd_two_sq : ((p : ℤ) - 2) ∣ 2 * ((s : ℤ) ^ 2 - ((2 : ℤ) ^ u) ^ 2) := by
    have hid : 2 * ((s : ℤ) ^ 2 - ((2 : ℤ) ^ u) ^ 2) =
        ((p : ℤ) ^ (2 * u + 1) - (2 : ℤ) ^ (2 * u + 1)) +
        ((p : ℤ) - 2) * (1 - 2 * (s : ℤ) ^ 2) := by
      have h2pow : (2 : ℤ) ^ (2 * u + 1) = 2 * ((2 : ℤ) ^ u) ^ 2 := by
        rw [pow_succ', ← pow_mul, mul_comm u 2]
      linarith [hs_int, h2pow]
    rw [hid]
    exact dvd_add hdvd_pow (dvd_mul_right _ _)
  have hodd_sub2 : Odd (p - 2) := by
    rcases hpo with ⟨k, hk⟩
    refine ⟨k - 1, ?_⟩
    omega
  have hcop_nat : Nat.Coprime (p - 2) 2 := hodd_sub2.coprime_two_right
  have hcop_int : IsCoprime ((p : ℤ) - 2) 2 := by
    have hc : IsCoprime (((p - 2 : ℕ) : ℤ)) ((2 : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr hcop_nat
    rw [Nat.cast_sub (by omega : 2 ≤ p)] at hc
    simpa using hc
  have hdvd_sq : ((p : ℤ) - 2) ∣ (s : ℤ) ^ 2 - ((2 : ℤ) ^ u) ^ 2 :=
    hcop_int.dvd_of_dvd_mul_left hdvd_two_sq
  have hdvd_fac : ((p : ℤ) - 2) ∣ ((s : ℤ) - 2 ^ u) * ((s : ℤ) + 2 ^ u) := by
    have hfac : ((s : ℤ) - 2 ^ u) * ((s : ℤ) + 2 ^ u) = (s : ℤ) ^ 2 - ((2 : ℤ) ^ u) ^ 2 := by ring
    rwa [hfac]
  have hmod : s ^ 2 ≡ 4 ^ u [MOD p - 2] := by
    rw [← Int.natCast_modEq_iff, Int.modEq_iff_dvd]
    have hcast : ((s ^ 2 : ℕ) : ℤ) = (s : ℤ) ^ 2 := by push_cast; rfl
    have h4 : ((4 ^ u : ℕ) : ℤ) = ((2 : ℤ) ^ u) ^ 2 := by
      push_cast
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
    have hpm2 : (((p - 2 : ℕ) : ℤ)) = (p : ℤ) - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ p), Nat.cast_ofNat]
    rw [hpm2, hcast, h4]
    simpa [dvd_neg] using dvd_neg.mpr hdvd_sq
  exact ⟨hmod, hdvd_fac⟩

/-! ### 2. Purely Algebraic Exclusion of `u ∈ {1, 2, 3, 4}` -/

private lemma cofactor_mod_p_cube_and_fourth_of_two_le {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u) (hu2 : 2 ≤ u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    32 * s ≡ 32 + 8 * p + 7 * p ^ 2 [MOD p ^ 3] ∧
    128 * s ≡ 128 + 32 * p + 28 * p ^ 2 + 25 * p ^ 3 [MOD p ^ 4] := by
  have h4_le : 4 ≤ 2 * u + 1 := by omega
  have hs_nat := even_index_twice_pred_mul_cofactor_sq hp hσq hplus
  have hp3 : 3 ≤ p := odd_prime_ge_three hp hpo
  have hs_int : 2 * ((p : ℤ) - 1) * (s : ℤ) ^ 2 = ((p : ℤ) - 2) + (p : ℤ) ^ (2 * u + 1) := by
    have hcast := congrArg (Nat.cast (R := ℤ)) hs_nat
    push_cast at hcast
    rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_sub (by omega : 2 ≤ p)] at hcast
    push_cast at hcast
    exact hcast
  let A : ℤ := 128 * (s : ℤ)
  let B : ℤ := 128 + 32 * (p : ℤ) + 28 * (p : ℤ) ^ 2 + 25 * (p : ℤ) ^ 3
  have hp4_dvd_A : (p : ℤ) ^ 4 ∣ 2 * ((p : ℤ) - 1) * A ^ 2 - 16384 * ((p : ℤ) - 2) := by
    have hid : 2 * ((p : ℤ) - 1) * A ^ 2 - 16384 * ((p : ℤ) - 2) = 16384 * (p : ℤ) ^ (2 * u + 1) := by
      dsimp [A]
      calc
        2 * ((p : ℤ) - 1) * (128 * (s : ℤ)) ^ 2 - 16384 * ((p : ℤ) - 2)
            = 16384 * (2 * ((p : ℤ) - 1) * (s : ℤ) ^ 2 - ((p : ℤ) - 2)) := by ring
        _ = 16384 * (p : ℤ) ^ (2 * u + 1) := by rw [hs_int]; ring
    rw [hid]
    exact dvd_mul_of_dvd_right (pow_dvd_pow (p : ℤ) h4_le) 16384
  have hp4_dvd_B : (p : ℤ) ^ 4 ∣ 2 * ((p : ℤ) - 1) * B ^ 2 - 16384 * ((p : ℤ) - 2) := by
    have hid : 2 * ((p : ℤ) - 1) * B ^ 2 - 16384 * ((p : ℤ) - 2) =
        (p : ℤ) ^ 4 * (1250 * (p : ℤ) ^ 3 + 1550 * (p : ℤ) ^ 2 + 1968 * (p : ℤ) + 11616) := by
      dsimp [B]
      ring
    rw [hid]
    exact dvd_mul_right _ _
  have hp4_dvd_prod : (p : ℤ) ^ 4 ∣ 2 * ((p : ℤ) - 1) * (A + B) * (A - B) := by
    have hdiff := dvd_sub hp4_dvd_A hp4_dvd_B
    have hfac : (2 * ((p : ℤ) - 1) * A ^ 2 - 16384 * ((p : ℤ) - 2)) -
        (2 * ((p : ℤ) - 1) * B ^ 2 - 16384 * ((p : ℤ) - 2)) =
        2 * ((p : ℤ) - 1) * (A + B) * (A - B) := by ring
    rwa [hfac] at hdiff
  have hpdvd : p ∣ s - 1 :=
    (even_index_exact_p_dvd_cofactor_pred hp hpo hs.pos hu hσq hplus hσs).1
  have hp_dvd_s1 : (p : ℤ) ∣ (s : ℤ) - 1 := by
    have h1 : 1 ≤ s := hs.pos
    have : ((s - 1 : ℕ) : ℤ) = (s : ℤ) - 1 := by rw [Nat.cast_sub h1, Nat.cast_one]
    rw [← this]
    exact Int.natCast_dvd_natCast.mpr hpdvd
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
  have hnot_dvd_AB : ¬ (p : ℤ) ∣ A + B := by
    intro hdiv
    have hsum_id : A + B = 256 + 128 * ((s : ℤ) - 1) +
        (p : ℤ) * (32 + 28 * (p : ℤ) + 25 * (p : ℤ) ^ 2) := by
      dsimp [A, B]
      ring
    rw [hsum_id] at hdiv
    have hd256 : (p : ℤ) ∣ 256 := by
      have hd_tail : (p : ℤ) ∣ 128 * ((s : ℤ) - 1) +
          (p : ℤ) * (32 + 28 * (p : ℤ) + 25 * (p : ℤ) ^ 2) :=
        dvd_add (dvd_mul_of_dvd_right hp_dvd_s1 128) (dvd_mul_right _ _)
      have := dvd_sub hdiv hd_tail
      simpa using this
    have hd256nat : p ∣ 2 ^ 8 := by
      have := Int.natCast_dvd_natCast.mp hd256
      simpa using this
    have hd2 : p ∣ 2 := hp.dvd_of_dvd_pow hd256nat
    have h2 : p = 2 := (Nat.dvd_prime Nat.prime_two).mp hd2 |>.resolve_left hp.ne_one
    subst h2
    exact absurd hpo (by decide)
  have hnot_dvd_coeff : ¬ (p : ℤ) ∣ 2 * ((p : ℤ) - 1) * (A + B) := by
    intro hdiv
    rcases hpZ.dvd_or_dvd hdiv with h2p1 | hAB
    · exact hnot_dvd_2p1 h2p1
    · exact hnot_dvd_AB hAB
  have hcop : IsCoprime ((p : ℤ) ^ 4) (2 * ((p : ℤ) - 1) * (A + B)) :=
    (hpZ.coprime_iff_not_dvd.mpr hnot_dvd_coeff).pow_left
  have hp4_dvd_sub : (p : ℤ) ^ 4 ∣ A - B := hcop.dvd_of_dvd_mul_left hp4_dvd_prod
  have hmod4 : 128 * s ≡ 128 + 32 * p + 28 * p ^ 2 + 25 * p ^ 3 [MOD p ^ 4] := by
    rw [← Int.natCast_modEq_iff, Int.modEq_iff_dvd]
    have hp4_dvd_rev : (p : ℤ) ^ 4 ∣ B - A := by
      rw [show B - A = -(A - B) by ring]
      exact dvd_neg.mpr hp4_dvd_sub
    simpa [A, B, Nat.cast_pow] using hp4_dvd_rev
  have hp3_dvd_sub : (p : ℤ) ^ 3 ∣ A - B :=
    (pow_dvd_pow (p : ℤ) (by decide : 3 ≤ 4)).trans hp4_dvd_sub
  have hp3_dvd_mul4 : (p : ℤ) ^ 3 ∣
      4 * (((32 + 8 * p + 7 * p ^ 2 : ℕ) : ℤ) - ((32 * s : ℕ) : ℤ)) := by
    have hid : 4 * (((32 + 8 * p + 7 * p ^ 2 : ℕ) : ℤ) - ((32 * s : ℕ) : ℤ)) =
        -(A - B) - 25 * (p : ℤ) ^ 3 := by
      dsimp [A, B]
      ring
    rw [hid]
    exact dvd_sub (dvd_neg.mpr hp3_dvd_sub) (dvd_mul_left _ _)
  have hnot_dvd_4 : ¬ (p : ℤ) ∣ 4 := by
    intro h4
    have h4nat : p ∣ 2 ^ 2 := by simpa using Int.natCast_dvd_natCast.mp h4
    have hd2 : p ∣ 2 := hp.dvd_of_dvd_pow h4nat
    have h2 : p = 2 := (Nat.dvd_prime Nat.prime_two).mp hd2 |>.resolve_left hp.ne_one
    subst h2
    exact absurd hpo (by decide)
  have hcop4 : IsCoprime ((p : ℤ) ^ 3) 4 := (hpZ.coprime_iff_not_dvd.mpr hnot_dvd_4).pow_left
  have hmod3 : 32 * s ≡ 32 + 8 * p + 7 * p ^ 2 [MOD p ^ 3] := by
    rw [← Int.natCast_modEq_iff, Int.modEq_iff_dvd]
    simpa [Nat.cast_pow] using hcop4.dvd_of_dvd_mul_left hp3_dvd_mul4
  exact ⟨hmod3, hmod4⟩

private def binSqrt (n lo hi : ℕ) : ℕ → Bool
  | 0 => false
  | fuel + 1 =>
    if hi < lo then false
    else
      let mid := (lo + hi) / 2
      let sq := mid * mid
      if sq == n then true
      else if sq < n then binSqrt n (mid + 1) hi fuel
      else if mid == 0 then false
      else binSqrt n lo (mid - 1) fuel

private lemma binSqrt_sound (n s : ℕ) (hs : s * s = n) :
    ∀ fuel lo hi : ℕ, lo ≤ s → s ≤ hi → hi + 1 - lo < 2 ^ fuel →
      binSqrt n lo hi fuel = true
  | 0, lo, hi, hlo, hhi, hbound => by
    exfalso
    simp only [pow_zero] at hbound
    omega
  | fuel + 1, lo, hi, hlo, hhi, hbound => by
    rw [binSqrt]
    have hnot_lt : ¬ hi < lo := by omega
    rw [ite_eq_right_iff.mpr (fun h => absurd h hnot_lt)]
    set mid := (lo + hi) / 2
    by_cases heq : mid * mid = n
    · simp [heq]
    · rw [ite_eq_right_iff.mpr (by simp [heq])]
      by_cases hlt : mid * mid < n
      · rw [ite_eq_left_iff.mpr (fun h => absurd hlt h)]
        have hmid_lt_s : mid < s := by nlinarith
        apply binSqrt_sound n s hs fuel (mid + 1) hi (by omega) hhi
        have : hi + 1 - (mid + 1) ≤ (hi + 1 - lo) / 2 := by omega
        have hpow : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by rw [pow_succ']
        omega
      · rw [ite_eq_right_iff.mpr (fun h => absurd h hlt)]
        have hgt : n < mid * mid := by omega
        have hs_lt_mid : s < mid := by nlinarith
        have hmid_ne0 : ¬ (mid == 0) = true := by
          simp only [beq_iff_eq]
          omega
        rw [ite_eq_right_iff.mpr (fun h => absurd h hmid_ne0)]
        apply binSqrt_sound n s hs fuel lo (mid - 1) hlo (by omega)
        have : (mid - 1) + 1 - lo ≤ (hi + 1 - lo) / 2 := by omega
        have hpow : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by rw [pow_succ']
        omega

private def checkSmallU2 : Bool :=
  (List.range 37).any fun p =>
    2 < p && p % 2 == 1 && binSqrt ((2 + p + p ^ 2 + p ^ 3 + p ^ 4) / 2) 0 (p ^ 2) 12

private def checkSmallU3 : Bool :=
  (List.range 131).any fun p =>
    2 < p && p % 2 == 1 &&
      binSqrt ((2 + p + p ^ 2 + p ^ 3 + p ^ 4 + p ^ 5 + p ^ 6) / 2) 0 (p ^ 3) 23

private lemma checkSmallU2_false : checkSmallU2 = false := by decide
private lemma checkSmallU3_false : checkSmallU3 = false := by decide

/-- Purely algebraic exclusion of small exponents `u ∈ {1, 2, 3, 4}` at any even
prime-power component index. -/
theorem even_index_small_u_exclusion {q p s u : ℕ}
    (hq : q.Prime) (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    5 ≤ u ∧ 11 ≤ 2 * u + 1 := by
  have hp3 : 3 ≤ p := odd_prime_ge_three hp hpo
  have hs_ge2 : 2 ≤ s := by
    have hq2 : 2 ≤ q := hq.two_le
    by_contra! hs1
    have hs_le1 : s ≤ 1 := by omega
    have : s ^ 2 ≤ 1 := Nat.pow_le_pow_left hs_le1 2
    omega
  have h_ne1 : u ≠ 1 := by
    intro hu1
    subst hu1
    have hsu := (even_index_cofactor_archimedean_sandwich hp hpo hu hσq hplus).2.2.1
    rw [pow_one] at hsu
    have hpdvd : p ∣ s - 1 :=
      (even_index_exact_p_dvd_cofactor_pred hp hpo hs.pos hu hσq hplus hσs).1
    have hle : p ≤ s - 1 := Nat.le_of_dvd (by omega) hpdvd
    omega
  have h_ne2 : u ≠ 2 := by
    intro hu2
    subst hu2
    have hsand := even_index_cofactor_archimedean_sandwich hp hpo hu hσq hplus
    have hsu : s < p ^ 2 := hsand.2.2.1
    have hus : p ^ 2 < 2 * s := hsand.2.2.2
    have hmod3 :=
      (cofactor_mod_p_cube_and_fourth_of_two_le hp hpo hs hu (by decide) hσq hplus hσs).1
    by_cases hp37 : 37 ≤ p
    · have hl_lt : 32 * s < p ^ 3 := by
        calc
          32 * s < 32 * p ^ 2 := by omega
          _ < p * p ^ 2 := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
          _ = p ^ 3 := by ring
      have hr_lt_8p2 : 32 + 8 * p + 7 * p ^ 2 < 8 * p ^ 2 := by
        have hpp : 32 + 8 * p < p ^ 2 := by nlinarith
        omega
      have hr_lt : 32 + 8 * p + 7 * p ^ 2 < p ^ 3 := by
        calc
          32 + 8 * p + 7 * p ^ 2 < 8 * p ^ 2 := hr_lt_8p2
          _ < p * p ^ 2 := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
          _ = p ^ 3 := by ring
      have heq : 32 * s = 32 + 8 * p + 7 * p ^ 2 := by
        have hm := hmod3
        rw [Nat.ModEq, Nat.mod_eq_of_lt hl_lt, Nat.mod_eq_of_lt hr_lt] at hm
        exact hm
      omega
    · have hp_lt : p < 37 := by omega
      have hq_val : q = 1 + p + p ^ 2 + p ^ 3 + p ^ 4 := by
        rw [← hσq, sigma_one_apply_prime_pow hp]
        simp [Finset.sum_range_succ]
      have hsq_eq : s * s = (2 + p + p ^ 2 + p ^ 3 + p ^ 4) / 2 := by
        have h2s2 : 2 * s ^ 2 = 2 + p + p ^ 2 + p ^ 3 + p ^ 4 := by omega
        rw [← sq]
        omega
      have hbound : p ^ 2 + 1 - 0 < 2 ^ 12 := by
        have : p ^ 2 < 37 ^ 2 := Nat.pow_lt_pow_left hp_lt (by decide)
        omega
      have hsqrt_true : binSqrt ((2 + p + p ^ 2 + p ^ 3 + p ^ 4) / 2) 0 (p ^ 2) 12 = true :=
        binSqrt_sound _ s hsq_eq 12 0 (p ^ 2) (Nat.zero_le s) hsu.le hbound
      have htrue : checkSmallU2 = true := by
        rw [checkSmallU2, List.any_eq_true]
        refine ⟨p, List.mem_range.mpr hp_lt, ?_⟩
        have hp2 : 2 < p := by omega
        have hmod2 : p % 2 = 1 := Nat.odd_iff.mp hpo
        simp [hp2, hmod2, hsqrt_true]
      rw [checkSmallU2_false] at htrue
      exact Bool.noConfusion htrue
  have h_ne3 : u ≠ 3 := by
    intro hu3
    subst hu3
    have hsand := even_index_cofactor_archimedean_sandwich hp hpo hu hσq hplus
    have hsu : s < p ^ 3 := hsand.2.2.1
    have hus : p ^ 3 < 2 * s := hsand.2.2.2
    have hmod4 :=
      (cofactor_mod_p_cube_and_fourth_of_two_le hp hpo hs hu (by decide) hσq hplus hσs).2
    by_cases hp131 : 131 ≤ p
    · have hl_lt : 128 * s < p ^ 4 := by
        calc
          128 * s < 128 * p ^ 3 := by omega
          _ < p * p ^ 3 := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
          _ = p ^ 4 := by ring
      have hr_lt_26p3 : 128 + 32 * p + 28 * p ^ 2 + 25 * p ^ 3 < 26 * p ^ 3 := by
        have hpp : 128 + 32 * p + 28 * p ^ 2 < p ^ 3 := by nlinarith
        omega
      have hr_lt : 128 + 32 * p + 28 * p ^ 2 + 25 * p ^ 3 < p ^ 4 := by
        calc
          128 + 32 * p + 28 * p ^ 2 + 25 * p ^ 3 < 26 * p ^ 3 := hr_lt_26p3
          _ < p * p ^ 3 := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
          _ = p ^ 4 := by ring
      have heq : 128 * s = 128 + 32 * p + 28 * p ^ 2 + 25 * p ^ 3 := by
        have hm := hmod4
        rw [Nat.ModEq, Nat.mod_eq_of_lt hl_lt, Nat.mod_eq_of_lt hr_lt] at hm
        exact hm
      omega
    · have hp_lt : p < 131 := by omega
      have hq_val : q = 1 + p + p ^ 2 + p ^ 3 + p ^ 4 + p ^ 5 + p ^ 6 := by
        rw [← hσq, sigma_one_apply_prime_pow hp]
        simp [Finset.sum_range_succ]
      have hsq_eq : s * s = (2 + p + p ^ 2 + p ^ 3 + p ^ 4 + p ^ 5 + p ^ 6) / 2 := by
        have h2s2 : 2 * s ^ 2 = 2 + p + p ^ 2 + p ^ 3 + p ^ 4 + p ^ 5 + p ^ 6 := by omega
        rw [← sq]
        omega
      have hbound : p ^ 3 + 1 - 0 < 2 ^ 23 := by
        have : p ^ 3 < 131 ^ 3 := Nat.pow_lt_pow_left hp_lt (by decide)
        omega
      have hsqrt_true :
          binSqrt ((2 + p + p ^ 2 + p ^ 3 + p ^ 4 + p ^ 5 + p ^ 6) / 2) 0 (p ^ 3) 23 = true :=
        binSqrt_sound _ s hsq_eq 23 0 (p ^ 3) (Nat.zero_le s) hsu.le hbound
      have htrue : checkSmallU3 = true := by
        rw [checkSmallU3, List.any_eq_true]
        refine ⟨p, List.mem_range.mpr hp_lt, ?_⟩
        have hp2 : 2 < p := by omega
        have hmod2 : p % 2 = 1 := Nat.odd_iff.mp hpo
        simp [hp2, hmod2, hsqrt_true]
      rw [checkSmallU3_false] at htrue
      exact Bool.noConfusion htrue
  have h_ne4 : u ≠ 4 := by
    intro hu4
    have hprime : (2 * u + 1).Prime := even_index_length_prime hq hp hu hσq
    rw [hu4] at hprime
    exact absurd hprime (by decide)
  have hu5 : 5 ≤ u := by omega
  exact ⟨hu5, by omega⟩

/-! ### 3. Explicit Integer Power Series of `g(8y) = (1 - 8y)^{-1/2} (1 - 4y)^{1/2}` -/

/-- Rational power series coefficients `c k` of `g(x) = (1 - x)^{-1/2} (1 - x/2)^{1/2}`,
defined via the logarithmic derivative recurrence
`(k + 1) * c (k + 1) = ∑ j ∈ range (k + 1), c j * (2 ^ (k + 1 - j) - 1) / 2 ^ (k + 2 - j)`. -/
def henselRatCoeff : ℕ → ℚ
  | 0 => 1
  | k + 1 =>
    (∑ j ∈ (Finset.range (k + 1)).attach,
      henselRatCoeff j.1 * (((2 : ℚ) ^ (k + 1 - j.1) - 1) / (2 : ℚ) ^ (k + 2 - j.1))) /
      ((k : ℚ) + 1)
decreasing_by
  exact Finset.mem_range.mp j.prop

lemma henselRatCoeff_zero : henselRatCoeff 0 = 1 := by
  rw [henselRatCoeff]

lemma henselRatCoeff_succ (k : ℕ) :
    henselRatCoeff (k + 1) =
      (∑ j ∈ Finset.range (k + 1),
        henselRatCoeff j * (((2 : ℚ) ^ (k + 1 - j) - 1) / (2 : ℚ) ^ (k + 2 - j))) /
        ((k : ℚ) + 1) := by
  conv_lhs => rw [henselRatCoeff]
  rw [Finset.sum_attach (Finset.range (k + 1))
    (fun j => henselRatCoeff j * (((2 : ℚ) ^ (k + 1 - j) - 1) / (2 : ℚ) ^ (k + 2 - j)))]

lemma henselRatCoeff_pos (k : ℕ) : 0 < henselRatCoeff k := by
  induction k using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero =>
      rw [henselRatCoeff_zero]
      norm_num
    | succ m =>
      rw [henselRatCoeff_succ]
      refine div_pos ?_ (by positivity)
      refine Finset.sum_pos ?_ ⟨0, Finset.mem_range.mpr (Nat.succ_pos m)⟩
      intro j hj
      have hj_lt : j < m + 1 := Finset.mem_range.mp hj
      have hcj : 0 < henselRatCoeff j := ih j hj_lt
      have hpow : (1 : ℚ) < (2 : ℚ) ^ (m + 1 - j) := by
        have h2 : (2 : ℕ) ≤ 2 ^ (m + 1 - j) :=
          Nat.le_self_pow (by omega) 2
        exact_mod_cast (by omega : 1 < 2 ^ (m + 1 - j))
      have hfrac : 0 < ((2 : ℚ) ^ (m + 1 - j) - 1) / (2 : ℚ) ^ (m + 2 - j) :=
        div_pos (sub_pos.mpr hpow) (by positivity)
      exact mul_pos hcj hfrac

private noncomputable def henselRatPoly (u : ℕ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (u + 1), Polynomial.C (henselRatCoeff k) * Polynomial.X ^ k

private noncomputable def henselLogDerivPoly (u : ℕ) : Polynomial ℚ :=
  ∑ m ∈ Finset.range u,
    Polynomial.C (((2 : ℚ) ^ (m + 1) - 1) / (2 : ℚ) ^ (m + 2)) * Polynomial.X ^ m

private lemma coeff_henselRatPoly (u k : ℕ) :
    (henselRatPoly u).coeff k = if k < u + 1 then henselRatCoeff k else 0 := by
  simp only [henselRatPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp

private lemma coeff_henselLogDerivPoly (u m : ℕ) :
    (henselLogDerivPoly u).coeff m =
      if m < u then ((2 : ℚ) ^ (m + 1) - 1) / (2 : ℚ) ^ (m + 2) else 0 := by
  simp only [henselLogDerivPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp

private lemma X_pow_dvd_henselRatPoly_deriv_sub (u : ℕ) :
    Polynomial.X ^ u ∣
      (henselRatPoly u).derivative - henselRatPoly u * henselLogDerivPoly u := by
  rw [Polynomial.X_pow_dvd_iff]
  intro k hk
  rw [Polynomial.coeff_sub, Polynomial.coeff_derivative, coeff_henselRatPoly u (k + 1),
    ite_eq_left_iff.mpr (fun h => absurd (by omega) h),
    Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (f := fun i j => (henselRatPoly u).coeff i * (henselLogDerivPoly u).coeff j)]
  have hsum :
      ∑ j ∈ Finset.range (k + 1),
        (henselRatPoly u).coeff j * (henselLogDerivPoly u).coeff (k - j) =
      ∑ j ∈ Finset.range (k + 1),
        henselRatCoeff j * (((2 : ℚ) ^ (k + 1 - j) - 1) / (2 : ℚ) ^ (k + 2 - j)) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj_le : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [coeff_henselRatPoly u j, ite_eq_left_iff.mpr (fun h => absurd (by omega) h),
      coeff_henselLogDerivPoly u (k - j), ite_eq_left_iff.mpr (fun h => absurd (by omega) h),
      show k - j + 1 = k + 1 - j by omega, show k - j + 2 = k + 2 - j by omega]
  rw [hsum, henselRatCoeff_succ]
  have hk0 : ((k : ℚ) + 1) ≠ 0 := by positivity
  field_simp [hk0]
  ring

private lemma X_pow_dvd_quad_mul_henselLogDerivPoly_sub_one (u : ℕ) :
    Polynomial.X ^ u ∣
      (4 - 6 * Polynomial.X + 2 * Polynomial.X ^ 2) * henselLogDerivPoly u - 1 := by
  rw [Polynomial.X_pow_dvd_iff]
  intro k hk
  have hmul :
      ((4 - 6 * Polynomial.X + 2 * Polynomial.X ^ 2) * henselLogDerivPoly u).coeff k =
      4 * (henselLogDerivPoly u).coeff k -
      6 * (if k = 0 then 0 else (henselLogDerivPoly u).coeff (k - 1)) +
      2 * (if k < 2 then 0 else (henselLogDerivPoly u).coeff (k - 2)) := by
    have hsplit : (4 - 6 * Polynomial.X + 2 * Polynomial.X ^ 2) * henselLogDerivPoly u =
        Polynomial.C 4 * henselLogDerivPoly u -
        Polynomial.C 6 * (Polynomial.X * henselLogDerivPoly u) +
        Polynomial.C 2 * (Polynomial.X ^ 2 * henselLogDerivPoly u) := by
      simp only [map_ofNat]
      ring
    rw [hsplit, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
    have hX1 : (Polynomial.X * henselLogDerivPoly u).coeff k =
        if k = 0 then 0 else (henselLogDerivPoly u).coeff (k - 1) := by
      cases k with
      | zero => simp
      | succ m => simp [Polynomial.coeff_X_mul]
    have hX2 : (Polynomial.X ^ 2 * henselLogDerivPoly u).coeff k =
        if k < 2 then 0 else (henselLogDerivPoly u).coeff (k - 2) := by
      rcases lt_or_ge k 2 with hk2 | hk2
      · rw [ite_eq_left_iff.mpr (fun h => absurd hk2 h)]
        have hk01 : k = 0 ∨ k = 1 := by omega
        rcases hk01 with rfl | rfl
        · simp
        · rw [pow_two, mul_assoc, Polynomial.coeff_X_mul, Polynomial.coeff_X_mul_zero]
      · rw [ite_eq_right_iff.mpr (fun h => absurd hk2 (not_le.mpr h))]
        obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
        rw [pow_two, mul_assoc, Polynomial.coeff_X_mul, Polynomial.coeff_X_mul]
        simp
    rw [hX1, hX2]
  rw [Polynomial.coeff_sub, hmul, Polynomial.coeff_one]
  rcases k with _ | _ | m
  · simp [coeff_henselLogDerivPoly, hk]
    norm_num
  · simp [coeff_henselLogDerivPoly, hk, (by omega : 0 < u)]
    norm_num
  · have hm1 : m + 1 < u := by omega
    have hm0 : m < u := by omega
    rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega)),
      ite_eq_right_iff.mpr (fun h => absurd h (by omega)),
      show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega,
      coeff_henselLogDerivPoly u (m + 2), ite_eq_left_iff.mpr (fun h => absurd hk h),
      coeff_henselLogDerivPoly u (m + 1), ite_eq_left_iff.mpr (fun h => absurd hm1 h),
      coeff_henselLogDerivPoly u m, ite_eq_left_iff.mpr (fun h => absurd hm0 h)]
    have hpow1 : (2 : ℚ) ^ (m + 2) = 2 * (2 : ℚ) ^ (m + 1) := by rw [pow_succ']
    have hpow2 : (2 : ℚ) ^ (m + 3) = 4 * (2 : ℚ) ^ (m + 1) := by
      rw [show m + 3 = (m + 1) + 2 by omega, pow_add]; ring
    have hpow3 : (2 : ℚ) ^ (m + 4) = 8 * (2 : ℚ) ^ (m + 1) := by
      rw [show m + 4 = (m + 1) + 3 by omega, pow_add]; ring
    have hnz : (2 : ℚ) ^ (m + 1) ≠ 0 := by positivity
    rw [show m + 2 + 1 = m + 3 by omega, show m + 2 + 2 = m + 4 by omega,
      show m + 1 + 1 = m + 2 by omega, show m + 1 + 2 = m + 3 by omega]
    rw [hpow1, hpow2, hpow3]
    rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]
    field_simp [hnz]
    ring

private lemma henselRatPoly_sq_mod_pow (u : ℕ) :
    Polynomial.X ^ (u + 1) ∣
      (1 - Polynomial.X) * henselRatPoly u ^ 2 - (1 - Polynomial.C (1 / 2 : ℚ) * Polynomial.X) := by
  set F := henselRatPoly u
  set H : Polynomial ℚ := (1 - Polynomial.X) * F ^ 2 - (1 - Polynomial.C (1 / 2 : ℚ) * Polynomial.X)
  have hH0 : H.coeff 0 = 0 := by
    simp [H, F, sq, Polynomial.mul_coeff_zero, coeff_henselRatPoly, henselRatCoeff_zero]
  have hderiv_id :
      (2 - Polynomial.X) * H.derivative + H =
      F * ((4 - 6 * Polynomial.X + 2 * Polynomial.X ^ 2) * F.derivative - F) := by
    have hFd : H.derivative =
        -F ^ 2 + 2 * (1 - Polynomial.X) * F * F.derivative + Polynomial.C (1 / 2 : ℚ) := by
      dsimp [H]
      simp only [Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_one,
        Polynomial.derivative_X, Polynomial.derivative_C, zero_sub, zero_mul,
        Polynomial.derivative_pow, Nat.cast_ofNat, map_ofNat]
      ring
    rw [hFd]
    have hhalf : (Polynomial.C (1 / 2 : ℚ) : Polynomial ℚ) * 2 = 1 := by
      rw [← map_ofNat Polynomial.C 2, ← map_mul]
      norm_num
    calc
      (2 - Polynomial.X) *
          (-F ^ 2 + 2 * (1 - Polynomial.X) * F * F.derivative + Polynomial.C (1 / 2 : ℚ)) +
        ((1 - Polynomial.X) * F ^ 2 - (1 - Polynomial.C (1 / 2 : ℚ) * Polynomial.X))
          = F * ((4 - 6 * Polynomial.X + 2 * Polynomial.X ^ 2) * F.derivative - F) +
              (Polynomial.C (1 / 2 : ℚ) * 2 - 1) := by ring
      _ = F * ((4 - 6 * Polynomial.X + 2 * Polynomial.X ^ 2) * F.derivative - F) := by
          rw [hhalf, sub_self, add_zero]
  have hdvd_ode : Polynomial.X ^ u ∣ (2 - Polynomial.X) * H.derivative + H := by
    rw [hderiv_id]
    have h1 := X_pow_dvd_henselRatPoly_deriv_sub u
    have h2 := X_pow_dvd_quad_mul_henselLogDerivPoly_sub_one u
    have hsplit : (4 - 6 * Polynomial.X + 2 * Polynomial.X ^ 2) * F.derivative - F =
        (4 - 6 * Polynomial.X + 2 * Polynomial.X ^ 2) * (F.derivative - F * henselLogDerivPoly u) +
        F * ((4 - 6 * Polynomial.X + 2 * Polynomial.X ^ 2) * henselLogDerivPoly u - 1) := by
      ring
    refine dvd_mul_of_dvd_right ?_ F
    rw [hsplit]
    exact dvd_add (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h2 _)
  have hcoeff_zero : ∀ k ≤ u, H.coeff k = 0 := by
    intro k
    induction k with
    | zero => intro _; exact hH0
    | succ m ih =>
      intro hm
      have hm_lt : m < u := by omega
      have hkm := (Polynomial.X_pow_dvd_iff.mp hdvd_ode) m hm_lt
      have hm_coeff : H.coeff m = 0 := ih (by omega)
      have hXderiv : (Polynomial.X * H.derivative).coeff m =
          if m = 0 then 0 else H.coeff m * m := by
        cases m with
        | zero => simp
        | succ r =>
          rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
          push_cast
          ring
      have hsplit2 : ((2 - Polynomial.X) * H.derivative + H).coeff m =
          2 * (H.coeff (m + 1) * ((m : ℚ) + 1)) -
          (if m = 0 then 0 else H.coeff m * m) + H.coeff m := by
        have hrew : (2 - Polynomial.X) * H.derivative + H =
            Polynomial.C 2 * H.derivative - Polynomial.X * H.derivative + H := by
          simp only [map_ofNat]
          ring
        rw [hrew, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
          Polynomial.coeff_derivative, hXderiv]
      rw [hsplit2, hm_coeff] at hkm
      simp only [zero_mul, ite_self, sub_zero, add_zero] at hkm
      have hfac_nz : (2 : ℚ) * ((m : ℚ) + 1) ≠ 0 := by positivity
      have : H.coeff (m + 1) * (2 * ((m : ℚ) + 1)) = 0 := by
        linarith
      exact (mul_eq_zero.mp this).resolve_right hfac_nz
  rw [Polynomial.X_pow_dvd_iff]
  intro k hk
  exact hcoeff_zero k (by omega)

/-- Upper bound `henselRatCoeff k ≤ 1 / 4` for all `k ≥ 1`. -/
lemma henselRatCoeff_le_quarter {k : ℕ} (hk : 1 ≤ k) : henselRatCoeff k ≤ 1 / 4 := by
  have hdvd := henselRatPoly_sq_mod_pow k
  set G : Polynomial ℚ := henselRatPoly k ^ 2
  have htelescope : ∀ m : ℕ,
      ∑ j ∈ Finset.range (m + 1), ((1 - Polynomial.X) * G).coeff j = G.coeff m := by
    intro m
    induction m with
    | zero =>
      simp [sub_mul]
    | succ r ih =>
      rw [Finset.sum_range_succ, ih]
      have hstep : ((1 - Polynomial.X) * G).coeff (r + 1) = G.coeff (r + 1) - G.coeff r := by
        rw [sub_mul, one_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul]
      rw [hstep]
      ring
  have hsum_val : ∑ j ∈ Finset.range (k + 1), ((1 - Polynomial.X) * G).coeff j = 1 / 2 := by
    have hcoeff_j : ∀ j ∈ Finset.range (k + 1),
        ((1 - Polynomial.X) * G).coeff j =
        (1 - Polynomial.C (1 / 2 : ℚ) * Polynomial.X).coeff j := by
      intro j hj
      have hj_lt : j < k + 1 := Finset.mem_range.mp hj
      have hsub0 := (Polynomial.X_pow_dvd_iff.mp hdvd) j hj_lt
      rw [Polynomial.coeff_sub] at hsub0
      exact sub_eq_zero.mp hsub0
    rw [Finset.sum_congr rfl hcoeff_j]
    have hk_sub : k + 1 = (k - 1) + 2 := by omega
    rw [hk_sub, Finset.sum_range_succ', Finset.sum_range_succ']
    have htail : ∑ x ∈ Finset.range (k - 1),
        (1 - Polynomial.C (1 / 2 : ℚ) * Polynomial.X).coeff (x + 1 + 1) = 0 := by
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_C_mul_X]
      simp
    rw [htail, zero_add]
    rw [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_C_mul_X]
    norm_num
  have hGk : G.coeff k = 1 / 2 := by
    rw [← htelescope k, hsum_val]
  have hGk_expand :
      G.coeff k = 2 * henselRatCoeff k +
        ∑ i ∈ Finset.Ico 1 k, henselRatCoeff i * henselRatCoeff (k - i) := by
    dsimp [G]
    rw [sq, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (f := fun i j => (henselRatPoly k).coeff i * (henselRatPoly k).coeff j)]
    have hterm :
        ∑ i ∈ Finset.range (k + 1),
          (henselRatPoly k).coeff i * (henselRatPoly k).coeff (k - i) =
        ∑ i ∈ Finset.range (k + 1), henselRatCoeff i * henselRatCoeff (k - i) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi_le : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [coeff_henselRatPoly k i, ite_eq_left_iff.mpr (fun h => absurd (by omega) h),
        coeff_henselRatPoly k (k - i), ite_eq_left_iff.mpr (fun h => absurd (by omega) h)]
    rw [hterm, Finset.sum_range_succ, Nat.sub_self, henselRatCoeff_zero, mul_one,
      ← Nat.Ico_zero_eq_range, Finset.sum_eq_sum_Ico_succ_bot hk, Nat.sub_zero,
      henselRatCoeff_zero, one_mul]
    ring
  have hnonneg : 0 ≤ ∑ i ∈ Finset.Ico 1 k, henselRatCoeff i * henselRatCoeff (k - i) :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (henselRatCoeff_pos i).le (henselRatCoeff_pos (k - i)).le
  linarith

private def henselACoeff (m : ℕ) : ℤ :=
  (Nat.centralBinom m : ℤ) * 2 ^ m

private def henselBCoeff : ℕ → ℤ
  | 0 => 1
  | m + 1 => -2 * ((Nat.centralBinom m / (m + 1) : ℕ) : ℤ)

/-- Integer power series coefficients `a k = 8 ^ k * c k` of
`g(8y) = (1 - 8y)^{-1/2} (1 - 4y)^{1/2}`, realized explicitly as the Cauchy product
of `(1 - 8y)^{-1/2}` and `(1 - 4y)^{1/2}`. -/
def henselScaledCoeff (k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (k + 1), henselACoeff i * henselBCoeff (k - i)

lemma henselScaledCoeff_zero : henselScaledCoeff 0 = 1 := by
  simp [henselScaledCoeff, henselACoeff, henselBCoeff, Nat.centralBinom_zero]

/-- Degree-`u` integer polynomial truncation `∑ k ∈ range (u + 1), henselScaledCoeff k * X ^ k`. -/
noncomputable def henselScaledPoly (u : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (u + 1), Polynomial.C (henselScaledCoeff k) * Polynomial.X ^ k

private noncomputable def henselAPoly (u : ℕ) : Polynomial ℚ :=
  ∑ m ∈ Finset.range (u + 1), Polynomial.C (henselACoeff m : ℚ) * Polynomial.X ^ m

private noncomputable def henselBPoly (u : ℕ) : Polynomial ℚ :=
  ∑ m ∈ Finset.range (u + 1), Polynomial.C (henselBCoeff m : ℚ) * Polynomial.X ^ m

private lemma coeff_henselAPoly (u m : ℕ) :
    (henselAPoly u).coeff m = if m < u + 1 then (henselACoeff m : ℚ) else 0 := by
  simp only [henselAPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp

private lemma coeff_henselBPoly (u m : ℕ) :
    (henselBPoly u).coeff m = if m < u + 1 then (henselBCoeff m : ℚ) else 0 := by
  simp only [henselBPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp

private lemma henselAPoly_sq_mod_pow (u : ℕ) :
    Polynomial.X ^ (u + 1) ∣ (1 - 8 * Polynomial.X) * henselAPoly u ^ 2 - 1 := by
  set A := henselAPoly u
  set HA : Polynomial ℚ := (1 - 8 * Polynomial.X) * A ^ 2 - 1
  have hHA0 : HA.coeff 0 = 0 := by
    simp [HA, A, sq, Polynomial.mul_coeff_zero, coeff_henselAPoly, henselACoeff,
      Nat.centralBinom_zero]
  have hode : Polynomial.X ^ u ∣ (1 - 8 * Polynomial.X) * A.derivative - 4 * A := by
    rw [Polynomial.X_pow_dvd_iff]
    intro m hm
    have hsplit : ((1 - 8 * Polynomial.X) * A.derivative - 4 * A).coeff m =
        A.derivative.coeff m -
        8 * (if m = 0 then 0 else A.derivative.coeff (m - 1)) - 4 * A.coeff m := by
      have hrew : (1 - 8 * Polynomial.X) * A.derivative - 4 * A =
          A.derivative - Polynomial.C 8 * (Polynomial.X * A.derivative) - Polynomial.C 4 * A := by
        simp only [map_ofNat]
        ring
      rw [hrew, Polynomial.coeff_sub, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.coeff_C_mul]
      cases m with
      | zero => simp
      | succ r => simp [Polynomial.coeff_X_mul]
    rw [hsplit]
    have hrec : ((m : ℚ) + 1) * (henselACoeff (m + 1) : ℚ) =
        (8 * (m : ℚ) + 4) * (henselACoeff m : ℚ) := by
      have hcb := Nat.succ_mul_centralBinom_succ m
      have hcbQ : ((m : ℚ) + 1) * (Nat.centralBinom (m + 1) : ℚ) =
          2 * (2 * (m : ℚ) + 1) * (Nat.centralBinom m : ℚ) := by
        exact_mod_cast hcb
      simp only [henselACoeff, Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat]
      have hpow : (2 : ℚ) ^ (m + 1) = 2 * (2 : ℚ) ^ m := by rw [pow_succ']
      rw [hpow]
      linear_combination 2 * (2 : ℚ) ^ m * hcbQ
    cases m with
    | zero =>
      simp only [Nat.cast_zero, zero_add, mul_zero, sub_zero, ↓reduceIte] at hrec ⊢
      rw [Polynomial.coeff_derivative, coeff_henselAPoly u 1,
        ite_eq_left_iff.mpr (fun h => absurd (by omega) h),
        coeff_henselAPoly u 0, ite_eq_left_iff.mpr (fun h => absurd (by omega) h)]
      push_cast
      linarith
    | succ r =>
      have hr_lt : r + 1 < u := hm
      rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega)),
        Polynomial.coeff_derivative, Polynomial.coeff_derivative,
        show r + 1 + 1 = r + 2 by omega, show r + 1 - 1 = r by omega,
        coeff_henselAPoly u (r + 2), ite_eq_left_iff.mpr (fun h => absurd (by omega) h),
        coeff_henselAPoly u (r + 1), ite_eq_left_iff.mpr (fun h => absurd (by omega) h)]
      push_cast at hrec ⊢
      linarith
  have hdvd_deriv : Polynomial.X ^ u ∣ HA.derivative := by
    have hid : HA.derivative = 2 * A * ((1 - 8 * Polynomial.X) * A.derivative - 4 * A) := by
      dsimp [HA]
      have h8 : (1 - 8 * Polynomial.X : Polynomial ℚ).derivative = -8 := by
        rw [show (8 : Polynomial ℚ) = Polynomial.C 8 by rw [map_ofNat]]
        simp
      rw [Polynomial.derivative_sub, Polynomial.derivative_one, sub_zero,
        Polynomial.derivative_mul, h8, Polynomial.derivative_pow]
      simp only [Nat.cast_ofNat, map_ofNat]
      ring
    rw [hid]
    exact dvd_mul_of_dvd_right hode _
  rw [Polynomial.X_pow_dvd_iff]
  intro k hk
  cases k with
  | zero => exact hHA0
  | succ m =>
    have hm_lt : m < u := by omega
    have hm := (Polynomial.X_pow_dvd_iff.mp hdvd_deriv) m hm_lt
    rw [Polynomial.coeff_derivative] at hm
    have hm_nz : ((m : ℚ) + 1) ≠ 0 := by positivity
    exact (mul_eq_zero.mp hm).resolve_right hm_nz

private lemma henselBPoly_sq_mod_pow (u : ℕ) :
    Polynomial.X ^ (u + 1) ∣ henselBPoly u ^ 2 - (1 - 4 * Polynomial.X) := by
  set B := henselBPoly u
  set HB : Polynomial ℚ := B ^ 2 - (1 - 4 * Polynomial.X)
  have hHB0 : HB.coeff 0 = 0 := by
    simp [HB, B, sq, Polynomial.mul_coeff_zero, coeff_henselBPoly, henselBCoeff]
  have hode : Polynomial.X ^ u ∣ (1 - 4 * Polynomial.X) * B.derivative + 2 * B := by
    rw [Polynomial.X_pow_dvd_iff]
    intro m hm
    have hsplit : ((1 - 4 * Polynomial.X) * B.derivative + 2 * B).coeff m =
        B.derivative.coeff m -
        4 * (if m = 0 then 0 else B.derivative.coeff (m - 1)) + 2 * B.coeff m := by
      have hrew : (1 - 4 * Polynomial.X) * B.derivative + 2 * B =
          B.derivative - Polynomial.C 4 * (Polynomial.X * B.derivative) + Polynomial.C 2 * B := by
        simp only [map_ofNat]
        ring
      rw [hrew, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.coeff_C_mul]
      cases m with
      | zero => simp
      | succ r => simp [Polynomial.coeff_X_mul]
    rw [hsplit]
    cases m with
    | zero =>
      rw [ite_eq_left_iff.mpr (fun h => absurd rfl h), mul_zero, sub_zero,
        Polynomial.coeff_derivative,
        coeff_henselBPoly u 1, ite_eq_left_iff.mpr (fun h => absurd (by omega) h),
        coeff_henselBPoly u 0, ite_eq_left_iff.mpr (fun h => absurd (by omega) h)]
      simp [henselBCoeff, Nat.centralBinom_zero]
    | succ r =>
      have hr1 : r + 1 < u := hm
      rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega)),
        Polynomial.coeff_derivative, Polynomial.coeff_derivative,
        show r + 1 + 1 = r + 2 by omega, show r + 1 - 1 = r by omega,
        coeff_henselBPoly u (r + 2), ite_eq_left_iff.mpr (fun h => absurd (by omega) h),
        coeff_henselBPoly u (r + 1), ite_eq_left_iff.mpr (fun h => absurd (by omega) h)]
      have hdiv1 : r + 1 ∣ Nat.centralBinom r := Nat.succ_dvd_centralBinom r
      have hdiv2 : r + 2 ∣ Nat.centralBinom (r + 1) := Nat.succ_dvd_centralBinom (r + 1)
      have hq1 : ((Nat.centralBinom r / (r + 1) : ℕ) : ℚ) * ((r : ℚ) + 1) =
          (Nat.centralBinom r : ℚ) := by
        exact_mod_cast Nat.div_mul_cancel hdiv1
      have hq2 : ((Nat.centralBinom (r + 1) / (r + 2) : ℕ) : ℚ) * ((r : ℚ) + 2) =
          (Nat.centralBinom (r + 1) : ℚ) := by
        exact_mod_cast Nat.div_mul_cancel hdiv2
      have hcb : ((r : ℚ) + 1) * (Nat.centralBinom (r + 1) : ℚ) =
          2 * (2 * (r : ℚ) + 1) * (Nat.centralBinom r : ℚ) := by
        exact_mod_cast Nat.succ_mul_centralBinom_succ r
      simp only [henselBCoeff, Int.cast_mul, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast]
      push_cast
      apply mul_right_cancel₀ (by positivity : ((r : ℚ) + 1) ≠ 0)
      rw [zero_mul]
      linear_combination -2 * ((r : ℚ) + 1) * hq2 + 4 * (2 * (r : ℚ) + 1) * hq1 - 2 * hcb
  have hderiv_id :
      (1 - 4 * Polynomial.X) * HB.derivative + 4 * HB =
      2 * B * ((1 - 4 * Polynomial.X) * B.derivative + 2 * B) := by
    dsimp [HB]
    have h4 : (1 - 4 * Polynomial.X : Polynomial ℚ).derivative = -4 := by
      rw [show (4 : Polynomial ℚ) = Polynomial.C 4 by rw [map_ofNat]]
      simp
    rw [Polynomial.derivative_sub, Polynomial.derivative_pow, h4]
    simp only [Nat.cast_ofNat, map_ofNat]
    ring
  have hdvd_ode : Polynomial.X ^ u ∣ (1 - 4 * Polynomial.X) * HB.derivative + 4 * HB := by
    rw [hderiv_id]
    exact dvd_mul_of_dvd_right hode _
  have hcoeff_zero : ∀ k ≤ u, HB.coeff k = 0 := by
    intro k
    induction k with
    | zero => intro _; exact hHB0
    | succ m ih =>
      intro hm
      have hm_lt : m < u := by omega
      have hkm := (Polynomial.X_pow_dvd_iff.mp hdvd_ode) m hm_lt
      have hm_coeff : HB.coeff m = 0 := ih (by omega)
      have hXderiv : (Polynomial.X * HB.derivative).coeff m =
          if m = 0 then 0 else HB.coeff m * m := by
        cases m with
        | zero => simp
        | succ r =>
          rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
          push_cast
          ring
      have hsplit : ((1 - 4 * Polynomial.X) * HB.derivative + 4 * HB).coeff m =
          HB.coeff (m + 1) * ((m : ℚ) + 1) -
          4 * (if m = 0 then 0 else HB.coeff m * m) + 4 * HB.coeff m := by
        have hrew : (1 - 4 * Polynomial.X) * HB.derivative + 4 * HB =
            HB.derivative - Polynomial.C 4 * (Polynomial.X * HB.derivative) + Polynomial.C 4 * HB := by
          simp only [map_ofNat]
          ring
        rw [hrew, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
          Polynomial.coeff_C_mul, Polynomial.coeff_derivative, hXderiv]
      rw [hsplit, hm_coeff] at hkm
      simp only [zero_mul, ite_self, mul_zero, sub_zero, add_zero] at hkm
      have hm_nz : ((m : ℚ) + 1) ≠ 0 := by positivity
      exact (mul_eq_zero.mp hkm).resolve_right hm_nz
  rw [Polynomial.X_pow_dvd_iff]
  intro k hk
  exact hcoeff_zero k (by omega)

private lemma X_pow_dvd_cancel_const_ne_zero {n : ℕ} {P Q : Polynomial ℚ}
    (hQ : Q.coeff 0 ≠ 0) (hdvd : Polynomial.X ^ n ∣ P * Q) :
    Polynomial.X ^ n ∣ P := by
  rw [Polynomial.X_pow_dvd_iff] at hdvd ⊢
  intro k hk
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    have hmul0 := hdvd k hk
    rw [Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (f := fun i j => P.coeff i * Q.coeff j),
      Finset.sum_range_succ, Nat.sub_self] at hmul0
    have htail : ∑ i ∈ Finset.range k, P.coeff i * Q.coeff (k - i) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have hi_lt : i < k := Finset.mem_range.mp hi
      rw [ih i hi_lt (hi_lt.trans hk), zero_mul]
    rw [htail, zero_add] at hmul0
    exact (mul_eq_zero.mp hmul0).resolve_right hQ

/-- Exact identity relating the integer coefficient `henselScaledCoeff k` and the rational
coefficient `henselRatCoeff k`: `(henselScaledCoeff k : ℚ) = 8 ^ k * henselRatCoeff k`. -/
theorem henselScaledCoeff_eq (k : ℕ) :
    (henselScaledCoeff k : ℚ) = (8 : ℚ) ^ k * henselRatCoeff k := by
  set G : Polynomial ℚ := (henselRatPoly k).comp (Polynomial.C 8 * Polynomial.X)
  have hG_coeff : ∀ j ≤ k, G.coeff j = (8 : ℚ) ^ j * henselRatCoeff j := by
    intro j hj
    dsimp [G, henselRatPoly]
    rw [Polynomial.sum_comp]
    simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp,
      mul_pow, ← Polynomial.C_pow, ← mul_assoc, ← map_mul, Polynomial.finsetSum_coeff,
      Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    rw [ite_eq_left_iff.mpr (fun h => absurd (Finset.mem_range.mpr (by omega)) h)]
    ring
  have hG_sq :
      Polynomial.X ^ (k + 1) ∣ (1 - 8 * Polynomial.X) * G ^ 2 - (1 - 4 * Polynomial.X) := by
    have hdvd := henselRatPoly_sq_mod_pow k
    obtain ⟨Q, hQ⟩ := hdvd
    have hcomp := congrArg (fun p => p.comp (Polynomial.C 8 * Polynomial.X)) hQ
    have hL : ((1 - Polynomial.X) * henselRatPoly k ^ 2 -
          (1 - Polynomial.C (1 / 2 : ℚ) * Polynomial.X)).comp (Polynomial.C 8 * Polynomial.X) =
        (1 - 8 * Polynomial.X) * G ^ 2 - (1 - 4 * Polynomial.X) := by
      simp only [Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.one_comp,
        Polynomial.X_comp, Polynomial.pow_comp, Polynomial.C_comp]
      have h4 : Polynomial.C (1 / 2 : ℚ) * (Polynomial.C 8 * Polynomial.X) = 4 * Polynomial.X := by
        rw [← mul_assoc, ← map_mul]
        norm_num
        rw [map_ofNat]
      have h8 : Polynomial.C (8 : ℚ) * Polynomial.X = 8 * Polynomial.X := by rw [map_ofNat]
      rw [h4, h8]
      rfl
    have hR : (Polynomial.X ^ (k + 1) * Q).comp (Polynomial.C 8 * Polynomial.X) =
        Polynomial.X ^ (k + 1) *
          (Polynomial.C ((8 : ℚ) ^ (k + 1)) * Q.comp (Polynomial.C 8 * Polynomial.X)) := by
      simp only [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp, mul_pow,
        ← Polynomial.C_pow]
      ring
    rw [hL, hR] at hcomp
    exact ⟨_, hcomp⟩
  have hAB_sq :
      Polynomial.X ^ (k + 1) ∣
        (1 - 8 * Polynomial.X) * (henselAPoly k * henselBPoly k) ^ 2 - (1 - 4 * Polynomial.X) := by
    have hid :
        (1 - 8 * Polynomial.X) * (henselAPoly k * henselBPoly k) ^ 2 - (1 - 4 * Polynomial.X) =
        ((1 - 8 * Polynomial.X) * henselAPoly k ^ 2 - 1) * henselBPoly k ^ 2 +
        (henselBPoly k ^ 2 - (1 - 4 * Polynomial.X)) := by ring
    rw [hid]
    exact dvd_add
      (dvd_mul_of_dvd_left (henselAPoly_sq_mod_pow k) _)
      (henselBPoly_sq_mod_pow k)
  have hdvd_prod :
      Polynomial.X ^ (k + 1) ∣
        (G - henselAPoly k * henselBPoly k) *
          ((1 - 8 * Polynomial.X) * (G + henselAPoly k * henselBPoly k)) := by
    have hfac :
        (G - henselAPoly k * henselBPoly k) *
          ((1 - 8 * Polynomial.X) * (G + henselAPoly k * henselBPoly k)) =
        ((1 - 8 * Polynomial.X) * G ^ 2 - (1 - 4 * Polynomial.X)) -
        ((1 - 8 * Polynomial.X) * (henselAPoly k * henselBPoly k) ^ 2 - (1 - 4 * Polynomial.X)) := by
      ring
    rw [hfac]
    exact dvd_sub hG_sq hAB_sq
  have hQ0 : ((1 - 8 * Polynomial.X) * (G + henselAPoly k * henselBPoly k)).coeff 0 ≠ 0 := by
    have hG0 : G.coeff 0 = 1 := by
      rw [hG_coeff 0 (Nat.zero_le k), pow_zero, henselRatCoeff_zero, mul_one]
    have hA0 : (henselAPoly k).coeff 0 = 1 := by
      simp [coeff_henselAPoly, henselACoeff, Nat.centralBinom_zero]
    have hB0 : (henselBPoly k).coeff 0 = 1 := by
      simp [coeff_henselBPoly, henselBCoeff]
    rw [Polynomial.mul_coeff_zero, Polynomial.coeff_sub, AddMonoidAlgebra.coeff_one_zero,
      show (8 * Polynomial.X : Polynomial ℚ).coeff 0 = 0 by simp, sub_zero, one_mul,
      Polynomial.coeff_add, hG0, Polynomial.mul_coeff_zero, hA0, hB0]
    norm_num
  have hdvd_diff : Polynomial.X ^ (k + 1) ∣ G - henselAPoly k * henselBPoly k :=
    X_pow_dvd_cancel_const_ne_zero hQ0 hdvd_prod
  have hcoeff_eq := (Polynomial.X_pow_dvd_iff.mp hdvd_diff) k (Nat.lt_succ_self k)
  rw [Polynomial.coeff_sub, sub_eq_zero, hG_coeff k le_rfl,
    Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (f := fun i j => (henselAPoly k).coeff i * (henselBPoly k).coeff j)] at hcoeff_eq
  rw [henselScaledCoeff]
  push_cast
  trans ∑ i ∈ Finset.range (k + 1), (henselAPoly k).coeff i * (henselBPoly k).coeff (k - i)
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi_le : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [coeff_henselAPoly k i, ite_eq_left_iff.mpr (fun h => absurd (by omega) h),
      coeff_henselBPoly k (k - i), ite_eq_left_iff.mpr (fun h => absurd (by omega) h)]
  · exact hcoeff_eq.symm

/-- The integer polynomial `henselScaledPoly u` satisfies
`(1 - 8 * X) * (henselScaledPoly u) ^ 2 ≡ 1 - 4 * X [MOD X ^ (u + 1)]` in `ℤ[X]`. -/
theorem henselScaledPoly_sq_mod_pow (u : ℕ) :
    Polynomial.X ^ (u + 1) ∣
      (1 - 8 * Polynomial.X) * henselScaledPoly u ^ 2 - (1 - 4 * Polynomial.X) := by
  rw [Polynomial.X_pow_dvd_iff]
  intro k hk
  have hAB_k : (henselScaledPoly u).map (Int.castRingHom ℚ) =
      (henselRatPoly u).comp (Polynomial.C 8 * Polynomial.X) := by
    ext j
    rw [Polynomial.coeff_map]
    have hscaled : (henselScaledPoly u).coeff j =
        if j < u + 1 then henselScaledCoeff j else 0 := by
      simp only [henselScaledPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
      rw [Finset.sum_ite_eq]
      simp
    have hcomp : ((henselRatPoly u).comp (Polynomial.C 8 * Polynomial.X)).coeff j =
        if j < u + 1 then (8 : ℚ) ^ j * henselRatCoeff j else 0 := by
      dsimp [henselRatPoly]
      rw [Polynomial.sum_comp]
      simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp,
        mul_pow, ← Polynomial.C_pow, ← mul_assoc, ← map_mul, Polynomial.finsetSum_coeff,
        Polynomial.coeff_C_mul_X_pow]
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_range]
      split_ifs with hj
      · ring
      · rfl
    rw [hscaled, hcomp]
    split_ifs with hj
    · exact henselScaledCoeff_eq j
    · simp
  have hQ_dvd :
      Polynomial.X ^ (u + 1) ∣
        ((1 - 8 * Polynomial.X) * henselScaledPoly u ^ 2 - (1 - 4 * Polynomial.X)).map
          (Int.castRingHom ℚ) := by
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_one, Polynomial.map_pow,
      Polynomial.map_ofNat, Polynomial.map_X, hAB_k]
    obtain ⟨Q, hQ⟩ := henselRatPoly_sq_mod_pow u
    have hcomp := congrArg (fun p => p.comp (Polynomial.C 8 * Polynomial.X)) hQ
    have hL : ((1 - Polynomial.X) * henselRatPoly u ^ 2 -
          (1 - Polynomial.C (1 / 2 : ℚ) * Polynomial.X)).comp (Polynomial.C 8 * Polynomial.X) =
        (1 - 8 * Polynomial.X) *
            ((henselRatPoly u).comp (Polynomial.C 8 * Polynomial.X)) ^ 2 -
          (1 - 4 * Polynomial.X) := by
      simp only [Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.one_comp,
        Polynomial.X_comp, Polynomial.pow_comp, Polynomial.C_comp]
      have h4 : Polynomial.C (1 / 2 : ℚ) * (Polynomial.C 8 * Polynomial.X) = 4 * Polynomial.X := by
        rw [← mul_assoc, ← map_mul]
        norm_num
        rw [map_ofNat]
      have h8 : Polynomial.C (8 : ℚ) * Polynomial.X = 8 * Polynomial.X := by rw [map_ofNat]
      rw [h4, h8]
    have hR : (Polynomial.X ^ (u + 1) * Q).comp (Polynomial.C 8 * Polynomial.X) =
        Polynomial.X ^ (u + 1) *
          (Polynomial.C ((8 : ℚ) ^ (u + 1)) * Q.comp (Polynomial.C 8 * Polynomial.X)) := by
      simp only [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp, mul_pow,
        ← Polynomial.C_pow]
      ring
    rw [hL, hR] at hcomp
    exact ⟨_, hcomp⟩
  have hQ0 := (Polynomial.X_pow_dvd_iff.mp hQ_dvd) k hk
  rw [Polynomial.coeff_map, eq_intCast, Int.cast_eq_zero] at hQ0
  exact hQ0

/-! ### 4. Unconditional Exponential Base Cap `p < 8 ^ u` -/

private def henselEval (u : ℕ) (p : ℤ) : ℤ :=
  ∑ k ∈ Finset.range (u + 1), henselScaledCoeff k * 8 ^ (u - k) * p ^ k

private lemma henselEval_cast_rat (u : ℕ) (p : ℤ) :
    (henselEval u p : ℚ) =
      (8 : ℚ) ^ u * ∑ k ∈ Finset.range (u + 1), henselRatCoeff k * (p : ℚ) ^ k := by
  dsimp [henselEval]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk_le : k ≤ u := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [henselScaledCoeff_eq k]
  have hpow : (8 : ℚ) ^ u = (8 : ℚ) ^ k * (8 : ℚ) ^ (u - k) := by
    rw [← pow_add, Nat.add_sub_of_le hk_le]
  rw [hpow]
  ring

private lemma henselEval_mod_p_succ (u : ℕ) {p : ℕ} (hp : p.Prime) (hpo : Odd p) :
    (p : ℤ) ^ (u + 1) ∣
      2 * ((p : ℤ) - 1) * henselEval u p ^ 2 - (8 : ℤ) ^ (2 * u) * ((p : ℤ) - 2) := by
  set D : Polynomial ℤ :=
    (1 - 8 * Polynomial.X) * henselScaledPoly u ^ 2 - (1 - 4 * Polynomial.X)
  have hdvd : Polynomial.X ^ (u + 1) ∣ D := henselScaledPoly_sq_mod_pow u
  have hdeg_scaled : (henselScaledPoly u).natDegree ≤ u := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun j hj => ?_
    simp only [henselScaledPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp [show ¬ (j ∈ Finset.range (u + 1)) by simp [Finset.mem_range]; omega]
  have hdeg_D : D.natDegree ≤ 2 * u + 1 := by
    dsimp [D]
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · refine (Polynomial.natDegree_mul_le).trans ?_
      have h1 : (1 - 8 * Polynomial.X : Polynomial ℤ).natDegree ≤ 1 := by
        refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun j hj => ?_
        rw [Polynomial.coeff_sub, Polynomial.coeff_one,
          show (8 * Polynomial.X : Polynomial ℤ) = Polynomial.C 8 * Polynomial.X by simp,
          Polynomial.coeff_C_mul_X]
        simp [show j ≠ 0 by omega, show j ≠ 1 by omega]
      have h2 : (henselScaledPoly u ^ 2).natDegree ≤ 2 * u :=
        (Polynomial.natDegree_pow_le).trans (by omega)
      omega
    · refine (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) ?_)
      refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun j hj => ?_
      rw [show (4 * Polynomial.X : Polynomial ℤ) = Polynomial.C 4 * Polynomial.X by simp,
        Polynomial.coeff_C_mul_X]
      simp [show j ≠ 1 by omega]
  have hD_decomp : D = ∑ j ∈ Finset.Ico (u + 1) (2 * u + 2), Polynomial.C (D.coeff j) * Polynomial.X ^ j := by
    ext k
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    split_ifs with hk
    · rfl
    · simp only [Finset.mem_Ico, not_and, not_lt] at hk
      rcases lt_or_ge k (u + 1) with hk_lt | hk_ge
      · exact (Polynomial.X_pow_dvd_iff.mp hdvd) k hk_lt
      · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg_D (hk hk_ge))
  let R : ℤ := ∑ j ∈ Finset.Ico (u + 1) (2 * u + 2),
    D.coeff j * (p : ℤ) ^ (j - (u + 1)) * 8 ^ (2 * u + 1 - j)
  have hid_rat :
      ((4 * (2 * ((p : ℤ) - 1) * henselEval u p ^ 2 - (8 : ℤ) ^ (2 * u) * ((p : ℤ) - 2)) : ℤ) : ℚ) =
      (((p : ℤ) ^ (u + 1) * (-R) : ℤ) : ℚ) := by
    have hDeval :
        ((D.map (Int.castRingHom ℚ)).eval ((p : ℚ) / 8)) =
        ∑ j ∈ Finset.Ico (u + 1) (2 * u + 2), (D.coeff j : ℚ) * ((p : ℚ) / 8) ^ j := by
      conv_lhs => rw [hD_decomp]
      simp [Polynomial.map_sum, Polynomial.eval_finsetSum]
    have hG_eval :
        (8 : ℚ) ^ u * ((henselScaledPoly u).map (Int.castRingHom ℚ)).eval ((p : ℚ) / 8) =
        (henselEval u p : ℚ) := by
      simp only [henselScaledPoly, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_pow, Polynomial.map_X, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      rw [Finset.mul_sum]
      dsimp [henselEval]
      push_cast
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_le : k ≤ u := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hpow : (8 : ℚ) ^ u = (8 : ℚ) ^ (u - k) * (8 : ℚ) ^ k := by
        rw [← pow_add, Nat.sub_add_cancel hk_le]
      rw [div_pow, hpow]
      have h8k : (8 : ℚ) ^ k ≠ 0 := by positivity
      field_simp [h8k]
    have hL_eval :
        (8 : ℚ) ^ (2 * u + 1) * ((D.map (Int.castRingHom ℚ)).eval ((p : ℚ) / 8)) =
        -4 * ((2 * ((p : ℚ) - 1) * (henselEval u p : ℚ) ^ 2 -
          (8 : ℚ) ^ (2 * u) * ((p : ℚ) - 2))) := by
      have hDmap :
          (D.map (Int.castRingHom ℚ)).eval ((p : ℚ) / 8) =
          (1 - (p : ℚ)) * (((henselScaledPoly u).map (Int.castRingHom ℚ)).eval ((p : ℚ) / 8)) ^ 2 -
            (1 - (p : ℚ) / 2) := by
        dsimp [D]
        simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_one, Polynomial.map_pow,
          Polynomial.map_ofNat, Polynomial.map_X, Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_X]
        ring
      rw [hDmap]
      calc
        (8 : ℚ) ^ (2 * u + 1) *
            ((1 - (p : ℚ)) * (((henselScaledPoly u).map (Int.castRingHom ℚ)).eval ((p : ℚ) / 8)) ^ 2 -
              (1 - (p : ℚ) / 2))
            = 8 * (1 - (p : ℚ)) *
                ((8 : ℚ) ^ u * ((henselScaledPoly u).map (Int.castRingHom ℚ)).eval ((p : ℚ) / 8)) ^ 2 -
              (8 : ℚ) ^ (2 * u + 1) * (1 - (p : ℚ) / 2) := by
          rw [mul_pow, ← pow_mul, mul_comm u 2, pow_succ']
          ring
        _ = 8 * (1 - (p : ℚ)) * (henselEval u p : ℚ) ^ 2 - (8 : ℚ) ^ (2 * u + 1) * (1 - (p : ℚ) / 2) := by
          rw [hG_eval]
        _ = -4 * ((2 * ((p : ℚ) - 1) * (henselEval u p : ℚ) ^ 2 -
              (8 : ℚ) ^ (2 * u) * ((p : ℚ) - 2))) := by
          rw [pow_succ']
          ring
    have hR_eval :
        (8 : ℚ) ^ (2 * u + 1) * ((D.map (Int.castRingHom ℚ)).eval ((p : ℚ) / 8)) =
        (p : ℚ) ^ (u + 1) * (R : ℚ) := by
      rw [hDeval, Finset.mul_sum]
      dsimp [R]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj_ge : u + 1 ≤ j := (Finset.mem_Ico.mp hj).1
      have hj_le : j ≤ 2 * u + 1 := Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hj).2
      have hp_pow : (p : ℚ) ^ j = (p : ℚ) ^ (u + 1) * (p : ℚ) ^ (j - (u + 1)) := by
        rw [← pow_add, Nat.add_sub_of_le hj_ge]
      have h8_pow : (8 : ℚ) ^ (2 * u + 1) = (8 : ℚ) ^ j * (8 : ℚ) ^ (2 * u + 1 - j) := by
        rw [← pow_add, Nat.add_sub_of_le hj_le]
      rw [div_pow, h8_pow, hp_pow]
      have h8j : (8 : ℚ) ^ j ≠ 0 := by positivity
      field_simp [h8j]
    have heq := hL_eval.symm.trans hR_eval
    push_cast
    linarith
  have hid_int :
      4 * (2 * ((p : ℤ) - 1) * henselEval u p ^ 2 - (8 : ℤ) ^ (2 * u) * ((p : ℤ) - 2)) =
      (p : ℤ) ^ (u + 1) * (-R) :=
    Int.cast_injective hid_rat
  have hdvd4 :
      (p : ℤ) ^ (u + 1) ∣
        4 * (2 * ((p : ℤ) - 1) * henselEval u p ^ 2 - (8 : ℤ) ^ (2 * u) * ((p : ℤ) - 2)) :=
    ⟨-R, hid_int⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hnot_dvd_4 : ¬ (p : ℤ) ∣ 4 := by
    intro h4
    have h4nat : p ∣ 2 ^ 2 := by simpa using Int.natCast_dvd_natCast.mp h4
    have hd2 : p ∣ 2 := hp.dvd_of_dvd_pow h4nat
    have h2 : p = 2 := (Nat.dvd_prime Nat.prime_two).mp hd2 |>.resolve_left hp.ne_one
    subst h2
    exact absurd hpo (by decide)
  have hcop4 : IsCoprime ((p : ℤ) ^ (u + 1)) 4 :=
    (hpZ.coprime_iff_not_dvd.mpr hnot_dvd_4).pow_left
  exact hcop4.dvd_of_dvd_mul_left hdvd4

/-- Unconditional exponential base cap `p < 8 ^ u` at any even prime-power component index. -/
theorem even_index_prime_lt_eight_pow_u {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    p < 8 ^ u := by
  by_contra! hge
  have hp8 : 8 ≤ p := le_trans (Nat.le_self_pow hu.ne' 8) hge
  have hsand := even_index_cofactor_archimedean_sandwich hp hpo hu hσq hplus
  have hsu : s < p ^ u := hsand.2.2.1
  have hus : p ^ u < 2 * s := hsand.2.2.2
  set P : ℤ := henselEval u (p : ℤ)
  have hP_rat : (P : ℚ) =
      (8 : ℚ) ^ u * ∑ k ∈ Finset.range (u + 1), henselRatCoeff k * (p : ℚ) ^ k := by
    simpa using henselEval_cast_rat u (p : ℤ)
  have hP_pos : 0 < P := by
    have hP_posQ : 0 < (P : ℚ) := by
      rw [hP_rat]
      refine mul_pos (by positivity) ?_
      refine Finset.sum_pos ?_ ⟨0, Finset.mem_range.mpr (Nat.succ_pos u)⟩
      intro k _
      exact mul_pos (henselRatCoeff_pos k) (by positivity)
    exact Int.cast_pos.mp hP_posQ
  have h2P_lt : 2 * P < (8 : ℤ) ^ u * (p : ℤ) ^ u := by
    have h2P_rat : 2 * (P : ℚ) < (8 : ℚ) ^ u * (p : ℚ) ^ u := by
      rw [hP_rat]
      have hsum_le :
          ∑ k ∈ Finset.range (u + 1), henselRatCoeff k * (p : ℚ) ^ k ≤
          1 + (1 / 4 : ℚ) * ∑ k ∈ Finset.Ico 1 (u + 1), (p : ℚ) ^ k := by
        rw [← Nat.Ico_zero_eq_range, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos u),
          pow_zero, henselRatCoeff_zero, mul_one, Finset.mul_sum]
        refine add_le_add le_rfl (Finset.sum_le_sum fun k hk => ?_)
        have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
        exact mul_le_mul_of_nonneg_right (henselRatCoeff_le_quarter hk1) (by positivity)
      have hgeom :
          ((p : ℚ) - 1) * ∑ k ∈ Finset.Ico 1 (u + 1), (p : ℚ) ^ k =
          (p : ℚ) ^ (u + 1) - (p : ℚ) := by
        have hg := mul_geom_sum (p : ℚ) (u + 1)
        have hsum_split :
            ∑ i ∈ Finset.range (u + 1), (p : ℚ) ^ i =
            1 + ∑ k ∈ Finset.Ico 1 (u + 1), (p : ℚ) ^ k := by
          rw [← Nat.Ico_zero_eq_range, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos u), pow_zero]
        rw [hsum_split] at hg
        linarith
      have hp_sub1_pos : (0 : ℚ) < (p : ℚ) - 1 := by
        have : (8 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp8
        linarith
      have hp_ge8Q : (8 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp8
      have hpu_ge_p : (p : ℚ) ≤ (p : ℚ) ^ u := by
        exact_mod_cast Nat.le_self_pow hu.ne' p
      have hpu_mul : 8 * (p : ℚ) ^ u ≤ (p : ℚ) ^ (u + 1) := by
        rw [pow_succ']
        exact mul_le_mul_of_nonneg_right hp_ge8Q (by positivity)
      have hineq :
          (1 + (1 / 4 : ℚ) * ∑ k ∈ Finset.Ico 1 (u + 1), (p : ℚ) ^ k) * ((p : ℚ) - 1) <
          ((1 / 2 : ℚ) * (p : ℚ) ^ u) * ((p : ℚ) - 1) := by
        have hL :
            (1 + (1 / 4 : ℚ) * ∑ k ∈ Finset.Ico 1 (u + 1), (p : ℚ) ^ k) * ((p : ℚ) - 1) =
            ((p : ℚ) - 1) + (1 / 4 : ℚ) * ((p : ℚ) ^ (u + 1) - (p : ℚ)) := by
          linarith [hgeom]
        have hR :
            ((1 / 2 : ℚ) * (p : ℚ) ^ u) * ((p : ℚ) - 1) =
            (1 / 2 : ℚ) * ((p : ℚ) ^ (u + 1) - (p : ℚ) ^ u) := by
          rw [pow_succ']
          ring
        rw [hL, hR]
        linarith
      have hsum_lt : ∑ k ∈ Finset.range (u + 1), henselRatCoeff k * (p : ℚ) ^ k <
          (1 / 2 : ℚ) * (p : ℚ) ^ u :=
        lt_of_le_of_lt hsum_le (lt_of_mul_lt_mul_right hineq hp_sub1_pos.le)
      have hmul := mul_lt_mul_of_pos_left hsum_lt (by positivity : (0 : ℚ) < (8 : ℚ) ^ u)
      linarith
    exact_mod_cast h2P_rat
  have hP_lt_pow : P < (p : ℤ) ^ (u + 1) := by
    have h8p : (8 : ℤ) ^ u * (p : ℤ) ^ u ≤ (p : ℤ) ^ (u + 1) := by
      have h8pZ : (8 : ℤ) ^ u ≤ (p : ℤ) := by exact_mod_cast hge
      rw [pow_succ']
      exact mul_le_mul_of_nonneg_right h8pZ (by positivity)
    linarith
  have hdvd_P := henselEval_mod_p_succ u hp hpo
  have hs_nat := even_index_twice_pred_mul_cofactor_sq hp hσq hplus
  have hs_int : 2 * ((p : ℤ) - 1) * (s : ℤ) ^ 2 - ((p : ℤ) - 2) = (p : ℤ) ^ (2 * u + 1) := by
    have hcast := congrArg (Nat.cast (R := ℤ)) hs_nat
    push_cast at hcast
    rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_sub (by omega : 2 ≤ p)] at hcast
    push_cast at hcast
    linarith
  have hdvd_s :
      (p : ℤ) ^ (u + 1) ∣
        2 * ((p : ℤ) - 1) * ((8 : ℤ) ^ u * (s : ℤ)) ^ 2 - (8 : ℤ) ^ (2 * u) * ((p : ℤ) - 2) := by
    have hid :
        2 * ((p : ℤ) - 1) * ((8 : ℤ) ^ u * (s : ℤ)) ^ 2 - (8 : ℤ) ^ (2 * u) * ((p : ℤ) - 2) =
        (8 : ℤ) ^ (2 * u) * (p : ℤ) ^ (2 * u + 1) := by
      calc
        2 * ((p : ℤ) - 1) * ((8 : ℤ) ^ u * (s : ℤ)) ^ 2 - (8 : ℤ) ^ (2 * u) * ((p : ℤ) - 2)
            = (8 : ℤ) ^ (2 * u) * (2 * ((p : ℤ) - 1) * (s : ℤ) ^ 2 - ((p : ℤ) - 2)) := by
          rw [mul_pow, ← pow_mul, mul_comm u 2]; ring
        _ = (8 : ℤ) ^ (2 * u) * (p : ℤ) ^ (2 * u + 1) := by rw [hs_int]
    rw [hid]
    exact dvd_mul_of_dvd_right (pow_dvd_pow (p : ℤ) (by omega)) _
  have hdvd_prod :
      (p : ℤ) ^ (u + 1) ∣
        ((8 : ℤ) ^ u * (s : ℤ) - P) *
          (2 * ((p : ℤ) - 1) * ((8 : ℤ) ^ u * (s : ℤ) + P)) := by
    have hfac :
        ((8 : ℤ) ^ u * (s : ℤ) - P) *
          (2 * ((p : ℤ) - 1) * ((8 : ℤ) ^ u * (s : ℤ) + P)) =
        (2 * ((p : ℤ) - 1) * ((8 : ℤ) ^ u * (s : ℤ)) ^ 2 - (8 : ℤ) ^ (2 * u) * ((p : ℤ) - 2)) -
        (2 * ((p : ℤ) - 1) * P ^ 2 - (8 : ℤ) ^ (2 * u) * ((p : ℤ) - 2)) := by ring
    rw [hfac]
    exact dvd_sub hdvd_s hdvd_P
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
  have hp_dvd_P_sub : (p : ℤ) ∣ P - (8 : ℤ) ^ u := by
    have hsplit : P - (8 : ℤ) ^ u =
        ∑ k ∈ Finset.Ico 1 (u + 1), henselScaledCoeff k * 8 ^ (u - k) * (p : ℤ) ^ k := by
      dsimp [P, henselEval]
      rw [← Nat.Ico_zero_eq_range, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos u),
        henselScaledCoeff_zero, pow_zero, Nat.sub_zero, one_mul, mul_one]
      ring
    rw [hsplit]
    refine Finset.dvd_sum fun k hk => ?_
    have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    exact dvd_mul_of_dvd_right (dvd_pow_self (p : ℤ) (by omega)) _
  have hnot_dvd_sum : ¬ (p : ℤ) ∣ (8 : ℤ) ^ u * (s : ℤ) + P := by
    intro hdiv
    have hid : 2 * (8 : ℤ) ^ u =
        ((8 : ℤ) ^ u * (s : ℤ) + P) - (8 : ℤ) ^ u * ((s : ℤ) - 1) - (P - (8 : ℤ) ^ u) := by
      ring
    have hd2u : (p : ℤ) ∣ 2 * (8 : ℤ) ^ u := by
      rw [hid]
      exact dvd_sub (dvd_sub hdiv (dvd_mul_of_dvd_right hp_dvd_s1 _)) hp_dvd_P_sub
    have hd2nat : p ∣ 2 ^ (3 * u + 1) := by
      have : ((2 ^ (3 * u + 1) : ℕ) : ℤ) = 2 * (8 : ℤ) ^ u := by
        push_cast
        rw [show (8 : ℤ) = 2 ^ 3 by norm_num, ← pow_mul, pow_succ']
      rw [← this] at hd2u
      exact Int.natCast_dvd_natCast.mp hd2u
    have hd2 : p ∣ 2 := hp.dvd_of_dvd_pow hd2nat
    have h2 : p = 2 := (Nat.dvd_prime Nat.prime_two).mp hd2 |>.resolve_left hp.ne_one
    subst h2
    exact absurd hpo (by decide)
  have hnot_dvd_coeff : ¬ (p : ℤ) ∣ 2 * ((p : ℤ) - 1) * ((8 : ℤ) ^ u * (s : ℤ) + P) := by
    intro hdiv
    rcases hpZ.dvd_or_dvd hdiv with h2p1 | hsum
    · exact hnot_dvd_2p1 h2p1
    · exact hnot_dvd_sum hsum
  have hcop : IsCoprime ((p : ℤ) ^ (u + 1)) (2 * ((p : ℤ) - 1) * ((8 : ℤ) ^ u * (s : ℤ) + P)) :=
    (hpZ.coprime_iff_not_dvd.mpr hnot_dvd_coeff).pow_left
  have hdvd_diff : (p : ℤ) ^ (u + 1) ∣ (8 : ℤ) ^ u * (s : ℤ) - P :=
    hcop.dvd_of_dvd_mul_right hdvd_prod
  have hs_posZ : (0 : ℤ) < (s : ℤ) := Int.natCast_pos.mpr hs.pos
  have h8s_pos : 0 < (8 : ℤ) ^ u * (s : ℤ) := by positivity
  have h8s_lt : (8 : ℤ) ^ u * (s : ℤ) < (p : ℤ) ^ (u + 1) := by
    have h1 : (8 : ℤ) ^ u * (s : ℤ) < (8 : ℤ) ^ u * (p : ℤ) ^ u := by
      have hsuZ : (s : ℤ) < (p : ℤ) ^ u := by exact_mod_cast hsu
      exact mul_lt_mul_of_pos_left hsuZ (by positivity)
    have h2 : (8 : ℤ) ^ u * (p : ℤ) ^ u ≤ (p : ℤ) ^ (u + 1) := by
      have hgeZ : (8 : ℤ) ^ u ≤ (p : ℤ) := by exact_mod_cast hge
      rw [pow_succ']
      exact mul_le_mul_of_nonneg_right hgeZ (by positivity)
    exact lt_of_lt_of_le h1 h2
  have heq : (8 : ℤ) ^ u * (s : ℤ) = P := by
    have h0 : (8 : ℤ) ^ u * (s : ℤ) - P = 0 := by
      rcases le_or_gt 0 ((8 : ℤ) ^ u * (s : ℤ) - P) with hnn | hneg
      · exact Int.eq_zero_of_dvd_of_nonneg_of_lt hnn (by linarith) hdvd_diff
      · have hopp := Int.eq_zero_of_dvd_of_nonneg_of_lt (by linarith) (by linarith)
          (dvd_neg.mpr hdvd_diff)
        linarith
    linarith
  have hlt_contra : 2 * (8 : ℤ) ^ u * (s : ℤ) < (8 : ℤ) ^ u * (p : ℤ) ^ u := by
    calc
      2 * (8 : ℤ) ^ u * (s : ℤ) = 2 * ((8 : ℤ) ^ u * (s : ℤ)) := by ring
      _ = 2 * P := by rw [heq]
      _ < (8 : ℤ) ^ u * (p : ℤ) ^ u := h2P_lt
  have h2s_lt : 2 * (s : ℤ) < (p : ℤ) ^ u := by
    have hpos8 : (0 : ℤ) < (8 : ℤ) ^ u := by positivity
    nlinarith
  have husZ : (p : ℤ) ^ u < 2 * (s : ℤ) := by exact_mod_cast hus
  linarith

end OddPerfect
