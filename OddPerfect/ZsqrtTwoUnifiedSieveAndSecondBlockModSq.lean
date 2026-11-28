module

public import OddPerfect.ZsqrtTwoInertPrimeOrderSieve
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Unified `ℤ√2` Legendre-Order Sieve & Second-Block Mod-`d ^ 2` Congruence
(`OddPerfect.ZsqrtTwoUnifiedSieveAndSecondBlockModSq`)

Combines the split-prime and inert-prime `ℤ√2` order sieves with the exact mod-`d ^ 2`
second-block cyclotomic congruence on exceptional Euler indices
`sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`, `d := (a + 1) / 2`):

1. `second_block_quotient_mod_d_sq`: proves
   `(z : ℤ) ^ 2 ≡ 1 + (d : ℤ) * (w : ℤ) ^ 2 [ZMOD (d : ℤ) ^ 2]` and deduces
   `¬ (d : ℤ) ^ 2 ∣ (z : ℤ) ^ 2 - 1`, `¬ d ^ 2 ∣ z - 1`, and `¬ d ^ 2 ∣ z + 1` whenever `¬ d ∣ w`.
2. `second_block_z_prime_divisors_one_mod_two_d`: proves `3 ≤ z`, `2 * d ∣ r - 1` for every
   prime factor `r` of `z`, and `2 * d + 1 ≤ z.minFac`.
3. `zsqrtTwo_fermat_unified_legendre_order_sieve`: unifies
   `zsqrtTwo_fermat_split_prime_order_obstruction` and
   `zsqrtTwo_fermat_inert_prime_order_obstruction` via `legendreSym r 2`.
4. `exceptional_euler_second_block_mod_sq_and_z_minFac_sieve`: bundles the full second-block
   mod-`d ^ 2` obstruction, `2 * d ∣ r - 1` factorization constraint, 16-prime `ℤ√2` sieves, and
   tightened `z.minFac` lower bounds for `d ∈ {17, 73, 241}`.
-/

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- Exact mod-`d ^ 2` second-block congruence
`(z : ℤ) ^ 2 ≡ 1 + (d : ℤ) * (w : ℤ) ^ 2 [ZMOD (d : ℤ) ^ 2]`, together with the non-divisibility
consequences `¬ (d : ℤ) ^ 2 ∣ (z : ℤ) ^ 2 - 1`, `¬ d ^ 2 ∣ z - 1`, and `¬ d ^ 2 ∣ z + 1`
when `¬ d ∣ w`. -/
theorem second_block_quotient_mod_d_sq {q d w z : ℕ}
    (hd_prime : d.Prime) (hd5 : 5 ≤ d) (hd_odd : Odd d)
    (hq1 : q + 1 = 2 * d * w ^ 2) (hdiv : (q ^ d + 1) / (q + 1) = d * z ^ 2) :
    (z : ℤ) ^ 2 ≡ 1 + (d : ℤ) * (w : ℤ) ^ 2 [ZMOD (d : ℤ) ^ 2] ∧
    (¬ d ∣ w → ¬ (d : ℤ) ^ 2 ∣ (z : ℤ) ^ 2 - 1 ∧ ¬ d ^ 2 ∣ z - 1 ∧ ¬ d ^ 2 ∣ z + 1) := by
  have hw_pos : 0 < w := by
    rcases eq_or_ne w 0 with rfl | hw0
    · simp at hq1
    · exact Nat.pos_of_ne_zero hw0
  have hd_pos : 0 < d := hd_prime.pos
  have hdvd_q1 : q + 1 ∣ q ^ d + 1 := by
    simpa using hd_odd.nat_add_dvd_pow_add_pow q 1
  have hmul_nat : (q + 1) * (d * z ^ 2) = q ^ d + 1 := by
    rw [← hdiv]
    exact Nat.mul_div_cancel' hdvd_q1
  have hz_pos : 0 < z := by
    rcases eq_or_ne z 0 with rfl | hz0
    · simp at hmul_nat
    · exact Nat.pos_of_ne_zero hz0
  let X : ℤ := (q + 1 : ℕ)
  have hX_eq : X = 2 * (d : ℤ) * (w : ℤ) ^ 2 := by
    dsimp [X]
    exact_mod_cast hq1
  have hX_ne : X ≠ 0 := by
    rw [hX_eq]
    positivity
  have hd_ne : (d : ℤ) ≠ 0 := by positivity
  have hq_eq : (q : ℤ) = X + (-1) := by
    dsimp [X]
    ring
  let f : ℕ → ℤ := fun j => X ^ j * (-1) ^ (d - j) * (d.choose j : ℤ)
  have hbin : ((q ^ d + 1 : ℕ) : ℤ) = (∑ j ∈ range (d + 1), f j) + 1 := by
    push_cast
    rw [hq_eq, add_pow]
  have hsplit0 : (∑ j ∈ range (d + 1), f j) = (∑ j ∈ range d, f (j + 1)) + f 0 :=
    Finset.sum_range_succ' f d
  have hf0 : f 0 + 1 = 0 := by
    simp [f, hd_odd.neg_one_pow]
  have hd_sub1 : d = (d - 1) + 1 := by omega
  have hsplit1 : (∑ j ∈ range d, f (j + 1)) = (∑ j ∈ range (d - 1), f (j + 2)) + f 1 := by
    conv_lhs => rw [hd_sub1]
    exact Finset.sum_range_succ' (fun j => f (j + 1)) (d - 1)
  have hf1 : f 1 = X * (d : ℤ) := by
    dsimp [f]
    have hdeven : Even (d - 1) := by
      obtain ⟨k, hk⟩ := hd_odd
      exact ⟨k, by omega⟩
    rw [pow_one, Nat.choose_one_right, hdeven.neg_one_pow, mul_one]
  have hd_sub2 : d - 1 = (d - 2) + 1 := by omega
  have hsplit2 : (∑ j ∈ range (d - 1), f (j + 2)) =
      (∑ j ∈ range (d - 2), f (j + 3)) + f 2 := by
    conv_lhs => rw [hd_sub2]
    exact Finset.sum_range_succ' (fun j => f (j + 2)) (d - 2)
  have hf2 : f 2 = -(X * (d : ℤ) * ((d : ℤ) * ((d : ℤ) - 1) * (w : ℤ) ^ 2)) := by
    dsimp [f]
    have hd2_odd : Odd (d - 2) := by
      obtain ⟨k, hk⟩ := hd_odd
      exact ⟨k - 1, by omega⟩
    have h2ch : 2 * d.choose 2 = d * (d - 1) := by
      rw [Nat.choose_two_right]
      have heven : 2 ∣ d * (d - 1) := by
        obtain ⟨k, hk⟩ := hd_odd
        refine ⟨d * k, ?_⟩
        rw [show d - 1 = 2 * k by omega]
        ring
      exact Nat.mul_div_cancel' heven
    have h2ch_z : 2 * (d.choose 2 : ℤ) = (d : ℤ) * ((d : ℤ) - 1) := by
      have : (2 * d.choose 2 : ℤ) = ((d * (d - 1) : ℕ) : ℤ) := by exact_mod_cast h2ch
      push_cast [show 1 ≤ d by omega] at this
      exact this
    rw [hd2_odd.neg_one_pow]
    calc
      X ^ 2 * (-1) * (d.choose 2 : ℤ)
          = -(X * X * (d.choose 2 : ℤ)) := by ring
      _ = -(X * (2 * (d : ℤ) * (w : ℤ) ^ 2) * (d.choose 2 : ℤ)) := by rw [← hX_eq]
      _ = -(X * (d : ℤ) * (w : ℤ) ^ 2 * (2 * (d.choose 2 : ℤ))) := by ring
      _ = -(X * (d : ℤ) * ((d : ℤ) * ((d : ℤ) - 1) * (w : ℤ) ^ 2)) := by
        rw [h2ch_z]
        ring
  have hdvd_tail : X * (d : ℤ) ^ 3 ∣ ∑ j ∈ range (d - 2), f (j + 3) := by
    apply Finset.dvd_sum
    intro j _
    dsimp [f]
    by_cases hj0 : j = 0
    · subst hj0
      simp only [zero_add]
      have hd_choose3 : d ∣ d.choose 3 :=
        Nat.Prime.dvd_choose_self hd_prime (by decide : 3 ≠ 0) (by omega : 3 < d)
      obtain ⟨c, hc⟩ := hd_choose3
      have hc_z : (d.choose 3 : ℤ) = (d : ℤ) * (c : ℤ) := by exact_mod_cast hc
      have hX3 : X ^ 3 = X * (4 * (d : ℤ) ^ 2 * (w : ℤ) ^ 4) := by
        calc
          X ^ 3 = X * X ^ 2 := by ring
          _ = X * (2 * (d : ℤ) * (w : ℤ) ^ 2) ^ 2 := by rw [← hX_eq]
          _ = X * (4 * (d : ℤ) ^ 2 * (w : ℤ) ^ 4) := by ring
      refine ⟨4 * (w : ℤ) ^ 4 * (-1) ^ (d - 3) * (c : ℤ), ?_⟩
      rw [hX3, hc_z]
      ring
    · have hj1 : 1 ≤ j := Nat.pos_of_ne_zero hj0
      have hpow : X ^ (j + 3) = X * X ^ 3 * X ^ (j - 1) := by
        rw [show j + 3 = 1 + 3 + (j - 1) by omega, pow_add, pow_add, pow_one]
      have hX3 : X ^ 3 = (d : ℤ) ^ 3 * (8 * (w : ℤ) ^ 6) := by
        rw [hX_eq]
        ring
      refine ⟨8 * (w : ℤ) ^ 6 * X ^ (j - 1) * (-1) ^ (d - (j + 3)) * (d.choose (j + 3) : ℤ), ?_⟩
      rw [hpow, hX3]
      ring
  obtain ⟨K, hK⟩ := hdvd_tail
  have hmul_z : ((q ^ d + 1 : ℕ) : ℤ) = X * (d : ℤ) * (z : ℤ) ^ 2 := by
    have hz_eq : ((q + 1) * (d * z ^ 2) : ℤ) = ((q ^ d + 1 : ℕ) : ℤ) := by
      exact_mod_cast hmul_nat
    dsimp [X]
    linarith
  have hsum_eq : X * (d : ℤ) * (z : ℤ) ^ 2 =
      X * (d : ℤ) * (1 - (d : ℤ) * ((d : ℤ) - 1) * (w : ℤ) ^ 2 + (d : ℤ) ^ 2 * K) := by
    rw [← hmul_z, hbin, hsplit0, add_assoc, hf0, add_zero, hsplit1, hsplit2, hf1, hf2, hK]
    ring
  have hz2_eq : (z : ℤ) ^ 2 =
      1 - (d : ℤ) * ((d : ℤ) - 1) * (w : ℤ) ^ 2 + (d : ℤ) ^ 2 * K :=
    mul_left_cancel₀ (mul_ne_zero hX_ne hd_ne) hsum_eq
  have hmod : (z : ℤ) ^ 2 ≡ 1 + (d : ℤ) * (w : ℤ) ^ 2 [ZMOD (d : ℤ) ^ 2] := by
    refine Int.modEq_iff_dvd.mpr ⟨(w : ℤ) ^ 2 - K, ?_⟩
    rw [hz2_eq]
    ring
  refine ⟨hmod, ?_⟩
  intro hndvd_w
  have hndvd_z2 : ¬ (d : ℤ) ^ 2 ∣ (z : ℤ) ^ 2 - 1 := by
    intro hd2_z2
    have h0 : (z : ℤ) ^ 2 - 1 ≡ 0 [ZMOD (d : ℤ) ^ 2] := Int.modEq_zero_iff_dvd.mpr hd2_z2
    have hsub : (z : ℤ) ^ 2 - 1 ≡ (d : ℤ) * (w : ℤ) ^ 2 [ZMOD (d : ℤ) ^ 2] := by
      simpa using hmod.sub_right 1
    have hd2_dw2 : (d : ℤ) ^ 2 ∣ (d : ℤ) * (w : ℤ) ^ 2 :=
      Int.modEq_zero_iff_dvd.mp (hsub.symm.trans h0)
    obtain ⟨c, hc⟩ := hd2_dw2
    have hd_dvd_w2_z : (d : ℤ) ∣ (w : ℤ) ^ 2 := by
      refine ⟨c, ?_⟩
      apply mul_left_cancel₀ hd_ne
      calc
        (d : ℤ) * (w : ℤ) ^ 2 = (d : ℤ) ^ 2 * c := hc
        _ = (d : ℤ) * ((d : ℤ) * c) := by ring
    have hd_dvd_w2 : d ∣ w ^ 2 := Int.natCast_dvd_natCast.mp hd_dvd_w2_z
    exact hndvd_w (hd_prime.dvd_of_dvd_pow hd_dvd_w2)
  refine ⟨hndvd_z2, ?_, ?_⟩
  · intro hd2_sub
    apply hndvd_z2
    have hd2_sub_z : (d : ℤ) ^ 2 ∣ (z : ℤ) - 1 := by
      have hz_ge : 1 ≤ z := hz_pos
      have hcast : (((z - 1 : ℕ) : ℤ)) = (z : ℤ) - 1 := by omega
      rw [← hcast]
      exact Int.natCast_dvd_natCast.mpr hd2_sub
    have hfac : (z : ℤ) ^ 2 - 1 = ((z : ℤ) - 1) * ((z : ℤ) + 1) := by ring
    rw [hfac]
    exact dvd_mul_of_dvd_left hd2_sub_z _
  · intro hd2_add
    apply hndvd_z2
    have hd2_add_z : (d : ℤ) ^ 2 ∣ (z : ℤ) + 1 := by
      exact_mod_cast hd2_add
    have hfac : (z : ℤ) ^ 2 - 1 = ((z : ℤ) - 1) * ((z : ℤ) + 1) := by ring
    rw [hfac]
    exact dvd_mul_of_dvd_right hd2_add_z _

/-- Every prime divisor `r` of `z` in `(q ^ d + 1) / (q + 1) = d * z ^ 2` satisfies
`2 * d ∣ r - 1`, giving `3 ≤ z` and `2 * d + 1 ≤ z.minFac`. -/
theorem second_block_z_prime_divisors_one_mod_two_d {q d w z : ℕ}
    (hq : q.Prime) (hd : d.Prime) (hd5 : 5 ≤ d) (hd_odd : Odd d)
    (hw : 0 < w) (hz_odd : Odd z)
    (hq1 : q + 1 = 2 * d * w ^ 2) (hdiv : (q ^ d + 1) / (q + 1) = d * z ^ 2)
    (hcop : Nat.Coprime w z) (hdz : ¬ d ∣ z) :
    3 ≤ z ∧ (∀ r ∈ z.primeFactors, 2 * d ∣ r - 1) ∧ 2 * d + 1 ≤ z.minFac := by
  have hdvd_q1 : q + 1 ∣ q ^ d + 1 := by
    simpa using hd_odd.nat_add_dvd_pow_add_pow q 1
  have hmul_nat : (q + 1) * (d * z ^ 2) = q ^ d + 1 := by
    rw [← hdiv]
    exact Nat.mul_div_cancel' hdvd_q1
  have hw2_ge : 1 ≤ w ^ 2 := Nat.one_le_pow 2 w hw
  have hq_ge : 2 * d ≤ q + 1 := by
    calc
      2 * d = 2 * d * 1 := by ring
      _ ≤ 2 * d * w ^ 2 := Nat.mul_le_mul_left (2 * d) hw2_ge
      _ = q + 1 := hq1.symm
  have hqd_ge : q ^ 2 ≤ q ^ d := Nat.pow_le_pow_right hq.pos (by omega : 2 ≤ d)
  have hq_gt : (q + 1) * d < q ^ d + 1 := by
    have hq_sub : 4 ≤ q - d := by omega
    have h1 : d < q * (q - d) := by
      calc
        d < (2 * d - 1) * 4 := by omega
        _ ≤ q * (q - d) := Nat.mul_le_mul (by omega) hq_sub
    have h2 : q ^ 2 = q * (q - d) + q * d := by
      calc
        q ^ 2 = q * q := by ring
        _ = q * ((q - d) + d) := by rw [Nat.sub_add_cancel (by omega : d ≤ q)]
        _ = q * (q - d) + q * d := by ring
    have hmul_qd : (q + 1) * d = q * d + d := by ring
    omega
  have hz_gt1 : 1 < z := by
    have hdz2 : d < d * z ^ 2 := by
      nlinarith [hmul_nat, hq_gt]
    have hz2_gt1 : 1 < z ^ 2 := by
      nlinarith [hd.pos, hdz2]
    nlinarith
  have hz_ge3 : 3 ≤ z := by
    obtain ⟨k, hk⟩ := hz_odd
    omega
  have hr_dvd : ∀ r ∈ z.primeFactors, 2 * d ∣ r - 1 := by
    intro r hr
    have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hrz : r ∣ z := Nat.dvd_of_mem_primeFactors hr
    have hr_ne2 : r ≠ 2 := by
      rintro rfl
      have : ¬ Odd z := Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr hrz)
      exact this hz_odd
    have hr_ne_d : r ≠ d := by
      rintro rfl
      exact hdz hrz
    have hnrw : ¬ r ∣ w := by
      intro hrw
      have : r ∣ Nat.gcd w z := Nat.dvd_gcd hrw hrz
      rw [hcop] at this
      exact hr_prime.not_dvd_one this
    have hnrq1 : ¬ r ∣ q + 1 := by
      intro hrq1
      rw [hq1] at hrq1
      rcases hr_prime.dvd_mul.mp hrq1 with h2d | hrw2
      · rcases hr_prime.dvd_mul.mp h2d with hr2 | hrd
        · have hle : r ≤ 2 := Nat.le_of_dvd (by decide) hr2
          have := hr_prime.two_le
          omega
        · have h1d := (hd.eq_one_or_self_of_dvd r hrd).resolve_left hr_prime.ne_one
          exact hr_ne_d h1d
      · exact hnrw (hr_prime.dvd_of_dvd_pow hrw2)
    have : Fact r.Prime := ⟨hr_prime⟩
    have hr_qd1 : r ∣ q ^ d + 1 :=
      hmul_nat ▸ dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (hrz.trans (dvd_pow_self z (by decide))) d) (q + 1)
    have hqd_zmod : (q : ZMod r) ^ d = -1 := by
      have h0 : ((q ^ d + 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff (q ^ d + 1) r).mpr hr_qd1
      push_cast at h0
      exact eq_neg_of_add_eq_zero_left h0
    have hq_ne0 : (q : ZMod r) ≠ 0 := by
      intro hq0
      rw [hq0, zero_pow hd.pos.ne'] at hqd_zmod
      have h10 : ((1 : ℕ) : ZMod r) = 0 := by
        push_cast
        exact neg_eq_zero.mp hqd_zmod.symm
      exact hr_prime.not_dvd_one ((ZMod.natCast_eq_zero_iff 1 r).mp h10)
    have hq_2d : (q : ZMod r) ^ (2 * d) = 1 := by
      rw [mul_comm, pow_mul, hqd_zmod]
      norm_num
    have hord_dvd : orderOf (q : ZMod r) ∣ 2 * d := orderOf_dvd_of_pow_eq_one hq_2d
    have h2_ne0 : (2 : ZMod r) ≠ 0 := by
      intro h20
      have hdvd2 : r ∣ 2 := (ZMod.natCast_eq_zero_iff 2 r).mp h20
      have hle2 : r ≤ 2 := Nat.le_of_dvd (by decide) hdvd2
      have := hr_prime.two_le
      omega
    have hord_ndvd_d : ¬ orderOf (q : ZMod r) ∣ d := by
      intro hdvd
      have h1 : (q : ZMod r) ^ d = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
      have h1m1 : (1 : ZMod r) = -1 := h1.symm.trans hqd_zmod
      have h20 : (2 : ZMod r) = 0 := by
        calc
          (2 : ZMod r) = 1 + 1 := by norm_num
          _ = 1 + (-1) := by nth_rw 2 [h1m1]
          _ = 0 := by ring
      exact h2_ne0 h20
    have hord_ndvd_2 : ¬ orderOf (q : ZMod r) ∣ 2 := by
      intro hdvd
      have h2 : (q : ZMod r) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
      rcases sq_eq_one_iff.mp h2 with hq1_z | hqm1_z
      · have h1 : (q : ZMod r) ^ d = 1 := by rw [hq1_z, one_pow]
        have h1m1 : (1 : ZMod r) = -1 := h1.symm.trans hqd_zmod
        have h20 : (2 : ZMod r) = 0 := by
          calc
            (2 : ZMod r) = 1 + 1 := by norm_num
            _ = 1 + (-1) := by nth_rw 2 [h1m1]
            _ = 0 := by ring
        exact h2_ne0 h20
      · have h0 : ((q + 1 : ℕ) : ZMod r) = 0 := by
          push_cast
          rw [hqm1_z]
          ring
        exact hnrq1 ((ZMod.natCast_eq_zero_iff (q + 1) r).mp h0)
    have hd_dvd_ord : d ∣ orderOf (q : ZMod r) := by
      by_contra hndvd
      have hcop_ord : Nat.Coprime (orderOf (q : ZMod r)) d :=
        (hd.coprime_iff_not_dvd.mpr hndvd).symm
      exact hord_ndvd_2 (hcop_ord.dvd_of_dvd_mul_right hord_dvd)
    obtain ⟨k, hk⟩ := hd_dvd_ord
    have hk_dvd2 : k ∣ 2 := by
      have : d * k ∣ d * 2 := by
        rw [← hk, mul_comm d 2]
        exact hord_dvd
      exact Nat.dvd_of_mul_dvd_mul_left hd.pos this
    have hk_eq2 : k = 2 := by
      have hk_le2 : k ≤ 2 := Nat.le_of_dvd (by decide) hk_dvd2
      have hk_ne0 : k ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hk
        rw [hk] at hord_dvd
        obtain ⟨c, hc⟩ := hord_dvd
        simp at hc
        omega
      have hk_ne1 : k ≠ 1 := by
        rintro rfl
        rw [mul_one] at hk
        exact hord_ndvd_d (hk ▸ dvd_refl d)
      omega
    have hord_eq : orderOf (q : ZMod r) = 2 * d := by
      rw [hk, hk_eq2, mul_comm]
    rw [← hord_eq]
    exact ZMod.orderOf_dvd_card_sub_one hq_ne0
  refine ⟨hz_ge3, hr_dvd, ?_⟩
  have hmin_mem : z.minFac ∈ z.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd z, by omega⟩
  have h2d_dvd_min : 2 * d ∣ z.minFac - 1 := hr_dvd z.minFac hmin_mem
  have hmin_ge2 : 2 ≤ z.minFac := (Nat.minFac_prime (by omega)).two_le
  have h2d_le_min : 2 * d ≤ z.minFac - 1 := Nat.le_of_dvd (by omega) h2d_dvd_min
  omega

/-- Unified `ℤ√2` Legendre-order sieve on `q ^ d + 1 = 2 * y ^ 2`: for any odd prime `r`,
rules out `r ∣ y` under either the split condition (`legendreSym r 2 = 1`, `d ∣ r - 1`,
`silverUnit ^ ((r - 1) / d) ≢ 1 [ZMOD r]`) or the inert condition (`legendreSym r 2 = -1`,
`d ∣ r + 1`, `¬ (r : ℤ) ∣ (silverUnit ^ ((r + 1) / d)).im`). -/
theorem zsqrtTwo_fermat_unified_legendre_order_sieve {q d y r : ℕ}
    (hq : q.Prime) (hd : d.Prime) (hd8 : d % 8 = 1)
    (hpow : q ^ d + 1 = 2 * y ^ 2) {k : ℤ} {α : ℤ√2}
    (hk1 : 1 ≤ |k|) (h2k : 2 * |k| ≤ (d : ℤ) - 1)
    (hz : (⟨1, (y : ℤ)⟩ : ℤ√2) = ((silverUnit ^ k : (ℤ√2)ˣ) : ℤ√2) * α ^ d)
    (hnorm : α.norm = (if Even k then -(q : ℤ) else (q : ℤ)))
    [Fact r.Prime] (hr2 : r ≠ 2)
    (hcond :
      (legendreSym r 2 = 1 ∧ d ∣ r - 1 ∧
        ¬ ((r : ℤ) ∣ (((silverUnit ^ ((r - 1) / d) : (ℤ√2)ˣ) : ℤ√2).re - 1) ∧
           (r : ℤ) ∣ (((silverUnit ^ ((r - 1) / d) : (ℤ√2)ˣ) : ℤ√2).im))) ∨
      (legendreSym r 2 = -1 ∧ d ∣ r + 1 ∧
        ¬ (r : ℤ) ∣ (((silverUnit ^ ((r + 1) / d) : (ℤ√2)ˣ) : ℤ√2).im))) :
    ¬ r ∣ y := by
  have hr_prime : r.Prime := Fact.out
  have hr_mod2 : r % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two hr_prime).mpr hr2
  rcases hcond with ⟨hleg, hdr, hne1⟩ | ⟨hleg, hdr, hne0⟩
  · have h2_ne0 : ((2 : ℕ) : ZMod r) ≠ 0 := by
      intro h0
      have hdvd2 : r ∣ 2 := (ZMod.natCast_eq_zero_iff 2 r).mp h0
      have hle2 : r ≤ 2 := Nat.le_of_dvd (by decide) hdvd2
      have := hr_prime.two_le
      omega
    have hsq : IsSquare (2 : ZMod r) := (legendreSym.eq_one_iff' (p := r) h2_ne0).mp hleg
    have hr8 : r % 8 = 1 ∨ r % 8 = 7 := (ZMod.exists_sq_eq_two_iff hr2).mp hsq
    exact zsqrtTwo_fermat_split_prime_order_obstruction hq hd hd8 hpow hk1 h2k hz hnorm
      hr_prime hr8 hdr hne1
  · have hnsq : ¬ IsSquare (2 : ZMod r) := (legendreSym.eq_neg_one_iff' (p := r)).mp hleg
    have hnot17 : ¬ (r % 8 = 1 ∨ r % 8 = 7) := (ZMod.exists_sq_eq_two_iff hr2).not.mp hnsq
    have hr8 : r % 8 = 3 ∨ r % 8 = 5 := by omega
    exact zsqrtTwo_fermat_inert_prime_order_obstruction hq hd hd8 hpow hk1 h2k hz hnorm
      hr_prime hr8 hdr hne0

/-- Unified second-block mod-`d ^ 2` obstruction, `2 * d ∣ r - 1` factorization constraint,
16-prime `ℤ√2` sieves, and tightened `z.minFac` lower bounds on
`sigma 1 (m ^ 2) / q ^ a = l * t ^ 2` (`a > 1`, `l.Prime`, `d := (a + 1) / 2`). -/
theorem exceptional_euler_second_block_mod_sq_and_z_minFac_sieve
    {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    let d := (a + 1) / 2
    ∃ y w z : ℕ,
      0 < y ∧ 0 < w ∧ 3 ≤ z ∧ Odd w ∧ Odd z ∧ Nat.Coprime w z ∧
      y = d * w * z ∧ q + 1 = 2 * d * w ^ 2 ∧ (q ^ d + 1) / (q + 1) = d * z ^ 2 ∧
      q ^ d + 1 = 2 * y ^ 2 ∧
      (z : ℤ) ^ 2 ≡ 1 + (d : ℤ) * (w : ℤ) ^ 2 [ZMOD (d : ℤ) ^ 2] ∧
      (d ∈ ({17, 41, 73, 89, 97, 113, 137, 193, 233, 241} : Finset ℕ) →
        ¬ (d : ℤ) ^ 2 ∣ (z : ℤ) ^ 2 - 1 ∧ ¬ d ^ 2 ∣ z - 1 ∧ ¬ d ^ 2 ∣ z + 1) ∧
      (∀ r ∈ z.primeFactors, 2 * d ∣ r - 1) ∧ 2 * d + 1 ≤ z.minFac ∧
      (d = 17 → 239 ≤ z.minFac ∧ 239 ≤ z ∧
        ∀ r ∈ ({67, 101, 103, 137, 373, 409, 509, 647, 883, 919, 953, 1019, 1291, 1327, 1361, 1427} : Finset ℕ),
          ¬ r ∣ y ∧ ¬ r ∣ w ∧ ¬ r ∣ z) ∧
      (d = 73 → 293 ≤ z.minFac ∧ 293 ≤ z ∧
        ∀ r ∈ ({439, 1021, 1459, 1607, 1753, 3359, 3943, 4673, 5693, 6131, 6277, 6863, 7883, 8467, 8761, 9781} : Finset ℕ),
          ¬ r ∣ y ∧ ¬ r ∣ w ∧ ¬ r ∣ z) ∧
      (d = 241 → 2411 ≤ z.minFac ∧ 2411 ≤ z ∧
        ∀ r ∈ ({1447, 3373, 5303, 7229, 9157, 11087, 16871, 18797, 22171, 26993, 28439, 28921, 30367, 33739, 45307, 47717} : Finset ℕ),
          ¬ r ∣ y ∧ ¬ r ∣ w ∧ ¬ r ∣ z) := by
  intro d
  obtain ⟨hd_prime, _, hd8, _, _, _, _⟩ :=
    exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
  change d.Prime at hd_prime
  change d % 8 = 1 at hd8
  have hd_odd : Odd d := Nat.odd_iff.mpr (by omega)
  have hd5 : 5 ≤ d := by
    have := hd_prime.two_le
    omega
  obtain ⟨y, _, _, hy_pos, _, hpow, _, _, _, _, _, _, h_pell_ndvd⟩ :=
    exceptional_euler_pell_fermat_quotient_profile hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨w, z, _, hw_odd, hz_odd, _, hq1, hdiv, hqd1, _, hcop, hdz, _⟩ :=
    exceptional_euler_second_block_exact_square hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨y1, w1, z1, _, _, _, hy1_dwz, hq1_1, hpow1, _, hs17, hs73, hs241⟩ :=
    exceptional_euler_split_prime_y_sieve hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨y2, w2, z2, _, _, _, hy2_dwz, hq1_2, hpow2, _, hi17, hi73, hi241⟩ :=
    exceptional_euler_inert_prime_y_sieve hN ho hq hq4 ha4 ha hqm hform hl hi
  have hw_pos : 0 < w := by
    rcases eq_or_ne w 0 with rfl | hw0
    · simp at hq1
    · exact Nat.pos_of_ne_zero hw0
  have hy_dwz : y = d * w * z := by
    have h2 : 2 * y ^ 2 = 2 * (d * w * z) ^ 2 := hpow.symm.trans hqd1
    have hsq : y ^ 2 = (d * w * z) ^ 2 := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h2
    exact (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp hsq
  have hy1_eq : y1 = y := by
    have h2 : 2 * y1 ^ 2 = 2 * y ^ 2 := hpow1.symm.trans hpow
    have hsq : y1 ^ 2 = y ^ 2 := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h2
    exact (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp hsq
  have hw1_eq : w1 = w := by
    have h2 : 2 * d * w1 ^ 2 = 2 * d * w ^ 2 := hq1_1.symm.trans hq1
    have hsq : w1 ^ 2 = w ^ 2 := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 * d) h2
    exact (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp hsq
  have hz1_eq : z1 = z := by
    have hmul : (d * w) * z1 = (d * w) * z := by
      calc
        (d * w) * z1 = d * w1 * z1 := by rw [hw1_eq]
        _ = y1 := hy1_dwz.symm
        _ = y := hy1_eq
        _ = d * w * z := hy_dwz
    exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < d * w) hmul
  have hy2_eq : y2 = y := by
    have h2 : 2 * y2 ^ 2 = 2 * y ^ 2 := hpow2.symm.trans hpow
    have hsq : y2 ^ 2 = y ^ 2 := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h2
    exact (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp hsq
  have hw2_eq : w2 = w := by
    have h2 : 2 * d * w2 ^ 2 = 2 * d * w ^ 2 := hq1_2.symm.trans hq1
    have hsq : w2 ^ 2 = w ^ 2 := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 * d) h2
    exact (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp hsq
  have hz2_eq : z2 = z := by
    have hmul : (d * w) * z2 = (d * w) * z := by
      calc
        (d * w) * z2 = d * w2 * z2 := by rw [hw2_eq]
        _ = y2 := hy2_dwz.symm
        _ = y := hy2_eq
        _ = d * w * z := hy_dwz
    exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < d * w) hmul
  rw [hy1_eq, hw1_eq, hz1_eq] at hs17 hs73 hs241
  rw [hy2_eq, hw2_eq, hz2_eq] at hi17 hi73 hi241
  obtain ⟨hmod_z2, hndvd_z2_of_w⟩ :=
    second_block_quotient_mod_d_sq hd_prime hd5 hd_odd hq1 hdiv
  obtain ⟨hz_ge3, hpf_dvd, hmin_ge⟩ :=
    second_block_z_prime_divisors_one_mod_two_d hq hd_prime hd5 hd_odd hw_pos hz_odd hq1 hdiv
      hcop hdz
  have h16_17 : d = 17 →
      ∀ r ∈ ({67, 101, 103, 137, 373, 409, 509, 647, 883, 919, 953, 1019, 1291, 1327, 1361, 1427} : Finset ℕ),
        ¬ r ∣ y ∧ ¬ r ∣ w ∧ ¬ r ∣ z := by
    intro hd17 r hr
    fin_cases hr
    · exact hi17 hd17 67 (by decide)
    · exact hi17 hd17 101 (by decide)
    · exact hs17 hd17 103 (by decide)
    · exact hs17 hd17 137 (by decide)
    · exact hi17 hd17 373 (by decide)
    · exact hs17 hd17 409 (by decide)
    · exact hi17 hd17 509 (by decide)
    · exact hs17 hd17 647 (by decide)
    · exact hi17 hd17 883 (by decide)
    · exact hs17 hd17 919 (by decide)
    · exact hs17 hd17 953 (by decide)
    · exact hi17 hd17 1019 (by decide)
    · exact hi17 hd17 1291 (by decide)
    · exact hs17 hd17 1327 (by decide)
    · exact hs17 hd17 1361 (by decide)
    · exact hi17 hd17 1427 (by decide)
  have h16_73 : d = 73 →
      ∀ r ∈ ({439, 1021, 1459, 1607, 1753, 3359, 3943, 4673, 5693, 6131, 6277, 6863, 7883, 8467, 8761, 9781} : Finset ℕ),
        ¬ r ∣ y ∧ ¬ r ∣ w ∧ ¬ r ∣ z := by
    intro hd73 r hr
    fin_cases hr
    · exact hs73 hd73 439 (by decide)
    · exact hi73 hd73 1021 (by decide)
    · exact hi73 hd73 1459 (by decide)
    · exact hs73 hd73 1607 (by decide)
    · exact hs73 hd73 1753 (by decide)
    · exact hs73 hd73 3359 (by decide)
    · exact hs73 hd73 3943 (by decide)
    · exact hs73 hd73 4673 (by decide)
    · exact hi73 hd73 5693 (by decide)
    · exact hi73 hd73 6131 (by decide)
    · exact hi73 hd73 6277 (by decide)
    · exact hs73 hd73 6863 (by decide)
    · exact hi73 hd73 7883 (by decide)
    · exact hi73 hd73 8467 (by decide)
    · exact hs73 hd73 8761 (by decide)
    · exact hi73 hd73 9781 (by decide)
  have h16_241 : d = 241 →
      ∀ r ∈ ({1447, 3373, 5303, 7229, 9157, 11087, 16871, 18797, 22171, 26993, 28439, 28921, 30367, 33739, 45307, 47717} : Finset ℕ),
        ¬ r ∣ y ∧ ¬ r ∣ w ∧ ¬ r ∣ z := by
    intro hd241 r hr
    fin_cases hr
    · exact hs241 hd241 1447 (by decide)
    · exact hi241 hd241 3373 (by decide)
    · exact hs241 hd241 5303 (by decide)
    · exact hi241 hd241 7229 (by decide)
    · exact hi241 hd241 9157 (by decide)
    · exact hs241 hd241 11087 (by decide)
    · exact hs241 hd241 16871 (by decide)
    · exact hi241 hd241 18797 (by decide)
    · exact hi241 hd241 22171 (by decide)
    · exact hs241 hd241 26993 (by decide)
    · exact hs241 hd241 28439 (by decide)
    · exact hs241 hd241 28921 (by decide)
    · exact hs241 hd241 30367 (by decide)
    · exact hi241 hd241 33739 (by decide)
    · exact hi241 hd241 45307 (by decide)
    · exact hi241 hd241 47717 (by decide)
  have hmin_prime : z.minFac.Prime := Nat.minFac_prime (by omega)
  have hmin_dvd : z.minFac ∣ z := Nat.minFac_dvd z
  have hmin_mem : z.minFac ∈ z.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hmin_prime, hmin_dvd, by omega⟩
  have hmin_le_z : z.minFac ≤ z := Nat.minFac_le (by omega)
  refine ⟨y, w, z, hy_pos, hw_pos, hz_ge3, hw_odd, hz_odd, hcop, hy_dwz, hq1, hdiv, hpow,
    hmod_z2, ?_, hpf_dvd, hmin_ge, ?_, ?_, ?_⟩
  · intro hd_mem
    have hndvd_q1 : ¬ d ^ 2 ∣ q + 1 := (h_pell_ndvd hd_mem).2
    have hndvd_w : ¬ d ∣ w := by
      intro hdw
      apply hndvd_q1
      change q + 1 = 2 * d * w ^ 2 at hq1
      rw [hq1]
      obtain ⟨k, hk⟩ := hdw
      refine ⟨2 * d * k ^ 2, ?_⟩
      rw [hk]
      ring
    exact hndvd_z2_of_w hndvd_w
  · intro hd17
    have h34 : 34 ∣ z.minFac - 1 := by simpa [hd17] using hpf_dvd z.minFac hmin_mem
    have hmin_ge35 : 35 ≤ z.minFac := by simpa [hd17] using hmin_ge
    have hmin_ge239 : 239 ≤ z.minFac := by
      by_contra hlt
      obtain ⟨k, hk⟩ := h34
      have hk_mem : k ∈ Finset.Icc 1 6 := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hmin_eq : z.minFac = 34 * k + 1 := by omega
      fin_cases hk_mem
      · rw [hmin_eq] at hmin_prime; norm_num at hmin_prime
      · rw [hmin_eq] at hmin_prime; norm_num at hmin_prime
      · have h103 : z.minFac = 103 := by omega
        exact (h16_17 hd17 103 (by decide)).2.2 (h103 ▸ hmin_dvd)
      · have h137 : z.minFac = 137 := by omega
        exact (h16_17 hd17 137 (by decide)).2.2 (h137 ▸ hmin_dvd)
      · rw [hmin_eq] at hmin_prime; norm_num at hmin_prime
      · rw [hmin_eq] at hmin_prime; norm_num at hmin_prime
    exact ⟨hmin_ge239, hmin_ge239.trans hmin_le_z, h16_17 hd17⟩
  · intro hd73
    have h146 : 146 ∣ z.minFac - 1 := by simpa [hd73] using hpf_dvd z.minFac hmin_mem
    have hmin_ge147 : 147 ≤ z.minFac := by simpa [hd73] using hmin_ge
    have hmin_ge293 : 293 ≤ z.minFac := by
      by_contra hlt
      obtain ⟨k, hk⟩ := h146
      have hk1 : k = 1 := by omega
      have h147 : z.minFac = 147 := by omega
      rw [h147] at hmin_prime
      norm_num at hmin_prime
    exact ⟨hmin_ge293, hmin_ge293.trans hmin_le_z, h16_73 hd73⟩
  · intro hd241
    have h482 : 482 ∣ z.minFac - 1 := by simpa [hd241] using hpf_dvd z.minFac hmin_mem
    have hmin_ge483 : 483 ≤ z.minFac := by simpa [hd241] using hmin_ge
    have hmin_ge2411 : 2411 ≤ z.minFac := by
      by_contra hlt
      obtain ⟨k, hk⟩ := h482
      have hk_mem : k ∈ Finset.Icc 1 4 := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hmin_eq : z.minFac = 482 * k + 1 := by omega
      fin_cases hk_mem
      · rw [hmin_eq] at hmin_prime; norm_num at hmin_prime
      · rw [hmin_eq] at hmin_prime; norm_num at hmin_prime
      · have h1447 : z.minFac = 1447 := by omega
        exact (h16_241 hd241 1447 (by decide)).2.2 (h1447 ▸ hmin_dvd)
      · rw [hmin_eq] at hmin_prime; norm_num at hmin_prime
    exact ⟨hmin_ge2411, hmin_ge2411.trans hmin_le_z, h16_241 hd241⟩

end OddPerfect
