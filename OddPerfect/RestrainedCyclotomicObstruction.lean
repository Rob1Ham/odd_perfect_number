module

public import OddPerfect.GlobalWave7Obstruction
public import OddPerfect.GeometricSquareClass
public import OddPerfect.AlternatingBlock
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Three-Free Restrained Cyclotomic Obstruction (`OddPerfect.RestrainedCyclotomicObstruction`)

Establishes the Euler exponent lift `21 ≤ N.factorization q` (`¬ 3 ∣ (N.factorization q + 1) / 2`)
for three-free restrained odd perfect candidates, constructs the coprime odd cyclotomic block pair
`B₁ = geometricBlock q l` and `B₂ = (q ^ l + 1) / (q + 1)` dividing `σ(q ^ a)` for any odd prime
`l ∣ (a + 1) / 2`, and extracts two distinct odd prime witnesses `w₁ ≠ w₂` in
`insert r₀ (squareSources N)` satisfying the cyclotomic congruence `w = l ∨ 2 * l ∣ w - 1`,
yielding in particular a square-source witness `u ∈ squareSources N` dividing `σ(q ^ a)`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- In the three-free restrained regime (`¬ 3 ∣ N`, `(largeSources N q).card ≤ 1`),
`6 ∤ N.factorization q + 1` rules out `N.factorization q = 17` and forces
`21 ≤ N.factorization q`, `¬ 3 ∣ (N.factorization q + 1) / 2`, and
`11 ≤ (N.factorization q + 1) / 2`. -/
theorem restrained_three_free_euler_exp_ge_21 {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r, r ≠ q → Even (N.factorization r))
    (h3 : ¬ 3 ∣ N) (hle : (largeSources N q).card ≤ 1) :
    21 ≤ N.factorization q ∧ ¬ 3 ∣ (N.factorization q + 1) / 2 ∧
      11 ≤ (N.factorization q + 1) / 2 := by
  obtain ⟨_, _, _, _, h17, _, _, _⟩ :=
    restrained_three_free_euler_exp_ge_17 ho hN hq hq4 he hev h3 hle
  have hndvd3 : ¬ 3 ∣ (N.factorization q + 1) / 2 := by
    intro h3d
    obtain ⟨k, hk⟩ := h3d
    have h6 : 6 ∣ N.factorization q + 1 := ⟨k, by omega⟩
    exact h3 (three_dvd_of_six_dvd_component_length hN hq h6)
  have h21 : 21 ≤ N.factorization q := by
    by_contra! hlt
    have heq17 : N.factorization q = 17 := by omega
    apply hndvd3
    rw [heq17]
    decide
  exact ⟨h21, hndvd3, by omega⟩

/-- For any prime `q ≡ 1 [MOD 4]`, exponent `a ≡ 1 [MOD 4]`, and odd prime `l ∣ (a + 1) / 2`,
the geometric block `B₁ = ∑ i ∈ range l, q ^ i` and alternating block `B₂ = (q ^ l + 1) / (q + 1)`
are coprime odd integers strictly greater than `1` whose product divides `σ(q ^ a)`. -/
theorem odd_prime_cyclotomic_pair_dvd_sigma {q a l : ℕ}
    (hq : q.Prime) (hq4 : q % 4 = 1) (ha4 : a % 4 = 1)
    (hl : l.Prime) (hl3 : 3 ≤ l) (hld : l ∣ (a + 1) / 2) :
    let B₁ := geometricBlock q l
    let B₂ := (q ^ l + 1) / (q + 1)
    (q + 1) * B₂ = q ^ l + 1 ∧
      1 < B₁ ∧ Odd B₁ ∧ 1 < B₂ ∧ Odd B₂ ∧
      Nat.Coprime B₁ B₂ ∧ B₁ * B₂ ∣ sigma 1 (q ^ a) := by
  intro B₁ B₂
  have hl_odd : Odd l := hl.odd_of_ne_two (by omega)
  have hq5 : 5 ≤ q := by
    have := hq.two_le
    omega
  have hdvd_ql : q + 1 ∣ q ^ l + 1 := by
    simpa using hl_odd.nat_add_dvd_pow_add_pow (x := q) (y := 1)
  have hB₂_eq : (q + 1) * B₂ = q ^ l + 1 := Nat.mul_div_cancel' hdvd_ql
  have hq_lt_ql : q < q ^ l := by
    calc
      q = q ^ 1 := (pow_one q).symm
      _ < q ^ l := Nat.pow_lt_pow_right hq.one_lt (by omega)
  have hB₁_mul : B₁ * (q - 1) = q ^ l - 1 := geom_sum_mul_of_one_le hq.one_le l
  have hB₁_gt1 : 1 < B₁ := by
    have hlt : 1 * (q - 1) < B₁ * (q - 1) := by
      rw [one_mul, hB₁_mul]
      exact Nat.sub_lt_sub_right hq.one_le hq_lt_ql
    exact Nat.lt_of_mul_lt_mul_right hlt
  have hB₁_odd : Odd B₁ := by
    have hq2 : q ≡ 1 [MOD 2] := show q % 2 = 1 % 2 by omega
    have hsum : (∑ j ∈ range l, q ^ j) ≡ ∑ j ∈ range l, 1 ^ j [MOD 2] :=
      Nat.ModEq.sum fun j _ => hq2.pow j
    have h1 : (∑ j ∈ range l, 1 ^ j) = l := by simp
    rw [h1] at hsum
    change B₁ ≡ l [MOD 2] at hsum
    have hl2 : l % 2 = 1 := Nat.odd_iff.mp hl_odd
    exact Nat.odd_iff.mpr (Eq.trans hsum hl2)
  have hB₂_gt1 : 1 < B₂ := by
    have hq_sq : q < q ^ 2 := by nlinarith
    have hq2_le : q ^ 2 ≤ q ^ l := Nat.pow_le_pow_right hq.pos (by omega)
    have hlt : (q + 1) * 1 < (q + 1) * B₂ := by
      rw [mul_one, hB₂_eq]
      omega
    exact Nat.lt_of_mul_lt_mul_left hlt
  have hB₂_odd : Odd B₂ := by
    have hql4 : q ^ l % 4 = 1 := by
      rw [Nat.pow_mod, hq4]
      simp
    have hmod : ((q + 1) * B₂) % 4 = 2 := by
      rw [hB₂_eq, Nat.add_mod, hql4]
    rw [Nat.mul_mod, show (q + 1) % 4 = 2 by omega] at hmod
    have hm : B₂ % 4 < 4 := Nat.mod_lt B₂ (by decide)
    have hpar : B₂ % 2 = 1 := by omega
    exact Nat.odd_iff.mpr hpar
  have hcop : Nat.Coprime B₁ B₂ := by
    by_contra hnc
    obtain ⟨p, hp, hp1, hp2⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    have hp_sub1 : p ∣ q ^ l - 1 := hB₁_mul ▸ dvd_mul_of_dvd_left hp1 (q - 1)
    have hp_add1 : p ∣ q ^ l + 1 := hB₂_eq ▸ dvd_mul_of_dvd_right hp2 (q + 1)
    have h1_le_ql : 1 ≤ q ^ l := Nat.one_le_pow l q hq.pos
    have hp2_div : p ∣ 2 := by
      have hsub : (q ^ l + 1) - (q ^ l - 1) = 2 := by omega
      rw [← hsub]
      exact Nat.dvd_sub hp_add1 hp_sub1
    have hp_eq2 : p = 2 := ((Nat.dvd_prime Nat.prime_two).mp hp2_div).resolve_left hp.ne_one
    rw [hp_eq2] at hp1
    have hB₁_even : B₁ % 2 = 0 := Nat.mod_eq_zero_of_dvd hp1
    have hB₁_mod : B₁ % 2 = 1 := Nat.odd_iff.mp hB₁_odd
    omega
  have hdvd_sig : B₁ * B₂ ∣ sigma 1 (q ^ a) := by
    have h2l : 2 * l ∣ a + 1 := by
      obtain ⟨k, hk⟩ := hld
      refine ⟨k, ?_⟩
      calc
        a + 1 = 2 * ((a + 1) / 2) := by omega
        _ = 2 * (l * k) := by rw [hk]
        _ = (2 * l) * k := by ring
    have hblock2l : geometricBlock q (2 * l) = (q + 1) * (B₁ * B₂) := by
      have hmul := geometricBlock_mul q l 2
      rw [show l * 2 = 2 * l by ring] at hmul
      have hg2 : geometricBlock (q ^ l) 2 = q ^ l + 1 := by
        rw [geometricBlock, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
        ring
      rw [hmul, hg2, ← hB₂_eq]
      change B₁ * ((q + 1) * B₂) = (q + 1) * (B₁ * B₂)
      ring
    have hB_dvd_2l : B₁ * B₂ ∣ geometricBlock q (2 * l) := by
      rw [hblock2l]
      exact dvd_mul_left (B₁ * B₂) (q + 1)
    obtain ⟨k, hk⟩ := h2l
    have h2l_dvd_sig : geometricBlock q (2 * l) ∣ sigma 1 (q ^ a) := by
      rw [sigma_one_apply_prime_pow hq]
      change geometricBlock q (2 * l) ∣ geometricBlock q (a + 1)
      rw [hk, geometricBlock_mul q (2 * l) k]
      exact dvd_mul_right _ _
    exact hB_dvd_2l.trans h2l_dvd_sig
  exact ⟨hB₂_eq, hB₁_gt1, hB₁_odd, hB₂_gt1, hB₂_odd, hcop, hdvd_sig⟩

private theorem prime_dvd_geometricBlock_order_dichotomy {q l w : ℕ}
    (hl : l.Prime) (hl_odd : Odd l) (hw : w.Prime) (hwo : Odd w)
    (hdvd : w ∣ geometricBlock q l) : w = l ∨ 2 * l ∣ w - 1 := by
  let : Fact w.Prime := ⟨hw⟩
  have hsum : (∑ j ∈ range l, (q : ZMod w) ^ j) = 0 := by
    have hcast : ((geometricBlock q l : ℕ) : ZMod w) = 0 :=
      (ZMod.natCast_eq_zero_iff _ w).mpr hdvd
    simpa [geometricBlock] using hcast
  have hq0 : (q : ZMod w) ≠ 0 := by
    intro h0
    rw [h0] at hsum
    have h1 : (∑ j ∈ range l, (0 : ZMod w) ^ j) = 1 := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hl.ne_zero
      rw [hk, Finset.sum_range_succ']
      simp
    rw [h1] at hsum
    exact one_ne_zero hsum
  by_cases hq1 : (q : ZMod w) = 1
  · left
    rw [hq1] at hsum
    have hlz : (l : ZMod w) = 0 := by simpa using hsum
    have hwl : w ∣ l := (ZMod.natCast_eq_zero_iff l w).mp hlz
    exact (Nat.dvd_prime hl).mp hwl |>.resolve_left hw.ne_one
  · right
    have hpow : (q : ZMod w) ^ l = 1 := by
      apply sub_eq_zero.mp
      rw [← geom_sum_mul, hsum, zero_mul]
    have hord_dvd : orderOf (q : ZMod w) ∣ l := orderOf_dvd_of_pow_eq_one hpow
    have hord_ne1 : orderOf (q : ZMod w) ≠ 1 := by
      intro h1
      exact hq1 (orderOf_eq_one_iff.mp h1)
    have hord_eq : orderOf (q : ZMod w) = l :=
      ((Nat.dvd_prime hl).mp hord_dvd).resolve_left hord_ne1
    have hl_dvd_sub : l ∣ w - 1 := by
      rw [← hord_eq]
      exact ZMod.orderOf_dvd_card_sub_one hq0
    have h2_dvd_sub : 2 ∣ w - 1 := by
      have hw_mod : w % 2 = 1 := Nat.odd_iff.mp hwo
      omega
    have hcop2l : Nat.Coprime 2 l := by
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      intro h
      exact (Nat.not_even_iff_odd.mpr hl_odd) (even_iff_two_dvd.mpr h)
    exact hcop2l.mul_dvd_of_dvd_of_dvd h2_dvd_sub hl_dvd_sub

private theorem prime_dvd_alternatingBlock_order_dichotomy {q l w : ℕ}
    (hl : l.Prime) (hl_odd : Odd l) (hw : w.Prime) (hwo : Odd w)
    (hdvd : w ∣ (q ^ l + 1) / (q + 1)) : w = l ∨ 2 * l ∣ w - 1 := by
  let : Fact w.Prime := ⟨hw⟩
  have hdvd_ql : q + 1 ∣ q ^ l + 1 := by
    simpa using hl_odd.nat_add_dvd_pow_add_pow (x := q) (y := 1)
  have hB₂_eq : (q + 1) * ((q ^ l + 1) / (q + 1)) = q ^ l + 1 :=
    Nat.mul_div_cancel' hdvd_ql
  have hpow_neg : (q : ZMod w) ^ l = -1 := by
    have h0 : w ∣ q ^ l + 1 := hB₂_eq ▸ dvd_mul_of_dvd_right hdvd (q + 1)
    have hz : ((q ^ l + 1 : ℕ) : ZMod w) = 0 := (ZMod.natCast_eq_zero_iff _ w).mpr h0
    push_cast at hz
    exact eq_neg_of_add_eq_zero_left hz
  have hq0 : (q : ZMod w) ≠ 0 := by
    intro h0
    rw [h0, zero_pow hl.ne_zero] at hpow_neg
    have h1 : (1 : ZMod w) = 0 := by
      have := neg_eq_iff_add_eq_zero.mp hpow_neg.symm
      simp at this
    exact one_ne_zero h1
  by_cases hq_neg1 : (q : ZMod w) = -1
  · left
    have hcast : (((q ^ l + 1) / (q + 1) : ℕ) : ℤ) = ∑ j ∈ range l, (-(q : ℤ)) ^ j := by
      simpa [alternatingBlock] using alternatingBlock_cast (x := q) hl_odd
    have hz := congrArg (Int.cast : ℤ → ZMod w) hcast
    have hB_zero : (((q ^ l + 1) / (q + 1) : ℕ) : ZMod w) = 0 :=
      (ZMod.natCast_eq_zero_iff _ w).mpr hdvd
    rw [Int.cast_natCast, hB_zero] at hz
    simp only [Int.cast_sum, Int.cast_pow, Int.cast_neg, Int.cast_natCast] at hz
    rw [hq_neg1] at hz
    have hlz : (l : ZMod w) = 0 := by
      simpa using hz.symm
    have hwl : w ∣ l := (ZMod.natCast_eq_zero_iff l w).mp hlz
    exact ((Nat.dvd_prime hl).mp hwl).resolve_left hw.ne_one
  · right
    have hpow2l : (q : ZMod w) ^ (2 * l) = 1 := by
      rw [show 2 * l = l * 2 by ring, pow_mul, hpow_neg]
      norm_num
    have hord_dvd : orderOf (q : ZMod w) ∣ 2 * l := orderOf_dvd_of_pow_eq_one hpow2l
    have hneg1_ne1 : (-1 : ZMod w) ≠ 1 := by
      intro h
      have h2 : (2 : ZMod w) = 0 := by
        have h' : (1 : ZMod w) + 1 = 0 := by
          calc
            (1 : ZMod w) + 1 = -1 + 1 := by rw [h]
            _ = 0 := by ring
        simpa [one_add_one_eq_two] using h'
      have hw2 : w ∣ 2 := (ZMod.natCast_eq_zero_iff 2 w).mp h2
      have hweq : w = 2 := (Nat.dvd_prime Nat.prime_two).mp hw2 |>.resolve_left hw.ne_one
      rw [hweq] at hwo
      exact (by decide : ¬ Odd 2) hwo
    have hndvd_l : ¬ orderOf (q : ZMod w) ∣ l := by
      rw [orderOf_dvd_iff_pow_eq_one, hpow_neg]
      exact hneg1_ne1
    have hndvd_2 : ¬ orderOf (q : ZMod w) ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      intro hsq
      obtain ⟨k, hk⟩ := hl_odd
      have hql_eq : (q : ZMod w) ^ l = (q : ZMod w) := by
        rw [hk, pow_add, pow_mul, hsq, one_pow, one_mul, pow_one]
      rw [hpow_neg] at hql_eq
      exact hq_neg1 hql_eq.symm
    have h2_dvd_ord : 2 ∣ orderOf (q : ZMod w) := by
      by_contra hnot
      have hcop : Nat.Coprime 2 (orderOf (q : ZMod w)) :=
        Nat.Prime.coprime_iff_not_dvd Nat.prime_two |>.mpr hnot
      exact hndvd_l (hcop.symm.dvd_of_dvd_mul_left hord_dvd)
    obtain ⟨m, hm⟩ := h2_dvd_ord
    have hm_dvd_l : m ∣ l := by
      rw [hm] at hord_dvd
      exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2) hord_dvd
    have hm_ne1 : m ≠ 1 := by
      intro h1
      apply hndvd_2
      rw [hm, h1, mul_one]
    have hm_eq : m = l := ((Nat.dvd_prime hl).mp hm_dvd_l).resolve_left hm_ne1
    have hord_eq : orderOf (q : ZMod w) = 2 * l := by rw [hm, hm_eq]
    rw [← hord_eq]
    exact ZMod.orderOf_dvd_card_sub_one hq0

/-- On a three-free restrained odd perfect number (`¬ 3 ∣ N`, `(largeSources N q).card ≤ 1`),
letting `d := (N.factorization q + 1) / 2` and `l := d.minFac`:
1. `l` is a prime `≥ 5` dividing `d`;
2. There exist two distinct odd primes `w₁ ≠ w₂` in `insert r₀ (squareSources N)` (where
   `largeSources N q = {r₀}`) with `w₁ ∣ geometricBlock q l`, `w₂ ∣ (q ^ l + 1) / (q + 1)`,
   both dividing `σ(q ^ N.factorization q)`, and both satisfying `w = l ∨ 2 * l ∣ w - 1`;
3. Consequently, at least one `u ∈ squareSources N` divides `σ(q ^ N.factorization q)` and
   satisfies `u = l ∨ 2 * l ∣ u - 1`. -/
theorem restrained_three_free_cyclotomic_square_source_witness {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r, r ≠ q → Even (N.factorization r))
    (h3 : ¬ 3 ∣ N) (hle : (largeSources N q).card ≤ 1) :
    let d := (N.factorization q + 1) / 2
    let l := d.minFac
    ∃ r₀, largeSources N q = {r₀} ∧ l.Prime ∧ 5 ≤ l ∧ l ∣ d ∧
      (∃ w₁ w₂ : ℕ, w₁ ≠ w₂ ∧ w₁.Prime ∧ Odd w₁ ∧ w₂.Prime ∧ Odd w₂ ∧
        w₁ ∈ insert r₀ (squareSources N) ∧ w₂ ∈ insert r₀ (squareSources N) ∧
        w₁ ∣ geometricBlock q l ∧ w₂ ∣ (q ^ l + 1) / (q + 1) ∧
        w₁ ∣ sigma 1 (q ^ N.factorization q) ∧ w₂ ∣ sigma 1 (q ^ N.factorization q) ∧
        (w₁ = l ∨ 2 * l ∣ w₁ - 1) ∧ (w₂ = l ∨ 2 * l ∣ w₂ - 1)) ∧
      (∃ u ∈ squareSources N, u ∣ sigma 1 (q ^ N.factorization q) ∧
        (u = l ∨ 2 * l ∣ u - 1)) := by
  intro d l
  obtain ⟨r₀, hr₀, _, _, _, _, _, _⟩ :=
    restrained_three_free_euler_exp_ge_17 ho hN hq hq4 he hev h3 hle
  obtain ⟨_, hndvd3, hd11⟩ :=
    restrained_three_free_euler_exp_ge_21 ho hN hq hq4 he hev h3 hle
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hl_prime : l.Prime := Nat.minFac_prime (by omega)
  have hl_dvd : l ∣ d := Nat.minFac_dvd d
  have hd_odd : Odd d := by
    dsimp [d]
    have : N.factorization q % 4 = 1 := he
    exact Nat.odd_iff.mpr (by omega)
  have hl_odd : Odd l := hd_odd.of_dvd_nat hl_dvd
  have hl_ne3 : l ≠ 3 := by
    intro h
    apply hndvd3
    rw [← h]
    exact hl_dvd
  have hl5 : 5 ≤ l := by
    have := hl_prime.two_le
    have := Nat.odd_iff.mp hl_odd
    omega
  obtain ⟨_, hB₁_gt1, hB₁_odd, hB₂_gt1, hB₂_odd, hcop, hprod_dvd⟩ :=
    odd_prime_cyclotomic_pair_dvd_sigma hq_prime hq4 he hl_prime (by omega) hl_dvd
  obtain ⟨w₁, hw₁_prime, hw₁_B₁⟩ := Nat.exists_prime_and_dvd (by omega : geometricBlock q l ≠ 1)
  obtain ⟨w₂, hw₂_prime, hw₂_B₂⟩ :=
    Nat.exists_prime_and_dvd (by omega : (q ^ l + 1) / (q + 1) ≠ 1)
  have hw₁_odd : Odd w₁ := hB₁_odd.of_dvd_nat hw₁_B₁
  have hw₂_odd : Odd w₂ := hB₂_odd.of_dvd_nat hw₂_B₂
  have hw₁_ne_w₂ : w₁ ≠ w₂ := by
    intro h
    subst h
    exact hw₁_prime.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hw₁_B₁ hw₂_B₂)
  have hw₁_sig : w₁ ∣ sigma 1 (q ^ N.factorization q) :=
    hw₁_B₁.trans ((dvd_mul_right _ _).trans hprod_dvd)
  have hw₂_sig : w₂ ∣ sigma 1 (q ^ N.factorization q) :=
    hw₂_B₂.trans ((dvd_mul_left _ _).trans hprod_dvd)
  have hmem_insert : ∀ {w : ℕ}, w.Prime → Odd w → w ∣ sigma 1 (q ^ N.factorization q) →
      w ∈ insert r₀ (squareSources N) := by
    intro w hw_prime hw_odd hw_sig
    have hw_N : w ∣ N := by
      apply dvd_perfect_of_exact_prime_pow hN hq_prime (Nat.ordProj_dvd N q) _ hw_prime hw_odd
      · rw [← sigma_one_apply]
        exact hw_sig
      · rw [hq_prime.pow_dvd_iff_le_factorization hN.2.ne']
        omega
    have hw_pf : w ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hw_prime, hw_N, hN.2.ne'⟩
    have hw_ne3 : w ≠ 3 := fun h => h3 (h ▸ hw_N)
    have hw_neq : w ≠ q := by
      intro h
      subst h
      have hmod := sigma_prime_pow_mod_self hq_prime (N.factorization w)
      have hdiv := Nat.mod_eq_zero_of_dvd hw_sig
      omega
    have hw_pos : 0 < N.factorization w := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hw_pf)
    obtain ⟨k, hk⟩ := hev w hw_neq
    rw [Finset.mem_insert]
    by_cases h2 : N.factorization w = 2
    · right
      exact Finset.mem_filter.mpr ⟨hw_pf, hw_ne3, h2⟩
    · left
      have hlarge : w ∈ largeSources N q :=
        Finset.mem_filter.mpr ⟨hw_pf, hw_ne3, hw_neq, by omega⟩
      rw [hr₀, Finset.mem_singleton] at hlarge
      exact hlarge
  have hw₁_ins : w₁ ∈ insert r₀ (squareSources N) := hmem_insert hw₁_prime hw₁_odd hw₁_sig
  have hw₂_ins : w₂ ∈ insert r₀ (squareSources N) := hmem_insert hw₂_prime hw₂_odd hw₂_sig
  have hw₁_dich := prime_dvd_geometricBlock_order_dichotomy hl_prime hl_odd hw₁_prime hw₁_odd hw₁_B₁
  have hw₂_dich := prime_dvd_alternatingBlock_order_dichotomy hl_prime hl_odd hw₂_prime hw₂_odd hw₂_B₂
  have hu_ex : ∃ u ∈ squareSources N, u ∣ sigma 1 (q ^ N.factorization q) ∧
      (u = l ∨ 2 * l ∣ u - 1) := by
    by_cases hw₁_r₀ : w₁ = r₀
    · have hw₂_ner₀ : w₂ ≠ r₀ := fun h => hw₁_ne_w₂ (hw₁_r₀.trans h.symm)
      exact ⟨w₂, (Finset.mem_insert.mp hw₂_ins).resolve_left hw₂_ner₀, hw₂_sig, hw₂_dich⟩
    · exact ⟨w₁, (Finset.mem_insert.mp hw₁_ins).resolve_left hw₁_r₀, hw₁_sig, hw₁_dich⟩
  exact ⟨r₀, hr₀, hl_prime, hl5, hl_dvd,
    ⟨w₁, w₂, hw₁_ne_w₂, hw₁_prime, hw₁_odd, hw₂_prime, hw₂_odd, hw₁_ins, hw₂_ins,
      hw₁_B₁, hw₂_B₂, hw₁_sig, hw₂_sig, hw₁_dich, hw₂_dich⟩, hu_ex⟩

end OddPerfect
