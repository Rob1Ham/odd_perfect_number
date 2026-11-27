module

public import OddPerfect.GlobalWave9Obstruction
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Three-Free Restrained Closure (`OddPerfect.ThreeFreeRestrainedClosure`)

Unconditionally eliminates all three-free restrained odd perfect numbers
(`¬ 3 ∣ N` and `(largeSources N q).card ≤ 1`):

1. `zelinsky_twoModThree_prime_pow_common_divisor_le`:
   For distinct odd `a, b ≥ 5` with `a ≡ b ≡ 2 [MOD 3]` and any odd prime `P ≡ 1 [MOD 3]`,
   if `P ^ c ∣ a ^ 2 + a + 1` and `P ^ c ∣ b ^ 2 + b + 1`, then `5 * P ^ c ≤ a + b + 1`.
2. `two_prime_smooth_sq_add_self_add_one_step`:
   For any three `{q, r₀}`-smooth values `u₀ < u₁ < u₂` with `u_i ≡ 2 [MOD 3]` and `5 ≤ u₀`,
   `25 * (u₀ ^ 2 + u₀ + 1) ≤ (u₁ + u₂ + 1) ^ 2` and `5 * u₀ + 3 ≤ 2 * u₂`.
3. `prod_sq_abundancy_le_of_five_halves_step`:
   On any list `M` satisfying the `5 * x + 3 ≤ 2 * y` step condition with head `≥ y₀ ≥ 5`,
   `2 * y₀ * ∏ x ∈ M, (x ^ 2 + x + 1) ≤ (2 * y₀ + 5) * ∏ x ∈ M, x ^ 2`.
4. Splitting `S = squareSources N` into even and odd sorted indices (`evenIdx` / `oddIdx`)
   and ruling out `{11, 23}` (plus `{5, 17}` simultaneously) yields `abundancy(N) < 2`,
   proving `two_le_largeSources_of_three_free` and `three_dvd_of_largeSources_le_one`,
   alongside `exists_eight_drop_at_three_of_largeSources_empty`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma nat_mul_lt_mul_closure {a b c d : ℕ} (h1 : a < b) (h2 : c < d) : a * c < b * d :=
  lt_of_le_of_lt (Nat.mul_le_mul_right c h1.le) (Nat.mul_lt_mul_of_pos_left h2 (by omega))

private lemma sigma_prime_pow_ratio_lt_closure {p k c₁ c₂ : ℕ} (hp : p.Prime) (hc₁ : 0 < c₁)
    (hcoef : c₁ * p ≤ c₂ * (p - 1)) :
    c₁ * sigma 1 (p ^ k) < c₂ * p ^ k := by
  have hgeom : (p - 1) * sigma 1 (p ^ k) < p * p ^ k := by
    rw [mul_comm (p - 1), mul_comm p, sigma_one_apply_prime_pow hp]
    have h := geom_sum_mul_add (p - 1) (k + 1)
    rw [Nat.sub_add_cancel hp.one_lt.le, pow_succ] at h
    omega
  have h1 : (p - 1) * (c₁ * sigma 1 (p ^ k)) < (p - 1) * (c₂ * p ^ k) := by
    calc
      (p - 1) * (c₁ * sigma 1 (p ^ k))
          = c₁ * ((p - 1) * sigma 1 (p ^ k)) := by ring
      _ < c₁ * (p * p ^ k) := Nat.mul_lt_mul_of_pos_left hgeom hc₁
      _ = (c₁ * p) * p ^ k := by ring
      _ ≤ (c₂ * (p - 1)) * p ^ k := Nat.mul_le_mul_right (p ^ k) hcoef
      _ = (p - 1) * (c₂ * p ^ k) := by ring
  exact Nat.lt_of_mul_lt_mul_left h1

private lemma abundancy_contradiction4_le {N σq σr Pev Pod q_pow r_pow Qev Qod cq dq cr dr cev dev cod dod : ℕ}
    (_hN_pos : 0 < N)
    (hσ_eq : σq * σr * Pev * Pod = 2 * N)
    (hN_eq : q_pow * r_pow * Qev * Qod = N)
    (hq : cq * σq < dq * q_pow)
    (hr : cr * σr < dr * r_pow)
    (hpev_pos : 0 < cev * Pev)
    (hpev : cev * Pev ≤ dev * Qev)
    (hpod_pos : 0 < cod * Pod)
    (hpod : cod * Pod ≤ dod * Qod)
    (hineq : dq * dr * dev * dod ≤ 2 * (cq * cr * cev * cod)) : False := by
  have hlt2 : (cq * σq) * (cr * σr) < (dq * q_pow) * (dr * r_pow) :=
    nat_mul_lt_mul_closure hq hr
  have hlt3 : ((cq * σq) * (cr * σr)) * (cev * Pev) < ((dq * q_pow) * (dr * r_pow)) * (dev * Qev) :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hlt2 hpev_pos) (Nat.mul_le_mul_left _ hpev)
  have hprod : (((cq * σq) * (cr * σr)) * (cev * Pev)) * (cod * Pod) <
      (((dq * q_pow) * (dr * r_pow)) * (dev * Qev)) * (dod * Qod) :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hlt3 hpod_pos) (Nat.mul_le_mul_left _ hpod)
  have hLHS : (((cq * σq) * (cr * σr)) * (cev * Pev)) * (cod * Pod) =
      (cq * cr * cev * cod) * (σq * σr * Pev * Pod) := by ring
  have hRHS : (((dq * q_pow) * (dr * r_pow)) * (dev * Qev)) * (dod * Qod) =
      (dq * dr * dev * dod) * (q_pow * r_pow * Qev * Qod) := by ring
  rw [hLHS, hRHS, hσ_eq, hN_eq] at hprod
  have hle : (dq * dr * dev * dod) * N ≤ (2 * (cq * cr * cev * cod)) * N :=
    Nat.mul_le_mul_right N hineq
  have hlt : (2 * (cq * cr * cev * cod)) * N < (2 * (cq * cr * cev * cod)) * N := by
    calc
      (2 * (cq * cr * cev * cod)) * N = (cq * cr * cev * cod) * (2 * N) := by ring
      _ < (dq * dr * dev * dod) * N := hprod
      _ ≤ (2 * (cq * cr * cev * cod)) * N := hle
  exact lt_irrefl _ hlt

private lemma eq_mul_pow_of_primeFactors_subset_pair {n p r : ℕ} (hn : n ≠ 0) (hpr : p ≠ r)
    (hsub : n.primeFactors ⊆ {p, r}) :
    n = p ^ n.factorization p * r ^ n.factorization r := by
  have hprod := Nat.prod_primeFactors_pow_factorization hn
  have hmul : (∏ x ∈ n.primeFactors, x ^ n.factorization x) =
      ∏ x ∈ ({p, r} : Finset ℕ), x ^ n.factorization x := by
    apply Finset.prod_subset hsub
    intro x _ hx_not
    have hfz : n.factorization x = 0 := Finsupp.notMem_support_iff.mp hx_not
    rw [hfz, pow_zero]
  conv_lhs => rw [hprod, hmul, Finset.prod_pair hpr]

private lemma zelinsky_aux_lt {a b P c : ℕ} (ha_odd : Odd a) (hb_odd : Odd b) (hab : a < b)
    (ha3 : a % 3 = 2) (hb3 : b % 3 = 2)
    (hP : P.Prime) (hP_odd : Odd P) (hP3 : P % 3 = 1) (hc : 1 ≤ c)
    (hda : P ^ c ∣ a ^ 2 + a + 1) (hdb : P ^ c ∣ b ^ 2 + b + 1) :
    5 * P ^ c ≤ a + b + 1 := by
  have ha2 : a % 2 = 1 := Nat.odd_iff.mp ha_odd
  have hb2 : b % 2 = 1 := Nat.odd_iff.mp hb_odd
  have hdiff_id : (b - a) * (a + b + 1) + (a ^ 2 + a + 1) = b ^ 2 + b + 1 := by
    zify [hab.le]
    ring
  have hdvd_prod : P ^ c ∣ (b - a) * (a + b + 1) := by
    rw [← hdiff_id] at hdb
    exact (Nat.dvd_add_left hda).mp hdb
  have hnot_both : ¬ (P ∣ b - a ∧ P ∣ a + b + 1) := by
    rintro ⟨hd1, hd2⟩
    have hsum_eq : (b - a) + (a + b + 1) = 2 * b + 1 := by omega
    have hP_2b1 : P ∣ 2 * b + 1 := hsum_eq ▸ dvd_add hd1 hd2
    have hP_sq : P ∣ (2 * b + 1) ^ 2 := hP_2b1.trans (dvd_pow_self _ (by decide : 2 ≠ 0))
    have hP_b : P ∣ b ^ 2 + b + 1 := (dvd_pow_self P (by omega : c ≠ 0)).trans hdb
    have hP_4b : P ∣ 4 * (b ^ 2 + b + 1) := dvd_mul_of_dvd_right hP_b 4
    have hid : (2 * b + 1) ^ 2 + 3 = 4 * (b ^ 2 + b + 1) := by ring
    rw [← hid] at hP_4b
    have hP_3 : P ∣ 3 := (Nat.dvd_add_right hP_sq).mp hP_4b
    have hP_le3 : P ≤ 3 := Nat.le_of_dvd (by decide) hP_3
    have hP2 := hP.two_le
    omega
  by_cases hP_diff : P ∣ b - a
  · have hP_sum_ndvd : ¬ P ∣ a + b + 1 := fun h => hnot_both ⟨hP_diff, h⟩
    have hcop : Nat.Coprime (P ^ c) (a + b + 1) :=
      (hP.coprime_iff_not_dvd.mpr hP_sum_ndvd).pow_left c
    have hd_diff : P ^ c ∣ b - a := hcop.dvd_of_dvd_mul_right hdvd_prod
    have h6_diff : 6 ∣ b - a := Nat.dvd_of_mod_eq_zero (by omega)
    have hP_ndvd6 : ¬ P ∣ 6 := by
      intro hd6
      have hle6 : P ≤ 6 := Nat.le_of_dvd (by decide) hd6
      have hP2 := hP.two_le
      have hP2_mod : P % 2 = 1 := Nat.odd_iff.mp hP_odd
      omega
    have hcop6 : Nat.Coprime 6 (P ^ c) :=
      (hP.coprime_iff_not_dvd.mpr hP_ndvd6).symm.pow_right c
    have h6P : 6 * P ^ c ∣ b - a := hcop6.mul_dvd_of_dvd_of_dvd h6_diff hd_diff
    have hle_diff : 6 * P ^ c ≤ b - a := Nat.le_of_dvd (by omega) h6P
    omega
  · have hcop : Nat.Coprime (P ^ c) (b - a) :=
      (hP.coprime_iff_not_dvd.mpr hP_diff).pow_left c
    have hd_sum : P ^ c ∣ a + b + 1 := hcop.dvd_of_dvd_mul_left hdvd_prod
    obtain ⟨m, hm⟩ := hd_sum
    have hm_pos : 0 < m := by
      by_contra! hm0
      have hm_eq : m = 0 := by omega
      rw [hm_eq, mul_zero] at hm
      omega
    have hm_odd : Odd m := by
      have hsum_odd : Odd (a + b + 1) := (ha_odd.add_odd hb_odd).add_odd (by decide : Odd 1)
      rw [hm] at hsum_odd
      exact hsum_odd.of_dvd_nat (dvd_mul_left m (P ^ c))
    have hm2 : m % 2 = 1 := Nat.odd_iff.mp hm_odd
    have hPc_mod3 : P ^ c % 3 = 1 := by
      rw [Nat.pow_mod, hP3, one_pow]
      norm_num
    have hsum_mod3 : (a + b + 1) % 3 = 2 := by omega
    have hm_mod3 : m % 3 = 2 := by
      have hmul_mod := congrArg (· % 3) hm
      rw [Nat.mul_mod, hPc_mod3] at hmul_mod
      omega
    have hm5 : 5 ≤ m := by omega
    nlinarith

/-- Zelinsky's common-divisor bound: for distinct odd `a, b ≥ 5` with `a ≡ b ≡ 2 [MOD 3]` and any
odd prime `P ≡ 1 [MOD 3]`, if `P ^ c ∣ a ^ 2 + a + 1` and `P ^ c ∣ b ^ 2 + b + 1`, then
`5 * P ^ c ≤ a + b + 1`. -/
theorem zelinsky_twoModThree_prime_pow_common_divisor_le
    {a b P c : ℕ} (ha_odd : Odd a) (hb_odd : Odd b) (hab : a ≠ b)
    (ha5 : 5 ≤ a) (_hb5 : 5 ≤ b) (ha3 : a % 3 = 2) (hb3 : b % 3 = 2)
    (hP : P.Prime) (hP_odd : Odd P) (hP3 : P % 3 = 1)
    (hda : P ^ c ∣ a ^ 2 + a + 1) (hdb : P ^ c ∣ b ^ 2 + b + 1) :
    5 * P ^ c ≤ a + b + 1 := by
  by_cases hc0 : c = 0
  · subst hc0
    rw [pow_zero, mul_one]
    omega
  · have hc : 1 ≤ c := by omega
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact zelinsky_aux_lt ha_odd hb_odd hlt ha3 hb3 hP hP_odd hP3 hc hda hdb
    · rw [add_comm a b]
      exact zelinsky_aux_lt hb_odd ha_odd hgt hb3 ha3 hP hP_odd hP3 hc hdb hda

private lemma two_prime_smooth_combine {q r₀ u₀ u₁ u₂ ut αt βt : ℕ}
    (hu12 : u₁ < u₂) (hut_ge : u₀ ≤ ut)
    (ht : ut ^ 2 + ut + 1 = q ^ αt * r₀ ^ βt)
    (hq_bd : 5 * q ^ αt ≤ u₁ + u₂ + 1)
    (hr_bd : 5 * r₀ ^ βt ≤ u₁ + u₂ + 1) :
    25 * (u₀ ^ 2 + u₀ + 1) ≤ (u₁ + u₂ + 1) ^ 2 ∧ 5 * u₀ + 3 ≤ 2 * u₂ := by
  have hsq_le : u₀ ^ 2 + u₀ + 1 ≤ ut ^ 2 + ut + 1 := by nlinarith
  have h25 : 25 * (u₀ ^ 2 + u₀ + 1) ≤ (u₁ + u₂ + 1) ^ 2 := by
    calc
      25 * (u₀ ^ 2 + u₀ + 1) ≤ 25 * (ut ^ 2 + ut + 1) := Nat.mul_le_mul_left 25 hsq_le
      _ = (5 * q ^ αt) * (5 * r₀ ^ βt) := by rw [ht]; ring
      _ ≤ (u₁ + u₂ + 1) * (u₁ + u₂ + 1) := Nat.mul_le_mul hq_bd hr_bd
      _ = (u₁ + u₂ + 1) ^ 2 := by ring
  have hsq_lt : (5 * u₀ + 2) ^ 2 < 25 * (u₀ ^ 2 + u₀ + 1) := by nlinarith
  have hlt_sq : (5 * u₀ + 2) ^ 2 < (u₁ + u₂ + 1) ^ 2 := lt_of_lt_of_le hsq_lt h25
  have hlt_lin : 5 * u₀ + 2 < u₁ + u₂ + 1 := by nlinarith
  have hstep : 5 * u₀ + 3 ≤ 2 * u₂ := by omega
  exact ⟨h25, hstep⟩

/-- On any strictly increasing triple `u₀ < u₁ < u₂` of odd `≥ 5` numbers `≡ 2 [MOD 3]` whose
`u ^ 2 + u + 1` values are `{q, r₀}`-smooth (`q, r₀` odd primes `≡ 1 [MOD 3]`), we have
`25 * (u₀ ^ 2 + u₀ + 1) ≤ (u₁ + u₂ + 1) ^ 2` and `5 * u₀ + 3 ≤ 2 * u₂`. -/
theorem two_prime_smooth_sq_add_self_add_one_step
    {q r₀ u₀ u₁ u₂ α₀ α₁ α₂ β₀ β₁ β₂ : ℕ}
    (hq : q.Prime) (hq_odd : Odd q) (hq3 : q % 3 = 1)
    (hr₀ : r₀.Prime) (hr₀_odd : Odd r₀) (hr₀3 : r₀ % 3 = 1)
    (hu01 : u₀ < u₁) (hu12 : u₁ < u₂)
    (hu0_odd : Odd u₀) (hu1_odd : Odd u₁) (hu2_odd : Odd u₂)
    (hu0_5 : 5 ≤ u₀) (hu0_3 : u₀ % 3 = 2) (hu1_3 : u₁ % 3 = 2) (hu2_3 : u₂ % 3 = 2)
    (h0 : u₀ ^ 2 + u₀ + 1 = q ^ α₀ * r₀ ^ β₀)
    (h1 : u₁ ^ 2 + u₁ + 1 = q ^ α₁ * r₀ ^ β₁)
    (h2 : u₂ ^ 2 + u₂ + 1 = q ^ α₂ * r₀ ^ β₂) :
    25 * (u₀ ^ 2 + u₀ + 1) ≤ (u₁ + u₂ + 1) ^ 2 ∧ 5 * u₀ + 3 ≤ 2 * u₂ := by
  have hu1_5 : 5 ≤ u₁ := by omega
  have hu2_5 : 5 ≤ u₂ := by omega
  have hq_dvd0 : q ^ α₀ ∣ u₀ ^ 2 + u₀ + 1 := h0 ▸ dvd_mul_right _ _
  have hq_dvd1 : q ^ α₁ ∣ u₁ ^ 2 + u₁ + 1 := h1 ▸ dvd_mul_right _ _
  have hq_dvd2 : q ^ α₂ ∣ u₂ ^ 2 + u₂ + 1 := h2 ▸ dvd_mul_right _ _
  have hr_dvd0 : r₀ ^ β₀ ∣ u₀ ^ 2 + u₀ + 1 := h0 ▸ dvd_mul_left _ _
  have hr_dvd1 : r₀ ^ β₁ ∣ u₁ ^ 2 + u₁ + 1 := h1 ▸ dvd_mul_left _ _
  have hr_dvd2 : r₀ ^ β₂ ∣ u₂ ^ 2 + u₂ + 1 := h2 ▸ dvd_mul_left _ _
  by_cases ha0 : α₀ ≤ α₁ ∨ α₀ ≤ α₂
  · by_cases hb0 : β₀ ≤ β₁ ∨ β₀ ≤ β₂
    · have hq_bd : 5 * q ^ α₀ ≤ u₁ + u₂ + 1 := by
        rcases ha0 with ha01 | ha02
        · have h := zelinsky_twoModThree_prime_pow_common_divisor_le hu0_odd hu1_odd hu01.ne
            hu0_5 hu1_5 hu0_3 hu1_3 hq hq_odd hq3 hq_dvd0 ((Nat.pow_dvd_pow q ha01).trans hq_dvd1)
          omega
        · have h := zelinsky_twoModThree_prime_pow_common_divisor_le hu0_odd hu2_odd (hu01.trans hu12).ne
            hu0_5 hu2_5 hu0_3 hu2_3 hq hq_odd hq3 hq_dvd0 ((Nat.pow_dvd_pow q ha02).trans hq_dvd2)
          omega
      have hr_bd : 5 * r₀ ^ β₀ ≤ u₁ + u₂ + 1 := by
        rcases hb0 with hb01 | hb02
        · have h := zelinsky_twoModThree_prime_pow_common_divisor_le hu0_odd hu1_odd hu01.ne
            hu0_5 hu1_5 hu0_3 hu1_3 hr₀ hr₀_odd hr₀3 hr_dvd0 ((Nat.pow_dvd_pow r₀ hb01).trans hr_dvd1)
          omega
        · have h := zelinsky_twoModThree_prime_pow_common_divisor_le hu0_odd hu2_odd (hu01.trans hu12).ne
            hu0_5 hu2_5 hu0_3 hu2_3 hr₀ hr₀_odd hr₀3 hr_dvd0 ((Nat.pow_dvd_pow r₀ hb02).trans hr_dvd2)
          omega
      exact two_prime_smooth_combine hu12 le_rfl h0 hq_bd hr_bd
    · have hb10 : β₁ ≤ β₀ := by omega
      have hb20 : β₂ ≤ β₀ := by omega
      by_cases ha1 : α₁ ≤ α₀ ∨ α₁ ≤ α₂
      · have hq_bd : 5 * q ^ α₁ ≤ u₁ + u₂ + 1 := by
          rcases ha1 with ha10 | ha12
          · have h := zelinsky_twoModThree_prime_pow_common_divisor_le hu1_odd hu0_odd hu01.ne.symm
              hu1_5 hu0_5 hu1_3 hu0_3 hq hq_odd hq3 hq_dvd1 ((Nat.pow_dvd_pow q ha10).trans hq_dvd0)
            omega
          · have h := zelinsky_twoModThree_prime_pow_common_divisor_le hu1_odd hu2_odd hu12.ne
              hu1_5 hu2_5 hu1_3 hu2_3 hq hq_odd hq3 hq_dvd1 ((Nat.pow_dvd_pow q ha12).trans hq_dvd2)
            omega
        have hr_bd : 5 * r₀ ^ β₁ ≤ u₁ + u₂ + 1 := by
          have h := zelinsky_twoModThree_prime_pow_common_divisor_le hu1_odd hu0_odd hu01.ne.symm
            hu1_5 hu0_5 hu1_3 hu0_3 hr₀ hr₀_odd hr₀3 hr_dvd1 ((Nat.pow_dvd_pow r₀ hb10).trans hr_dvd0)
          omega
        exact two_prime_smooth_combine hu12 hu01.le h1 hq_bd hr_bd
      · have ha21 : α₂ ≤ α₁ := by omega
        have hq_bd : 5 * q ^ α₂ ≤ u₁ + u₂ + 1 := by
          have h := zelinsky_twoModThree_prime_pow_common_divisor_le hu2_odd hu1_odd hu12.ne.symm
            hu2_5 hu1_5 hu2_3 hu1_3 hq hq_odd hq3 hq_dvd2 ((Nat.pow_dvd_pow q ha21).trans hq_dvd1)
          omega
        have hr_bd : 5 * r₀ ^ β₂ ≤ u₁ + u₂ + 1 := by
          have h := zelinsky_twoModThree_prime_pow_common_divisor_le hu2_odd hu0_odd (hu01.trans hu12).ne.symm
            hu2_5 hu0_5 hu2_3 hu0_3 hr₀ hr₀_odd hr₀3 hr_dvd2 ((Nat.pow_dvd_pow r₀ hb20).trans hr_dvd0)
          omega
        exact two_prime_smooth_combine hu12 (hu01.trans hu12).le h2 hq_bd hr_bd
  · have ha10 : α₁ ≤ α₀ := by omega
    have ha20 : α₂ ≤ α₀ := by omega
    by_cases hb1 : β₁ ≤ β₀ ∨ β₁ ≤ β₂
    · have hq_bd : 5 * q ^ α₁ ≤ u₁ + u₂ + 1 := by
        have h := zelinsky_twoModThree_prime_pow_common_divisor_le hu1_odd hu0_odd hu01.ne.symm
          hu1_5 hu0_5 hu1_3 hu0_3 hq hq_odd hq3 hq_dvd1 ((Nat.pow_dvd_pow q ha10).trans hq_dvd0)
        omega
      have hr_bd : 5 * r₀ ^ β₁ ≤ u₁ + u₂ + 1 := by
        rcases hb1 with hb10 | hb12
        · have h := zelinsky_twoModThree_prime_pow_common_divisor_le hu1_odd hu0_odd hu01.ne.symm
            hu1_5 hu0_5 hu1_3 hu0_3 hr₀ hr₀_odd hr₀3 hr_dvd1 ((Nat.pow_dvd_pow r₀ hb10).trans hr_dvd0)
          omega
        · have h := zelinsky_twoModThree_prime_pow_common_divisor_le hu1_odd hu2_odd hu12.ne
            hu1_5 hu2_5 hu1_3 hu2_3 hr₀ hr₀_odd hr₀3 hr_dvd1 ((Nat.pow_dvd_pow r₀ hb12).trans hr_dvd2)
          omega
      exact two_prime_smooth_combine hu12 hu01.le h1 hq_bd hr_bd
    · have hb21 : β₂ ≤ β₁ := by omega
      have hq_bd : 5 * q ^ α₂ ≤ u₁ + u₂ + 1 := by
        have h := zelinsky_twoModThree_prime_pow_common_divisor_le hu2_odd hu0_odd (hu01.trans hu12).ne.symm
          hu2_5 hu0_5 hu2_3 hu0_3 hq hq_odd hq3 hq_dvd2 ((Nat.pow_dvd_pow q ha20).trans hq_dvd0)
        omega
      have hr_bd : 5 * r₀ ^ β₂ ≤ u₁ + u₂ + 1 := by
        have h := zelinsky_twoModThree_prime_pow_common_divisor_le hu2_odd hu1_odd hu12.ne.symm
          hu2_5 hu1_5 hu2_3 hu1_3 hr₀ hr₀_odd hr₀3 hr_dvd2 ((Nat.pow_dvd_pow r₀ hb21).trans hr_dvd1)
        omega
      exact two_prime_smooth_combine hu12 (hu01.trans hu12).le h2 hq_bd hr_bd

/-- Product abundancy bound along a chain satisfying `5 * x + 3 ≤ 2 * y`:
`2 * y₀ * ∏ (x^2 + x + 1) ≤ (2 * y₀ + 5) * ∏ x^2`. -/
theorem prod_sq_abundancy_le_of_five_halves_step :
    ∀ (M : List ℕ), M.IsChain (fun x y => 5 * x + 3 ≤ 2 * y) →
      (∀ x ∈ M, 5 ≤ x) →
      ∀ y₀ : ℕ, 5 ≤ y₀ → (∀ x ∈ M.head?, y₀ ≤ x) →
      2 * y₀ * (M.map (fun x => x ^ 2 + x + 1)).prod ≤
        (2 * y₀ + 5) * (M.map (fun x => x ^ 2)).prod
  | [], _, _, y₀, _, _ => by
      simp
  | [a], _, hge, y₀, _, hhead => by
      have ha : 5 ≤ a := hge a (by simp)
      have hya : y₀ ≤ a := hhead a rfl
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      have h1 : 2 * y₀ * (a + 1) ≤ 2 * a * (a + 1) := Nat.mul_le_mul_right _ (by omega)
      have h2 : 2 * a * (a + 1) ≤ 5 * a ^ 2 := by nlinarith
      nlinarith
  | a :: b :: rest, hchain, hge, y₀, hy₀, hhead => by
      have ha : 5 ≤ a := hge a (by simp)
      have hb : 5 ≤ b := hge b (by simp)
      have hya : y₀ ≤ a := hhead a rfl
      have hab : 5 * a + 3 ≤ 2 * b := hchain.rel
      have ih := prod_sq_abundancy_le_of_five_halves_step (b :: rest) hchain.tail
        (fun x hx => hge x (by simp [hx])) b hb
        (fun x hx => by simp at hx; subst hx; exact le_rfl)
      set P_num := ((b :: rest).map (fun x => x ^ 2 + x + 1)).prod
      set P_den := ((b :: rest).map (fun x => x ^ 2)).prod
      have hquad : 10 * (a ^ 2 + a + 1) + 4 * b ≤ 6 * a * b := by
        have hstep1 : (3 * a - 2) * (5 * a + 3) ≤ (3 * a - 2) * (2 * b) :=
          Nat.mul_le_mul_left _ hab
        have hstep2 : 10 * (a ^ 2 + a + 1) ≤ (3 * a - 2) * (5 * a + 3) := by
          have ha3 : 2 ≤ 3 * a := by omega
          zify [ha3]
          nlinarith
        have hstep3 : (3 * a - 2) * (2 * b) + 4 * b = 6 * a * b := by
          have ha3 : 2 ≤ 3 * a := by omega
          zify [ha3]
          ring
        omega
      have hcoef_ab : 2 * a * (a ^ 2 + a + 1) * (2 * b + 5) ≤ (2 * a + 5) * a ^ 2 * (2 * b) := by
        have hmul_a := Nat.mul_le_mul_left a hquad
        nlinarith
      have hstep : 2 * b * (2 * a * ((a ^ 2 + a + 1) * P_num)) ≤
          2 * b * ((2 * a + 5) * (a ^ 2 * P_den)) := by
        calc
          2 * b * (2 * a * ((a ^ 2 + a + 1) * P_num))
              = (2 * a * (a ^ 2 + a + 1)) * (2 * b * P_num) := by ring
          _ ≤ (2 * a * (a ^ 2 + a + 1)) * ((2 * b + 5) * P_den) := Nat.mul_le_mul_left _ ih
          _ = (2 * a * (a ^ 2 + a + 1) * (2 * b + 5)) * P_den := by ring
          _ ≤ ((2 * a + 5) * a ^ 2 * (2 * b)) * P_den := Nat.mul_le_mul_right _ hcoef_ab
          _ = 2 * b * ((2 * a + 5) * (a ^ 2 * P_den)) := by ring
      have ha_step : 2 * a * ((a ^ 2 + a + 1) * P_num) ≤ (2 * a + 5) * (a ^ 2 * P_den) :=
        Nat.le_of_mul_le_mul_left hstep (by omega)
      have hy_step : (2 * a) * (2 * y₀ * ((a ^ 2 + a + 1) * P_num)) ≤
          (2 * a) * ((2 * y₀ + 5) * (a ^ 2 * P_den)) := by
        calc
          (2 * a) * (2 * y₀ * ((a ^ 2 + a + 1) * P_num))
              = (2 * y₀) * (2 * a * ((a ^ 2 + a + 1) * P_num)) := by ring
          _ ≤ (2 * y₀) * ((2 * a + 5) * (a ^ 2 * P_den)) := Nat.mul_le_mul_left _ ha_step
          _ = ((2 * y₀) * (2 * a + 5)) * (a ^ 2 * P_den) := by ring
          _ ≤ ((2 * y₀ + 5) * (2 * a)) * (a ^ 2 * P_den) :=
              Nat.mul_le_mul_right _ (by nlinarith [hya])
          _ = (2 * a) * ((2 * y₀ + 5) * (a ^ 2 * P_den)) := by ring
      simp only [List.map_cons, List.prod_cons]
      exact Nat.le_of_mul_le_mul_left hy_step (by omega)

private def evenIdx : List ℕ → List ℕ
  | [] => []
  | [x] => [x]
  | x :: _ :: xs => x :: evenIdx xs

private def oddIdx : List ℕ → List ℕ
  | [] => []
  | [_] => []
  | _ :: y :: xs => y :: oddIdx xs

private lemma prod_map_evenIdx_mul_oddIdx (f : ℕ → ℕ) :
    ∀ L : List ℕ, (L.map f).prod = ((evenIdx L).map f).prod * ((oddIdx L).map f).prod
  | [] => by simp [evenIdx, oddIdx]
  | [x] => by simp [evenIdx, oddIdx]
  | x :: y :: xs => by
      simp only [evenIdx, oddIdx, List.map_cons, List.prod_cons]
      rw [prod_map_evenIdx_mul_oddIdx f xs]
      ring

private lemma mem_evenIdx_subset : ∀ {L : List ℕ} {x : ℕ}, x ∈ evenIdx L → x ∈ L
  | [], _ => by simp [evenIdx]
  | [a], x => by simp [evenIdx]
  | a :: b :: xs, x => by
      simp only [evenIdx, List.mem_cons]
      rintro (rfl | hx)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (mem_evenIdx_subset hx))

private lemma mem_oddIdx_subset : ∀ {L : List ℕ} {x : ℕ}, x ∈ oddIdx L → x ∈ L
  | [], _ => by simp [oddIdx]
  | [a], _ => by simp [oddIdx]
  | a :: b :: xs, x => by
      simp only [oddIdx, List.mem_cons]
      rintro (rfl | hx)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (mem_oddIdx_subset hx))

private lemma oddIdx_mem_tail : ∀ {h : ℕ} {t : List ℕ} {y : ℕ}, y ∈ oddIdx (h :: t) → y ∈ t
  | _, [], _ => by simp [oddIdx]
  | _, b :: xs, y => by
      simp only [oddIdx, List.mem_cons]
      rintro (rfl | hy)
      · exact Or.inl rfl
      · exact Or.inr (mem_oddIdx_subset hy)

private lemma evenIdx_head?_cons (a : ℕ) (t : List ℕ) : (evenIdx (a :: t)).head? = some a := by
  cases t with
  | nil => simp [evenIdx]
  | cons b xs => simp [evenIdx]

private lemma evenIdx_isChain {R : ℕ → ℕ → Prop} :
    ∀ L : List ℕ, L.IsChain (· < ·) →
      (∀ a b c, a ∈ L → b ∈ L → c ∈ L → a < b → b < c → R a c) →
      (evenIdx L).IsChain R
  | [], _, _ => by simp [evenIdx]
  | [x], _, _ => by simp [evenIdx]
  | [x, y], _, _ => by simp [evenIdx]
  | x :: y :: z :: xs, hchain, hR => by
      have htail : (z :: xs).IsChain (· < ·) := hchain.tail.tail
      have hR' : ∀ a b c, a ∈ z :: xs → b ∈ z :: xs → c ∈ z :: xs → a < b → b < c → R a c :=
        fun a b c ha hb hc hab hbc =>
          hR a b c (by simp [ha]) (by simp [hb]) (by simp [hc]) hab hbc
      have ih := evenIdx_isChain (z :: xs) htail hR'
      have hxy : x < y := hchain.rel
      have hyz : y < z := hchain.tail.rel
      have hxz : R x z := hR x y z (by simp) (by simp) (by simp) hxy hyz
      rw [evenIdx]
      refine ih.cons ?_
      intro v hv
      rw [evenIdx_head?_cons] at hv
      injection hv with hv
      subst hv
      exact hxz

private lemma oddIdx_isChain {R : ℕ → ℕ → Prop} :
    ∀ L : List ℕ, L.IsChain (· < ·) →
      (∀ a b c, a ∈ L → b ∈ L → c ∈ L → a < b → b < c → R a c) →
      (oddIdx L).IsChain R
  | [], _, _ => by simp [oddIdx]
  | [_], _, _ => by simp [oddIdx]
  | [_, y], _, _ => by simp [oddIdx]
  | [_, y, _], _, _ => by simp [oddIdx]
  | x :: y :: z :: w :: xs, hchain, hR => by
      have htail : (z :: w :: xs).IsChain (· < ·) := hchain.tail.tail
      have hR' : ∀ a b c, a ∈ z :: w :: xs → b ∈ z :: w :: xs → c ∈ z :: w :: xs →
          a < b → b < c → R a c :=
        fun a b c ha hb hc hab hbc =>
          hR a b c (by simp [ha]) (by simp [hb]) (by simp [hc]) hab hbc
      have ih := oddIdx_isChain (z :: w :: xs) htail hR'
      have hyz : y < z := hchain.tail.rel
      have hzw : z < w := hchain.tail.tail.rel
      have hyw : R y w := hR y z w (by simp) (by simp) (by simp) hyz hzw
      simp only [oddIdx] at ih ⊢
      refine ih.cons ?_
      intro v hv
      simp only [List.head?_cons] at hv
      injection hv with hv
      subst hv
      exact hyw

private lemma three_free_restrained_structure {N q r₀ : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (h3 : ¬ 3 ∣ N) (hr₀ : largeSources N q = {r₀}) :
    q.Prime ∧ Odd q ∧ q % 12 = 1 ∧ 13 ≤ q ∧
    r₀ ∈ N.primeFactors ∧ r₀.Prime ∧ Odd r₀ ∧ r₀ ≠ q ∧
    r₀ % 3 = 1 ∧ 7 ≤ r₀ ∧
    N.primeFactors = insert q (insert r₀ (squareSources N)) ∧
    r₀ ∉ squareSources N ∧ q ∉ insert r₀ (squareSources N) ∧
    (∀ u ∈ squareSources N,
      u.Prime ∧ Odd u ∧ N.factorization u = 2 ∧ u % 3 = 2 ∧ 5 ≤ u ∧
      sigma 1 (u ^ N.factorization u) = u ^ 2 + u + 1 ∧
      (u ^ 2 + u + 1).primeFactors ⊆ {q, r₀}) := by
  have hle : (largeSources N q).card ≤ 1 := by rw [hr₀, Finset.card_singleton]
  obtain ⟨r₁, hr₁, hq12, hr₁3, _, hq13, hr₁7, _⟩ :=
    restrained_three_free_euler_exp_ge_17 ho hN hq hq4 he hev h3 hle
  have hr_eq : r₁ = r₀ := by
    have : r₁ ∈ ({r₀} : Finset ℕ) := by rw [← hr₀, hr₁]; exact Finset.mem_singleton_self r₁
    exact Finset.mem_singleton.mp this
  subst r₁
  have hr₀_mem_large : r₀ ∈ largeSources N q := by rw [hr₀]; exact Finset.mem_singleton_self r₀
  obtain ⟨hr₀_mem, _, hr₀q, _⟩ := Finset.mem_filter.mp hr₀_mem_large
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hq_odd : Odd q := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hq)
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀_mem
  have hr₀_odd : Odd r₀ := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr₀_mem)
  have h3not : 3 ∉ N.primeFactors := fun h => h3 (Nat.dvd_of_mem_primeFactors h)
  have hsq1_zero : (squareSourcesOne N).card = 0 := by
    have h3zero : N.factorization 3 = 0 := Finsupp.notMem_support_iff.mp h3not
    have := squareSourcesOne_card_le_three_exponent hN
    omega
  have hpart : N.primeFactors = insert q (insert r₀ (squareSources N)) := by
    ext r
    simp only [Finset.mem_insert, squareSources, Finset.mem_filter]
    constructor
    · intro hr
      by_cases hrq : r = q
      · exact Or.inl hrq
      · have hr3 : r ≠ 3 := fun h => h3not (h ▸ hr)
        have hpos : 0 < N.factorization r := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr)
        obtain ⟨k, hk⟩ := hev r hrq
        by_cases htwo : N.factorization r = 2
        · exact Or.inr (Or.inr ⟨hr, hr3, htwo⟩)
        · have hlarge_r : r ∈ largeSources N q :=
            Finset.mem_filter.mpr ⟨hr, hr3, hrq, by omega⟩
          rw [hr₀, Finset.mem_singleton] at hlarge_r
          exact Or.inr (Or.inl hlarge_r)
    · rintro (rfl | rfl | ⟨hr, _, _⟩)
      · exact hq
      · exact hr₀_mem
      · exact hr
  have hr₀_not_S : r₀ ∉ squareSources N := by
    intro h
    have := (Finset.mem_filter.mp h).2.2
    omega
  have hq_not_ins : q ∉ insert r₀ (squareSources N) := by
    intro h
    rcases Finset.mem_insert.mp h with hqr | hqS
    · exact hr₀q hqr.symm
    · have := (Finset.mem_filter.mp hqS).2.2
      omega
  have hS_prop : ∀ u ∈ squareSources N,
      u.Prime ∧ Odd u ∧ N.factorization u = 2 ∧ u % 3 = 2 ∧ 5 ≤ u ∧
      sigma 1 (u ^ N.factorization u) = u ^ 2 + u + 1 ∧
      (u ^ 2 + u + 1).primeFactors ⊆ {q, r₀} := by
    intro u hu
    obtain ⟨hu_mem, _, hu_exp2⟩ := Finset.mem_filter.mp hu
    have hup := Nat.prime_of_mem_primeFactors hu_mem
    have hu_odd := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hu_mem)
    have hu_mod3 : u % 3 = 2 := by
      by_contra! hne2
      have h0or1 : u % 3 = 0 ∨ u % 3 = 1 := by omega
      rcases h0or1 with h0 | h1
      · have hd3 : 3 ∣ u := Nat.dvd_of_mod_eq_zero h0
        have heq3 := (Nat.dvd_prime hup).mp hd3
        have := hup.two_le
        omega
      · have hu_sq1 : u ∈ squareSourcesOne N := Finset.mem_filter.mpr ⟨hu, h1⟩
        have hpos : 0 < (squareSourcesOne N).card := Finset.card_pos.mpr ⟨u, hu_sq1⟩
        omega
    have hu5 : 5 ≤ u := by
      have := hup.two_le
      have := Nat.odd_iff.mp hu_odd
      omega
    have hsig : sigma 1 (u ^ N.factorization u) = u ^ 2 + u + 1 := by
      rw [hu_exp2, sigma_one_apply_prime_pow hup]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero]
      ring
    have hsub : (u ^ 2 + u + 1).primeFactors ⊆ {q, r₀} := by
      intro w hw
      obtain ⟨hw_prime, hw_dvd, _⟩ := Nat.mem_primeFactors.mp hw
      have hsum_odd : Odd (u ^ 2 + u + 1) :=
        ((hu_odd.pow).add_odd hu_odd).add_odd (by decide : Odd 1)
      have hw_odd : Odd w := hsum_odd.of_dvd_nat hw_dvd
      have hw_ne3 : w ≠ 3 := by
        intro h
        subst h
        have hsum_mod3 : (u ^ 2 + u + 1) % 3 = 1 := by
          rw [Nat.add_mod, Nat.add_mod (u ^ 2), Nat.pow_mod, hu_mod3]
        omega
      have hw_mod3 : w % 3 = 1 :=
        (prime_dvd_sq_add_self_add_one hw_prime hw_dvd).resolve_left hw_ne3
      have hwN : w ∣ N := by
        apply dvd_perfect_of_exact_prime_pow hN hup (Nat.ordProj_dvd N u) _ hw_prime hw_odd
        · rw [← sigma_one_apply, hsig]
          exact hw_dvd
        · rw [hup.pow_dvd_iff_le_factorization hN.2.ne']
          omega
      have hw_mem := Nat.mem_primeFactors.mpr ⟨hw_prime, hwN, hN.2.ne'⟩
      rw [hpart, Finset.mem_insert, Finset.mem_insert] at hw_mem
      rcases hw_mem with rfl | rfl | hwS
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · have hw_sq1 : w ∈ squareSourcesOne N := Finset.mem_filter.mpr ⟨hwS, hw_mod3⟩
        have hpos : 0 < (squareSourcesOne N).card := Finset.card_pos.mpr ⟨w, hw_sq1⟩
        omega
    exact ⟨hup, hu_odd, hu_exp2, hu_mod3, hu5, hsig, hsub⟩
  exact ⟨hq_prime, hq_odd, hq12, hq13, hr₀_mem, hr₀_prime, hr₀_odd, hr₀q, hr₁3, hr₁7,
    hpart, hr₀_not_S, hq_not_ins, hS_prop⟩

/-- Unconditional elimination of all three-free restrained odd perfect numbers:
if `¬ 3 ∣ N`, then at least two non-Euler primes `r ≠ 3` have exponent `≥ 4`. -/
theorem two_le_largeSources_of_three_free {N q : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) (h3 : ¬ 3 ∣ N) :
    2 ≤ (largeSources N q).card := by
  by_contra! hlt
  have hle : (largeSources N q).card ≤ 1 := by omega
  obtain ⟨r₀, hr₀, _, _, _, _, _, _⟩ :=
    restrained_three_free_euler_exp_ge_17 ho hN hq hq4 he hev h3 hle
  obtain ⟨hq_prime, hq_odd, hq12, hq13, hr₀_mem, hr₀_prime, hr₀_odd, hr₀q, hr₀3, hr₀7,
    hpart, hr₀_not_S, hq_not_ins, hS_prop⟩ :=
    three_free_restrained_structure ho hN hq hq4 he hev h3 hr₀
  let S := squareSources N
  have hS_not_11 : 11 ∉ S := by
    intro h11
    have hsub := (hS_prop 11 h11).2.2.2.2.2.2
    have h7_mem : 7 ∈ (11 ^ 2 + 11 + 1).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨by norm_num, by norm_num, by norm_num⟩
    have h19_mem : 19 ∈ (11 ^ 2 + 11 + 1).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨by norm_num, by norm_num, by norm_num⟩
    have h7 := Finset.mem_insert.mp (hsub h7_mem)
    have h19 := Finset.mem_insert.mp (hsub h19_mem)
    rcases h7 with h7q | h7r <;> rcases h19 with h19q | h19r
    · omega
    · omega
    · omega
    · rw [Finset.mem_singleton] at h7r h19r
      omega
  have hS_not_23 : 23 ∉ S := by
    intro h23
    have hsub := (hS_prop 23 h23).2.2.2.2.2.2
    have h7_mem : 7 ∈ (23 ^ 2 + 23 + 1).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨by norm_num, by norm_num, by norm_num⟩
    have h79_mem : 79 ∈ (23 ^ 2 + 23 + 1).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨by norm_num, by norm_num, by norm_num⟩
    have h7 := Finset.mem_insert.mp (hsub h7_mem)
    have h79 := Finset.mem_insert.mp (hsub h79_mem)
    rcases h7 with h7q | h7r <;> rcases h79 with h79q | h79r
    · omega
    · omega
    · omega
    · rw [Finset.mem_singleton] at h7r h79r
      omega
  have h5_r0 : 5 ∈ S → r₀ = 31 := by
    intro h5
    have hsub := (hS_prop 5 h5).2.2.2.2.2.2
    have h31_mem : 31 ∈ (5 ^ 2 + 5 + 1).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨by norm_num, by norm_num, by norm_num⟩
    rcases Finset.mem_insert.mp (hsub h31_mem) with hq31 | hr31
    · omega
    · exact (Finset.mem_singleton.mp hr31).symm
  have h17_r0 : 17 ∈ S → r₀ = 307 := by
    intro h17
    have hsub := (hS_prop 17 h17).2.2.2.2.2.2
    have h307_mem : 307 ∈ (17 ^ 2 + 17 + 1).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨by norm_num, by norm_num, by norm_num⟩
    rcases Finset.mem_insert.mp (hsub h307_mem) with hq307 | hr307
    · omega
    · exact (Finset.mem_singleton.mp hr307).symm
  have h5_17_excl : ¬ (5 ∈ S ∧ 17 ∈ S) := by
    rintro ⟨h5, h17⟩
    have := h5_r0 h5
    have := h17_r0 h17
    omega
  have hS_cases : ∀ u ∈ S, u = 5 ∨ u = 17 ∨ 29 ≤ u := by
    intro u hu
    obtain ⟨_, hu_odd, _, hu3, hu5, _, _⟩ := hS_prop u hu
    have hu2 : u % 2 = 1 := Nat.odd_iff.mp hu_odd
    have hne11 : u ≠ 11 := fun h => hS_not_11 (h ▸ hu)
    have hne23 : u ≠ 23 := fun h => hS_not_23 (h ▸ hu)
    omega
  have hS_pow : ∀ u ∈ S,
      u ^ 2 + u + 1 =
        q ^ (u ^ 2 + u + 1).factorization q * r₀ ^ (u ^ 2 + u + 1).factorization r₀ := by
    intro u hu
    exact eq_mul_pow_of_primeFactors_subset_pair (by omega) hr₀q.symm
      (hS_prop u hu).2.2.2.2.2.2
  let L := S.sort
  have hL_chain_lt : L.IsChain (· < ·) := (Finset.sortedLT_sort S).isChain
  have hL_pair_lt : L.Pairwise (· < ·) := (Finset.sortedLT_sort S).pairwise
  have hL_mem : ∀ x, x ∈ L ↔ x ∈ S := fun x => Finset.mem_sort (· ≤ ·)
  have hprod_sort : ∀ f : ℕ → ℕ, (∏ u ∈ S, f u) = (L.map f).prod := by
    intro f
    rw [← Finset.prod_map_toList S f]
    exact ((Finset.sort_perm_toList S (· ≤ ·)).map f).prod_eq.symm
  let P_ev_num := ((evenIdx L).map (fun u => u ^ 2 + u + 1)).prod
  let P_ev_den := ((evenIdx L).map (fun u => u ^ 2)).prod
  let P_od_num := ((oddIdx L).map (fun u => u ^ 2 + u + 1)).prod
  let P_od_den := ((oddIdx L).map (fun u => u ^ 2)).prod
  have hN_eq : q ^ N.factorization q * r₀ ^ N.factorization r₀ * P_ev_den * P_od_den = N := by
    have hfac := Nat.prod_primeFactors_pow_factorization hN.2.ne'
    rw [hpart, Finset.prod_insert hq_not_ins, Finset.prod_insert hr₀_not_S] at hfac
    have hS_prod : (∏ u ∈ S, u ^ N.factorization u) = P_ev_den * P_od_den := by
      have h1 : (∏ u ∈ S, u ^ N.factorization u) = ∏ u ∈ S, u ^ 2 :=
        Finset.prod_congr rfl fun u hu => by rw [(hS_prop u hu).2.2.1]
      rw [h1, hprod_sort]
      exact prod_map_evenIdx_mul_oddIdx (fun u => u ^ 2) L
    rw [hS_prod] at hfac
    calc
      q ^ N.factorization q * r₀ ^ N.factorization r₀ * P_ev_den * P_od_den
          = q ^ N.factorization q * (r₀ ^ N.factorization r₀ * (P_ev_den * P_od_den)) := by ring
      _ = N := hfac.symm
  have hσ_eq : sigma 1 (q ^ N.factorization q) * sigma 1 (r₀ ^ N.factorization r₀) *
      P_ev_num * P_od_num = 2 * N := by
    have hσN : sigma 1 N = 2 * N :=
      (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).mp hN)
    have hmul : sigma 1 N = ∏ p ∈ N.primeFactors, sigma 1 (p ^ N.factorization p) :=
      isMultiplicative_sigma.multiplicative_factorization (sigma 1) hN.2.ne'
    rw [hσN, hpart, Finset.prod_insert hq_not_ins, Finset.prod_insert hr₀_not_S] at hmul
    have hS_prod : (∏ u ∈ S, sigma 1 (u ^ N.factorization u)) = P_ev_num * P_od_num := by
      have h1 : (∏ u ∈ S, sigma 1 (u ^ N.factorization u)) = ∏ u ∈ S, (u ^ 2 + u + 1) :=
        Finset.prod_congr rfl fun u hu => (hS_prop u hu).2.2.2.2.2.1
      rw [h1, hprod_sort]
      exact prod_map_evenIdx_mul_oddIdx (fun u => u ^ 2 + u + 1) L
    rw [hS_prod] at hmul
    calc
      sigma 1 (q ^ N.factorization q) * sigma 1 (r₀ ^ N.factorization r₀) * P_ev_num * P_od_num
          = sigma 1 (q ^ N.factorization q) *
              (sigma 1 (r₀ ^ N.factorization r₀) * (P_ev_num * P_od_num)) := by ring
      _ = 2 * N := hmul.symm
  have hstep_triple : ∀ a b c, a ∈ L → b ∈ L → c ∈ L → a < b → b < c → 5 * a + 3 ≤ 2 * c := by
    intro a b c ha hb hc hab hbc
    rw [hL_mem] at ha hb hc
    obtain ⟨_, ha_odd, _, ha3, ha5, _, _⟩ := hS_prop a ha
    obtain ⟨_, hb_odd, _, hb3, _, _, _⟩ := hS_prop b hb
    obtain ⟨_, hc_odd, _, hc3, _, _, _⟩ := hS_prop c hc
    exact (two_prime_smooth_sq_add_self_add_one_step
      hq_prime hq_odd (by omega : q % 3 = 1) hr₀_prime hr₀_odd hr₀3
      hab hbc ha_odd hb_odd hc_odd ha5 ha3 hb3 hc3
      (hS_pow a ha) (hS_pow b hb) (hS_pow c hc)).2
  have hev_chain : (evenIdx L).IsChain (fun x y => 5 * x + 3 ≤ 2 * y) :=
    evenIdx_isChain L hL_chain_lt hstep_triple
  have hod_chain : (oddIdx L).IsChain (fun x y => 5 * x + 3 ≤ 2 * y) :=
    oddIdx_isChain L hL_chain_lt hstep_triple
  have hev_ge5 : ∀ x ∈ evenIdx L, 5 ≤ x := fun x hx =>
    (hS_prop x ((hL_mem x).mp (mem_evenIdx_subset hx))).2.2.2.2.1
  have hod_ge5 : ∀ x ∈ oddIdx L, 5 ≤ x := fun x hx =>
    (hS_prop x ((hL_mem x).mp (mem_oddIdx_subset hx))).2.2.2.2.1
  have hP_ev_pos : 0 < P_ev_num := List.prod_pos (by
    intro y hy
    rcases List.mem_map.mp hy with ⟨u, _, rfl⟩
    positivity)
  have hP_od_pos : 0 < P_od_num := List.prod_pos (by
    intro y hy
    rcases List.mem_map.mp hy with ⟨u, _, rfl⟩
    positivity)
  have hq_coef : 12 * q ≤ 13 * (q - 1) := by
    have hq1 : 1 ≤ q := le_trans (by decide) hq13
    zify [hq1]
    linarith [hq13]
  have hq_ratio : 12 * sigma 1 (q ^ N.factorization q) < 13 * q ^ N.factorization q :=
    sigma_prime_pow_ratio_lt_closure hq_prime (by decide) hq_coef
  have hod_head_gt : ∀ y ∈ (oddIdx L).head?, ∃ h ∈ S, h < y ∧ y ∈ S := by
    intro y hy
    cases hL_eq : L with
    | nil => simp [hL_eq, oddIdx] at hy
    | cons h t =>
        have hy_od : y ∈ oddIdx (h :: t) := by
          rw [← hL_eq]
          exact List.mem_of_head? hy
        have hy_t : y ∈ t := oddIdx_mem_tail hy_od
        have hpair' : (h :: t).Pairwise (· < ·) := hL_eq ▸ hL_pair_lt
        have hh_lt : h < y := (List.pairwise_cons.mp hpair').1 y hy_t
        have hh_S : h ∈ S := (hL_mem h).mp (hL_eq ▸ List.mem_cons_self)
        have hy_S : y ∈ S := (hL_mem y).mp (hL_eq ▸ List.mem_cons_of_mem _ hy_t)
        exact ⟨h, hh_S, hh_lt, hy_S⟩
  by_cases h5 : 5 ∈ S
  · have hr0_eq : r₀ = 31 := h5_r0 h5
    have hnot17 : 17 ∉ S := fun h17 => h5_17_excl ⟨h5, h17⟩
    have hr₀_coef : 30 * r₀ ≤ 31 * (r₀ - 1) := by omega
    have hr_ratio : 30 * sigma 1 (r₀ ^ N.factorization r₀) < 31 * r₀ ^ N.factorization r₀ :=
      sigma_prime_pow_ratio_lt_closure hr₀_prime (by decide) hr₀_coef
    have hev_head : ∀ x ∈ (evenIdx L).head?, 5 ≤ x := fun x hx =>
      hev_ge5 x (List.mem_of_head? hx)
    have hP_ev_bd : 10 * P_ev_num ≤ 15 * P_ev_den := by
      simpa using prod_sq_abundancy_le_of_five_halves_step (evenIdx L) hev_chain hev_ge5 5 (by decide) hev_head
    have hod_head : ∀ y ∈ (oddIdx L).head?, 29 ≤ y := by
      intro y hy
      obtain ⟨h, hh_S, hh_lt, hy_S⟩ := hod_head_gt y hy
      have hh5 : 5 ≤ h := (hS_prop h hh_S).2.2.2.2.1
      rcases hS_cases y hy_S with rfl | rfl | h29
      · omega
      · exact (hnot17 hy_S).elim
      · exact h29
    have hP_od_bd : 58 * P_od_num ≤ 63 * P_od_den := by
      simpa using prod_sq_abundancy_le_of_five_halves_step (oddIdx L) hod_chain hod_ge5 29 (by decide) hod_head
    exact abundancy_contradiction4_le (cq := 12) (dq := 13) (cr := 30) (dr := 31)
      (cev := 10) (dev := 15) (cod := 58) (dod := 63)
      hN.2 hσ_eq hN_eq hq_ratio hr_ratio
      (Nat.mul_pos (by decide) hP_ev_pos) hP_ev_bd
      (Nat.mul_pos (by decide) hP_od_pos) hP_od_bd
      (by norm_num)
  · have hr₀_coef : 6 * r₀ ≤ 7 * (r₀ - 1) := by
      have hr1 : 1 ≤ r₀ := le_trans (by decide) hr₀7
      zify [hr1]
      linarith [hr₀7]
    have hr_ratio : 6 * sigma 1 (r₀ ^ N.factorization r₀) < 7 * r₀ ^ N.factorization r₀ :=
      sigma_prime_pow_ratio_lt_closure hr₀_prime (by decide) hr₀_coef
    have hev_head : ∀ x ∈ (evenIdx L).head?, 17 ≤ x := by
      intro x hx
      have hx_S : x ∈ S := (hL_mem x).mp (mem_evenIdx_subset (List.mem_of_head? hx))
      rcases hS_cases x hx_S with rfl | rfl | h29
      · exact (h5 hx_S).elim
      · omega
      · omega
    have hP_ev_bd : 34 * P_ev_num ≤ 39 * P_ev_den := by
      simpa using prod_sq_abundancy_le_of_five_halves_step (evenIdx L) hev_chain hev_ge5 17 (by decide) hev_head
    have hod_head : ∀ y ∈ (oddIdx L).head?, 29 ≤ y := by
      intro y hy
      obtain ⟨h, hh_S, hh_lt, hy_S⟩ := hod_head_gt y hy
      have hh17 : 17 ≤ h := by
        rcases hS_cases h hh_S with rfl | rfl | h29
        · exact (h5 hh_S).elim
        · omega
        · omega
      rcases hS_cases y hy_S with rfl | rfl | h29
      · exact (h5 hy_S).elim
      · omega
      · exact h29
    have hP_od_bd : 58 * P_od_num ≤ 63 * P_od_den := by
      simpa using prod_sq_abundancy_le_of_five_halves_step (oddIdx L) hod_chain hod_ge5 29 (by decide) hod_head
    exact abundancy_contradiction4_le (cq := 12) (dq := 13) (cr := 6) (dr := 7)
      (cev := 34) (dev := 39) (cod := 58) (dod := 63)
      hN.2 hσ_eq hN_eq hq_ratio hr_ratio
      (Nat.mul_pos (by decide) hP_ev_pos) hP_ev_bd
      (Nat.mul_pos (by decide) hP_od_pos) hP_od_bd
      (by norm_num)

/-- Every restrained odd perfect number (`(largeSources N q).card ≤ 1`) must be divisible by `3`. -/
theorem three_dvd_of_largeSources_le_one {N q : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hle : (largeSources N q).card ≤ 1) :
    3 ∣ N := by
  by_contra h3
  have h2 := two_le_largeSources_of_three_free ho hN hq hq4 he hev h3
  omega

/-- If `largeSources N q = ∅`, then `3 ∈ N.primeFactors` and the component index at `3` yields
at least an `8`-factor drop: `cardFactors (componentIndex N 3) + 8 ≤ cardFactors N`. -/
theorem exists_eight_drop_at_three_of_largeSources_empty {N q : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r)) (hempty : largeSources N q = ∅) :
    3 ∈ N.primeFactors ∧ cardFactors (componentIndex N 3) + 8 ≤ cardFactors N := by
  have h3_8 := eight_le_three_exponent_of_largeSources_empty ho hN hq hq4 he hev hempty
  have h3_mem : 3 ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨by decide, Nat.dvd_of_factorization_pos (by omega), hN.2.ne'⟩
  have hbal := cardFactors_componentIndex_add_eq hN h3_mem
  have hpow_gt1 : 1 < ordProj[3] N := one_lt_pow₀ (by decide) (by omega)
  have hsig_gt1 : 1 < sigma 1 (ordProj[3] N) :=
    hpow_gt1.trans (self_lt_sigma_of_one_lt hpow_gt1)
  have hsig_pos : 0 < cardFactors (sigma 1 (ordProj[3] N)) :=
    cardFactors_pos_iff_one_lt.mpr hsig_gt1
  exact ⟨h3_mem, by omega⟩

end OddPerfect
