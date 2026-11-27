module

public import OddPerfect.GlobalWave11Obstruction
import Mathlib.Tactic.Ring

/-!
# Ten-Factor Component-Index Drop Obstruction (`OddPerfect.TenFactorDropObstruction`)

Establishes the structural obstruction profile when no prime component `p ∈ N.primeFactors`
drops the prime-factor multiplicity of its component index by at least `10`
(`∀ p ∈ N.primeFactors, cardFactors N < cardFactors (componentIndex N p) + 10`), together with
unconditional obstructions on `5`-adic and `q`-adic Euler exponents and tenth-power divisors:
1. `five_factorization_mod_six_ne_five` & `euler_five_exponent_mod_twelve`:
   For every odd perfect number `N`, `N.factorization 5 % 6 ≠ 5` (since `3, 7 ∣ σ(5^5) = 3906`
   forces `105 ∣ N`, contradicting Sylvester's `not_dvd_105_of_odd_perfect`), so when `q = 5`
   the Euler exponent `a` satisfies `a % 12 = 1 ∨ a % 12 = 9` (and `1 < a → 9 ≤ a`).
2. `six_le_cardFactors_sigma_fifth_pow_of_five_mod_twelve`:
   For every prime `q ≡ 5 [MOD 12]` with `q ≠ 5`, `6 ≤ cardFactors (sigma 1 (q ^ 5))`.
3. `four_le_cardFactors_sigma_eighth_pow_of_one_mod_three`:
   For every prime `r ≡ 1 [MOD 3]`, `4 ≤ cardFactors (sigma 1 (r ^ 8))`.
4. `no_ten_factor_drop_profile`: absence of a ten-factor drop forces:
   - `N.factorization p + cardFactors (sigma 1 (ordProj[p] N)) ≤ 10` for all `p ∈ N.primeFactors`,
   - either `N.factorization q = 1`, or `N.factorization q = 5` with `q % 12 = 1`, `13 ≤ q`,
     `3 ∣ N`, and `((q + 1) / 2).Prime ∧ (q ^ 2 - q + 1).Prime ∧ ((q ^ 2 + q + 1) / 3).Prime`,
   - tenth-power-freeness (`∀ p, p.Prime → ¬ p ^ 10 ∣ N`),
   - at any eighth-power prime `r` (`N.factorization r = 8`): `(1 + r + r ^ 2).Prime`,
     `(1 + r ^ 3 + r ^ 6).Prime`, and `r % 3 ≠ 1`,
   - global support density `2 * cardFactors N + 1 ≤ 10 * N.primeFactors.card`.
5. Unconditional ten-factor component-index drop triggers under `¬ 3 ∣ N ∧ 1 < N.factorization q`,
   any tenth power `p ^ 10 ∣ N`, Fermat linear Euler `q > 5`, or `largeSources N q = ∅` with
   `N.factorization 3 ≠ 8`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- For every odd perfect number `N`, `N.factorization 5 % 6 ≠ 5`. -/
theorem five_factorization_mod_six_ne_five {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    N.factorization 5 % 6 ≠ 5 := by
  intro h5mod
  have hk_pos : 0 < N.factorization 5 := by omega
  have h5_dvd : 5 ∣ N := Nat.dvd_of_factorization_pos hk_pos.ne'
  have hk_dvd : 5 ^ N.factorization 5 ∣ N := Nat.ordProj_dvd N 5
  have hk_next : ¬ 5 ^ (N.factorization 5 + 1) ∣ N :=
    Nat.pow_succ_factorization_not_dvd hN.2.ne' (by decide : Nat.Prime 5)
  obtain ⟨m, hm_eq⟩ : ∃ m, N.factorization 5 + 1 = 6 * m :=
    ⟨(N.factorization 5 + 1) / 6, by omega⟩
  have hgb_eq :
      (∑ d ∈ (5 ^ N.factorization 5).divisors, d) =
        geometricBlock 5 (N.factorization 5 + 1) := by
    rw [← sigma_one_apply, sigma_one_apply_prime_pow (by decide : Nat.Prime 5)]
    rfl
  have hgb_mul :
      geometricBlock 5 (N.factorization 5 + 1) =
        geometricBlock 5 6 * geometricBlock (5 ^ 6) m := by
    rw [hm_eq, geometricBlock_mul 5 6 m]
  have hgb6 : geometricBlock 5 6 = 3906 := by
    simp only [geometricBlock, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      zero_add]
    norm_num
  have h3_sig : 3 ∣ ∑ d ∈ (5 ^ N.factorization 5).divisors, d := by
    rw [hgb_eq, hgb_mul, hgb6]
    exact dvd_mul_of_dvd_left (by decide : 3 ∣ 3906) _
  have h7_sig : 7 ∣ ∑ d ∈ (5 ^ N.factorization 5).divisors, d := by
    rw [hgb_eq, hgb_mul, hgb6]
    exact dvd_mul_of_dvd_left (by decide : 7 ∣ 3906) _
  have h3_dvd : 3 ∣ N :=
    dvd_perfect_of_exact_prime_pow hN (by decide) hk_dvd hk_next (by decide) (by decide) h3_sig
  have h7_dvd : 7 ∣ N :=
    dvd_perfect_of_exact_prime_pow hN (by decide) hk_dvd hk_next (by decide) (by decide) h7_sig
  have h15_dvd : 15 ∣ N := (by decide : Nat.Coprime 3 5).mul_dvd_of_dvd_of_dvd h3_dvd h5_dvd
  have h105_dvd : 105 ∣ N := (by decide : Nat.Coprime 15 7).mul_dvd_of_dvd_of_dvd h15_dvd h7_dvd
  exact not_dvd_105_of_odd_perfect hN ho h105_dvd

/-- If the Euler prime is `5` (`N = 5 ^ a * m ^ 2`, `¬ 5 ∣ m`, `a % 4 = 1`), then
`a % 12 = 1 ∨ a % 12 = 9`, and hence `1 < a → 9 ≤ a`. -/
theorem euler_five_exponent_mod_twelve {N a m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hm : ¬ 5 ∣ m)
    (hform : N = 5 ^ a * m ^ 2) (ha4 : a % 4 = 1) :
    (a % 12 = 1 ∨ a % 12 = 9) ∧ (1 < a → 9 ≤ a) := by
  have hm0 : m ≠ 0 := by
    intro h0
    apply hN.2.ne'
    rw [hform, h0, zero_pow (by decide : 2 ≠ 0), mul_zero]
  have ha_eq : N.factorization 5 = a := by
    rw [hform, Nat.factorization_mul (pow_ne_zero a (by decide)) (pow_ne_zero 2 hm0)]
    simp only [Finsupp.coe_add, Pi.add_apply, Nat.Prime.factorization_pow (by decide : Nat.Prime 5),
      Finsupp.single_eq_same, Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [Nat.factorization_eq_zero_of_not_dvd hm, mul_zero, add_zero]
  have ha6 : a % 6 ≠ 5 := by
    rw [← ha_eq]
    exact five_factorization_mod_six_ne_five ho hN
  have h12 : a % 12 = 1 ∨ a % 12 = 9 := by omega
  refine ⟨h12, ?_⟩
  intro hgt
  omega

/-- For every prime `q ≡ 5 [MOD 12]` with `q ≠ 5`, `σ(q^5)` has at least `6` prime factors
with multiplicity. -/
theorem six_le_cardFactors_sigma_fifth_pow_of_five_mod_twelve {q : ℕ}
    (hq : q.Prime) (hq12 : q % 12 = 5) (hq5 : q ≠ 5) :
    6 ≤ cardFactors (sigma 1 (q ^ 5)) := by
  have h17 : 17 ≤ q := by omega
  obtain ⟨k, rfl⟩ : ∃ k, q = 12 * k + 17 := ⟨(q - 17) / 12, by omega⟩
  rw [sigma_one_apply_prime_pow hq]
  have hfac :
      (∑ i ∈ range (5 + 1), (12 * k + 17) ^ i) =
        2 * 3 * (2 * k + 3) * 3 * (48 * k ^ 2 + 132 * k + 91) *
          (144 * k ^ 2 + 420 * k + 307) := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
    ring
  rw [hfac,
    cardFactors_mul (by positivity) (by positivity),
    cardFactors_mul (by positivity) (by positivity),
    cardFactors_mul (by positivity) (by positivity),
    cardFactors_mul (by positivity) (by positivity),
    cardFactors_mul (by positivity) (by positivity)]
  have hc1 : 0 < cardFactors 2 := cardFactors_pos_iff_one_lt.mpr (by omega)
  have hc2 : 0 < cardFactors 3 := cardFactors_pos_iff_one_lt.mpr (by omega)
  have hc3 : 0 < cardFactors (2 * k + 3) := cardFactors_pos_iff_one_lt.mpr (by omega)
  have hc4 : 0 < cardFactors (48 * k ^ 2 + 132 * k + 91) :=
    cardFactors_pos_iff_one_lt.mpr (by omega)
  have hc5 : 0 < cardFactors (144 * k ^ 2 + 420 * k + 307) :=
    cardFactors_pos_iff_one_lt.mpr (by omega)
  omega

/-- For every prime `r ≡ 1 [MOD 3]`, `σ(r^8)` has at least `4` prime factors
with multiplicity. -/
theorem four_le_cardFactors_sigma_eighth_pow_of_one_mod_three {r : ℕ}
    (hr : r.Prime) (hr3 : r % 3 = 1) :
    4 ≤ cardFactors (sigma 1 (r ^ 8)) := by
  have hr4 : 4 ≤ r := by
    have := hr.two_le
    omega
  rw [sigma_one_apply_prime_pow hr]
  change 4 ≤ cardFactors (geometricBlock r (3 * 3))
  rw [geometricBlock_mul r 3 3]
  have h1 : geometricBlock r 3 = 1 + r + r ^ 2 := by
    simp only [geometricBlock, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      zero_add, pow_zero, pow_one]
  have h2 : geometricBlock (r ^ 3) 3 = 1 + r ^ 3 + r ^ 6 := by
    simp only [geometricBlock, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      zero_add, pow_zero, pow_one]
    ring
  have hr_mod : r ≡ 1 [MOD 3] := hr3
  have hdvd1 : 3 ∣ 1 + r + r ^ 2 := by
    have hm : 1 + r + r ^ 2 ≡ 1 + 1 + 1 ^ 2 [MOD 3] :=
      ((Nat.ModEq.refl 1).add hr_mod).add (hr_mod.pow 2)
    change (1 + r + r ^ 2) % 3 = 0 at hm
    exact Nat.dvd_of_mod_eq_zero hm
  have hdvd2 : 3 ∣ 1 + r ^ 3 + r ^ 6 := by
    have hm : 1 + r ^ 3 + r ^ 6 ≡ 1 + 1 ^ 3 + 1 ^ 6 [MOD 3] :=
      ((Nat.ModEq.refl 1).add (hr_mod.pow 3)).add (hr_mod.pow 6)
    change (1 + r ^ 3 + r ^ 6) % 3 = 0 at hm
    exact Nat.dvd_of_mod_eq_zero hm
  obtain ⟨s, hs⟩ := hdvd1
  obtain ⟨t, ht⟩ := hdvd2
  have hr2_ge : 16 ≤ r ^ 2 := by nlinarith
  have hr3_ge : 64 ≤ r ^ 3 := by nlinarith
  have hr6_ge : 4096 ≤ r ^ 6 := by nlinarith
  have hs_gt1 : 1 < s := by omega
  have ht_gt1 : 1 < t := by omega
  rw [h1, h2, hs, ht,
    cardFactors_mul (by positivity) (by positivity),
    cardFactors_mul (by positivity) (by positivity),
    cardFactors_mul (by positivity) (by positivity)]
  have hc3 : 0 < cardFactors 3 := cardFactors_pos_iff_one_lt.mpr (by omega)
  have hcs : 0 < cardFactors s := cardFactors_pos_iff_one_lt.mpr hs_gt1
  have hct : 0 < cardFactors t := cardFactors_pos_iff_one_lt.mpr ht_gt1
  omega

/-- Structural profile of an odd perfect number lacking a ten-factor component-index drop. -/
theorem no_ten_factor_drop_profile {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (_hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hno : ∀ p ∈ N.primeFactors, cardFactors N < cardFactors (componentIndex N p) + 10) :
    (∀ p ∈ N.primeFactors, N.factorization p + cardFactors (sigma 1 (ordProj[p] N)) ≤ 10) ∧
    (N.factorization q = 1 ∨
      (N.factorization q = 5 ∧ q % 12 = 1 ∧ 13 ≤ q ∧ 3 ∣ N ∧
        ((q + 1) / 2).Prime ∧ (q ^ 2 - q + 1).Prime ∧ ((q ^ 2 + q + 1) / 3).Prime)) ∧
    (∀ p : ℕ, p.Prime → ¬ p ^ 10 ∣ N) ∧
    (∀ r ∈ N.primeFactors, N.factorization r = 8 →
      (1 + r + r ^ 2).Prime ∧ (1 + r ^ 3 + r ^ 6).Prime ∧ r % 3 ≠ 1) ∧
    2 * cardFactors N + 1 ≤ 10 * N.primeFactors.card := by
  have hcap : ∀ p ∈ N.primeFactors,
      N.factorization p + cardFactors (sigma 1 (ordProj[p] N)) ≤ 10 := by
    intro p hp
    have hbal := cardFactors_componentIndex_add_eq hN hp
    have hlt := hno p hp
    omega
  have hsig_pos_of : ∀ p : ℕ, p.Prime → N.factorization p ≠ 0 →
      0 < cardFactors (sigma 1 (ordProj[p] N)) := by
    intro p hp hp_ne0
    have hpow_gt1 : 1 < ordProj[p] N := one_lt_pow₀ hp.one_lt hp_ne0
    have hsig_gt1 : 1 < sigma 1 (ordProj[p] N) :=
      hpow_gt1.trans (self_lt_sigma_of_one_lt hpow_gt1)
    exact cardFactors_pos_iff_one_lt.mpr hsig_gt1
  have hq_dichotomy :
      N.factorization q = 1 ∨
        (N.factorization q = 5 ∧ q % 12 = 1 ∧ 13 ≤ q ∧ 3 ∣ N ∧
          ((q + 1) / 2).Prime ∧ (q ^ 2 - q + 1).Prime ∧ ((q ^ 2 + q + 1) / 3).Prime) := by
    have hq_cap := hcap q hq
    have hq_prime := Nat.prime_of_mem_primeFactors hq
    have hq_pos : 0 < N.factorization q := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hq)
    have hsig_pos := hsig_pos_of q hq_prime hq_pos.ne'
    have hq_le9 : N.factorization q ≤ 9 := by omega
    rcases (show N.factorization q = 1 ∨ N.factorization q = 5 ∨ N.factorization q = 9 by
        omega) with h1 | h5 | h9
    · exact Or.inl h1
    · right
      have hq_ord : ordProj[q] N = q ^ 5 := by rw [h5]
      have hcf5 : cardFactors (sigma 1 (q ^ 5)) ≤ 5 := by
        rw [hq_ord, h5] at hq_cap
        omega
      have hq_ne5 : q ≠ 5 := by
        intro hq5
        subst hq5
        have hbad := five_factorization_mod_six_ne_five ho hN
        omega
      have hndvd3 : ¬ 3 ∣ q := by
        intro h3
        rcases (Nat.dvd_prime hq_prime).mp h3 with h_one | h_three
        · omega
        · omega
      have hq12 : q % 12 = 1 := by
        by_contra hnot1
        have hq12_5 : q % 12 = 5 := by
          have hq3 : q % 3 ≠ 0 := fun h0 => hndvd3 (Nat.dvd_of_mod_eq_zero h0)
          omega
        have h6 := six_le_cardFactors_sigma_fifth_pow_of_five_mod_twelve hq_prime hq12_5 hq_ne5
        omega
      have h13 : 13 ≤ q := by
        have := hq_prime.two_le
        omega
      obtain ⟨k, hqk⟩ : ∃ k, q = 12 * k + 13 := ⟨(q - 13) / 12, by omega⟩
      have hsig5_fac :
          sigma 1 (q ^ 5) =
            2 * 3 * (6 * k + 7) * (144 * k ^ 2 + 300 * k + 157) *
              (48 * k ^ 2 + 108 * k + 61) := by
        rw [sigma_one_apply_prime_pow hq_prime, hqk]
        simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
        ring
      have hcf_sum :
          cardFactors 2 + cardFactors 3 + cardFactors (6 * k + 7) +
            cardFactors (144 * k ^ 2 + 300 * k + 157) +
            cardFactors (48 * k ^ 2 + 108 * k + 61) ≤ 5 := by
        rw [hsig5_fac,
          cardFactors_mul (by positivity) (by positivity),
          cardFactors_mul (by positivity) (by positivity),
          cardFactors_mul (by positivity) (by positivity),
          cardFactors_mul (by positivity) (by positivity)] at hcf5
        exact hcf5
      have hc2 : 0 < cardFactors 2 := cardFactors_pos_iff_one_lt.mpr (by omega)
      have hc3 : 0 < cardFactors 3 := cardFactors_pos_iff_one_lt.mpr (by omega)
      have hca : 0 < cardFactors (6 * k + 7) := cardFactors_pos_iff_one_lt.mpr (by omega)
      have hcb : 0 < cardFactors (144 * k ^ 2 + 300 * k + 157) :=
        cardFactors_pos_iff_one_lt.mpr (by omega)
      have hcc : 0 < cardFactors (48 * k ^ 2 + 108 * k + 61) :=
        cardFactors_pos_iff_one_lt.mpr (by omega)
      have hpa : (6 * k + 7).Prime := cardFactors_eq_one_iff_prime.mp (by omega)
      have hpb : (144 * k ^ 2 + 300 * k + 157).Prime := cardFactors_eq_one_iff_prime.mp (by omega)
      have hpc : (48 * k ^ 2 + 108 * k + 61).Prime := cardFactors_eq_one_iff_prime.mp (by omega)
      have heq1 : (q + 1) / 2 = 6 * k + 7 := by omega
      have heq2 : q ^ 2 - q + 1 = 144 * k ^ 2 + 300 * k + 157 := by
        have hq_sq : q ≤ q ^ 2 := Nat.le_self_pow (by decide : 2 ≠ 0) q
        have hq_id : q ^ 2 + 1 = q + (144 * k ^ 2 + 300 * k + 157) := by
          rw [hqk]
          ring
        omega
      have heq3 : (q ^ 2 + q + 1) / 3 = 48 * k ^ 2 + 108 * k + 61 := by
        have hdiv : q ^ 2 + q + 1 = 3 * (48 * k ^ 2 + 108 * k + 61) := by
          rw [hqk]
          ring
        omega
      have h3_dvd : 3 ∣ N := by
        have hk_dvd : q ^ 5 ∣ N := by
          simpa [h5] using Nat.ordProj_dvd N q
        have hk_next : ¬ q ^ (5 + 1) ∣ N := by
          simpa [h5] using Nat.pow_succ_factorization_not_dvd hN.2.ne' hq_prime
        have h3_sig : 3 ∣ ∑ d ∈ (q ^ 5).divisors, d := by
          rw [← sigma_one_apply, hsig5_fac]
          refine ⟨2 * (6 * k + 7) * (144 * k ^ 2 + 300 * k + 157) * (48 * k ^ 2 + 108 * k + 61), ?_⟩
          ring
        exact dvd_perfect_of_exact_prime_pow hN hq_prime hk_dvd hk_next
          (by decide) (by decide) h3_sig
      refine ⟨h5, hq12, h13, h3_dvd, ?_, ?_, ?_⟩
      · rwa [heq1]
      · rwa [heq2]
      · rwa [heq3]
    · exfalso
      have h5 : 5 ≤ q := by
        have := hq_prime.two_le
        omega
      have hq_ord : ordProj[q] N = q ^ 9 := by rw [h9]
      rw [hq_ord, h9] at hq_cap
      have hsig9 : 2 ≤ cardFactors (sigma 1 (q ^ 9)) := by
        rw [sigma_one_apply_prime_pow hq_prime]
        change 2 ≤ cardFactors (geometricBlock q (2 * 5))
        rw [geometricBlock_mul q 2 5]
        have hg2 : geometricBlock q 2 = 2 * ((1 + q) / 2) := by
          simp only [geometricBlock, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
            zero_add, pow_zero, pow_one]
          omega
        have hg5_pos : 0 < geometricBlock (q ^ 2) 5 := by
          simp only [geometricBlock, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
            zero_add, pow_zero]
          positivity
        have hhalf_gt1 : 1 < (1 + q) / 2 := by omega
        rw [hg2, cardFactors_mul (by positivity) hg5_pos.ne',
          cardFactors_mul (by decide : (2 : ℕ) ≠ 0) (by omega)]
        have hc2 : 0 < cardFactors 2 := cardFactors_pos_iff_one_lt.mpr (by omega)
        have hch : 0 < cardFactors ((1 + q) / 2) := cardFactors_pos_iff_one_lt.mpr hhalf_gt1
        omega
      omega
  have hten_free : ∀ p : ℕ, p.Prime → ¬ p ^ 10 ∣ N := by
    intro p hp hd
    have hm : p ∈ N.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, (dvd_pow_self p (by decide : 10 ≠ 0)).trans hd, hN.2.ne'⟩
    have h10 : 10 ≤ N.factorization p := (hp.pow_dvd_iff_le_factorization hN.2.ne').1 hd
    have hp_cap := hcap p hm
    have hsig_pos := hsig_pos_of p hp (by omega)
    omega
  have heighth : ∀ r ∈ N.primeFactors, N.factorization r = 8 →
      (1 + r + r ^ 2).Prime ∧ (1 + r ^ 3 + r ^ 6).Prime ∧ r % 3 ≠ 1 := by
    intro r hr hr8
    have hr_prime := Nat.prime_of_mem_primeFactors hr
    have hr_cap := hcap r hr
    have hord : ordProj[r] N = r ^ 8 := by rw [hr8]
    rw [hord, hr8] at hr_cap
    have hcf8 : cardFactors (sigma 1 (r ^ 8)) ≤ 2 := by omega
    have hr_ne1 : r % 3 ≠ 1 := by
      intro hr3
      have h4 := four_le_cardFactors_sigma_eighth_pow_of_one_mod_three hr_prime hr3
      omega
    have hsig8 : sigma 1 (r ^ 8) = (1 + r + r ^ 2) * (1 + r ^ 3 + r ^ 6) := by
      rw [sigma_one_apply_prime_pow hr_prime]
      change geometricBlock r (3 * 3) = _
      rw [geometricBlock_mul r 3 3]
      have h1 : geometricBlock r 3 = 1 + r + r ^ 2 := by
        simp only [geometricBlock, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
          zero_add, pow_zero, pow_one]
      have h2 : geometricBlock (r ^ 3) 3 = 1 + r ^ 3 + r ^ 6 := by
        simp only [geometricBlock, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
          zero_add, pow_zero, pow_one]
        ring
      rw [h1, h2]
    have hr2 : 2 ≤ r := hr_prime.two_le
    have hr2_pos : 1 ≤ r ^ 2 := Nat.one_le_pow 2 r hr_prime.pos
    have hr3_pos : 1 ≤ r ^ 3 := Nat.one_le_pow 3 r hr_prime.pos
    have hr6_pos : 1 ≤ r ^ 6 := Nat.one_le_pow 6 r hr_prime.pos
    have h1_gt1 : 1 < 1 + r + r ^ 2 := by omega
    have h2_gt1 : 1 < 1 + r ^ 3 + r ^ 6 := by omega
    rw [hsig8, cardFactors_mul (by omega) (by omega)] at hcf8
    have hc1 : 0 < cardFactors (1 + r + r ^ 2) := cardFactors_pos_iff_one_lt.mpr h1_gt1
    have hc2 : 0 < cardFactors (1 + r ^ 3 + r ^ 6) := cardFactors_pos_iff_one_lt.mpr h2_gt1
    exact ⟨cardFactors_eq_one_iff_prime.mp (by omega),
      cardFactors_eq_one_iff_prime.mp (by omega), hr_ne1⟩
  have hdensity : 2 * cardFactors N + 1 ≤ 10 * N.primeFactors.card := by
    calc
      2 * cardFactors N + 1
          = 1 + 2 * cardFactors N := by omega
      _ = ∑ p ∈ N.primeFactors, (N.factorization p + cardFactors (sigma 1 (ordProj[p] N))) :=
            (sum_component_factor_capture ho hN).symm
      _ ≤ ∑ _p ∈ N.primeFactors, 10 := Finset.sum_le_sum hcap
      _ = 10 * N.primeFactors.card := by simp [Nat.mul_comm]
  exact ⟨hcap, hq_dichotomy, hten_free, heighth, hdensity⟩

/-- In a `3`-free odd perfect number, an Euler prime exponent strictly greater than `1` forces
a ten-factor component-index drop. -/
theorem exists_componentIndex_cardFactors_add_ten_le_of_three_free_euler_exp_gt_one {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (h3 : ¬ 3 ∣ N) (hgt : 1 < N.factorization q) :
    ∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 10 ≤ cardFactors N := by
  by_contra! hno
  obtain ⟨_, hq_dich, _, _, _⟩ := no_ten_factor_drop_profile ho hN hq hq4 he hev hno
  rcases hq_dich with hq1 | ⟨_, _, _, h3_dvd, _⟩
  · omega
  · exact h3 h3_dvd

/-- Any prime tenth power dividing `N` forces a ten-factor component-index drop. -/
theorem exists_componentIndex_cardFactors_add_ten_le_of_tenth_power {N : ℕ}
    (ho : Odd N) (hN : N.Perfect) (h10 : ∃ p : ℕ, p.Prime ∧ p ^ 10 ∣ N) :
    ∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 10 ≤ cardFactors N := by
  by_contra! hno
  obtain ⟨q, hq, hq4, he, hev⟩ := euler_exponents ho hN
  obtain ⟨_, _, hfree10, _, _⟩ := no_ten_factor_drop_profile ho hN hq hq4 he hev hno
  obtain ⟨p, hp, hd⟩ := h10
  exact hfree10 p hp hd

/-- Every linear Euler odd perfect number `N = q * m ^ 2` with Fermat prime `q > 5`
has a prime sixteenth power `r₀ ^ 16 ∣ N` and hence admits a ten-factor component-index drop. -/
theorem linear_euler_fermat_gt_five_forces_ten_drop {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m)
    (hform : N = q * m ^ 2) (hfermat : ∃ k : ℕ, q - 1 = 2 ^ k) (hq5 : 5 < q) :
    (∃ r₀ : ℕ, r₀.Prime ∧ r₀ ^ 16 ∣ N) ∧
    (∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 10 ≤ cardFactors N) := by
  obtain ⟨⟨r₀, hr₀_prime, hr₀_16⟩, _⟩ :=
    linear_euler_fermat_gt_five_forces_eight_drop ho hN hq hqm hform hfermat hq5
  have hr₀_10 : r₀ ^ 10 ∣ N := (pow_dvd_pow r₀ (by decide : 10 ≤ 16)).trans hr₀_16
  exact ⟨⟨r₀, hr₀_prime, hr₀_16⟩,
    exists_componentIndex_cardFactors_add_ten_le_of_tenth_power ho hN ⟨r₀, hr₀_prime, hr₀_10⟩⟩

/-- If `largeSources N q = ∅` and `N.factorization 3 ≠ 8`, then `3 ∈ N.primeFactors` and the
component index at `3` yields at least a `10`-factor drop:
`cardFactors (componentIndex N 3) + 10 ≤ cardFactors N`. -/
theorem exists_ten_drop_at_three_of_largeSources_empty_of_ne_eight {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hempty : largeSources N q = ∅) (hne8 : N.factorization 3 ≠ 8) :
    3 ∈ N.primeFactors ∧ cardFactors (componentIndex N 3) + 10 ≤ cardFactors N := by
  have h3_8 := eight_le_three_exponent_of_largeSources_empty ho hN hq hq4 he hev hempty
  have h3_even : Even (N.factorization 3) := by
    apply hev 3
    intro hq3
    subst hq3
    norm_num at hq4
  have h3_10 : 10 ≤ N.factorization 3 := by
    rcases h3_even with ⟨k, hk⟩
    omega
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
