module

public import OddPerfect.GlobalWave9Obstruction
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Linear Euler Order Obstruction (`OddPerfect.LinearEulerOrderObstruction`)

Establishes the cyclotomic-order vs. congruent-1 source dichotomy for the unique Euler-prime
source `r₀` on any linear Euler odd perfect number `N = q * m ^ 2` (`q.Prime`, `q % 4 = 1`,
`¬ q ∣ m`):
1. `linear_euler_unique_source_order_dichotomy`:
   The unique `q`-source prime `r₀ ∈ m.primeFactors` (with `e₀ := m.factorization r₀`,
   `N.factorization r₀ = 2 * e₀`, `v_q(σ(r₀ ^ (2 * e₀))) = 1`) satisfies either:
   - **Congruent-1 branch**: `r₀ % q = 1 ∧ 2 * q + 1 ≤ r₀ ∧ q ∣ 2 * e₀ + 1 ∧
     ¬ q ^ 2 ∣ 2 * e₀ + 1 ∧ q - 1 ≤ N.factorization r₀`, or
   - **Cyclotomic order branch**: `∃ l : ℕ, l.Prime ∧ Odd l ∧ l ∣ 2 * e₀ + 1 ∧ 4 * l ∣ q - 1 ∧
     13 ≤ q`.
2. `linear_euler_fermat_prime_obstruction`:
   When `q` is a Fermat prime (`∃ k : ℕ, q - 1 = 2 ^ k`), the cyclotomic order branch is
   impossible, forcing the congruent-1 branch and `r₀ ^ (q - 1) ∣ N`.
3. `linear_euler_five_profile` & `linear_euler_fermat_gt_five_forces_eight_drop`:
   - At `q = 5`, forces `r₀ ∈ largeSources N 5` with `11 ≤ r₀`, `r₀ % 10 = 1`,
     `5 ∣ N.factorization r₀ + 1`, `¬ 25 ∣ N.factorization r₀ + 1`, and `4 ≤ N.factorization r₀`.
   - For any Fermat prime `q > 5`, forces `r₀ ^ 16 ∣ N` and an unconditional eight-factor
     component-index drop `cardFactors (componentIndex N p) + 8 ≤ cardFactors N`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- **Unique `q`-Source Congruent-1 vs. Cyclotomic-Order Dichotomy**:
On any linear Euler odd perfect number `N = q * m ^ 2` (`q.Prime`, `q % 4 = 1`, `¬ q ∣ m`),
the unique `q`-source prime `r₀ ∈ m.primeFactors` satisfies either the congruent-1 branch
(`r₀ ≡ 1 [MOD q]`, `2 * q + 1 ≤ r₀`, `q ∥ 2 * e₀ + 1`, `q - 1 ≤ N.factorization r₀`) or the
cyclotomic order branch (`∃ l, l.Prime ∧ Odd l ∧ l ∣ 2 * e₀ + 1 ∧ 4 * l ∣ q - 1 ∧ 13 ≤ q`). -/
theorem linear_euler_unique_source_order_dichotomy {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hq4 : q % 4 = 1)
    (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2) :
    ∃ r₀ ∈ m.primeFactors,
      let e₀ := m.factorization r₀
      N.factorization r₀ = 2 * e₀ ∧
      q ∣ sigma 1 (r₀ ^ (2 * e₀)) ∧
      (sigma 1 (r₀ ^ (2 * e₀))).factorization q = 1 ∧
      ((r₀ % q = 1 ∧ 2 * q + 1 ≤ r₀ ∧ q ∣ 2 * e₀ + 1 ∧ ¬ q ^ 2 ∣ 2 * e₀ + 1 ∧
          q - 1 ≤ N.factorization r₀) ∨
        (∃ l : ℕ, l.Prime ∧ Odd l ∧ l ∣ 2 * e₀ + 1 ∧ 4 * l ∣ q - 1 ∧ 13 ≤ q)) := by
  obtain ⟨_, r₀, hr₀_m, hq_dvd_sig, hfact_r0, _, _, _⟩ :=
    linear_euler_unique_q_source_and_bound ho hN hq hqm hform
  refine ⟨r₀, hr₀_m, ?_⟩
  let e₀ := m.factorization r₀
  have hmodd : Odd m :=
    ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
  have hm0 : m ≠ 0 := hmodd.pos.ne'
  have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀_m
  have hr₀_dvd_m : r₀ ∣ m := Nat.dvd_of_mem_primeFactors hr₀_m
  have hr₀_odd : Odd r₀ := hmodd.of_dvd_nat hr₀_dvd_m
  have hr₀_ne_q : r₀ ≠ q := by
    rintro rfl
    exact hqm hr₀_dvd_m
  have hq_odd : Odd q := ho.of_dvd_nat (hform ▸ dvd_mul_right q (m ^ 2))
  have hq5 : 5 ≤ q := by
    have := hq.two_le
    omega
  have hN_fact_r₀ : N.factorization r₀ = 2 * e₀ := by
    rw [hform, Nat.factorization_mul hq.ne_zero hm20, Finsupp.add_apply,
      hq.factorization, Finsupp.single_eq_of_ne hr₀_ne_q, zero_add,
      Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  have hsig_ne0 : sigma 1 (r₀ ^ (2 * e₀)) ≠ 0 :=
    (sigma_pos 1 _ (pow_ne_zero _ hr₀_prime.ne_zero)).ne'
  have hnq2_sig : ¬ q ^ 2 ∣ sigma 1 (r₀ ^ (2 * e₀)) := by
    intro hq2
    have hle : 2 ≤ (sigma 1 (r₀ ^ (2 * e₀))).factorization q :=
      (hq.pow_dvd_iff_le_factorization hsig_ne0).mp hq2
    change (sigma 1 (r₀ ^ (2 * e₀))).factorization q = 1 at hfact_r0
    omega
  refine ⟨hN_fact_r₀, hq_dvd_sig, hfact_r0, ?_⟩
  by_cases hr₀q1 : r₀ % q = 1
  · left
    have hr₀_ge : 2 * q + 1 ≤ r₀ := by
      have hdiv : q * (r₀ / q) + 1 = r₀ := by
        have h := Nat.div_add_mod r₀ q
        rw [hr₀q1] at h
        exact h
      have hk1 : 1 ≤ r₀ / q := by
        by_contra hk0
        have hk_eq0 : r₀ / q = 0 := Nat.lt_one_iff.mp (Nat.not_le.mp hk0)
        rw [hk_eq0, mul_zero, zero_add] at hdiv
        have := hr₀_prime.one_lt
        omega
      have hk2 : 2 ≤ r₀ / q := by
        by_contra hklt
        have hk_eq1 : r₀ / q = 1 :=
          Nat.le_antisymm (Nat.le_of_lt_succ (Nat.not_le.mp hklt)) hk1
        rw [hk_eq1, mul_one] at hdiv
        obtain ⟨a, ha⟩ := hq_odd
        obtain ⟨b, hb⟩ := hr₀_odd
        omega
      nlinarith
    have hr₀_modEq : r₀ ≡ 1 [MOD q] := by
      change r₀ % q = 1 % q
      rw [hr₀q1, Nat.mod_eq_of_lt hq.one_lt]
    have hq_dvd_exp : q ∣ 2 * e₀ + 1 := by
      have hmod := sigma_modEq_of_one hr₀_prime hr₀_modEq (2 * e₀)
      change sigma 1 (r₀ ^ (2 * e₀)) % q = (2 * e₀ + 1) % q at hmod
      have h0 : sigma 1 (r₀ ^ (2 * e₀)) % q = 0 := Nat.mod_eq_zero_of_dvd hq_dvd_sig
      exact Nat.dvd_of_mod_eq_zero (by omega)
    have hq_sub1_le : q - 1 ≤ N.factorization r₀ := by
      have hle : q ≤ 2 * e₀ + 1 := Nat.le_of_dvd (Nat.succ_pos _) hq_dvd_exp
      omega
    have hnq2_exp : ¬ q ^ 2 ∣ 2 * e₀ + 1 := by
      rintro ⟨t, ht⟩
      have hblock :
          sigma 1 (r₀ ^ (2 * e₀)) =
            geometricBlock r₀ q * geometricBlock (r₀ ^ q) (q * t) := by
        rw [sigma_one_apply_prime_pow hr₀_prime]
        change geometricBlock r₀ (2 * e₀ + 1) = _
        rw [ht, pow_two, mul_assoc, geometricBlock_mul]
      have h1 : q ∣ geometricBlock r₀ q := by
        have hmod := geom_modEq_of_one hr₀_modEq q
        change geometricBlock r₀ q % q = q % q at hmod
        rw [Nat.mod_self] at hmod
        exact Nat.dvd_of_mod_eq_zero hmod
      have h2 : q ∣ geometricBlock (r₀ ^ q) (q * t) := by
        have hmod := geom_modEq_of_one (by simpa using hr₀_modEq.pow q) (q * t)
        change geometricBlock (r₀ ^ q) (q * t) % q = (q * t) % q at hmod
        rw [Nat.mul_mod_right] at hmod
        exact Nat.dvd_of_mod_eq_zero hmod
      apply hnq2_sig
      rw [hblock, pow_two]
      exact Nat.mul_dvd_mul h1 h2
    exact ⟨hr₀q1, hr₀_ge, hq_dvd_exp, hnq2_exp, hq_sub1_le⟩
  · right
    let : Fact q.Prime := ⟨hq⟩
    have hr₀_zmod_ne1 : (r₀ : ZMod q) ≠ 1 := by
      intro h1
      have h1' : (r₀ : ZMod q) = ((1 : ℕ) : ZMod q) := by simpa using h1
      rw [ZMod.natCast_eq_natCast_iff'] at h1'
      rw [Nat.mod_eq_of_lt hq.one_lt] at h1'
      exact hr₀q1 h1'
    have hnq_r0 : ¬ q ∣ r₀ := by
      intro hqr
      rcases (Nat.dvd_prime hr₀_prime).mp hqr with h1 | hEq
      · exact hq.ne_one h1
      · exact hr₀_ne_q hEq.symm
    have hr₀_zmod_ne0 : (r₀ : ZMod q) ≠ 0 :=
      (ZMod.natCast_eq_zero_iff r₀ q).not.mpr hnq_r0
    have hord_dvd_exp : orderOf (r₀ : ZMod q) ∣ 2 * e₀ + 1 := by
      have hd := (dvd_sum_divisors_prime_pow_iff hr₀_prime hq (2 * e₀)).mp
        ((sigma_one_apply (r₀ ^ (2 * e₀))).symm ▸ hq_dvd_sig)
      split_ifs at hd with h
      · exact False.elim (hr₀_zmod_ne1 h)
      · exact hd
    have hord_dvd_sub1 : orderOf (r₀ : ZMod q) ∣ q - 1 :=
      ZMod.orderOf_dvd_card_sub_one hr₀_zmod_ne0
    have hord_ne1 : orderOf (r₀ : ZMod q) ≠ 1 :=
      mt orderOf_eq_one_iff.mp hr₀_zmod_ne1
    let l := (orderOf (r₀ : ZMod q)).minFac
    have hl_prime : l.Prime := Nat.minFac_prime hord_ne1
    have hl_dvd_ord : l ∣ orderOf (r₀ : ZMod q) := Nat.minFac_dvd _
    have hl_dvd_exp : l ∣ 2 * e₀ + 1 := hl_dvd_ord.trans hord_dvd_exp
    have hl_odd : Odd l := by
      have h_odd_exp : Odd (2 * e₀ + 1) := ⟨e₀, rfl⟩
      exact h_odd_exp.of_dvd_nat hl_dvd_exp
    have hl_dvd_sub1 : l ∣ q - 1 := hl_dvd_ord.trans hord_dvd_sub1
    have h4_dvd_sub1 : 4 ∣ q - 1 := Nat.dvd_of_mod_eq_zero (by omega)
    have hcop4l : Nat.Coprime 4 l := by
      have hl2 : l ≠ 2 := by
        intro h2
        rw [h2] at hl_odd
        exact (by decide : ¬ Odd 2) hl_odd
      have hcop2l : Nat.Coprime 2 l :=
        (Nat.coprime_primes Nat.prime_two hl_prime).mpr hl2.symm
      simpa using hcop2l.pow_left 2
    have h4l_dvd_sub1 : 4 * l ∣ q - 1 :=
      hcop4l.mul_dvd_of_dvd_of_dvd h4_dvd_sub1 hl_dvd_sub1
    have hl_ge3 : 3 ≤ l := by
      have := hl_prime.two_le
      obtain ⟨k, hk⟩ := hl_odd
      omega
    have hq13 : 13 ≤ q := by
      have hle : 4 * l ≤ q - 1 := Nat.le_of_dvd (by omega) h4l_dvd_sub1
      omega
    exact ⟨l, hl_prime, hl_odd, hl_dvd_exp, h4l_dvd_sub1, hq13⟩

/-- **Fermat-Prime Linear Euler Obstruction**:
When `q` is a Fermat prime (`q % 4 = 1`, `∃ k, q - 1 = 2 ^ k`) in the linear Euler branch
`N = q * m ^ 2` (`¬ q ∣ m`), the cyclotomic order branch is ruled out because no odd prime `l`
can divide `2 ^ k`, forcing `r₀ % q = 1`, `2 * q + 1 ≤ r₀`, `q ∥ N.factorization r₀ + 1`,
`q - 1 ≤ N.factorization r₀`, and `r₀ ^ (q - 1) ∣ N`. -/
theorem linear_euler_fermat_prime_obstruction {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hq4 : q % 4 = 1)
    (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2) (hfermat : ∃ k : ℕ, q - 1 = 2 ^ k) :
    ∃ r₀ ∈ m.primeFactors,
      r₀ % q = 1 ∧ 2 * q + 1 ≤ r₀ ∧ q ∣ N.factorization r₀ + 1 ∧
      ¬ q ^ 2 ∣ N.factorization r₀ + 1 ∧ q - 1 ≤ N.factorization r₀ ∧ r₀ ^ (q - 1) ∣ N := by
  obtain ⟨r₀, hr₀_m, hN_fact_r₀, _, _, hdich⟩ :=
    linear_euler_unique_source_order_dichotomy ho hN hq hq4 hqm hform
  rcases hdich with ⟨hr₀q1, hr₀_ge, hq_dvd_exp, hnq2_exp, hq_sub1_le⟩ |
      ⟨l, hl_prime, hl_odd, _, h4l_dvd, _⟩
  · have hq_dvd_N : q ∣ N.factorization r₀ + 1 := by simpa [hN_fact_r₀] using hq_dvd_exp
    have hnq2_N : ¬ q ^ 2 ∣ N.factorization r₀ + 1 := by simpa [hN_fact_r₀] using hnq2_exp
    have hr₀_pow_dvd : r₀ ^ (q - 1) ∣ N :=
      (pow_dvd_pow r₀ hq_sub1_le).trans (Nat.ordProj_dvd N r₀)
    exact ⟨r₀, hr₀_m, hr₀q1, hr₀_ge, hq_dvd_N, hnq2_N, hq_sub1_le, hr₀_pow_dvd⟩
  · exfalso
    obtain ⟨k, hk⟩ := hfermat
    have hl_dvd_pow : l ∣ 2 ^ k := hk ▸ (dvd_mul_left l 4).trans h4l_dvd
    have hl_dvd_2 : l ∣ 2 := hl_prime.dvd_of_dvd_pow hl_dvd_pow
    have hl2 : l = 2 := ((Nat.dvd_prime Nat.prime_two).mp hl_dvd_2).resolve_left hl_prime.ne_one
    rw [hl2] at hl_odd
    exact (by decide : ¬ Odd 2) hl_odd

/-- **Linear Euler `q = 5` Profile**:
Every odd perfect number of the form `N = 5 * m ^ 2` with `¬ 5 ∣ m` has a prime factor
`r₀ ∈ N.primeFactors` belonging to `largeSources N 5` with `11 ≤ r₀`, `r₀ % 10 = 1`,
`5 ∣ N.factorization r₀ + 1`, `¬ 25 ∣ N.factorization r₀ + 1`, and `4 ≤ N.factorization r₀`. -/
theorem linear_euler_five_profile {N m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (h5m : ¬ 5 ∣ m) (hform : N = 5 * m ^ 2) :
    ∃ r₀ ∈ N.primeFactors,
      11 ≤ r₀ ∧ r₀ % 10 = 1 ∧ 5 ∣ N.factorization r₀ + 1 ∧
      ¬ 25 ∣ N.factorization r₀ + 1 ∧ 4 ≤ N.factorization r₀ ∧ r₀ ∈ largeSources N 5 := by
  obtain ⟨r₀, hr₀_m, hr₀5, hr₀_ge11, h5_dvd, hn25_dvd, h4_le, _⟩ :=
    linear_euler_fermat_prime_obstruction ho hN (by decide) (by decide) h5m hform ⟨2, by decide⟩
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀_m
  have hr₀_dvd_N : r₀ ∣ N :=
    (Nat.dvd_of_mem_primeFactors hr₀_m).trans
      ((dvd_pow_self m (by decide : 2 ≠ 0)).trans (hform ▸ dvd_mul_left (m ^ 2) 5))
  have hr₀_N : r₀ ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hr₀_prime, hr₀_dvd_N, ho.pos.ne'⟩
  have hr₀_odd : Odd r₀ := ho.of_dvd_nat hr₀_dvd_N
  have hr₀_mod10 : r₀ % 10 = 1 := by
    obtain ⟨t, ht⟩ := hr₀_odd
    omega
  have hr₀_large : r₀ ∈ largeSources N 5 := by
    rw [largeSources, Finset.mem_filter]
    exact ⟨hr₀_N, by omega, by omega, h4_le⟩
  exact ⟨r₀, hr₀_N, hr₀_ge11, hr₀_mod10, h5_dvd, by simpa using hn25_dvd, h4_le, hr₀_large⟩

/-- **Fermat Prime `q > 5` Linear Euler Eight-Factor Drop**:
Every linear Euler odd perfect number `N = q * m ^ 2` whose Euler prime `q > 5` is a Fermat prime
(`∃ k, q - 1 = 2 ^ k`) has a prime `r₀` with `r₀ ^ 16 ∣ N`, and hence suffers an unconditional
eight-factor component-index drop `∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 8 ≤ cardFactors N`. -/
theorem linear_euler_fermat_gt_five_forces_eight_drop {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m)
    (hform : N = q * m ^ 2) (hfermat : ∃ k : ℕ, q - 1 = 2 ^ k) (hq5 : 5 < q) :
    (∃ r₀ : ℕ, r₀.Prime ∧ r₀ ^ 16 ∣ N) ∧
    (∃ p ∈ N.primeFactors, cardFactors (componentIndex N p) + 8 ≤ cardFactors N) := by
  obtain ⟨k, hk⟩ := hfermat
  have hk4 : 4 ≤ k := by
    by_contra hklt
    have hk_le3 : k ≤ 3 := by omega
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
    · omega
    · omega
    · omega
    · have hq9 : q = 9 := by omega
      rw [hq9] at hq
      exact (by decide : ¬ Nat.Prime 9) hq
  have h16_le : 16 ≤ q - 1 := by
    have hpow : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk4
    omega
  have hq4 : q % 4 = 1 := by
    have h4_dvd : 4 ∣ q - 1 := by
      have hpow : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
      simpa [← hk] using hpow
    obtain ⟨t, ht⟩ := h4_dvd
    omega
  obtain ⟨r₀, hr₀_m, _, _, _, _, _, hr₀_pow⟩ :=
    linear_euler_fermat_prime_obstruction ho hN hq hq4 hqm hform ⟨k, hk⟩
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀_m
  have hr₀_16 : r₀ ^ 16 ∣ N := (pow_dvd_pow r₀ h16_le).trans hr₀_pow
  have hr₀_8 : r₀ ^ 8 ∣ N := (pow_dvd_pow r₀ (by decide : 8 ≤ 16)).trans hr₀_16
  exact ⟨⟨r₀, hr₀_prime, hr₀_16⟩,
    exists_componentIndex_cardFactors_add_eight_le_of_eighth_power ho hN ⟨r₀, hr₀_prime, hr₀_8⟩⟩

end OddPerfect
