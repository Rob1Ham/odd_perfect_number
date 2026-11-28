module

public import OddPerfect.TotientOrderTower
public import OddPerfect.PrimeFive
public import OddPerfect.SixthPowerFreeS51CollisionDensityPinch
public import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Tactic.Ring

/-!
# Carmichael Exponent and Totient 2-Power Obstructions (`OddPerfect.CarmichaelExponentAndTotientTwoPowObstruction`)

Establishes two unconditional structural divisibility and size obstructions for any odd perfect
number `N`:

1. `odd_perfect_carmichael_exact_lcm_and_euler_cofactor_dvd`:
   Exact prime-power LCM formula for `ArithmeticFunction.carmichael N`, unconditional divisibility
   by `4` and by the prime-power cofactor `∏ p ∈ N.primeFactors, p ^ (N.factorization p - 1)`,
   and in any Euler form `N = q ^ a * m ^ 2`, divisibility `4 * q ^ (a - 1) * m ∣ carmichael N`
   together with `16 * N ≤ q * (carmichael N) ^ 2` (and strict `16 * N < (carmichael N) ^ 2`
   whenever `1 < a`).
2. `odd_perfect_totient_two_pow_and_euler_divisibility`:
   Unconditional divisibility `2 ^ (ω(N) + 1) ∣ N.totient`, `128 ∣ N.totient`,
   `2 ^ (ω(N) + 1) * (∏ p ∈ N.primeFactors, p ^ (N.factorization p - 1)) ∣ N.totient`,
   Euler-form divisibility `2 ^ (ω(N) + 1) * q ^ (a - 1) * m ∣ N.totient`, and for sixth-power-free
   `N`, `149 ≤ ω(N)` and `2 ^ 150 ∣ N.totient`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma odd_perfect_euler_form_factorization {N q a m : ℕ}
    (hN0 : N ≠ 0) (hq : q.Prime) (ha : 0 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2) :
    m ≠ 0 ∧
    q ∈ N.primeFactors ∧
    N.factorization q = a ∧
    (∀ r ∈ m.primeFactors, r ∈ N.primeFactors ∧ r ≠ q ∧ N.factorization r = 2 * m.factorization r) ∧
    (∀ r : ℕ, r ≠ q → Even (N.factorization r)) := by
  have hm0 : m ≠ 0 := by
    intro hm0
    rw [hm0, zero_pow (by decide : 2 ≠ 0), mul_zero] at hform
    exact hN0 hform
  have hqa0 : q ^ a ≠ 0 := pow_ne_zero a hq.ne_zero
  have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hfac_eq : ∀ r : ℕ, N.factorization r = a * q.factorization r + 2 * m.factorization r := by
    intro r
    rw [hform, Nat.factorization_mul hqa0 hm20, Finsupp.add_apply,
      Nat.factorization_pow, Nat.factorization_pow, Finsupp.smul_apply, Finsupp.smul_apply,
      smul_eq_mul, smul_eq_mul]
  have hmq0 : m.factorization q = 0 :=
    Finsupp.notMem_support_iff.mp (fun hmem => hqm (Nat.dvd_of_mem_primeFactors hmem))
  have hNq : N.factorization q = a := by
    rw [hfac_eq q, hq.factorization_self, hmq0, mul_one, mul_zero, add_zero]
  have hq_mem : q ∈ N.primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨hq, ?_, hN0⟩
    rw [hform]
    exact dvd_mul_of_dvd_left (dvd_pow_self q ha.ne') (m ^ 2)
  have hm_rel : ∀ r ∈ m.primeFactors,
      r ∈ N.primeFactors ∧ r ≠ q ∧ N.factorization r = 2 * m.factorization r := by
    intro r hr
    have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hr_dvd_m : r ∣ m := Nat.dvd_of_mem_primeFactors hr
    have hrq : r ≠ q := fun h => hqm (h ▸ hr_dvd_m)
    have hr_mem : r ∈ N.primeFactors := by
      refine Nat.mem_primeFactors.mpr ⟨hr_prime, ?_, hN0⟩
      rw [hform]
      exact dvd_mul_of_dvd_right (dvd_trans hr_dvd_m (dvd_pow_self m (by decide))) (q ^ a)
    have hqr0 : q.factorization r = 0 := by
      rw [hq.factorization]
      simp [Ne.symm hrq]
    have hNr : N.factorization r = 2 * m.factorization r := by
      rw [hfac_eq r, hqr0, mul_zero, zero_add]
    exact ⟨hr_mem, hrq, hNr⟩
  have hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r) := by
    intro r hrq
    have hqr0 : q.factorization r = 0 := by
      rw [hq.factorization]
      simp [Ne.symm hrq]
    rw [hfac_eq r, hqr0, mul_zero, zero_add]
    exact even_two_mul _
  exact ⟨hm0, hq_mem, hNq, hm_rel, hev⟩

/-- **1. Exact Carmichael LCM and Euler-Cofactor Divisibility**:
For any odd perfect number `N`:
- `ArithmeticFunction.carmichael N = N.primeFactors.lcm (fun p => p ^ (N.factorization p - 1) * (p - 1))`;
- `4 ∣ ArithmeticFunction.carmichael N`;
- `∏ p ∈ N.primeFactors, p ^ (N.factorization p - 1) ∣ ArithmeticFunction.carmichael N`;
- In any Euler representation `N = q ^ a * m ^ 2`, `4 * q ^ (a - 1) * m ∣ ArithmeticFunction.carmichael N`,
  `16 * N ≤ q * (ArithmeticFunction.carmichael N) ^ 2`, and if `1 < a`, then
  `16 * N < (ArithmeticFunction.carmichael N) ^ 2`. -/
theorem odd_perfect_carmichael_exact_lcm_and_euler_cofactor_dvd
    {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    ArithmeticFunction.carmichael N =
      N.primeFactors.lcm (fun p => p ^ (N.factorization p - 1) * (p - 1)) ∧
    4 ∣ ArithmeticFunction.carmichael N ∧
    (∏ p ∈ N.primeFactors, p ^ (N.factorization p - 1)) ∣ ArithmeticFunction.carmichael N ∧
    (∀ q a m : ℕ, q.Prime → q % 4 = 1 → 0 < a → ¬ q ∣ m → N = q ^ a * m ^ 2 →
      4 * q ^ (a - 1) * m ∣ ArithmeticFunction.carmichael N ∧
      16 * N ≤ q * (ArithmeticFunction.carmichael N) ^ 2 ∧
      (1 < a → 16 * N < (ArithmeticFunction.carmichael N) ^ 2)) := by
  have hn0 : N ≠ 0 := hN.2.ne'
  have : NeZero N := ⟨hn0⟩
  have hlcm_eq : ArithmeticFunction.carmichael N =
      N.primeFactors.lcm (fun p => p ^ (N.factorization p - 1) * (p - 1)) := by
    rw [ArithmeticFunction.carmichael_factorization N]
    refine Finset.lcm_congr rfl fun p hp => ?_
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp_odd : Odd p := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
    have hp2 : p ≠ 2 := fun h => (by decide : ¬ Odd 2) (h ▸ hp_odd)
    have hp_pos : 0 < N.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
    rw [ArithmeticFunction.carmichael_pow_of_prime_ne_two (N.factorization p) hp_prime hp2,
      Nat.totient_prime_pow hp_prime hp_pos]
  have h4_dvd : 4 ∣ ArithmeticFunction.carmichael N := by
    obtain ⟨q, hq_mem, hq4, _, _⟩ := euler_exponents ho hN
    have h4_sub : 4 ∣ q - 1 := by
      have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
      have := hq_prime.two_le
      omega
    have hsub_dvd : q - 1 ∣ q ^ (N.factorization q - 1) * (q - 1) := dvd_mul_left _ _
    have hfac_dvd : q ^ (N.factorization q - 1) * (q - 1) ∣ ArithmeticFunction.carmichael N := by
      rw [hlcm_eq]
      exact Finset.dvd_lcm hq_mem
    exact h4_sub.trans (hsub_dvd.trans hfac_dvd)
  have hprod_dvd : (∏ p ∈ N.primeFactors, p ^ (N.factorization p - 1)) ∣
      ArithmeticFunction.carmichael N := by
    have hpair : Set.Pairwise (N.primeFactors : Set ℕ)
        (Nat.Coprime.onFun fun p => p ^ (N.factorization p - 1)) := by
      intro p hp r hr hpr
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr
      exact ((Nat.coprime_primes hp_prime hr_prime).mpr hpr).pow _ _
    rw [← Finset.lcm_eq_prod hpair, hlcm_eq]
    refine Finset.lcm_dvd fun p hp => ?_
    exact (dvd_mul_right _ _).trans (Finset.dvd_lcm hp)
  have heuler_clause :
      ∀ q a m : ℕ, q.Prime → q % 4 = 1 → 0 < a → ¬ q ∣ m → N = q ^ a * m ^ 2 →
        4 * q ^ (a - 1) * m ∣ ArithmeticFunction.carmichael N ∧
        16 * N ≤ q * (ArithmeticFunction.carmichael N) ^ 2 ∧
        (1 < a → 16 * N < (ArithmeticFunction.carmichael N) ^ 2) := by
    intro q a m hq hq4 ha hqm hform
    obtain ⟨hm0, hq_mem, hNq, hm_rel, hev_m⟩ :=
      odd_perfect_euler_form_factorization hn0 hq ha hqm hform
    have hqa_dvd : q ^ (a - 1) ∣ ArithmeticFunction.carmichael N := by
      have h1 : q ^ (a - 1) ∣ q ^ (N.factorization q - 1) * (q - 1) := by
        rw [hNq]
        exact dvd_mul_right _ _
      have h2 : q ^ (N.factorization q - 1) * (q - 1) ∣ ArithmeticFunction.carmichael N := by
        rw [hlcm_eq]
        exact Finset.dvd_lcm hq_mem
      exact h1.trans h2
    have hm_dvd : m ∣ ArithmeticFunction.carmichael N := by
      have hpair_m : Set.Pairwise (m.primeFactors : Set ℕ)
          (Nat.Coprime.onFun fun r => r ^ m.factorization r) := by
        intro r hr s hs hrs
        have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr
        have hs_prime : s.Prime := Nat.prime_of_mem_primeFactors hs
        exact ((Nat.coprime_primes hr_prime hs_prime).mpr hrs).pow _ _
      nth_rw 1 [Nat.prod_primeFactors_pow_factorization hm0]
      rw [← Finset.lcm_eq_prod hpair_m]
      refine Finset.lcm_dvd fun r hr => ?_
      obtain ⟨hr_mem, _, hNr⟩ := hm_rel r hr
      have hr_m_pos : 0 < m.factorization r := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr)
      have hpow_le : m.factorization r ≤ N.factorization r - 1 := by omega
      have hdvd1 : r ^ m.factorization r ∣ r ^ (N.factorization r - 1) :=
        Nat.pow_dvd_pow r hpow_le
      have hdvd2 : r ^ (N.factorization r - 1) ∣ r ^ (N.factorization r - 1) * (r - 1) :=
        dvd_mul_right _ _
      have hdvd3 : r ^ (N.factorization r - 1) * (r - 1) ∣ ArithmeticFunction.carmichael N := by
        rw [hlcm_eq]
        exact Finset.dvd_lcm hr_mem
      exact hdvd1.trans (hdvd2.trans hdvd3)
    have hq_odd : Odd q := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hq_mem)
    have hm_odd : Odd m := by
      refine ho.of_dvd_nat ?_
      rw [hform]
      exact dvd_mul_of_dvd_right (dvd_pow_self m (by decide)) (q ^ a)
    have hcop_4_q : Nat.Coprime 4 (q ^ (a - 1)) := by
      have h2q : Nat.Coprime 2 q := Nat.prime_two.coprime_iff_not_dvd.mpr hq_odd.not_two_dvd_nat
      exact (show (4 : ℕ) = 2 ^ 2 by decide) ▸ h2q.pow 2 (a - 1)
    have hcop_4_m : Nat.Coprime 4 m := by
      have h2m : Nat.Coprime 2 m := Nat.prime_two.coprime_iff_not_dvd.mpr hm_odd.not_two_dvd_nat
      exact (show (4 : ℕ) = 2 ^ 2 by decide) ▸ h2m.pow_left 2
    have hcop_q_m : Nat.Coprime (q ^ (a - 1)) m :=
      (hq.coprime_iff_not_dvd.mpr hqm).pow_left (a - 1)
    have h4q_dvd : 4 * q ^ (a - 1) ∣ ArithmeticFunction.carmichael N :=
      hcop_4_q.mul_dvd_of_dvd_of_dvd h4_dvd hqa_dvd
    have h4qm_dvd : 4 * q ^ (a - 1) * m ∣ ArithmeticFunction.carmichael N :=
      (hcop_4_m.mul_left hcop_q_m).mul_dvd_of_dvd_of_dvd h4q_dvd hm_dvd
    have hcar_pos : 0 < ArithmeticFunction.carmichael N := by
      by_contra! hle
      have hcar0 : ArithmeticFunction.carmichael N = 0 := by omega
      have htot0 : N.totient = 0 := by
        have hd := ArithmeticFunction.carmichael_dvd_totient N
        rw [hcar0, zero_dvd_iff] at hd
        exact hd
      have htot_pos : 0 < N.totient := Nat.totient_pos.mpr hN.2
      omega
    have hle_car : 4 * q ^ (a - 1) * m ≤ ArithmeticFunction.carmichael N :=
      Nat.le_of_dvd hcar_pos h4qm_dvd
    have hsq_le : 16 * q ^ (2 * (a - 1)) * m ^ 2 ≤ (ArithmeticFunction.carmichael N) ^ 2 := by
      have hpow2 : (4 * q ^ (a - 1) * m) ^ 2 ≤ (ArithmeticFunction.carmichael N) ^ 2 :=
        Nat.pow_le_pow_left hle_car 2
      have hid : (4 * q ^ (a - 1) * m) ^ 2 = 16 * q ^ (2 * (a - 1)) * m ^ 2 := by
        ring
      rwa [← hid]
    have hle_16N : 16 * N ≤ q * (ArithmeticFunction.carmichael N) ^ 2 := by
      have hexp : a ≤ 2 * (a - 1) + 1 := by omega
      have hq_pow : q ^ a ≤ q * q ^ (2 * (a - 1)) := by
        calc
          q ^ a ≤ q ^ (2 * (a - 1) + 1) := Nat.pow_le_pow_right hq.pos hexp
          _ = q * q ^ (2 * (a - 1)) := by rw [pow_succ']
      calc
        16 * N = 16 * q ^ a * m ^ 2 := by rw [hform]; ring
        _ ≤ 16 * (q * q ^ (2 * (a - 1))) * m ^ 2 := by
          gcongr
        _ = q * (16 * q ^ (2 * (a - 1)) * m ^ 2) := by ring
        _ ≤ q * (ArithmeticFunction.carmichael N) ^ 2 := by
          gcongr
    have hlt_16N : 1 < a → 16 * N < (ArithmeticFunction.carmichael N) ^ 2 := by
      intro ha1
      obtain ⟨q₀, _, _, he0, _⟩ := euler_exponents ho hN
      have hqq0 : q₀ = q := by
        by_contra hne
        have heven_q0 : Even (N.factorization q₀) := hev_m q₀ hne
        obtain ⟨k, hk⟩ := heven_q0
        omega
      have ha4 : a % 4 = 1 := by
        rw [← hNq, ← hqq0]
        exact he0
      have ha5 : 5 ≤ a := by omega
      have hexp_lt : a < 2 * (a - 1) := by omega
      have hq_pow_lt : q ^ a < q ^ (2 * (a - 1)) :=
        Nat.pow_lt_pow_right hq.one_lt hexp_lt
      have hm2_pos : 0 < m ^ 2 := sq_pos_of_ne_zero hm0
      calc
        16 * N = 16 * q ^ a * m ^ 2 := by rw [hform]; ring
        _ < 16 * q ^ (2 * (a - 1)) * m ^ 2 := by
          gcongr
        _ ≤ (ArithmeticFunction.carmichael N) ^ 2 := hsq_le
    exact ⟨h4qm_dvd, hle_16N, hlt_16N⟩
  exact ⟨hlcm_eq, h4_dvd, hprod_dvd, heuler_clause⟩

/-- **2. Totient 2-Power and Euler-Form Divisibility**:
For any odd perfect number `N`:
- `2 ^ (N.primeFactors.card + 1) ∣ N.totient`;
- `128 ∣ N.totient`;
- `2 ^ (N.primeFactors.card + 1) * (∏ p ∈ N.primeFactors, p ^ (N.factorization p - 1)) ∣ N.totient`;
- In any Euler representation `N = q ^ a * m ^ 2`, `2 ^ (N.primeFactors.card + 1) * q ^ (a - 1) * m ∣ N.totient`;
- If `N` is sixth-power-free, then `149 ≤ N.primeFactors.card` and `2 ^ 150 ∣ N.totient`. -/
theorem odd_perfect_totient_two_pow_and_euler_divisibility
    {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    2 ^ (N.primeFactors.card + 1) ∣ N.totient ∧
    128 ∣ N.totient ∧
    2 ^ (N.primeFactors.card + 1) * (∏ p ∈ N.primeFactors, p ^ (N.factorization p - 1)) ∣ N.totient ∧
    (∀ q a m : ℕ, q.Prime → q % 4 = 1 → 0 < a → ¬ q ∣ m → N = q ^ a * m ^ 2 →
      2 ^ (N.primeFactors.card + 1) * q ^ (a - 1) * m ∣ N.totient) ∧
    ((∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) →
      149 ≤ N.primeFactors.card ∧
      2 ^ 150 ∣ N.totient) := by
  have hn0 : N ≠ 0 := hN.2.ne'
  have htot_eq :
      N.totient =
        (∏ p ∈ N.primeFactors, p ^ (N.factorization p - 1)) *
          (∏ p ∈ N.primeFactors, (p - 1)) := by
    rw [Nat.totient_eq_prod_factorization hn0, Finsupp.prod, Nat.support_factorization,
      Finset.prod_mul_distrib]
  have h6 : 6 ≤ N.primeFactors.card := six_le_distinct_prime_factor_count ho hN
  have h2_pow_sub : 2 ^ (N.primeFactors.card + 1) ∣ ∏ p ∈ N.primeFactors, (p - 1) := by
    obtain ⟨q, hq_mem, hq4, _, _⟩ := euler_exponents ho hN
    rw [← Finset.mul_prod_erase N.primeFactors (fun p => p - 1) hq_mem]
    have h4_dvd : 2 ^ 2 ∣ q - 1 := by
      have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
      have := hq_prime.two_le
      omega
    have hrest_dvd :
        2 ^ (N.primeFactors.card - 1) ∣ ∏ r ∈ N.primeFactors.erase q, (r - 1) := by
      have hcard_er : (N.primeFactors.erase q).card = N.primeFactors.card - 1 :=
        Finset.card_erase_of_mem hq_mem
      rw [← hcard_er, ← Finset.prod_const (b := (2 : ℕ))]
      refine Finset.prod_dvd_prod_of_dvd _ _ fun r hr => ?_
      have hr_mem : r ∈ N.primeFactors := Finset.mem_of_mem_erase hr
      have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr_mem
      have hr_odd : Odd r := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr_mem)
      obtain ⟨t, ht⟩ := hr_odd
      have := hr_prime.two_le
      omega
    have hmul_dvd := mul_dvd_mul h4_dvd hrest_dvd
    have hexp : 2 + (N.primeFactors.card - 1) = N.primeFactors.card + 1 := by omega
    rwa [← pow_add, hexp] at hmul_dvd
  have hfull_dvd :
      2 ^ (N.primeFactors.card + 1) * (∏ p ∈ N.primeFactors, p ^ (N.factorization p - 1)) ∣
        N.totient := by
    calc
      2 ^ (N.primeFactors.card + 1) * (∏ p ∈ N.primeFactors, p ^ (N.factorization p - 1))
          ∣ (∏ p ∈ N.primeFactors, (p - 1)) *
              (∏ p ∈ N.primeFactors, p ^ (N.factorization p - 1)) :=
        mul_dvd_mul_right h2_pow_sub _
      _ = N.totient := by rw [htot_eq, mul_comm]
  have h2pow_dvd : 2 ^ (N.primeFactors.card + 1) ∣ N.totient :=
    (dvd_mul_right _ _).trans hfull_dvd
  have h128_dvd : 128 ∣ N.totient := by
    have h2_7 : (128 : ℕ) = 2 ^ 7 := by decide
    rw [h2_7]
    exact (Nat.pow_dvd_pow 2 (by omega)).trans h2pow_dvd
  have heuler_tot :
      ∀ q a m : ℕ, q.Prime → q % 4 = 1 → 0 < a → ¬ q ∣ m → N = q ^ a * m ^ 2 →
        2 ^ (N.primeFactors.card + 1) * q ^ (a - 1) * m ∣ N.totient := by
    intro q a m hq _ ha hqm hform
    obtain ⟨hm0, hq_mem, hNq, hm_rel, _⟩ :=
      odd_perfect_euler_form_factorization hn0 hq ha hqm hform
    have hm_sub : m.primeFactors ⊆ N.primeFactors.erase q := by
      intro r hr
      obtain ⟨hr_mem, hrq, _⟩ := hm_rel r hr
      exact Finset.mem_erase.mpr ⟨hrq, hr_mem⟩
    have hm_dvd_er : m ∣ ∏ r ∈ N.primeFactors.erase q, r ^ (N.factorization r - 1) := by
      nth_rw 1 [Nat.prod_primeFactors_pow_factorization hm0]
      have hd1 : (∏ r ∈ m.primeFactors, r ^ m.factorization r) ∣
          ∏ r ∈ m.primeFactors, r ^ (N.factorization r - 1) := by
        refine Finset.prod_dvd_prod_of_dvd _ _ fun r hr => ?_
        have hr_m_pos : 0 < m.factorization r := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr)
        have hNr := (hm_rel r hr).2.2
        exact Nat.pow_dvd_pow r (by omega)
      have hd2 : (∏ r ∈ m.primeFactors, r ^ (N.factorization r - 1)) ∣
          ∏ r ∈ N.primeFactors.erase q, r ^ (N.factorization r - 1) :=
        Finset.prod_dvd_prod_of_subset _ _ _ hm_sub
      exact hd1.trans hd2
    have hqm_dvd_prod : q ^ (a - 1) * m ∣ ∏ p ∈ N.primeFactors, p ^ (N.factorization p - 1) := by
      rw [← Finset.mul_prod_erase N.primeFactors (fun p => p ^ (N.factorization p - 1)) hq_mem, hNq]
      exact mul_dvd_mul_left _ hm_dvd_er
    have hcomb : 2 ^ (N.primeFactors.card + 1) * q ^ (a - 1) * m ∣
        2 ^ (N.primeFactors.card + 1) * (∏ p ∈ N.primeFactors, p ^ (N.factorization p - 1)) := by
      rw [mul_assoc]
      exact mul_dvd_mul_left _ hqm_dvd_prod
    exact hcomb.trans hfull_dvd
  have hfree_clause : (∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) →
      149 ≤ N.primeFactors.card ∧ 2 ^ 150 ∣ N.totient := by
    intro hfree
    obtain ⟨q, hq_mem, hq4, he, hev⟩ := euler_exponents ho hN
    have h443 : 443 ≤ N.primeFactors.card :=
      (sixth_power_free_collision_excess_ge_221 ho hN hq_mem hq4 he hev hfree).1
    have h149 : 149 ≤ N.primeFactors.card := by omega
    have h2_150 : 2 ^ 150 ∣ N.totient :=
      (Nat.pow_dvd_pow 2 (by omega : 150 ≤ N.primeFactors.card + 1)).trans h2pow_dvd
    exact ⟨h149, h2_150⟩
  exact ⟨h2pow_dvd, h128_dvd, hfull_dvd, heuler_tot, hfree_clause⟩

end OddPerfect
