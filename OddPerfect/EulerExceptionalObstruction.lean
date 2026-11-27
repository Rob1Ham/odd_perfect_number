module

public import OddPerfect.DrisRegimes
public import OddPerfect.OddGeometricSquares
public import OddPerfect.OddGraphWeight
import OddPerfect.IndexWeight
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

namespace OddPerfect

open ArithmeticFunction Finset

private lemma not_prime_of_proper_dvd {p n : ℕ} (hp : 1 < p) (hd : p ∣ n) (hlt : p < n) :
    ¬ n.Prime := by
  intro hn
  rcases hn.eq_one_or_self_of_dvd p hd with rfl | rfl <;> omega

private lemma exceptional_small_d_not_prime_two_d_sub_one :
    ∀ d : Fin 97, d.val.Prime → d.val % 8 = 1 → ¬ (2 * d.val - 1).Prime := by
  decide +kernel

private lemma exceptional_gt_17_lt_97_cases :
    ∀ d : Fin 97, d.val.Prime → d.val % 8 = 1 → 17 < d.val →
      d.val = 41 ∨ d.val = 73 ∨ d.val = 89 := by
  decide +kernel

private lemma exceptional_41_small_w_factor :
    ∀ w : Fin 21, Odd w.val →
      (3 ∣ 82 * w.val ^ 2 - 1 ∧ 3 < 82 * w.val ^ 2 - 1) ∨
      (11 ∣ 82 * w.val ^ 2 - 1 ∧ 11 < 82 * w.val ^ 2 - 1) ∨
      (19 ∣ 82 * w.val ^ 2 - 1 ∧ 19 < 82 * w.val ^ 2 - 1) ∨
      (29 ∣ 82 * w.val ^ 2 - 1 ∧ 29 < 82 * w.val ^ 2 - 1) := by
  decide +kernel

private lemma exceptional_41_small_w_not_prime (w : ℕ) (hw21 : w < 21) (hw_odd : Odd w) :
    ¬ (82 * w ^ 2 - 1).Prime := by
  rcases exceptional_41_small_w_factor ⟨w, hw21⟩ hw_odd with h | h | h | h
  · exact not_prime_of_proper_dvd (by decide) h.1 h.2
  · exact not_prime_of_proper_dvd (by decide) h.1 h.2
  · exact not_prime_of_proper_dvd (by decide) h.1 h.2
  · exact not_prime_of_proper_dvd (by decide) h.1 h.2

private lemma ten_pow_740_le_pow_9_pow_96 : (10 : ℕ) ^ 740 ≤ (10 ^ 9) ^ 96 := by
  have h1 : (10 : ℕ) ^ 740 ≤ 10 ^ (9 * 96) :=
    pow_le_pow_right₀ (by decide) (by decide)
  rw [pow_mul] at h1
  exact h1

/-- Unconditional parameter floors (`17 ≤ d`, `33 ≤ a`, `193 ≤ q`, `137 ≤ l`, `3 ≤ t`)
on the prime-times-square Euler-index branch `I = l * t ^ 2` with `a > 1`. -/
theorem exceptional_index_parameter_floors {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    let d := (a + 1) / 2
    17 ≤ d ∧ 33 ≤ a ∧ 193 ≤ q ∧ 8 * d + 1 ≤ l ∧ 137 ≤ l ∧ 3 ≤ t := by
  intro d
  obtain ⟨hd_prime, hd8, hq16, w, hw⟩ :=
    prime_mul_square_index_forces_exceptional_prime_length hN ho hq hq4 ha4 ha hqm hform (Or.inr hl) hi
  change d.Prime at hd_prime
  change d % 8 = 1 at hd8
  change (q + 1) / 2 = d * w ^ 2 at hw
  have hd_ne_1 : d ≠ 1 := hd_prime.ne_one
  have hd_ne_9 : d ≠ 9 := by
    intro h
    rw [h] at hd_prime
    exact (by decide : ¬ Nat.Prime 9) hd_prime
  have hd17 : 17 ≤ d := by omega
  have ha_eq : a + 1 = 2 * d := by dsimp [d]; omega
  have ha33 : 33 ≤ a := by omega
  obtain ⟨_, _, hl_mod⟩ :=
    prime_mul_square_euler_index_order hN ho hq hq4 ha4 ha hqm hform (Or.inr hl) hi
  change l ≡ 1 [MOD 8 * d] at hl_mod
  have h8d_dvd : 8 * d ∣ l - 1 := (Nat.modEq_iff_dvd' hl.one_le).mp hl_mod.symm
  have hl_gt1 : 1 < l := hl.one_lt
  have h8d_le : 8 * d ≤ l - 1 := Nat.le_of_dvd (by omega) h8d_dvd
  have hl_bound : 8 * d + 1 ≤ l := by omega
  have hl137 : 137 ≤ l := by omega
  have hq_half : q + 1 = 2 * ((q + 1) / 2) := by omega
  have hq_eq : q + 1 = 2 * (d * w ^ 2) := by rw [hq_half, hw]
  have hw_odd : Odd w := by
    have hdw_odd : Odd (d * w ^ 2) := Nat.odd_iff.mpr (by rw [← hw]; omega)
    exact (hdw_odd.of_dvd_nat (dvd_mul_left _ _)).of_dvd_nat (dvd_pow_self w (by decide : 2 ≠ 0))
  have hw_pos : 1 ≤ w := hw_odd.pos
  have hq193 : 193 ≤ q := by
    by_cases hd97 : 97 ≤ d
    · have hw2 : 1 ≤ w ^ 2 := Nat.one_le_pow 2 w hw_pos
      have hmul : 2 * 97 * 1 ≤ 2 * (d * w ^ 2) := by nlinarith
      omega
    · have hd_lt : d < 97 := by omega
      by_cases hw3 : 3 ≤ w
      · have hw2 : 9 ≤ w ^ 2 := by nlinarith
        have hmul : 2 * 17 * 9 ≤ 2 * (d * w ^ 2) := by nlinarith
        omega
      · have hw1 : w = 1 := by
          obtain ⟨k, hk⟩ := hw_odd
          omega
        rw [hw1, one_pow, mul_one] at hq_eq
        have hq_val : q = 2 * d - 1 := by omega
        have hnot : ¬ (2 * d - 1).Prime :=
          exceptional_small_d_not_prime_two_d_sub_one ⟨d, hd_lt⟩ hd_prime hd8
        exact absurd (hq_val ▸ hq) hnot
  have hI8 := prime_mul_square_euler_index_one_mod_eight hN ho hq hq4 ha4 ha hqm hform l t (Or.inr hl) hi
  rw [hi] at hI8
  have ht_odd : Odd t := by
    have ht2_odd : Odd (l * t ^ 2) := Nat.odd_iff.mpr (by omega)
    exact ht2_odd.of_dvd_nat (dvd_mul_of_dvd_right (dvd_pow_self t (by decide : 2 ≠ 0)) l)
  have ht_ne1 : t ≠ 1 := by
    rintro rfl
    obtain ⟨i, _, hleft, hright, _⟩ :=
      exists_component_index hN hq hform (fun h => hqm (hq.dvd_of_dvd_pow h))
    have hi_eq : i = l := by
      have hdiv : sigma 1 (m ^ 2) / q ^ a = i := by
        rw [hleft, Nat.mul_div_cancel_left i (pow_pos hq.pos a)]
      rw [← hdiv, hi]
      simp
    have hqm2 : ¬ q ∣ m ^ 2 := fun h => hqm (hq.dvd_of_dvd_pow h)
    have hi_not_prime := component_index_not_prime hN ho hq (by omega : 0 < a) hform hqm2 hleft hright
    exact hi_not_prime (hi_eq ▸ hl)
  have ht3 : 3 ≤ t := by
    obtain ⟨k, hk⟩ := ht_odd
    omega
  exact ⟨hd17, ha33, hq193, hl_bound, hl137, ht3⟩

/-- If `d = (a + 1) / 2 > 17` on the `I = l * t ^ 2` branch, then `N > 10 ^ 740`. -/
theorem exceptional_index_size_gt_ten_pow_740_of_gt_17 {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2)
    (hd17 : 17 < (a + 1) / 2) :
    10 ^ 740 < N := by
  let d := (a + 1) / 2
  obtain ⟨hd_prime, hd8, hq16, w, hw⟩ :=
    prime_mul_square_index_forces_exceptional_prime_length hN ho hq hq4 ha4 ha hqm hform (Or.inr hl) hi
  change d.Prime at hd_prime
  change d % 8 = 1 at hd8
  change (q + 1) / 2 = d * w ^ 2 at hw
  obtain ⟨_, _, hq193, _, _, _⟩ :=
    exceptional_index_parameter_floors hN ho hq hq4 ha4 ha hqm hform hl hi
  have ha_eq : a + 1 = 2 * d := by dsimp [d]; omega
  have h2379 := (euler_component_index_ge_2379 hN ho hq hq4 ha4 hqm hform).1
  have hqa_pos : 0 < q ^ a := pow_pos hq.pos a
  have hN_lower : 2379 * q ^ (2 * a) < 2 * N := by
    have hmul := Nat.mul_lt_mul_of_pos_left h2379 hqa_pos
    calc 2379 * q ^ (2 * a) = q ^ a * (2379 * q ^ a) := by rw [two_mul, pow_add]; ring
      _ < q ^ a * (2 * m ^ 2) := hmul
      _ = 2 * N := by rw [hform]; ring
  have hq_half : q + 1 = 2 * ((q + 1) / 2) := by omega
  have hq_eq : q + 1 = 2 * d * w ^ 2 := by rw [hq_half, hw]; ring
  have hw_odd : Odd w := by
    have hdw_odd : Odd (d * w ^ 2) := Nat.odd_iff.mpr (by rw [← hw]; omega)
    exact (hdw_odd.of_dvd_nat (dvd_mul_left _ _)).of_dvd_nat (dvd_pow_self w (by decide : 2 ≠ 0))
  have hq_ge_10_pow_740 : 2 * 10 ^ 740 < 2379 * q ^ (2 * a) := by
    by_cases hd97 : 97 ≤ d
    · have ha_ge : 4 * 96 ≤ 2 * a := by omega
      have h193_4 : 10 ^ 9 < 193 ^ 4 := by decide
      have hpow96 : (10 ^ 9) ^ 96 < (193 ^ 4) ^ 96 := Nat.pow_lt_pow_left h193_4 (by decide)
      have hpow_q : (193 ^ 4) ^ 96 ≤ q ^ (2 * a) := by
        rw [← pow_mul]
        exact (pow_le_pow_left₀ (by decide) hq193 (4 * 96)).trans
          (pow_le_pow_right₀ hq.one_lt.le ha_ge)
      have h10_lt : 10 ^ 740 < q ^ (2 * a) :=
        lt_of_le_of_lt ten_pow_740_le_pow_9_pow_96 (lt_of_lt_of_le hpow96 hpow_q)
      have h_mul1 : 2 * 10 ^ 740 < 2379 * 10 ^ 740 :=
        Nat.mul_lt_mul_of_pos_right (by decide) (pow_pos (by decide) 740)
      have h_mul2 : 2379 * 10 ^ 740 < 2379 * q ^ (2 * a) :=
        Nat.mul_lt_mul_of_pos_left h10_lt (by decide)
      exact h_mul1.trans h_mul2
    · have hd_lt : d < 97 := by omega
      have hcases := exceptional_gt_17_lt_97_cases ⟨d, hd_lt⟩ hd_prime hd8 hd17
      dsimp only at hcases
      rcases hcases with hd41 | hd73 | hd89
      · have ha81 : 2 * a = 9 * 18 := by omega
        have hw_ge21 : 21 ≤ w := by
          by_contra! hw21
          have hnot := exceptional_41_small_w_not_prime w hw21 hw_odd
          have hq_val : q = 82 * w ^ 2 - 1 := by
            rw [hd41] at hq_eq
            omega
          exact hnot (hq_val ▸ hq)
        have hq_ge : 36161 ≤ q := by
          have hw2 : 441 ≤ w ^ 2 := by nlinarith
          have : 82 * 441 ≤ 2 * d * w ^ 2 := by rw [hd41]; nlinarith
          omega
        have h36161_9 : 10 ^ 41 < 36161 ^ 9 := by decide
        have hpow18 : (10 ^ 41) ^ 18 < (36161 ^ 9) ^ 18 := Nat.pow_lt_pow_left h36161_9 (by decide)
        have hpow_q : (36161 ^ 9) ^ 18 ≤ q ^ (2 * a) := by
          rw [← pow_mul, ha81]
          exact pow_le_pow_left₀ (by decide) hq_ge (9 * 18)
        have h738_lt : (10 ^ 41) ^ 18 < q ^ (2 * a) := lt_of_lt_of_le hpow18 hpow_q
        have h740 : 2 * (10 : ℕ) ^ 740 = 200 * (10 ^ 41) ^ 18 := by
          rw [show (740 : ℕ) = 2 + 41 * 18 by decide, pow_add, pow_mul, show (10 : ℕ) ^ 2 = 100 by decide]
          ring
        have h_mul1 : 200 * (10 ^ 41) ^ 18 < 2379 * (10 ^ 41) ^ 18 :=
          Nat.mul_lt_mul_of_pos_right (by decide) (pow_pos (pow_pos (by decide) 41) 18)
        have h_mul2 : 2379 * (10 ^ 41) ^ 18 < 2379 * q ^ (2 * a) :=
          Nat.mul_lt_mul_of_pos_left h738_lt (by decide)
        rw [h740]
        exact h_mul1.trans h_mul2
      · have hw3 : 3 ≤ w := by
          by_contra! hw3
          have hw1 : w = 1 := by obtain ⟨k, hk⟩ := hw_odd; omega
          rw [hw1, hd73] at hq_eq
          omega
        have hq_ge : 1313 ≤ q := by
          have hw2 : 9 ≤ w ^ 2 := by nlinarith
          have : 146 * 9 ≤ 2 * d * w ^ 2 := by rw [hd73]; nlinarith
          omega
        have ha_ge : 3 * 96 ≤ 2 * a := by omega
        have h1313_3 : 10 ^ 9 < 1313 ^ 3 := by decide
        have hpow96 : (10 ^ 9) ^ 96 < (1313 ^ 3) ^ 96 := Nat.pow_lt_pow_left h1313_3 (by decide)
        have hpow_q : (1313 ^ 3) ^ 96 ≤ q ^ (2 * a) := by
          rw [← pow_mul]
          exact (pow_le_pow_left₀ (by decide) hq_ge (3 * 96)).trans
            (pow_le_pow_right₀ hq.one_lt.le ha_ge)
        have h10_lt : 10 ^ 740 < q ^ (2 * a) :=
          lt_of_le_of_lt ten_pow_740_le_pow_9_pow_96 (lt_of_lt_of_le hpow96 hpow_q)
        have h_mul1 : 2 * 10 ^ 740 < 2379 * 10 ^ 740 :=
          Nat.mul_lt_mul_of_pos_right (by decide) (pow_pos (by decide) 740)
        have h_mul2 : 2379 * 10 ^ 740 < 2379 * q ^ (2 * a) :=
          Nat.mul_lt_mul_of_pos_left h10_lt (by decide)
        exact h_mul1.trans h_mul2
      · have hw3 : 3 ≤ w := by
          by_contra! hw3
          have hw1 : w = 1 := by obtain ⟨k, hk⟩ := hw_odd; omega
          rw [hw1, hd89] at hq_eq
          omega
        have hq_ge : 1313 ≤ q := by
          have hw2 : 9 ≤ w ^ 2 := by nlinarith
          have : 178 * 9 ≤ 2 * d * w ^ 2 := by rw [hd89]; nlinarith
          omega
        have ha_ge : 3 * 96 ≤ 2 * a := by omega
        have h1313_3 : 10 ^ 9 < 1313 ^ 3 := by decide
        have hpow96 : (10 ^ 9) ^ 96 < (1313 ^ 3) ^ 96 := Nat.pow_lt_pow_left h1313_3 (by decide)
        have hpow_q : (1313 ^ 3) ^ 96 ≤ q ^ (2 * a) := by
          rw [← pow_mul]
          exact (pow_le_pow_left₀ (by decide) hq_ge (3 * 96)).trans
            (pow_le_pow_right₀ hq.one_lt.le ha_ge)
        have h10_lt : 10 ^ 740 < q ^ (2 * a) :=
          lt_of_le_of_lt ten_pow_740_le_pow_9_pow_96 (lt_of_lt_of_le hpow96 hpow_q)
        have h_mul1 : 2 * 10 ^ 740 < 2379 * 10 ^ 740 :=
          Nat.mul_lt_mul_of_pos_right (by decide) (pow_pos (by decide) 740)
        have h_mul2 : 2379 * 10 ^ 740 < 2379 * q ^ (2 * a) :=
          Nat.mul_lt_mul_of_pos_left h10_lt (by decide)
        exact h_mul1.trans h_mul2
  omega

/-- Exact odd-valuation cancellation law on `sigma 1 (m ^ 2) = q ^ a * l * t ^ 2`
and nonempty odd-sigma targets for every non-`3^2` prime factor of `m`. -/
theorem exceptional_index_cofactor_odd_targets {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    oddValuationPrimes (sigma 1 (m ^ 2)) = {q, l} ∧
    q ≠ l ∧
    ∀ r ∈ m.primeFactors, ¬ (r = 3 ∧ m.factorization 3 = 2) → (oddSigmaTargets N r).Nonempty := by
  obtain ⟨_, y, v, _, _, _, hm_eq, _, _, hlm, _, _⟩ :=
    exceptional_index_cofactor_factorization hN ho hq hq4 ha4 ha hqm hform hl hi
  have hql : q ≠ l := by
    rintro rfl
    exact hqm hlm
  have hm_ne : m ≠ 0 :=
    (ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self m (by decide : 2 ≠ 0)) _)).pos.ne'
  have ht_ne : t ≠ 0 := by
    rintro rfl
    simp [hm_ne] at hm_eq
  have htm : t ∣ m := ⟨l * v * y, by rw [hm_eq]; ring⟩
  have hqt : ¬ q ∣ t := fun h => hqm (h.trans htm)
  obtain ⟨i, _, hleft, _, _⟩ :=
    exists_component_index hN hq hform (fun h => hqm (hq.dvd_of_dvd_pow h))
  have hsig_eq : sigma 1 (m ^ 2) = q ^ a * (l * t ^ 2) := by
    have hi_eq : i = l * t ^ 2 := by
      rw [← hi, hleft, Nat.mul_div_cancel_left i (pow_pos hq.pos a)]
    rw [hleft, hi_eq]
  have hqa_ne : q ^ a ≠ 0 := pow_ne_zero a hq.ne_zero
  have hlt2_ne : l * t ^ 2 ≠ 0 := mul_ne_zero hl.ne_zero (pow_ne_zero 2 ht_ne)
  have ht2_ne : t ^ 2 ≠ 0 := pow_ne_zero 2 ht_ne
  have hodd_primes : oddValuationPrimes (sigma 1 (m ^ 2)) = {q, l} := by
    ext u
    rw [mem_oddValuationPrimes, hsig_eq,
      Nat.factorization_mul hqa_ne hlt2_ne, Finsupp.add_apply,
      Nat.factorization_mul hl.ne_zero ht2_ne, Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    simp only [mem_insert, mem_singleton]
    constructor
    · intro hu_odd
      by_contra hnot
      push Not at hnot
      obtain ⟨huq, hul⟩ := hnot
      have hfac_ne : (q ^ a * (l * t ^ 2)).factorization u ≠ 0 := by
        rw [Nat.factorization_mul hqa_ne hlt2_ne, Finsupp.add_apply,
          Nat.factorization_mul hl.ne_zero ht2_ne, Finsupp.add_apply,
          Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
          Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
        exact hu_odd.pos.ne'
      have hup : u.Prime := Nat.prime_of_mem_primeFactors (Finsupp.mem_support_iff.mpr hfac_ne)
      have hu_not_q : ¬ u ∣ q := fun h => huq ((Nat.prime_dvd_prime_iff_eq hup hq).mp h)
      have hu_not_l : ¬ u ∣ l := fun h => hul ((Nat.prime_dvd_prime_iff_eq hup hl).mp h)
      rw [Nat.factorization_eq_zero_of_not_dvd hu_not_q,
        Nat.factorization_eq_zero_of_not_dvd hu_not_l] at hu_odd
      simp only [mul_zero, zero_add] at hu_odd
      exact (Nat.not_odd_iff_even.mpr (even_two_mul (t.factorization u))) hu_odd
    · rintro (huq | hul)
      · rw [huq]
        have hq_not_l : ¬ q ∣ l := fun h => hql ((Nat.prime_dvd_prime_iff_eq hq hl).mp h)
        rw [hq.factorization_self, mul_one,
          Nat.factorization_eq_zero_of_not_dvd hq_not_l,
          Nat.factorization_eq_zero_of_not_dvd hqt, mul_zero, add_zero, add_zero]
        exact Nat.odd_iff.mpr (by omega)
      · rw [hul]
        have hl_not_q : ¬ l ∣ q := fun h => hql.symm ((Nat.prime_dvd_prime_iff_eq hl hq).mp h)
        rw [Nat.factorization_eq_zero_of_not_dvd hl_not_q, mul_zero, zero_add,
          hl.factorization_self]
        exact ⟨t.factorization l, by ring⟩
  refine ⟨hodd_primes, hql, ?_⟩
  intro r hr_mem hr_exc
  have hr : r.Prime := Nat.prime_of_mem_primeFactors hr_mem
  have hr_dvd_m : r ∣ m := Nat.dvd_of_mem_primeFactors hr_mem
  have hr_ne_q : r ≠ q := fun h => hqm (h ▸ hr_dvd_m)
  have hr_not_q : ¬ r ∣ q := fun h => hr_ne_q ((Nat.prime_dvd_prime_iff_eq hr hq).mp h)
  have hr_dvd_N : r ∣ N :=
    hr_dvd_m.trans ((dvd_pow_self m (by decide : 2 ≠ 0)).trans (hform ▸ dvd_mul_left _ _))
  have hrN : r ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hr, hr_dvd_N, hN.2.ne'⟩
  have hval_r : N.factorization r = 2 * m.factorization r := by
    rw [hform, Nat.factorization_mul hqa_ne (pow_ne_zero 2 hm_ne), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_eq_zero_of_not_dvd hr_not_q, mul_zero, zero_add,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have hm_pos : 0 < m.factorization r := (hr.dvd_iff_one_le_factorization hm_ne).mp hr_dvd_m
  have hN_pos : 0 < N.factorization r := by omega
  have hN_even : Even (N.factorization r) := ⟨m.factorization r, by omega⟩
  have hnot_sq : ¬ IsSquare (sigma 1 (r ^ N.factorization r)) := by
    rw [sigma_prime_pow_isSquare_iff_of_even hr hN_pos hN_even]
    rintro ⟨rfl, h4⟩
    apply hr_exc
    refine ⟨rfl, ?_⟩
    omega
  have hex_odd : ∃ p : ℕ, Odd ((sigma 1 (r ^ N.factorization r)).factorization p) := by
    by_contra! hall
    exact hnot_sq (Nat.isSquare_iff_even_factorization.mpr (fun p _ => hall p))
  obtain ⟨p, hp⟩ := hex_odd
  rw [oddSigmaTargets_eq_of_even hN ho hrN hN_even]
  exact ⟨p, mem_oddValuationPrimes.mpr hp⟩

end OddPerfect
