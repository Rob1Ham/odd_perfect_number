module

public import OddPerfect.PositiveHalfReturn
public import OddPerfect.ExceptionalOrder
public import OddPerfect.ExceptionalIndexSources
public import OddPerfect.IndexBound2379
public import OddPerfect.ExponentOneSize
public import OddPerfect.SecondLargestPrime
public import OddPerfect.SizeBound300
import all OddPerfect.EulerSquareClass
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

namespace OddPerfect

open ArithmeticFunction

/-- On the `I = l * t^2` branch with `a > 1`, the Euler half-blocks yield
an explicit cofactor factorization `m = l * v * y * t` with coprimality,
divisibility `d * w ∣ y`, `l ∣ m`, `d ∣ m`, and exact valuation coupling
on all prime factors of `y`. -/
theorem exceptional_index_cofactor_factorization {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1) (ha4 : a % 4 = 1)
    (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2) (hl : l.Prime)
    (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    let d := (a + 1) / 2
    ∃ w y v : ℕ, q + 1 = 2 * d * w ^ 2 ∧ q ^ d + 1 = 2 * y ^ 2 ∧
      geometricBlock q d = l * v ^ 2 ∧ m = l * v * y * t ∧
      Nat.Coprime (l * v) y ∧ d * w ∣ y ∧ l ∣ m ∧ d ∣ m ∧
      ∀ r ∈ y.primeFactors, m.factorization r = y.factorization r + t.factorization r := by
  let d := (a + 1) / 2
  obtain ⟨w, y, v, hq1, hqd1, hgeom⟩ :=
    prime_mul_square_euler_block_equations hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨i, hi_pos, hleft, hright, _⟩ :=
    exists_component_index hN hq hform (fun h => hqm (hq.dvd_of_dvd_pow h))
  have hi_eq : i = l * t ^ 2 := by
    rw [← hi, hleft, Nat.mul_div_cancel_left i (pow_pos hq.pos a)]
  obtain ⟨hbal, hcopAB, _, hB2, _⟩ := euler_half_blocks hq hq4 ha4 hright
  have hB : (q ^ d + 1) / 2 = y ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
    exact hB2.trans hqd1
  have hm_sq : m ^ 2 = (l * v * y * t) ^ 2 := by
    rw [hbal, hgeom, hB, hi_eq]
    ring
  have hm_eq : m = l * v * y * t := Nat.pow_left_injective (by decide : 2 ≠ 0) hm_sq
  have hcop_lv_y : Nat.Coprime (l * v) y := by
    have hcop' : (l * v ^ 2).Coprime (y ^ 2) := by
      rw [← hgeom, ← hB]
      exact hcopAB
    exact (hcop'.coprime_dvd_left ⟨v, by ring⟩).coprime_dvd_right (dvd_pow_self y (by decide : 2 ≠ 0))
  have hd_pos : 0 < d := by dsimp [d]; omega
  have hd_odd : Odd d := Nat.odd_iff.mpr (by dsimp [d]; omega)
  have hq_odd : Odd q := Nat.odd_iff.mpr (by omega)
  have hw_ne : w ≠ 0 := by rintro rfl; simp at hq1
  have hy_ne : y ≠ 0 := by rintro rfl; simp at hqd1
  have hdw_ne : d * w ≠ 0 := mul_ne_zero hd_pos.ne' hw_ne
  have hH_eq : (q + 1) / 2 = d * w ^ 2 := by
    rw [hq1, mul_assoc, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  have hH_odd : Odd ((q + 1) / 2) := Nat.odd_iff.mpr (by omega)
  have hdwy : d * w ∣ y := by
    apply (Nat.factorization_le_iff_dvd hdw_ne hy_ne).mp
    intro r
    by_cases hr : r ∈ (d * w).primeFactors
    · obtain ⟨hrp, hrdw, _⟩ := Nat.mem_primeFactors.mp hr
      have hrH : r ∣ (q + 1) / 2 := hrdw.trans ⟨w, by rw [hH_eq]; ring⟩
      have hro : Odd r := hH_odd.of_dvd_nat hrH
      have hrq : r ∣ q + 1 := hrH.trans ⟨2, by omega⟩
      have hval := half_sum_valuation hq_odd hd_odd hrp hro hrq
      change ((q ^ d + 1) / 2).factorization r = ((q + 1) / 2).factorization r + d.factorization r at hval
      rw [hB, hH_eq, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
        Nat.factorization_mul hd_pos.ne' (pow_ne_zero 2 hw_ne), Finsupp.add_apply,
        Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hval
      rw [Nat.factorization_mul hd_pos.ne' hw_ne, Finsupp.add_apply]
      omega
    · rw [Finsupp.notMem_support_iff.mp hr]
      exact Nat.zero_le _
  have hlm : l ∣ m := ⟨v * y * t, by rw [hm_eq]; ring⟩
  have hdm : d ∣ m := (dvd_mul_right d w).trans (hdwy.trans ⟨l * v * t, by rw [hm_eq]; ring⟩)
  have hm_ne : m ≠ 0 :=
    (ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self m (by decide : 2 ≠ 0)) _)).pos.ne'
  have hv_ne : v ≠ 0 := by
    rintro rfl
    simp [hm_ne] at hm_eq
  have ht_ne : t ≠ 0 := by
    rintro rfl
    simp at hi_eq
    omega
  have hlv_ne : l * v ≠ 0 := mul_ne_zero hl.ne_zero hv_ne
  refine ⟨w, y, v, hq1, hqd1, hgeom, hm_eq, hcop_lv_y, hdwy, hlm, hdm, ?_⟩
  intro r hr
  have hr_prime := Nat.prime_of_mem_primeFactors hr
  have hry : r ∣ y := Nat.dvd_of_mem_primeFactors hr
  have hrlv : ¬ r ∣ l * v := fun hd =>
    hr_prime.not_dvd_one (hcop_lv_y.gcd_eq_one ▸ Nat.dvd_gcd hd hry)
  rw [hm_eq, mul_assoc (l * v) y t,
    Nat.factorization_mul hlv_ne (mul_ne_zero hy_ne ht_ne), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hrlv, zero_add,
    Nat.factorization_mul hy_ne ht_ne, Finsupp.add_apply]

/-- Unconditional lower bound on the Euler index at exponent one from the
`10^300 < N` lower bound. -/
theorem euler_exponent_one_index_gt_five_mul_ten_pow_99 {N q m : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2) :
    5 * 10 ^ 99 < sigma 1 (m ^ 2) / q := by
  have hN300 := ten_pow_three_hundred_lt_of_odd_perfect ho hN
  have h1 : (2 : ℕ) * (5 * 10 ^ 99) ^ 3 = 250 * 10 ^ 297 := by
    rw [mul_pow, ← pow_mul, show (5 : ℕ) ^ 3 = 125 by decide, show 99 * 3 = 297 by decide,
      ← mul_assoc, show 2 * 125 = 250 by decide]
  have h2 : (10 : ℕ) ^ 300 = 1000 * 10 ^ 297 := by
    rw [show (300 : ℕ) = 3 + 297 by decide, pow_add, show (10 : ℕ) ^ 3 = 1000 by decide]
  have h3 : 250 * 10 ^ 297 ≤ 1000 * 10 ^ 297 := Nat.mul_le_mul_right _ (by decide)
  have hsize : 2 * (5 * 10 ^ 99) ^ 3 ≤ N := by omega
  exact exponent_one_index_gt_of_size hN ho hq hqm hform hsize

/-- Dris's conjecture `q^a < m` holds whenever `2 * q^a ≤ I`. -/
theorem dris_of_two_mul_pow_le_index {N q a m : ℕ}
    (hN : N.Perfect) (_ho : Odd N) (hq : q.Prime) (_hq4 : q % 4 = 1) (ha4 : a % 4 = 1)
    (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hI : 2 * q ^ a ≤ sigma 1 (m ^ 2) / q ^ a) :
    q ^ a < m := by
  obtain ⟨i, hi_pos, hleft, hright, _⟩ :=
    exists_component_index hN hq hform (fun h => hqm (hq.dvd_of_dvd_pow h))
  have hi_eq : sigma 1 (m ^ 2) / q ^ a = i := by
    rw [hleft, Nat.mul_div_cancel_left i (pow_pos hq.pos a)]
  rw [hi_eq] at hI
  have ha_pos : 0 < a := by omega
  have hsig_gt : q ^ a < sigma 1 (q ^ a) := by
    rw [sigma_one_apply_prime_pow hq, Finset.sum_range_succ]
    have hsum : 0 < ∑ j ∈ Finset.range a, q ^ j :=
      Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨0, Finset.mem_range.mpr ha_pos, by simp⟩
    omega
  have hsq : (q ^ a) ^ 2 < m ^ 2 := by
    have h1 : 2 * (q ^ a) ^ 2 = q ^ a * (2 * q ^ a) := by ring
    have h2 : q ^ a * (2 * q ^ a) ≤ q ^ a * i := Nat.mul_le_mul_left _ hI
    have h3 : q ^ a * i < sigma 1 (q ^ a) * i := Nat.mul_lt_mul_of_pos_right hsig_gt hi_pos
    nlinarith
  nlinarith

/-- Dris's conjecture `q^a < m` holds whenever `2 * m ≤ I`. -/
theorem dris_of_two_mul_cofactor_le_index {N q a m : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (_hq4 : q % 4 = 1) (ha4 : a % 4 = 1)
    (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hI : 2 * m ≤ sigma 1 (m ^ 2) / q ^ a) :
    q ^ a < m := by
  obtain ⟨i, hi_pos, hleft, hright, _⟩ :=
    exists_component_index hN hq hform (fun h => hqm (hq.dvd_of_dvd_pow h))
  have hi_eq : sigma 1 (m ^ 2) / q ^ a = i := by
    rw [hleft, Nat.mul_div_cancel_left i (pow_pos hq.pos a)]
  rw [hi_eq] at hI
  have ha_pos : 0 < a := by omega
  have hsig_gt : q ^ a < sigma 1 (q ^ a) := by
    rw [sigma_one_apply_prime_pow hq, Finset.sum_range_succ]
    have hsum : 0 < ∑ j ∈ Finset.range a, q ^ j :=
      Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨0, Finset.mem_range.mpr ha_pos, by simp⟩
    omega
  have hm_pos : 0 < m :=
    (ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self m (by decide : 2 ≠ 0)) _)).pos
  have hlt : q ^ a * (2 * m) < m * (2 * m) := by
    have hq_pos : 0 < q ^ a := pow_pos hq.pos a
    calc q ^ a * (2 * m) ≤ q ^ a * i := Nat.mul_le_mul_left _ hI
      _ < sigma 1 (q ^ a) * i := Nat.mul_lt_mul_of_pos_right hsig_gt hi_pos
      _ = 2 * m ^ 2 := hright
      _ = m * (2 * m) := by ring
  exact Nat.lt_of_mul_lt_mul_right hlt

/-- Dris's conjecture holds unconditionally whenever `q^a ≤ 1189`. -/
theorem dris_of_small_euler_pow {N q a m : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1) (ha4 : a % 4 = 1)
    (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2) (hsmall : q ^ a ≤ 1189) :
    q ^ a < m := by
  have h2379 := (euler_component_index_ge_2379 hN ho hq hq4 ha4 hqm hform).2
  exact dris_of_two_mul_pow_le_index hN ho hq hq4 ha4 hqm hform (by omega)

/-- At Euler exponent one, if `q` is not the largest prime factor of `N`,
then Dris's conjecture `q < m` holds unconditionally. -/
theorem dris_exponent_one_of_not_largest_prime {N q m r : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2) (hrN : r ∈ N.primeFactors) (hqr : q < r) :
    q < m := by
  have _ := hqm
  have hqN : q ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hform ▸ dvd_mul_right _ _, hN.2.ne'⟩
  have h5 := prime_pow_five_lt_two_mul_of_lt ho hN hqN hrN hqr
  rw [hform] at h5
  have h4 : q ^ 4 < 2 * m ^ 2 := by
    have hmul : q * q ^ 4 < q * (2 * m ^ 2) := by
      calc q * q ^ 4 = q ^ 5 := by ring
        _ < 2 * (q * m ^ 2) := h5
        _ = q * (2 * m ^ 2) := by ring
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hq5 : 5 ≤ q := by have := hq.two_le; omega
  have hq2_2 : 2 ≤ q ^ 2 := by nlinarith
  have h2q2 : 2 * q ^ 2 ≤ q ^ 4 := by
    calc 2 * q ^ 2 ≤ q ^ 2 * q ^ 2 := Nat.mul_le_mul_right _ hq2_2
      _ = q ^ 4 := by ring
  have hsq : q ^ 2 < m ^ 2 := by omega
  nlinarith

/-- Structural consequences whenever Dris's conjecture fails (`m ≤ q^a`). -/
theorem dris_failure_consequences {N q a m : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1) (ha4 : a % 4 = 1)
    (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2) (hfail : m ≤ q ^ a) :
    let i := sigma 1 (m ^ 2) / q ^ a
    m < q ^ a ∧ i < 2 * m ∧ i < 2 * q ^ a ∧ N < q ^ (3 * a) ∧
      (∀ r ∈ N.primeFactors, a = 1 → r ≤ q) ∧
      (a = 1 → q ^ 2 < 3 * m ^ 2 ∧ m < i ∧ i < 2 * q ∧ 5 * 10 ^ 99 < q) := by
  intro i
  have ha_pos : 0 < a := by omega
  have hm_lt : m < q ^ a := by
    refine lt_of_le_of_ne hfail ?_
    intro heq
    apply hqm
    rw [heq]
    exact dvd_pow_self q ha_pos.ne'
  have hi_lt_2m : i < 2 * m := by
    by_contra! hle
    exact hm_lt.not_ge (dris_of_two_mul_cofactor_le_index hN ho hq hq4 ha4 hqm hform hle).le
  have hi_lt_2q : i < 2 * q ^ a := by omega
  have hN_lt : N < q ^ (3 * a) := by
    have hm_sq : m ^ 2 < (q ^ a) ^ 2 := by nlinarith
    have hq_pos : 0 < q ^ a := pow_pos hq.pos a
    calc N = q ^ a * m ^ 2 := hform
      _ < q ^ a * (q ^ a) ^ 2 := Nat.mul_lt_mul_of_pos_left hm_sq hq_pos
      _ = q ^ (3 * a) := by rw [← pow_mul]; ring
  have hmax : ∀ r ∈ N.primeFactors, a = 1 → r ≤ q := by
    intro r hrN ha1
    subst a
    by_contra! hqr
    have hform1 : N = q * m ^ 2 := by simpa using hform
    have hqm_lt := dris_exponent_one_of_not_largest_prime hN ho hq hq4 hqm hform1 hrN hqr
    simp only [pow_one] at hfail
    omega
  refine ⟨hm_lt, hi_lt_2m, hi_lt_2q, hN_lt, hmax, ?_⟩
  intro ha1
  subst a
  have hform1 : N = q * m ^ 2 := by simpa using hform
  have hqN : q ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hform1 ▸ dvd_mul_right _ _, hN.2.ne'⟩
  have hcube := prime_cube_lt_three_mul hN ho hqN
  have hq2_lt : q ^ 2 < 3 * m ^ 2 := by
    have hmul : q * q ^ 2 < q * (3 * m ^ 2) := by
      calc q * q ^ 2 = q ^ 3 := by ring
        _ < 3 * N := hcube
        _ = q * (3 * m ^ 2) := by rw [hform1]; ring
    exact Nat.lt_of_mul_lt_mul_left hmul
  have h_size := exponent_one_size_lt_twice_index_cube hN ho hq hqm hform1
  have hi1 : i = sigma 1 (m ^ 2) / q := by simp [i]
  have hm_le_i : m ≤ i := by
    have hm2_le : m ^ 2 ≤ i ^ 2 := by simpa [← hi1] using h_size.2.1
    nlinarith
  have hm_lt_i : m < i := by
    refine lt_of_le_of_ne hm_le_i ?_
    intro heq
    obtain ⟨u, hu_pos, hleft, hright, _⟩ :=
      exists_component_index hN hq hform (fun h => hqm (hq.dvd_of_dvd_pow h))
    have hu_eq : u = i := by
      dsimp [i]
      rw [hleft, Nat.mul_div_cancel_left u (pow_pos hq.pos 1)]
    rw [hu_eq, ← heq] at hright
    have hm_pos : 0 < m :=
      (ho.of_dvd_nat (hform1 ▸ dvd_mul_of_dvd_right (dvd_pow_self m (by decide : 2 ≠ 0)) _)).pos
    have hsig1 : sigma 1 q = q + 1 := by
      rw [← pow_one q, sigma_one_apply_prime_pow hq]
      simp [Finset.sum_range_succ, add_comm]
    rw [pow_one] at hright
    rw [hsig1] at hright
    have hq_eq : q + 1 = 2 * m := by
      apply Nat.mul_right_cancel hm_pos
      nlinarith
    have hm_le3 : m ≤ 3 := by nlinarith
    have hi_gt := euler_exponent_one_index_gt_five_mul_ten_pow_99 hN ho hq hqm hform1
    rw [← hi1, ← heq] at hi_gt
    have h5_99 : 3 < 5 * 10 ^ 99 := by
      have : 1 ≤ 10 ^ 99 := Nat.one_le_pow 99 10 (by decide)
      omega
    omega
  have hi_lt_2q1 : i < 2 * q := by simpa using hi_lt_2q
  have hq_gt : 5 * 10 ^ 99 < q := by
    have hN300 := ten_pow_three_hundred_lt_of_odd_perfect ho hN
    have hq3 : 10 ^ 300 < q ^ 3 := by
      have hN_lt1 : N < q ^ 3 := by simpa using hN_lt
      exact hN300.trans hN_lt1
    have hq100 : 10 ^ 100 < q := by
      have hpow3 : ((10 : ℕ) ^ 100) ^ 3 = 10 ^ 300 := by rw [← pow_mul]
      rw [← hpow3] at hq3
      by_contra! hle
      exact hq3.not_ge (Nat.pow_le_pow_left hle 3)
    have h5_100 : 5 * 10 ^ 99 < 10 ^ 100 := by
      have h100 : (10 : ℕ) ^ 100 = 10 * 10 ^ 99 := by
        rw [show (100 : ℕ) = 1 + 99 by decide, pow_add, pow_one]
      have hpos99 : 0 < 10 ^ 99 := by positivity
      omega
    exact h5_100.trans hq100
  exact ⟨hq2_lt, hm_lt_i, hi_lt_2q1, hq_gt⟩

end OddPerfect
