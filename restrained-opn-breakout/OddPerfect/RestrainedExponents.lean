module

public import OddPerfect.CyclotomicRootSlope
public import OddPerfect.Dickson
public import OddPerfect.FewPrimes
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Primality
import Mathlib.Tactic.Ring

/-!
# Restrained Exponents, Unconditional `v_3(N) ≥ 8` When `largeSources = ∅`, and Bounded Non-Square Finiteness

Stepping Stone S9a:
1. Unconditional `6 ≤ N.factorization 3` and `8 ≤ N.factorization 3` when `largeSources N q = ∅`
   (`six_le_three_exponent_of_largeSources_empty`, `eight_le_three_exponent_of_largeSources_empty`).
2. Ochem–Zelinsky restrained-exponent (`(largeSources N q).card ≤ 1`) structural bounds when
   `¬ 3 ∣ N` (`restrained_three_free_bounds`,
   `restrained_three_free_euler_exp_one_forces_sixth_power`,
   `restrained_three_free_residue_obstruction`).
3. Uniform finiteness of odd perfect numbers under bounded non-square exponent budget
   (`finite_of_bounded_nonSquare_exponents`).
-/

public section

namespace OddPerfect

open ArithmeticFunction

/-! ## 1. Unconditional `3`-Exponent Lower Bounds When `largeSources N q = ∅` -/

private lemma factorization_eq_two_of_largeSources_empty {N q r : ℕ} (hN : N.Perfect)
    (hev : ∀ s, s ≠ q → Even (N.factorization s)) (hempty : largeSources N q = ∅)
    (hr : r.Prime) (hr3 : r ≠ 3) (hrq : r ≠ q) (hrN : r ∣ N) :
    N.factorization r = 2 := by
  have hmem : r ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hr, hrN, hN.2.ne'⟩
  have hpos : 0 < N.factorization r := (hr.dvd_iff_one_le_factorization hN.2.ne').mp hrN
  have hev_r := hev r hrq
  have hnot_large : r ∉ largeSources N q := by simp [hempty]
  have hlt4 : ¬ 4 ≤ N.factorization r := fun h4 =>
    hnot_large (Finset.mem_filter.mpr ⟨hmem, hr3, hrq, h4⟩)
  obtain ⟨k, hk⟩ := hev_r
  omega

private lemma ne_of_mod_four {p q : ℕ} (hp : p % 4 = 3) (hq : q % 4 = 1) : p ≠ q := by omega
private lemma mod4_3 : 3 % 4 = 3 := by omega
private lemma mod4_7 : 7 % 4 = 3 := by omega
private lemma mod4_11 : 11 % 4 = 3 := by omega
private lemma mod4_19 : 19 % 4 = 3 := by omega
private lemma mod4_31 : 31 % 4 = 3 := by omega
private lemma mod4_127 : 127 % 4 = 3 := by omega
private lemma mod4_163 : 163 % 4 = 3 := by omega
private lemma mod4_331 : 331 % 4 = 3 := by omega
private lemma mod4_547 : 547 % 4 = 3 := by omega
private lemma mod4_811 : 811 % 4 = 3 := by omega
private lemma mod4_5419 : 5419 % 4 = 3 := by omega
private lemma mod3_7 : 7 % 3 = 1 := by omega
private lemma mod3_19 : 19 % 3 = 1 := by omega
private lemma mod3_31 : 31 % 3 = 1 := by omega
private lemma mod3_127 : 127 % 3 = 1 := by omega
private lemma mod3_331 : 331 % 3 = 1 := by omega
private lemma mod3_547 : 547 % 3 = 1 := by omega
private lemma mod3_1093 : 1093 % 3 = 1 := by omega
private lemma mod3_5419 : 5419 % 3 = 1 := by omega
private lemma half_398581 : (398581 + 1) / 2 = 19 * 10489 := by omega

private lemma seven_cycle_mem_squareSourcesOne {N q : ℕ} (hN : N.Perfect)
    (hq4 : q % 4 = 1) (hev : ∀ s, s ≠ q → Even (N.factorization s))
    (hempty : largeSources N q = ∅) (h7 : 7 ∣ N) :
    ({7, 19, 31, 127, 331, 5419} : Finset ℕ) ⊆ squareSourcesOne N := by
  have mod4_3_exp2 : ∀ r : ℕ, r.Prime → r ≠ 3 → r % 4 = 3 → r ∣ N → N.factorization r = 2 := by
    intro r hr hr3 hr4 hrN
    exact factorization_eq_two_of_largeSources_empty hN hev hempty hr hr3
      (ne_of_mod_four hr4 hq4) hrN
  have step : ∀ p r : ℕ, p.Prime → p ≠ 3 → p % 4 = 3 → p ∣ N →
      r.Prime → Odd r → r ∣ 1 + p + p ^ 2 → r ∣ N := by
    intro p r hp hp3 hp4 hpN hr hr_odd hd
    have hpe : N.factorization p = 2 := mod4_3_exp2 p hp hp3 hp4 hpN
    have hpow : p ^ 2 ∣ N := (hp.pow_dvd_iff_le_factorization hN.2.ne').2 (by linarith)
    have hnext : ¬ p ^ 3 ∣ N := fun h => by
      have := (hp.pow_dvd_iff_le_factorization hN.2.ne').1 h
      linarith
    apply dvd_perfect_of_exact_prime_pow hN hp hpow hnext hr hr_odd
    rw [← sigma_one_apply, sigma_one_apply_prime_pow hp]
    simpa [Finset.sum_range_succ, add_assoc, add_comm, add_left_comm] using hd
  have h19 : 19 ∣ N := step 7 19 (by norm_num) (by norm_num) mod4_7 h7
    (by norm_num) ⟨9, by norm_num⟩ ⟨3, by norm_num⟩
  have h127 : 127 ∣ N := step 19 127 (by norm_num) (by norm_num) mod4_19 h19
    (by norm_num) ⟨63, by norm_num⟩ ⟨3, by norm_num⟩
  have h5419_prime : Nat.Prime 5419 :=
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 43] }])
  have h5419 : 5419 ∣ N := step 127 5419 (by norm_num) (by norm_num) mod4_127 h127
    h5419_prime ⟨2709, by norm_num⟩ ⟨3, by norm_num⟩
  have h31 : 31 ∣ N := step 5419 31 h5419_prime (by norm_num) mod4_5419 h5419
    (by norm_num) ⟨15, by norm_num⟩ ⟨947451, by norm_num⟩
  have h331 : 331 ∣ N := step 31 331 (by norm_num) (by norm_num) mod4_31 h31
    (by norm_num) ⟨165, by norm_num⟩ ⟨3, by norm_num⟩
  have mem_sq1 : ∀ r : ℕ, r.Prime → r ≠ 3 → r % 4 = 3 → r % 3 = 1 → r ∣ N →
      r ∈ squareSourcesOne N := by
    intro r hr hr3 hr4 hr_mod3 hrN
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr
        ⟨Nat.mem_primeFactors.mpr ⟨hr, hrN, hN.2.ne'⟩, hr3, mod4_3_exp2 r hr hr3 hr4 hrN⟩,
       hr_mod3⟩
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_sq1 7 (by norm_num) (by norm_num) mod4_7 mod3_7 h7
  · exact mem_sq1 19 (by norm_num) (by norm_num) mod4_19 mod3_19 h19
  · exact mem_sq1 31 (by norm_num) (by norm_num) mod4_31 mod3_31 h31
  · exact mem_sq1 127 (by norm_num) (by norm_num) mod4_127 mod3_127 h127
  · exact mem_sq1 331 (by norm_num) (by norm_num) mod4_331 mod3_331 h331
  · exact mem_sq1 5419 h5419_prime (by norm_num) mod4_5419 mod3_5419 h5419

private lemma four_le_three_exponent_of_largeSources_empty {N q : ℕ} (ho : Odd N)
    (hN : N.Perfect) (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1)
    (he : N.factorization q % 4 = 1) (hev : ∀ r, r ≠ q → Even (N.factorization r))
    (hempty : largeSources N q = ∅) :
    3 ∣ N ∧ 4 ≤ N.factorization 3 := by
  have hq_prime := Nat.prime_of_mem_primeFactors hq
  have h3_dvd : 3 ∣ N := by
    by_contra h3
    have hsq : ∀ r : ℕ, r.Prime → r ∣ N → r ≠ q → N.factorization r = 2 := by
      intro r hr hrN hrq
      have hr3 : r ≠ 3 := fun h => h3 (h ▸ hrN)
      exact factorization_eq_two_of_largeSources_empty hN hev hempty hr hr3 hrq hrN
    exact steuerwald_three_free hN ho hq_prime hq4 he hsq h3
  have h3_pos : 1 ≤ N.factorization 3 :=
    (Nat.prime_three.dvd_iff_one_le_factorization hN.2.ne').mp h3_dvd
  have h3_even : Even (N.factorization 3) := hev 3 (ne_of_mod_four mod4_3 hq4)
  have h3_ne2 : N.factorization 3 ≠ 2 := by
    intro h3_eq2
    have hsq : ∀ r : ℕ, r.Prime → r ∣ N → r ≠ q → N.factorization r = 2 := by
      intro r hr hrN hrq
      by_cases hr3 : r = 3
      · subst hr3; exact h3_eq2
      · exact factorization_eq_two_of_largeSources_empty hN hev hempty hr hr3 hrq hrN
    exact steuerwald_three_present hN hq_prime hq4 he hsq h3_dvd
  obtain ⟨k, hk⟩ := h3_even
  exact ⟨h3_dvd, by omega⟩

/-- If an odd perfect number has no non-Euler prime `r ≠ 3` of exponent `≥ 4`,
then `3 ^ 6 ∣ N` (`6 ≤ N.factorization 3`). -/
theorem six_le_three_exponent_of_largeSources_empty {N q : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r, r ≠ q → Even (N.factorization r)) (hempty : largeSources N q = ∅) :
    6 ≤ N.factorization 3 := by
  obtain ⟨_, h3_ge4⟩ :=
    four_le_three_exponent_of_largeSources_empty ho hN hq hq4 he hev hempty
  have h3_even : Even (N.factorization 3) := hev 3 (ne_of_mod_four mod4_3 hq4)
  have h3_ne4 : N.factorization 3 ≠ 4 := by
    intro h3_eq4
    have hpow : 3 ^ 4 ∣ N :=
      (Nat.prime_three.pow_dvd_iff_le_factorization hN.2.ne').2 (by linarith)
    have hnext : ¬ 3 ^ 5 ∣ N := fun h => by
      have := (Nat.prime_three.pow_dvd_iff_le_factorization hN.2.ne').1 h
      linarith
    have h11 : 11 ∣ N := by
      apply dvd_perfect_of_exact_prime_pow hN (by norm_num) hpow hnext (by norm_num) ⟨5, rfl⟩
      rw [← sigma_one_apply, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
      exact ⟨11, by norm_num [Finset.sum_range_succ]⟩
    have h11_exp : N.factorization 11 = 2 :=
      factorization_eq_two_of_largeSources_empty hN hev hempty (by norm_num) (by norm_num)
        (ne_of_mod_four mod4_11 hq4) h11
    have h11_pow : 11 ^ 2 ∣ N :=
      ((by norm_num : Nat.Prime 11).pow_dvd_iff_le_factorization hN.2.ne').2 (by linarith)
    have h11_next : ¬ 11 ^ 3 ∣ N := fun h => by
      have := ((by norm_num : Nat.Prime 11).pow_dvd_iff_le_factorization hN.2.ne').1 h
      linarith
    have h7 : 7 ∣ N := by
      apply dvd_perfect_of_exact_prime_pow hN (by norm_num) h11_pow h11_next (by norm_num) ⟨3, rfl⟩
      rw [← sigma_one_apply, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
      exact ⟨19, by norm_num [Finset.sum_range_succ]⟩
    have hsub := seven_cycle_mem_squareSourcesOne hN hq4 hev hempty h7
    have hcard6 : ({7, 19, 31, 127, 331, 5419} : Finset ℕ).card = 6 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
      · norm_num
      all_goals simp only [Finset.mem_insert, Finset.mem_singleton]; norm_num
    have hcard : 6 ≤ (squareSourcesOne N).card := hcard6 ▸ Finset.card_le_card hsub
    have hbound := squareSourcesOne_card_le_three_exponent hN
    linarith
  obtain ⟨k, hk⟩ := h3_even
  omega

/-- If an odd perfect number has no non-Euler prime `r ≠ 3` of exponent `≥ 4`,
then `3 ^ 8 ∣ N` (`8 ≤ N.factorization 3`). -/
theorem eight_le_three_exponent_of_largeSources_empty {N q : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r, r ≠ q → Even (N.factorization r)) (hempty : largeSources N q = ∅) :
    8 ≤ N.factorization 3 := by
  have h3_ge6 := six_le_three_exponent_of_largeSources_empty ho hN hq hq4 he hev hempty
  have h3_even : Even (N.factorization 3) := hev 3 (ne_of_mod_four mod4_3 hq4)
  have hq_prime := Nat.prime_of_mem_primeFactors hq
  have hq_dvd : q ∣ N := Nat.dvd_of_mem_primeFactors hq
  have euler_half_dvd : ∀ r : ℕ, r.Prime → Odd r → r ∣ (q + 1) / 2 → r ∣ N := by
    intro r hr hr_odd hdr
    have hq_pow : q ^ N.factorization q ∣ N := Nat.ordProj_dvd _ _
    have hq_next : ¬ q ^ (N.factorization q + 1) ∣ N := fun h => by
      have := (hq_prime.pow_dvd_iff_le_factorization hN.2.ne').1 h
      linarith
    have hq_odd_exp : Odd (N.factorization q) := Nat.odd_iff.mpr (by omega)
    have hr_succ : r ∣ q + 1 := by
      have h := dvd_mul_of_dvd_right hdr 2
      have hq_odd : Odd q := Nat.odd_iff.mpr (by omega)
      rwa [show 2 * ((q + 1) / 2) = q + 1 by omega] at h
    apply dvd_perfect_of_exact_prime_pow hN hq_prime hq_pow hq_next hr hr_odd
    rw [← sigma_one_apply]
    exact hr_succ.trans (succ_dvd_sigma_prime_pow hq_prime hq_odd_exp)
  have step_sq : ∀ p r : ℕ, p.Prime → p ≠ 3 → p ≠ q → p ∣ N →
      r.Prime → Odd r → r ∣ 1 + p + p ^ 2 → r ∣ N := by
    intro p r hp hp3 hpq hpN hr hr_odd hd
    have hpe : N.factorization p = 2 :=
      factorization_eq_two_of_largeSources_empty hN hev hempty hp hp3 hpq hpN
    have hpow : p ^ 2 ∣ N := (hp.pow_dvd_iff_le_factorization hN.2.ne').2 (by linarith)
    have hnext : ¬ p ^ 3 ∣ N := fun h => by
      have := (hp.pow_dvd_iff_le_factorization hN.2.ne').1 h
      linarith
    apply dvd_perfect_of_exact_prime_pow hN hp hpow hnext hr hr_odd
    rw [← sigma_one_apply, sigma_one_apply_prime_pow hp]
    simpa [Finset.sum_range_succ, add_assoc, add_comm, add_left_comm] using hd
  have mem_sq1 : ∀ r : ℕ, r.Prime → r ≠ 3 → r ≠ q → r % 3 = 1 → r ∣ N →
      r ∈ squareSourcesOne N := by
    intro r hr hr3 hrq hr_mod3 hrN
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr
        ⟨Nat.mem_primeFactors.mpr ⟨hr, hrN, hN.2.ne'⟩, hr3,
          factorization_eq_two_of_largeSources_empty hN hev hempty hr hr3 hrq hrN⟩,
       hr_mod3⟩
  have h3_ne6 : N.factorization 3 ≠ 6 := by
    intro h3_eq6
    have h3_pow : 3 ^ 6 ∣ N :=
      (Nat.prime_three.pow_dvd_iff_le_factorization hN.2.ne').2 (by linarith)
    have h3_next : ¬ 3 ^ 7 ∣ N := fun h => by
      have := (Nat.prime_three.pow_dvd_iff_le_factorization hN.2.ne').1 h
      linarith
    have h1093_prime : Nat.Prime 1093 :=
      by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13] }])
    have h1093 : 1093 ∣ N := by
      apply dvd_perfect_of_exact_prime_pow hN (by norm_num) h3_pow h3_next h1093_prime ⟨546, by norm_num⟩
      rw [← sigma_one_apply, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
      exact ⟨1, by norm_num [Finset.sum_range_succ]⟩
    by_cases hq_1093 : q = 1093
    · have h547_prime : Nat.Prime 547 := by norm_num
      have h547 : 547 ∣ N := euler_half_dvd 547 h547_prime ⟨273, by norm_num⟩ (by rw [hq_1093])
      have h163_prime : Nat.Prime 163 := by norm_num
      have h163 : 163 ∣ N := step_sq 547 163 h547_prime (by norm_num)
        (ne_of_mod_four mod4_547 hq4) h547 h163_prime ⟨81, by norm_num⟩ ⟨1839, by norm_num⟩
      have h7 : 7 ∣ N := step_sq 163 7 h163_prime (by norm_num)
        (ne_of_mod_four mod4_163 hq4) h163 (by norm_num) ⟨3, by norm_num⟩ ⟨3819, by norm_num⟩
      have hcyc := seven_cycle_mem_squareSourcesOne hN hq4 hev hempty h7
      have h547_mem : 547 ∈ squareSourcesOne N :=
        mem_sq1 547 h547_prime (by norm_num) (ne_of_mod_four mod4_547 hq4) mod3_547 h547
      have hsub : insert 547 ({7, 19, 31, 127, 331, 5419} : Finset ℕ) ⊆ squareSourcesOne N :=
        Finset.insert_subset_iff.mpr ⟨h547_mem, hcyc⟩
      have hcard7 : (insert 547 ({7, 19, 31, 127, 331, 5419} : Finset ℕ)).card = 7 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · norm_num
        all_goals simp only [Finset.mem_insert, Finset.mem_singleton]; norm_num
      have hcard : 7 ≤ (squareSourcesOne N).card := hcard7 ▸ Finset.card_le_card hsub
      have hbound := squareSourcesOne_card_le_three_exponent hN
      linarith
    · have h1093_ne : (1093 : ℕ) ≠ q := Ne.symm hq_1093
      have h1093_mem : 1093 ∈ squareSourcesOne N :=
        mem_sq1 1093 h1093_prime (by norm_num) h1093_ne mod3_1093 h1093
      have hclose_cyc : 7 ∣ N → False := by
        intro h7
        have hcyc := seven_cycle_mem_squareSourcesOne hN hq4 hev hempty h7
        have hsub : insert 1093 ({7, 19, 31, 127, 331, 5419} : Finset ℕ) ⊆ squareSourcesOne N :=
          Finset.insert_subset_iff.mpr ⟨h1093_mem, hcyc⟩
        have hcard7 : (insert 1093 ({7, 19, 31, 127, 331, 5419} : Finset ℕ)).card = 7 := by
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
            Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
            Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
          · norm_num
          all_goals simp only [Finset.mem_insert, Finset.mem_singleton]; norm_num
        have hcard : 7 ≤ (squareSourcesOne N).card := hcard7 ▸ Finset.card_le_card hsub
        have hbound := squareSourcesOne_card_le_three_exponent hN
        linarith
      have h398581_prime : Nat.Prime 398581 :=
        by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 73] }])
      have h398581 : 398581 ∣ N := step_sq 1093 398581 h1093_prime (by norm_num) h1093_ne h1093
        h398581_prime ⟨199290, by norm_num⟩ ⟨3, by norm_num⟩
      by_cases hq_398581 : q = 398581
      · have h19 : 19 ∣ N := euler_half_dvd 19 (by norm_num) ⟨9, by norm_num⟩
          (by rw [hq_398581]; exact ⟨10489, half_398581⟩)
        have h127 : 127 ∣ N := step_sq 19 127 (by norm_num) (by norm_num)
          (ne_of_mod_four mod4_19 hq4) h19 (by norm_num) ⟨63, by norm_num⟩ ⟨3, by norm_num⟩
        have h5419_prime : Nat.Prime 5419 :=
          by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 43] }])
        have h5419 : 5419 ∣ N := step_sq 127 5419 (by norm_num) (by norm_num)
          (ne_of_mod_four mod4_127 hq4) h127 h5419_prime ⟨2709, by norm_num⟩ ⟨3, by norm_num⟩
        have h31 : 31 ∣ N := step_sq 5419 31 h5419_prime (by norm_num)
          (ne_of_mod_four mod4_5419 hq4) h5419 (by norm_num) ⟨15, by norm_num⟩ ⟨947451, by norm_num⟩
        have h331 : 331 ∣ N := step_sq 31 331 (by norm_num) (by norm_num)
          (ne_of_mod_four mod4_31 hq4) h31 (by norm_num) ⟨165, by norm_num⟩ ⟨3, by norm_num⟩
        have h7 : 7 ∣ N := step_sq 331 7 (by norm_num) (by norm_num)
          (ne_of_mod_four mod4_331 hq4) h331 (by norm_num) ⟨3, by norm_num⟩ ⟨15699, by norm_num⟩
        exact hclose_cyc h7
      · have h398581_ne : (398581 : ℕ) ≠ q := Ne.symm hq_398581
        have h1621_prime : Nat.Prime 1621 :=
          by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5] }])
        have h1621 : 1621 ∣ N := step_sq 398581 1621 h398581_prime (by norm_num) h398581_ne
          h398581 h1621_prime ⟨810, by norm_num⟩ ⟨98005683, by norm_num⟩
        by_cases hq_1621 : q = 1621
        · have h811_prime : Nat.Prime 811 := by norm_num
          have h811 : 811 ∣ N := euler_half_dvd 811 h811_prime ⟨405, by norm_num⟩ (by rw [hq_1621])
          have h31 : 31 ∣ N := step_sq 811 31 h811_prime (by norm_num)
            (ne_of_mod_four mod4_811 hq4) h811 (by norm_num) ⟨15, by norm_num⟩ ⟨21243, by norm_num⟩
          have h331 : 331 ∣ N := step_sq 31 331 (by norm_num) (by norm_num)
            (ne_of_mod_four mod4_31 hq4) h31 (by norm_num) ⟨165, by norm_num⟩ ⟨3, by norm_num⟩
          have h7 : 7 ∣ N := step_sq 331 7 (by norm_num) (by norm_num)
            (ne_of_mod_four mod4_331 hq4) h331 (by norm_num) ⟨3, by norm_num⟩ ⟨15699, by norm_num⟩
          exact hclose_cyc h7
        · have h7 : 7 ∣ N := step_sq 1621 7 h1621_prime (by norm_num) (Ne.symm hq_1621) h1621
            (by norm_num) ⟨3, by norm_num⟩ ⟨375609, by norm_num⟩
          exact hclose_cyc h7
  obtain ⟨k, hk⟩ := h3_even
  omega

/-! ## 2. Ochem–Zelinsky Restrained-Exponent (`(largeSources N q).card ≤ 1`) Bounds -/

private lemma three_free_partition {N q : ℕ} (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (he : N.factorization q % 4 = 1) (hev : ∀ r, r ≠ q → Even (N.factorization r))
    (h3 : ¬ 3 ∣ N) :
    N.factorization 3 = 0 ∧
    (squareSourcesOne N).card = 0 ∧
    (squareSources N).card = (squareSourcesTwo N).card ∧
    N.primeFactors.erase q = squareSources N ∪ largeSources N q ∧
    Disjoint (squareSources N) (largeSources N q) ∧
    (squareSources N).card + (largeSources N q).card + 1 = N.primeFactors.card := by
  have h3not : 3 ∉ N.primeFactors := fun h => h3 (Nat.dvd_of_mem_primeFactors h)
  have h3zero : N.factorization 3 = 0 := Finsupp.notMem_support_iff.mp h3not
  have hsq1_zero : (squareSourcesOne N).card = 0 := by
    have := squareSourcesOne_card_le_three_exponent hN
    omega
  have hsq_card : (squareSources N).card = (squareSourcesTwo N).card := by
    rw [squareSources_eq_union_one_two N,
      Finset.card_union_of_disjoint (squareSourcesOne_disjoint_two N), hsq1_zero, zero_add]
  have hpos {r : ℕ} (hr : r ∈ N.primeFactors) : 0 < N.factorization r :=
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr)
  have hparts : N.primeFactors.erase q = squareSources N ∪ largeSources N q := by
    ext r
    simp only [Finset.mem_erase, squareSources, largeSources, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hrq, hr⟩
      have hr3 : r ≠ 3 := fun h => h3not (h ▸ hr)
      obtain ⟨k, hk⟩ := hev r hrq
      have := hpos hr
      by_cases htwo : N.factorization r = 2
      · exact Or.inl ⟨hr, hr3, htwo⟩
      · exact Or.inr ⟨hr, hr3, hrq, by omega⟩
    · rintro (⟨hr, _, htwo⟩ | ⟨hr, _, hrq, _⟩)
      · exact ⟨fun h => by subst r; omega, hr⟩
      · exact ⟨hrq, hr⟩
  have hdis : Disjoint (squareSources N) (largeSources N q) := by
    apply Finset.disjoint_left.mpr
    intro r hs hl
    have htwo := (Finset.mem_filter.mp hs).2.2
    have hlarge := (Finset.mem_filter.mp hl).2.2.2
    omega
  have hcard : (squareSources N).card + (largeSources N q).card + 1 = N.primeFactors.card := by
    rw [← Finset.card_union_of_disjoint hdis, ← hparts, Finset.card_erase_add_one hq]
  exact ⟨h3zero, hsq1_zero, hsq_card, hparts, hdis, hcard⟩

/-- In the `3`-free Ochem–Zelinsky restrained regime `(largeSources N q).card ≤ 1`,
there is a unique non-Euler prime `r₀` with `4 ≤ N.factorization r₀`, and
`3 * (N.primeFactors.card - 2) ≤ 4 + N.factorization q + N.factorization r₀`
(in particular `14 ≤ N.factorization q + N.factorization r₀`). -/
theorem restrained_three_free_bounds {N q : ℕ} (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r, r ≠ q → Even (N.factorization r))
    (h3 : ¬ 3 ∣ N) (hle : (largeSources N q).card ≤ 1) :
    ∃ r₀, largeSources N q = {r₀} ∧
      3 * (N.primeFactors.card - 2) ≤ 4 + N.factorization q + N.factorization r₀ ∧
      14 ≤ N.factorization q + N.factorization r₀ := by
  obtain ⟨h3zero, hsq1_zero, hsq_card, _, _, hcard⟩ :=
    three_free_partition hN hq he hev h3
  have hne_zero : (largeSources N q).card ≠ 0 := by
    intro h0
    have hempty := Finset.card_eq_zero.mp h0
    have h6 := six_le_three_exponent_of_largeSources_empty ho hN hq hq4 he hev hempty
    omega
  have hcard1 : (largeSources N q).card = 1 := by omega
  obtain ⟨r₀, hr₀⟩ := Finset.card_eq_one.mp hcard1
  have hinc := squareSources_root_slot_incidence ho hN hq hq4 he hev
  rw [← hsq_card, hsq1_zero, hr₀] at hinc
  simp only [Finset.card_singleton, Finset.sum_singleton, mul_zero, add_zero, mul_one] at hinc
  have hsq_eq : (squareSources N).card = N.primeFactors.card - 2 := by
    rw [hr₀, Finset.card_singleton] at hcard
    omega
  have h8 := eight_le_distinct_prime_factor_count_of_three_free ho hN h3
  have hbound : 3 * (N.primeFactors.card - 2) ≤ 4 + N.factorization q + N.factorization r₀ := by
    omega
  exact ⟨r₀, hr₀, hbound, by omega⟩

/-- If `¬ 3 ∣ N`, `N.factorization q = 1`, and `largeSources N q = {r₀}`, then
`14 ≤ N.factorization r₀` (so `r₀ ^ 14 ∣ N`). -/
theorem restrained_three_free_euler_exp_one_forces_sixth_power {N q r₀ : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1)
    (he : N.factorization q = 1) (hev : ∀ r, r ≠ q → Even (N.factorization r))
    (h3 : ¬ 3 ∣ N) (hlarge : largeSources N q = {r₀}) :
    14 ≤ N.factorization r₀ := by
  have he4 : N.factorization q % 4 = 1 := by omega
  have hle : (largeSources N q).card ≤ 1 := by rw [hlarge]; simp
  obtain ⟨r₁, hr₁, _, hsum⟩ := restrained_three_free_bounds ho hN hq hq4 he4 hev h3 hle
  have hr_eq : r₁ = r₀ := by
    have : r₁ ∈ ({r₀} : Finset ℕ) := by rw [← hlarge, hr₁]; exact Finset.mem_singleton_self r₁
    exact Finset.mem_singleton.mp this
  subst r₁
  have hr₀_mem : r₀ ∈ largeSources N q := by rw [hlarge]; exact Finset.mem_singleton_self r₀
  have hr₀_neq : r₀ ≠ q := (Finset.mem_filter.mp hr₀_mem).2.2.1
  obtain ⟨k, hk⟩ := hev r₀ hr₀_neq
  omega

/-- If `¬ 3 ∣ N`, `largeSources N q = {r₀}`, and `r₀ % 3 ≠ 1`, then every `u ∈ squareSources N`
has `(normalizedSquareSum u).primeFactors ⊆ {q}`, forcing `q % 3 = 1`,
`2 * (N.primeFactors.card - 2) ≤ 1 + N.factorization q`, and `13 ≤ N.factorization q`. -/
theorem restrained_three_free_residue_obstruction {N q r₀ : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors) (_hq4 : q % 4 = 1)
    (he : N.factorization q % 4 = 1) (hev : ∀ r, r ≠ q → Even (N.factorization r))
    (h3 : ¬ 3 ∣ N) (hlarge : largeSources N q = {r₀}) (hr₀_mod : r₀ % 3 ≠ 1) :
    (∀ u ∈ squareSources N, (normalizedSquareSum u).primeFactors ⊆ {q}) ∧
      q % 3 = 1 ∧
      2 * (N.primeFactors.card - 2) ≤ 1 + N.factorization q ∧
      13 ≤ N.factorization q := by
  obtain ⟨_, hsq1_zero, _, hparts, _, hcard⟩ :=
    three_free_partition hN hq he hev h3
  have hs : squareSources N ⊆ N.primeFactors := Finset.filter_subset _ _
  have source {u : ℕ} (hu : u ∈ squareSources N) :
      u.Prime ∧ 3 < u ∧ N.factorization u = 2 := by
    obtain ⟨hmem, hne3, hex⟩ := Finset.mem_filter.mp hu
    have hprime := Nat.prime_of_mem_primeFactors hmem
    have hodd := Nat.odd_iff.mp (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hmem))
    have := hprime.two_le
    exact ⟨hprime, by omega, hex⟩
  have localDiv (u : ℕ) (hu : u ∈ squareSources N) :
      normalizedSquareSum u ∣ sigma 1 (u ^ N.factorization u) := by
    obtain ⟨hu', hu3, h2⟩ := source hu
    rw [h2]
    exact normalizedSquareSum_dvd_sigma hu' hu3
  have hcover_mod : ∀ u ∈ squareSources N, ∀ r ∈ (normalizedSquareSum u).primeFactors,
      r = q ∧ r % 3 = 1 := by
    intro u hu r hr
    obtain ⟨hup, hu3, he2⟩ := source hu
    obtain ⟨hrp, hrd, _⟩ := Nat.mem_primeFactors.mp hr
    have hd := hrd.trans (localDiv u hu)
    have hpoly := hd
    rw [he2, sigma_one_apply_prime_pow hup] at hpoly
    have hmod := (prime_dvd_sq_add_self_add_one hrp (by
      simpa [Finset.sum_range_succ, add_comm, add_assoc, add_left_comm] using hpoly)).resolve_left
      (fun h => three_not_dvd_normalizedSquareSum hup hu3 (h ▸ hrd))
    have hodd := hrp.odd_of_ne_two (by omega)
    have hrN : r ∣ N := by
      apply dvd_perfect_of_exact_prime_pow hN hup (Nat.ordProj_dvd _ _) _ hrp hodd
      · rwa [← sigma_one_apply]
      · rw [hup.pow_dvd_iff_le_factorization hN.2.ne']
        omega
    have hmem := Nat.mem_primeFactors.mpr ⟨hrp, hrN, hN.2.ne'⟩
    refine ⟨?_, hmod⟩
    by_contra hrq
    have hrerase : r ∈ N.primeFactors.erase q := Finset.mem_erase.mpr ⟨hrq, hmem⟩
    rw [hparts, Finset.mem_union] at hrerase
    rcases hrerase with hr_sq | hr_large
    · have hr_sq1 : r ∈ squareSourcesOne N := Finset.mem_filter.mpr ⟨hr_sq, hmod⟩
      have hpos : 0 < (squareSourcesOne N).card := Finset.card_pos.mpr ⟨r, hr_sq1⟩
      omega
    · rw [hlarge, Finset.mem_singleton] at hr_large
      subst hr_large
      exact hr₀_mod hmod
  have hcover : ∀ u ∈ squareSources N, (normalizedSquareSum u).primeFactors ⊆ {q} := by
    intro u hu r hr
    exact Finset.mem_singleton.mpr (hcover_mod u hu r hr).1
  have hsq_eq : (squareSources N).card = N.primeFactors.card - 2 := by
    rw [hlarge, Finset.card_singleton] at hcard
    omega
  have h8 := eight_le_distinct_prime_factor_count_of_three_free ho hN h3
  have hsq_pos : 0 < (squareSources N).card := by omega
  obtain ⟨u₀, hu₀⟩ := Finset.card_pos.mp hsq_pos
  have hq_mod3 : q % 3 = 1 := by
    obtain ⟨hu₀p, hu₀3, _⟩ := source hu₀
    have hgt1 := normalizedSquareSum_one_lt hu₀p hu₀3
    obtain ⟨w, hw⟩ := Nat.nonempty_primeFactors.mpr hgt1
    obtain ⟨rfl, hw_mod⟩ := hcover_mod u₀ hu₀ w hw
    exact hw_mod
  have hupper := sum_cardFactors_le_target_exponents hN (squareSources N) {q}
    normalizedSquareSum hs localDiv hcover (fun r hr => by
      rw [Finset.mem_singleton.mp hr]
      exact ⟨Nat.prime_of_mem_primeFactors hq, ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hq)⟩)
  rw [Finset.sum_singleton] at hupper
  let A := (squareSources N).filter fun u => (normalizedSquareSum u).Prime
  have hA_le : A.card ≤ 1 := by
    have himg_sub : A.image normalizedSquareSum ⊆ {q} := by
      intro w hw
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨huS, hwp⟩ := Finset.mem_filter.mp hu
      exact hcover u huS (Nat.mem_primeFactors.mpr ⟨hwp, dvd_rfl, hwp.ne_zero⟩)
    have hcard_img : A.card = (A.image normalizedSquareSum).card := by
      symm
      apply Finset.card_image_of_injOn
      intro u hu v hv heq
      obtain ⟨hup, hu3, _⟩ := source (Finset.mem_filter.mp hu).1
      obtain ⟨hvp, hv3, _⟩ := source (Finset.mem_filter.mp hv).1
      exact normalizedSquareSum_injective hup hu3 hvp hv3 heq
    rw [hcard_img]
    exact (Finset.card_le_card himg_sub).trans (by simp)
  have hlower := squareSources_count_le_normalized_count ho
  change 2 * (squareSources N).card ≤
    (∑ u ∈ squareSources N, cardFactors (normalizedSquareSum u)) + A.card at hlower
  have h2bound : 2 * (N.primeFactors.card - 2) ≤ 1 + N.factorization q := by omega
  have hq_ge13 : 13 ≤ N.factorization q := by omega
  exact ⟨hcover, hq_mod3, h2bound, hq_ge13⟩

/-! ## 3. Finiteness Under Bounded Non-Square Exponent Budget -/

/-- For every `E : ℕ`, the set of odd perfect numbers whose non-square exponent budget
`N.factorization q + N.factorization 3 + ∑ r ∈ largeSources N q, N.factorization r`
is at most `E` is finite. -/
theorem finite_of_bounded_nonSquare_exponents (E : ℕ) :
    Set.Finite {N : ℕ | Odd N ∧ N.Perfect ∧ ∃ q ∈ N.primeFactors, q % 4 = 1 ∧
      N.factorization q % 4 = 1 ∧ (∀ r, r ≠ q → Even (N.factorization r)) ∧
      N.factorization q + N.factorization 3 + (∑ r ∈ largeSources N q, N.factorization r) ≤ E} := by
  apply (dickson_finite ((8 * E + 39) / 5)).subset
  rintro N ⟨ho, hN, q, hq, hq4, he, hev, hbudget⟩
  refine ⟨ho, hN, ?_⟩
  let S := (N.primeFactors.erase q).erase 3
  have hpos {r : ℕ} (hr : r ∈ N.primeFactors) : 0 < N.factorization r :=
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr)
  have hparts : S = squareSources N ∪ largeSources N q := by
    ext r
    simp only [S, Finset.mem_erase, squareSources, largeSources, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hr3, hrq, hr⟩
      obtain ⟨k, hk⟩ := hev r hrq
      have := hpos hr
      by_cases htwo : N.factorization r = 2
      · exact Or.inl ⟨hr, hr3, htwo⟩
      · exact Or.inr ⟨hr, hr3, hrq, by omega⟩
    · rintro (⟨hr, hr3, htwo⟩ | ⟨hr, hr3, hrq, _⟩)
      · exact ⟨hr3, fun h => by subst r; omega, hr⟩
      · exact ⟨hr3, hrq, hr⟩
  have hdis : Disjoint (squareSources N) (largeSources N q) := by
    apply Finset.disjoint_left.mpr
    intro r hs hl
    have htwo := (Finset.mem_filter.mp hs).2.2
    have hlarge := (Finset.mem_filter.mp hl).2.2.2
    omega
  have hsum_S : (∑ r ∈ S, N.factorization r) =
      2 * (squareSources N).card + ∑ r ∈ largeSources N q, N.factorization r := by
    rw [hparts, Finset.sum_union hdis]
    congr 1
    calc
      _ = ∑ _r ∈ squareSources N, (2 : ℕ) :=
        Finset.sum_congr rfl fun _ hr => (Finset.mem_filter.mp hr).2.2
      _ = _ := by simp [Nat.mul_comm]
  have htot : N.primeFactorsList.length =
      N.factorization q + ∑ r ∈ N.primeFactors.erase q, N.factorization r := by
    rw [← cardFactors_apply, cardFactors_eq_sum_factorization]
    exact (Finset.add_sum_erase N.primeFactors _ hq).symm
  have hlen_eq : N.primeFactorsList.length =
      N.factorization q + N.factorization 3 + 2 * (squareSources N).card +
        ∑ r ∈ largeSources N q, N.factorization r := by
    by_cases h3 : 3 ∈ N.primeFactors
    · have h3q : 3 ≠ q := by omega
      have h3mem := Finset.mem_erase.mpr ⟨h3q, h3⟩
      have h3sum : N.factorization 3 + (∑ r ∈ S, N.factorization r) =
          ∑ r ∈ N.primeFactors.erase q, N.factorization r :=
        Finset.add_sum_erase _ _ h3mem
      omega
    · have h3zero : N.factorization 3 = 0 := Finsupp.notMem_support_iff.mp h3
      have h3erase : S = N.primeFactors.erase q :=
        Finset.erase_eq_of_notMem fun h => h3 (Finset.mem_of_mem_erase h)
      rw [← h3erase] at htot
      omega
  have hsq_le : (squareSources N).card ≤ N.primeFactors.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hslope := cyclotomic_prime_factor_count ho hN
  have hfive : 5 * N.primeFactors.card ≤ 8 * E + 39 := by omega
  exact (Nat.le_div_iff_mul_le (by decide : 0 < 5)).2 (by linarith)

end OddPerfect
