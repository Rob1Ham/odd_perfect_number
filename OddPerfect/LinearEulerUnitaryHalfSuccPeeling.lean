module

public import OddPerfect.LinearEulerCycleDecay
public import OddPerfect.LinearEulerSquareDescent
public import OddPerfect.GlobalObstruction
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Linear Euler Unitary Half-Successor Peeling

Eliminates the trivial half-successor escape hatch in `linear_euler_collision_or_half_succ_hit`
on any linear Euler odd perfect number `N = q * m ^ 2` by splitting on
`Nat.Coprime ((q + 1) / 2) (componentIndex N q)`:

1. `linear_euler_half_succ_not_coprime_index_forces_euler_collision`:
   If `¬ Nat.Coprime ((q + 1) / 2) (componentIndex N q)`, any prime `s` dividing their gcd
   is an odd prime in `m.primeFactors` dividing `σ(ordProj[q] N) = q + 1`, `componentIndex N q`,
   `σ(m ^ 2)`, and `σ(ordProj[p] (m ^ 2))` for some `p ∈ m.primeFactors` with `p ≠ s`, `p ≠ q`.
2. `linear_euler_coprime_half_succ_index_square_split`:
   If `Nat.Coprime ((q + 1) / 2) (componentIndex N q)`, then `(q + 1) / 2 = h ^ 2` and
   `componentIndex N q = u ^ 2` are coprime odd squares with `m = h * u`, `3 ≤ h`, `1 < u`,
   `q = 2 * h ^ 2 - 1`, `q % 8 = 1`, `17 ≤ q`, and `¬ 3 ∣ N → q % 24 = 1 ∧ 7 ≤ h ∧ 97 ≤ q`.
3. `linear_euler_coprime_half_succ_pure_square_balance` and
   `linear_euler_coprime_half_succ_forces_square_collision`:
   Canceling `h ^ 2` yields the pure-square unitary balance
   `(c₀ * σ(h ^ 2)) * σ(B_pure) = r₀ ^ (2 * e₀) * B_pure`, and a Finset pigeonhole +
   Ljunggren (`sigma_prime_pow_isSquare_iff_of_even`) + `five_le_distinct_prime_factor_count`
   argument forces a nontrivial odd-prime `σ`-collision between two distinct prime components
   `p₁ ≠ p₂ ∈ m.primeFactors`.
4. `linear_euler_unconditional_nontrivial_sigma_collision`:
   Global synthesis combining (1), (2), and (3) for every linear Euler odd perfect number.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma componentIndex_linear_euler_eq {N q m : ℕ}
    (ho : Odd N) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2) :
    ordProj[q] N = q ∧
    ordCompl[q] N = m ^ 2 ∧
    componentIndex N q = sigma 1 (m ^ 2) / q := by
  have hm_odd : Odd m :=
    ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hq_ndvd_m2 : ¬ q ∣ m ^ 2 := fun h => hqm (hq.dvd_of_dvd_pow h)
  have hfact_q : N.factorization q = 1 := by
    rw [hform, Nat.factorization_mul hq.ne_zero hm20, Finsupp.add_apply,
      hq.factorization_self, Nat.factorization_eq_zero_of_not_dvd hq_ndvd_m2, add_zero]
  have hord : ordProj[q] N = q := by
    rw [hfact_q, pow_one]
  have hcompl : ordCompl[q] N = m ^ 2 := by
    rw [hfact_q, pow_one, hform, Nat.mul_div_cancel_left _ hq.pos]
  have hci : componentIndex N q = sigma 1 (m ^ 2) / q := by
    rw [componentIndex, hcompl, hord]
  exact ⟨hord, hcompl, hci⟩

private lemma ordProj_sq_eq_pow {m p : ℕ} (hm0 : m ≠ 0) :
    ordProj[p] (m ^ 2) = p ^ (2 * m.factorization p) := by
  rw [pow_two, Nat.factorization_mul hm0 hm0, Finsupp.add_apply, ← two_mul]

private lemma isSquare_of_coprime_mul_eq_sq {a b m : ℕ}
    (hm0 : m ≠ 0) (hcop : Nat.Coprime a b) (hmul : a * b = m ^ 2) :
    IsSquare a ∧ IsSquare b := by
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmul
    exact pow_ne_zero 2 hm0 hmul.symm
  have hb0 : b ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmul
    exact pow_ne_zero 2 hm0 hmul.symm
  have h_even_both : ∀ p : ℕ, p.Prime → Even (a.factorization p) ∧ Even (b.factorization p) := by
    intro p hp
    have hfact : a.factorization p + b.factorization p = 2 * m.factorization p := by
      calc
        a.factorization p + b.factorization p
            = (a * b).factorization p := by rw [Nat.factorization_mul ha0 hb0, Finsupp.add_apply]
        _ = (m ^ 2).factorization p := by rw [hmul]
        _ = 2 * m.factorization p := by
            rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    by_cases hpa : p ∣ a
    · have hpb : ¬ p ∣ b := fun hpb => hp.not_dvd_one (hcop ▸ Nat.dvd_gcd hpa hpb)
      have hb_zero : b.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpb
      rw [hb_zero] at hfact ⊢
      exact ⟨⟨m.factorization p, by omega⟩, ⟨0, rfl⟩⟩
    · have ha_zero : a.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpa
      rw [ha_zero] at hfact ⊢
      exact ⟨⟨0, rfl⟩, ⟨m.factorization p, by omega⟩⟩
  exact ⟨(Nat.isSquare_iff_even_factorization).mpr fun p hp => (h_even_both p hp).1,
    (Nat.isSquare_iff_even_factorization).mpr fun p hp => (h_even_both p hp).2⟩

/-- **1. Non-Coprime Half-Successor & Index Forces an Euler-to-Square Collision**:
If `¬ Nat.Coprime ((q + 1) / 2) (componentIndex N q)`, any prime `s` dividing their gcd is an
odd prime in `m.primeFactors` (`s ≠ q`) yielding a simultaneous `σ`-collision between the Euler
component `q` (`s ∣ σ(ordProj[q] N) = q + 1`) and a distinct square component `p ∈ m.primeFactors`
(`p ≠ s`, `p ≠ q`, `s ∣ σ(ordProj[p] (m ^ 2))`). -/
theorem linear_euler_half_succ_not_coprime_index_forces_euler_collision {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hncop : ¬ Nat.Coprime ((q + 1) / 2) (componentIndex N q)) :
    ∃ s ∈ m.primeFactors, ∃ p ∈ m.primeFactors,
      s.Prime ∧ Odd s ∧ s ≠ q ∧ p ≠ s ∧ p ≠ q ∧
      s ∣ (q + 1) / 2 ∧
      2 * s ∣ q + 1 ∧
      s ∣ sigma 1 (ordProj[q] N) ∧
      s ∣ componentIndex N q ∧
      s ∣ sigma 1 (m ^ 2) ∧
      s ∣ sigma 1 (ordProj[p] (m ^ 2)) := by
  have hq_odd : Odd q := ho.of_dvd_nat (hform ▸ dvd_mul_right q (m ^ 2))
  have hm_odd : Odd m :=
    ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  obtain ⟨hord_q, _, hci_eq⟩ := componentIndex_linear_euler_eq ho hq hqm hform
  obtain ⟨h_half_mul, _, _⟩ := linear_euler_half_succ_mul_index_and_deficient_square ho hN hq hqm hform
  rw [← hci_eq] at h_half_mul
  have hg_ne1 : Nat.gcd ((q + 1) / 2) (componentIndex N q) ≠ 1 := hncop
  obtain ⟨s, hs_prime, hs_gcd⟩ := Nat.exists_prime_and_dvd hg_ne1
  have hs_half : s ∣ (q + 1) / 2 := hs_gcd.trans (Nat.gcd_dvd_left _ _)
  have hs_ci : s ∣ componentIndex N q := hs_gcd.trans (Nat.gcd_dvd_right _ _)
  have hs_m2 : s ∣ m ^ 2 := h_half_mul ▸ hs_half.trans (dvd_mul_right _ _)
  have hs_m : s ∣ m := hs_prime.dvd_of_dvd_pow hs_m2
  have hs_mem : s ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hs_prime, hs_m, hm0⟩
  have hs_odd : Odd s := hm_odd.of_dvd_nat hs_m
  have hs_ne_q : s ≠ q := fun h => hqm (h ▸ hs_m)
  have hq1_even : q + 1 = 2 * ((q + 1) / 2) := by
    have := Nat.odd_iff.mp hq_odd
    omega
  have hs_2_q1 : 2 * s ∣ q + 1 := by
    rw [hq1_even]
    exact Nat.mul_dvd_mul_left 2 hs_half
  have hsig_q0 : sigma 1 q = q + 1 := by
    rw [← pow_one q, sigma_one_apply_prime_pow hq]
    simp [Finset.sum_range_succ]
    ring
  have hsig_q : sigma 1 (ordProj[q] N) = q + 1 := by
    rw [hord_q, hsig_q0]
  have hs_sig_q : s ∣ sigma 1 (ordProj[q] N) := by
    rw [hsig_q]
    exact (dvd_mul_left s 2).trans hs_2_q1
  have hq_cop_m2 : q.Coprime (m ^ 2) := (hq.coprime_iff_not_dvd.mpr hqm).pow_right 2
  have hsig_N : sigma 1 N = 2 * N :=
    (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul ho.pos).mp hN)
  have hq_dvd_sigm2 : q ∣ sigma 1 (m ^ 2) := by
    have hsig_bal : (q + 1) * sigma 1 (m ^ 2) = 2 * (q * m ^ 2) := by
      calc
        (q + 1) * sigma 1 (m ^ 2)
            = sigma 1 q * sigma 1 (m ^ 2) := by rw [hsig_q0]
        _ = sigma 1 (q * m ^ 2) := (isMultiplicative_sigma.map_mul_of_coprime hq_cop_m2).symm
        _ = sigma 1 N := by rw [← hform]
        _ = 2 * N := hsig_N
        _ = 2 * (q * m ^ 2) := by rw [hform]
    have hq_cop_q1 : q.Coprime (q + 1) :=
      hq.coprime_iff_not_dvd.mpr (fun hd => hq.not_dvd_one ((Nat.dvd_add_right (dvd_refl q)).mp hd))
    exact hq_cop_q1.dvd_of_dvd_mul_left ⟨2 * m ^ 2, by rw [hsig_bal]; ring⟩
  have hsigm2_eq : sigma 1 (m ^ 2) = q * componentIndex N q := by
    rw [hci_eq]
    exact (Nat.mul_div_cancel' hq_dvd_sigm2).symm
  have hs_sig_m2 : s ∣ sigma 1 (m ^ 2) := by
    rw [hsigm2_eq]
    exact hs_ci.trans (dvd_mul_left _ _)
  have hsigm2_prod : sigma 1 (m ^ 2) = ∏ p ∈ m.primeFactors, sigma 1 (ordProj[p] (m ^ 2)) := by
    rw [isMultiplicative_sigma.multiplicative_factorization (sigma 1) hm20]
    exact Finset.prod_congr
      ((m ^ 2).support_factorization.trans (Nat.primeFactors_pow m (by decide : 2 ≠ 0)))
      fun _ _ => rfl
  obtain ⟨p, hp_mem, hs_dvd_p⟩ := by
    rw [hsigm2_prod] at hs_sig_m2
    exact (hs_prime.prime.dvd_finsetProd_iff _).mp hs_sig_m2
  have hp_ne_s : p ≠ s := by
    intro hps
    subst hps
    rw [ordProj_sq_eq_pow hm0, Nat.dvd_iff_mod_eq_zero, sigma_prime_pow_mod_self hs_prime] at hs_dvd_p
    have := hs_prime.two_le
    omega
  have hp_ne_q : p ≠ q := fun h => hqm (h ▸ Nat.dvd_of_mem_primeFactors hp_mem)
  exact ⟨s, hs_mem, p, hp_mem, hs_prime, hs_odd, hs_ne_q, hp_ne_s, hp_ne_q,
    hs_half, hs_2_q1, hs_sig_q, hs_ci, hs_sig_m2, hs_dvd_p⟩

/-- **2. Coprime Half-Successor & Index Square Split and Congruences**:
When `Nat.Coprime ((q + 1) / 2) (componentIndex N q)`, both `(q + 1) / 2 = h ^ 2` and
`componentIndex N q = u ^ 2` are coprime odd squares with `m = h * u`, `3 ≤ h`, `1 < u`,
`q = 2 * h ^ 2 - 1`, `q % 8 = 1`, `17 ≤ q`, and `¬ 3 ∣ N → q % 24 = 1 ∧ 7 ≤ h ∧ 97 ≤ q`. -/
theorem linear_euler_coprime_half_succ_index_square_split {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hcop : Nat.Coprime ((q + 1) / 2) (componentIndex N q)) :
    (∃ h u : ℕ,
      Odd h ∧ 3 ≤ h ∧ Odd u ∧ 1 < u ∧ Nat.Coprime h u ∧
      m = h * u ∧
      (q + 1) / 2 = h ^ 2 ∧
      q = 2 * h ^ 2 - 1 ∧
      componentIndex N q = u ^ 2 ∧
      sigma 1 (m ^ 2) = q * u ^ 2 ∧
      (¬ 3 ∣ N → 7 ≤ h)) ∧
    q % 8 = 1 ∧
    17 ≤ q ∧
    (¬ 3 ∣ N → q % 24 = 1 ∧ 97 ≤ q) := by
  have hq_odd : Odd q := ho.of_dvd_nat (hform ▸ dvd_mul_right q (m ^ 2))
  have hm_odd : Odd m :=
    ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  obtain ⟨_, _, hci_eq⟩ := componentIndex_linear_euler_eq ho hq hqm hform
  obtain ⟨h_half_mul, _, _⟩ := linear_euler_half_succ_mul_index_and_deficient_square ho hN hq hqm hform
  rw [← hci_eq] at h_half_mul
  obtain ⟨⟨h, hh_sq⟩, ⟨u, hu_sq⟩⟩ := isSquare_of_coprime_mul_eq_sq hm0 hcop h_half_mul
  have hhalf_eq : (q + 1) / 2 = h ^ 2 := by rw [hh_sq, pow_two]
  have hci_sq_eq : componentIndex N q = u ^ 2 := by rw [hu_sq, pow_two]
  have hm_sq_eq : (h * u) ^ 2 = m ^ 2 := by
    calc
      (h * u) ^ 2 = h ^ 2 * u ^ 2 := by ring
      _ = ((q + 1) / 2) * componentIndex N q := by rw [hhalf_eq, hci_sq_eq]
      _ = m ^ 2 := h_half_mul
  have hm_eq : m = h * u := (Nat.pow_left_injective (by decide : 2 ≠ 0) hm_sq_eq).symm
  have hh_odd : Odd h := hm_odd.of_dvd_nat ⟨u, hm_eq⟩
  have hu_odd : Odd u := hm_odd.of_dvd_nat ⟨h, by rw [hm_eq, mul_comm]⟩
  have hcop_hu : Nat.Coprime h u := by
    have h1 : Nat.Coprime (h ^ 2) (u ^ 2) := by rwa [← hhalf_eq, ← hci_sq_eq]
    exact (Nat.coprime_pow_left_iff (by decide : 0 < 2) h _).mp
      ((Nat.coprime_pow_right_iff (by decide : 0 < 2) _ u).mp h1)
  have hq_ge3 : 3 ≤ q := by
    have := hq.two_le
    obtain ⟨k, hk⟩ := hq_odd
    omega
  have hhalf_ge2 : 2 ≤ (q + 1) / 2 := by omega
  have hh_ge3 : 3 ≤ h := by
    have hh_ne0 : h ≠ 0 := hh_odd.pos.ne'
    have hh_ne1 : h ≠ 1 := by
      intro h1
      rw [h1, one_pow] at hhalf_eq
      omega
    obtain ⟨k, hk⟩ := hh_odd
    omega
  obtain ⟨r₀, hr₀_m, _, _, _, hr₀_dvd_iq, _, _, _⟩ :=
    linear_euler_unique_source_dvd_sigma_B_and_index ho hN hq hqm hform
  rw [← hci_eq, hci_sq_eq] at hr₀_dvd_iq
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀_m
  have hr₀_dvd_u : r₀ ∣ u := hr₀_prime.dvd_of_dvd_pow hr₀_dvd_iq
  have hu_gt1 : 1 < u := by
    have hu_pos : 0 < u := hu_odd.pos
    have hle := Nat.le_of_dvd hu_pos hr₀_dvd_u
    have := hr₀_prime.two_le
    omega
  have hq1_even : q + 1 = 2 * ((q + 1) / 2) := by
    have := Nat.odd_iff.mp hq_odd
    omega
  have hq_eq : q = 2 * h ^ 2 - 1 := by
    have h2 : q + 1 = 2 * h ^ 2 := by rw [hq1_even, hhalf_eq]
    omega
  have hsigm2_eq : sigma 1 (m ^ 2) = q * u ^ 2 := by
    obtain ⟨_, _, _, _, hiq_eq, _, _, _, _⟩ := linear_euler_cofactor_quotient_structure ho hN hq hqm hform
    have hq_dvd : q ∣ sigma 1 (m ^ 2) := by
      have h_iq_ci : sigma 1 (m ^ 2) / q = componentIndex N q := hci_eq.symm
      obtain ⟨h_half_mul', _, _⟩ :=
        linear_euler_half_succ_mul_index_and_deficient_square ho hN hq hqm hform
      have hsig_N : sigma 1 N = 2 * N :=
        (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul ho.pos).mp hN)
      have hq_cop_m2 : q.Coprime (m ^ 2) := (hq.coprime_iff_not_dvd.mpr hqm).pow_right 2
      have hsig_q : sigma 1 q = q + 1 := by
        rw [← pow_one q, sigma_one_apply_prime_pow hq]
        simp [Finset.sum_range_succ]
        ring
      have hsig_bal : (q + 1) * sigma 1 (m ^ 2) = 2 * (q * m ^ 2) := by
        calc
          (q + 1) * sigma 1 (m ^ 2) = sigma 1 q * sigma 1 (m ^ 2) := by rw [hsig_q]
          _ = sigma 1 (q * m ^ 2) := (isMultiplicative_sigma.map_mul_of_coprime hq_cop_m2).symm
          _ = sigma 1 N := by rw [← hform]
          _ = 2 * N := hsig_N
          _ = 2 * (q * m ^ 2) := by rw [hform]
      have hq_cop_q1 : q.Coprime (q + 1) :=
        hq.coprime_iff_not_dvd.mpr (fun hd => hq.not_dvd_one ((Nat.dvd_add_right (dvd_refl q)).mp hd))
      exact hq_cop_q1.dvd_of_dvd_mul_left ⟨2 * m ^ 2, by rw [hsig_bal]; ring⟩
    rw [← hci_sq_eq, hci_eq]
    exact (Nat.mul_div_cancel' hq_dvd).symm
  have hh2_mod8 : h ^ 2 % 8 = 1 := by
    obtain ⟨k, rfl⟩ := hh_odd
    have hk2 : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
    have hkeven : 2 ∣ k * (k + 1) := by
      rcases Nat.even_or_odd k with ⟨t, ht⟩ | ⟨t, ht⟩
      · exact ⟨t * (k + 1), by rw [ht]; ring⟩
      · exact ⟨k * (t + 1), by rw [ht]; ring⟩
    obtain ⟨t, ht⟩ := hkeven
    rw [hk2, ht]
    omega
  have hq_mod8 : q % 8 = 1 := by
    have h8 : h ^ 2 = 8 * (h ^ 2 / 8) + 1 := by omega
    rw [hq_eq, h8]
    omega
  have hq_ge17 : 17 ≤ q := by
    have hh2_ge9 : 9 ≤ h ^ 2 := by nlinarith
    omega
  have h3_branch : ¬ 3 ∣ N → q % 24 = 1 ∧ 7 ≤ h ∧ 97 ≤ q := by
    intro h3N
    have h3h : ¬ 3 ∣ h := by
      intro hd
      apply h3N
      rw [hform, hm_eq]
      exact hd.trans ((dvd_mul_right h u).trans ((dvd_pow_self (h * u) (by decide : 2 ≠ 0)).trans (dvd_mul_left ((h * u) ^ 2) q)))
    have hh_ne3 : h ≠ 3 := fun h3 => h3h (by rw [h3])
    have hh_ge5 : 5 ≤ h := by
      obtain ⟨k, hk⟩ := hh_odd
      omega
    have hh_ne5 : h ≠ 5 := by
      intro h5
      rw [h5] at hq_eq
      have hq49 : q = 49 := by omega
      rw [hq49] at hq
      exact absurd hq (by decide)
    have hh_ge7 : 7 ≤ h := by
      obtain ⟨k, hk⟩ := hh_odd
      omega
    have hq_ge97 : 97 ≤ q := by
      have hh2_ge49 : 49 ≤ h ^ 2 := by nlinarith
      omega
    have hh2_mod3 : h ^ 2 % 3 = 1 := by
      have hmod3 : h % 3 = 1 ∨ h % 3 = 2 := by
        have hnz : h % 3 ≠ 0 := fun h0 => h3h (Nat.dvd_of_mod_eq_zero h0)
        omega
      rcases hmod3 with h1 | h2
      · rw [pow_two, Nat.mul_mod, h1]
      · rw [pow_two, Nat.mul_mod, h2]
    have hh2_mod24 : h ^ 2 % 24 = 1 := by omega
    have hq_mod24 : q % 24 = 1 := by
      have h24 : h ^ 2 = 24 * (h ^ 2 / 24) + 1 := by omega
      rw [hq_eq, h24]
      omega
    exact ⟨hq_mod24, hh_ge7, hq_ge97⟩
  exact ⟨⟨h, u, hh_odd, hh_ge3, hu_odd, hu_gt1, hcop_hu, hm_eq, hhalf_eq, hq_eq,
    hci_sq_eq, hsigm2_eq, fun h3N => (h3_branch h3N).2.1⟩,
    hq_mod8, hq_ge17, fun h3N => ⟨(h3_branch h3N).1, (h3_branch h3N).2.2⟩⟩

/-- **3a. Pure-Square Unitary Balance**:
Under `Nat.Coprime ((q + 1) / 2) (componentIndex N q)`, the unique `q`-source `r₀` divides `u`
(so `¬ r₀ ∣ h`), `ordCompl[r₀] (m ^ 2) = h ^ 2 * B_pure` for `B_pure := ordCompl[r₀] (u ^ 2)`,
and canceling `h ^ 2 > 0` yields `(c₀ * sigma 1 (h ^ 2)) * sigma 1 B_pure = r₀ ^ (2 * e₀) * B_pure`. -/
theorem linear_euler_coprime_half_succ_pure_square_balance {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hcop : Nat.Coprime ((q + 1) / 2) (componentIndex N q)) :
    ∃ h u r₀ : ℕ,
      Odd h ∧ 3 ≤ h ∧ Odd u ∧ 1 < u ∧ Nat.Coprime h u ∧
      m = h * u ∧ (q + 1) / 2 = h ^ 2 ∧ componentIndex N q = u ^ 2 ∧
      r₀ ∈ m.primeFactors ∧ r₀ ∈ u.primeFactors ∧ ¬ r₀ ∣ h ∧
      let e₀ := m.factorization r₀
      let c₀ := sigma 1 (r₀ ^ (2 * e₀)) / q
      let B_pure := ordCompl[r₀] (u ^ 2)
      q ∣ sigma 1 (r₀ ^ (2 * e₀)) ∧
      u.factorization r₀ = e₀ ∧
      u ^ 2 = r₀ ^ (2 * e₀) * B_pure ∧
      ordCompl[r₀] (m ^ 2) = h ^ 2 * B_pure ∧
      Nat.Coprime (h ^ 2) B_pure ∧
      (c₀ * sigma 1 (h ^ 2)) * sigma 1 B_pure = r₀ ^ (2 * e₀) * B_pure := by
  have hq_odd : Odd q := ho.of_dvd_nat (hform ▸ dvd_mul_right q (m ^ 2))
  have hm_odd : Odd m :=
    ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  obtain ⟨_, _, hci_eq⟩ := componentIndex_linear_euler_eq ho hq hqm hform
  obtain ⟨⟨h, u, hh_odd, hh_ge3, hu_odd, hu_gt1, hcop_hu, hm_eq, hhalf_eq, _,
    hci_sq_eq, _, _⟩, _, _, _⟩ :=
    linear_euler_coprime_half_succ_index_square_split ho hN hq hqm hform hcop
  obtain ⟨r₀, hr₀_m, hq_dvd, _, _, hr₀_dvd_iq, _, _, _⟩ :=
    linear_euler_unique_source_dvd_sigma_B_and_index ho hN hq hqm hform
  rw [← hci_eq, hci_sq_eq] at hr₀_dvd_iq
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀_m
  have hr₀_dvd_u : r₀ ∣ u := hr₀_prime.dvd_of_dvd_pow hr₀_dvd_iq
  have hu0 : u ≠ 0 := hu_odd.pos.ne'
  have hr₀_u : r₀ ∈ u.primeFactors := Nat.mem_primeFactors.mpr ⟨hr₀_prime, hr₀_dvd_u, hu0⟩
  have hr₀_ndvd_h : ¬ r₀ ∣ h := fun hd =>
    hr₀_prime.not_dvd_one (hcop_hu ▸ Nat.dvd_gcd hd hr₀_dvd_u)
  have hh0 : h ≠ 0 := hh_odd.pos.ne'
  have hu_fact : u.factorization r₀ = m.factorization r₀ := by
    rw [hm_eq, Nat.factorization_mul hh0 hu0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hr₀_ndvd_h, zero_add]
  let e₀ := m.factorization r₀
  let c₀ := sigma 1 (r₀ ^ (2 * e₀)) / q
  let B_pure := ordCompl[r₀] (u ^ 2)
  have hu2_split : u ^ 2 = r₀ ^ (2 * e₀) * B_pure := by
    have hord_u : ordProj[r₀] (u ^ 2) = r₀ ^ (2 * e₀) := by
      rw [ordProj_sq_eq_pow hu0, hu_fact]
    rw [← hord_u]
    exact (Nat.ordProj_mul_ordCompl_eq_self (u ^ 2) r₀).symm
  have hord_m2 : ordProj[r₀] (m ^ 2) = r₀ ^ (2 * e₀) := ordProj_sq_eq_pow hm0
  have hcompl_m2 : ordCompl[r₀] (m ^ 2) = h ^ 2 * B_pure := by
    have hfact_m2 : (m ^ 2).factorization r₀ = 2 * e₀ := by
      dsimp [e₀]
      rw [pow_two, Nat.factorization_mul hm0 hm0, Finsupp.add_apply, ← two_mul]
    rw [hfact_m2, hm_eq, mul_pow, hu2_split,
      show h ^ 2 * (r₀ ^ (2 * e₀) * B_pure) = r₀ ^ (2 * e₀) * (h ^ 2 * B_pure) by ring,
      Nat.mul_div_cancel_left _ (pow_pos hr₀_prime.pos _)]
  have hcop_h2_Bpure : Nat.Coprime (h ^ 2) B_pure := by
    have hcop_h2_u2 : Nat.Coprime (h ^ 2) (u ^ 2) := (hcop_hu.pow_left 2).pow_right 2
    exact hcop_h2_u2.coprime_dvd_right (Nat.ordCompl_dvd (u ^ 2) r₀)
  obtain ⟨_, _, _, _, _, h_bal, _, _, _⟩ :=
    linear_euler_cofactor_quotient_structure_of_source ho hN hq hqm hform hr₀_m hq_dvd
  change (q + 1) * c₀ * sigma 1 (ordCompl[r₀] (m ^ 2)) =
    2 * r₀ ^ (2 * e₀) * ordCompl[r₀] (m ^ 2) at h_bal
  have hq1_even : q + 1 = 2 * ((q + 1) / 2) := by
    have := Nat.odd_iff.mp hq_odd
    omega
  have h_half_bal : (((q + 1) / 2) * c₀) * sigma 1 (ordCompl[r₀] (m ^ 2)) =
      r₀ ^ (2 * e₀) * ordCompl[r₀] (m ^ 2) := by
    apply Nat.mul_left_cancel (by decide : 0 < 2)
    calc
      2 * ((((q + 1) / 2) * c₀) * sigma 1 (ordCompl[r₀] (m ^ 2)))
          = (2 * ((q + 1) / 2)) * c₀ * sigma 1 (ordCompl[r₀] (m ^ 2)) := by ring
      _ = (q + 1) * c₀ * sigma 1 (ordCompl[r₀] (m ^ 2)) := by rw [← hq1_even]
      _ = 2 * r₀ ^ (2 * e₀) * ordCompl[r₀] (m ^ 2) := h_bal
      _ = 2 * (r₀ ^ (2 * e₀) * ordCompl[r₀] (m ^ 2)) := by ring
  have h_pure_bal : (c₀ * sigma 1 (h ^ 2)) * sigma 1 B_pure = r₀ ^ (2 * e₀) * B_pure := by
    rw [hhalf_eq, hcompl_m2, isMultiplicative_sigma.map_mul_of_coprime hcop_h2_Bpure] at h_half_bal
    apply Nat.mul_left_cancel (pow_pos hh_odd.pos 2)
    calc
      h ^ 2 * ((c₀ * sigma 1 (h ^ 2)) * sigma 1 B_pure)
          = (h ^ 2 * c₀) * (sigma 1 (h ^ 2) * sigma 1 B_pure) := by ring
      _ = r₀ ^ (2 * e₀) * (h ^ 2 * B_pure) := h_half_bal
      _ = h ^ 2 * (r₀ ^ (2 * e₀) * B_pure) := by ring
  exact ⟨h, u, r₀, hh_odd, hh_ge3, hu_odd, hu_gt1, hcop_hu, hm_eq, hhalf_eq, hci_sq_eq,
    hr₀_m, hr₀_u, hr₀_ndvd_h, hq_dvd, hu_fact, hu2_split, hcompl_m2, hcop_h2_Bpure, h_pure_bal⟩

/-- **3b. Coprime Half-Successor & Index Forces a Square-Component `σ`-Collision**:
When `Nat.Coprime ((q + 1) / 2) (componentIndex N q)`, there must exist an odd prime `r'` and
two distinct primes `p₁ ≠ p₂` in `m.primeFactors` such that `r' ∣ σ(ordProj[p₁] (m ^ 2))` and
`r' ∣ σ(ordProj[p₂] (m ^ 2))`. -/
theorem linear_euler_coprime_half_succ_forces_square_collision {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hcop : Nat.Coprime ((q + 1) / 2) (componentIndex N q)) :
    ∃ r' : ℕ, r'.Prime ∧ Odd r' ∧
      ∃ p₁ ∈ m.primeFactors, ∃ p₂ ∈ m.primeFactors,
        p₁ ≠ p₂ ∧
        r' ∣ sigma 1 (ordProj[p₁] (m ^ 2)) ∧
        r' ∣ sigma 1 (ordProj[p₂] (m ^ 2)) := by
  by_contra h_nocoll
  have hm_odd : Odd m :=
    ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  obtain ⟨_, _, hci_eq⟩ := componentIndex_linear_euler_eq ho hq hqm hform
  obtain ⟨⟨h, u, hh_odd, hh_ge3, hu_odd, _, hcop_hu, hm_eq, _, _, _, hsigm2_eq, _⟩, _, _, _⟩ :=
    linear_euler_coprime_half_succ_index_square_split ho hN hq hqm hform hcop
  have hh0 : h ≠ 0 := hh_odd.pos.ne'
  have hu0 : u ≠ 0 := hu_odd.pos.ne'
  have hu20 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu0
  obtain ⟨_, r₀, hr₀_m, hq_dvd_r0, _, _, _, huniq⟩ :=
    linear_euler_unique_q_source_and_bound ho hN hq hqm hform
  obtain ⟨_, _, hr₀_dvd_iq, _, _, _⟩ :=
    linear_euler_unique_source_dvd_sigma_B_and_index_of_source ho hN hq hqm hform hr₀_m hq_dvd_r0
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀_m
  have hr₀_dvd_u : r₀ ∣ u := by
    have h1 : r₀ ∣ sigma 1 (m ^ 2) / q := hr₀_dvd_iq
    rw [← hci_eq] at h1
    have h_ci_u2 : componentIndex N q = u ^ 2 := by
      have hsig_u2 : sigma 1 (m ^ 2) = q * u ^ 2 := hsigm2_eq
      rw [hci_eq, hsig_u2, Nat.mul_div_cancel_left _ hq.pos]
    rw [h_ci_u2] at h1
    exact hr₀_prime.dvd_of_dvd_pow h1
  have hr₀_u : r₀ ∈ u.primeFactors := Nat.mem_primeFactors.mpr ⟨hr₀_prime, hr₀_dvd_u, hu0⟩
  let S := m.primeFactors.erase r₀
  let F : ℕ → Finset ℕ := fun z => (sigma 1 (ordProj[z] (m ^ 2))).primeFactors
  have hm_pf_union : m.primeFactors = h.primeFactors ∪ u.primeFactors := by
    rw [hm_eq]
    exact Nat.primeFactors_mul hh0 hu0
  have hhu_disj : Disjoint h.primeFactors u.primeFactors := hcop_hu.disjoint_primeFactors
  have hm_pf_card : m.primeFactors.card = h.primeFactors.card + u.primeFactors.card := by
    rw [hm_pf_union]
    exact Finset.card_union_of_disjoint hhu_disj
  have hh_pf_pos : 1 ≤ h.primeFactors.card := by
    have hh_ne1 : h ≠ 1 := by omega
    obtain ⟨p, hp⟩ := Nat.exists_prime_and_dvd hh_ne1
    exact Finset.card_pos.mpr ⟨p, Nat.mem_primeFactors.mpr ⟨hp.1, hp.2, hh0⟩⟩
  have hS_card : S.card = m.primeFactors.card - 1 := Finset.card_erase_of_mem hr₀_m
  have hu_le_S : u.primeFactors.card ≤ S.card := by omega
  have hsigm2_prod : sigma 1 (m ^ 2) = ∏ p ∈ m.primeFactors, sigma 1 (ordProj[p] (m ^ 2)) := by
    rw [isMultiplicative_sigma.multiplicative_factorization (sigma 1) hm20]
    exact Finset.prod_congr
      ((m ^ 2).support_factorization.trans (Nat.primeFactors_pow m (by decide : 2 ≠ 0)))
      fun _ _ => rfl
  have hz_prop : ∀ z ∈ S,
      z.Prime ∧ 0 < m.factorization z ∧
      1 < sigma 1 (ordProj[z] (m ^ 2)) ∧
      sigma 1 (ordProj[z] (m ^ 2)) ∣ u ^ 2 ∧
      F z ⊆ u.primeFactors ∧
      1 ≤ (F z).card := by
    intro z hz
    have hz_m : z ∈ m.primeFactors := Finset.mem_of_mem_erase hz
    have hz_ne : z ≠ r₀ := Finset.ne_of_mem_erase hz
    have hz_prime : z.Prime := Nat.prime_of_mem_primeFactors hz_m
    have hz_pos : 0 < m.factorization z :=
      (hz_prime.dvd_iff_one_le_factorization hm0).mp (Nat.dvd_of_mem_primeFactors hz_m)
    have hord_z : ordProj[z] (m ^ 2) = z ^ (2 * m.factorization z) := ordProj_sq_eq_pow hm0
    have hord_gt1 : 1 < ordProj[z] (m ^ 2) := by
      rw [hord_z]
      exact Nat.one_lt_pow (by omega) hz_prime.one_lt
    have hsig_gt1 : 1 < sigma 1 (ordProj[z] (m ^ 2)) :=
      hord_gt1.trans (self_lt_sigma_of_one_lt hord_gt1)
    have hsig_dvd_m2 : sigma 1 (ordProj[z] (m ^ 2)) ∣ sigma 1 (m ^ 2) := by
      rw [hsigm2_prod]
      exact Finset.dvd_prod_of_mem _ hz_m
    have hq_ndvd_z : ¬ q ∣ sigma 1 (ordProj[z] (m ^ 2)) := by
      intro hqd
      rw [hord_z] at hqd
      exact hz_ne (huniq z hz_m hqd)
    have hq_cop_z : Nat.Coprime q (sigma 1 (ordProj[z] (m ^ 2))) :=
      hq.coprime_iff_not_dvd.mpr hq_ndvd_z
    have hsig_dvd_u2 : sigma 1 (ordProj[z] (m ^ 2)) ∣ u ^ 2 := by
      rw [hsigm2_eq] at hsig_dvd_m2
      exact hq_cop_z.symm.dvd_of_dvd_mul_left hsig_dvd_m2
    have hFz_sub : F z ⊆ u.primeFactors := by
      intro x hx
      have hx_prime := Nat.prime_of_mem_primeFactors hx
      have hx_dvd := (Nat.dvd_of_mem_primeFactors hx).trans hsig_dvd_u2
      exact Nat.mem_primeFactors.mpr ⟨hx_prime, hx_prime.dvd_of_dvd_pow hx_dvd, hu0⟩
    have hFz_pos : 1 ≤ (F z).card := by
      obtain ⟨x, hx⟩ := Nat.exists_prime_and_dvd hsig_gt1.ne'
      exact Finset.card_pos.mpr ⟨x, Nat.mem_primeFactors.mpr ⟨hx.1, hx.2, by omega⟩⟩
    exact ⟨hz_prime, hz_pos, hsig_gt1, hsig_dvd_u2, hFz_sub, hFz_pos⟩
  have hF_disj : (S : Set ℕ).PairwiseDisjoint F := by
    intro z₁ hz₁ z₂ hz₂ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro r' hr'₁ hr'₂
    have hr'_prime : r'.Prime := Nat.prime_of_mem_primeFactors hr'₁
    have hz₁_m : z₁ ∈ m.primeFactors := Finset.mem_of_mem_erase hz₁
    have hz₂_m : z₂ ∈ m.primeFactors := Finset.mem_of_mem_erase hz₂
    have hz₁_odd : Odd z₁ := hm_odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hz₁_m)
    have hord₁_odd : Odd (ordProj[z₁] (m ^ 2)) := by
      rw [ordProj_sq_eq_pow hm0]
      exact hz₁_odd.pow
    have hord₁_sq : IsSquare (ordProj[z₁] (m ^ 2)) := by
      rw [ordProj_sq_eq_pow hm0]
      exact ⟨z₁ ^ m.factorization z₁, by ring⟩
    have hsig₁_odd : Odd (sigma 1 (ordProj[z₁] (m ^ 2))) :=
      (odd_sigma_iff_square_of_odd hord₁_odd).mpr hord₁_sq
    have hr'_odd : Odd r' := hsig₁_odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr'₁)
    exact h_nocoll ⟨r', hr'_prime, hr'_odd, z₁, hz₁_m, z₂, hz₂_m, hne,
      Nat.dvd_of_mem_primeFactors hr'₁, Nat.dvd_of_mem_primeFactors hr'₂⟩
  let U := S.biUnion F
  have hU_sub : U ⊆ u.primeFactors := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨z, hz, hxz⟩
    exact (hz_prop z hz).2.2.2.2.1 hxz
  have hU_le : U.card ≤ u.primeFactors.card := Finset.card_le_card hU_sub
  have hU_eq : U.card = ∑ z ∈ S, (F z).card := Finset.card_biUnion hF_disj
  have hS_le_U : S.card ≤ U.card := by
    rw [hU_eq]
    calc
      S.card = ∑ _z ∈ S, 1 := by simp
      _ ≤ ∑ z ∈ S, (F z).card := Finset.sum_le_sum fun z hz => (hz_prop z hz).2.2.2.2.2
  have h_sum_eq : ∑ z ∈ S, (F z).card = ∑ _z ∈ S, 1 := by
    have h1 : ∑ z ∈ S, (F z).card ≤ ∑ _z ∈ S, 1 := by
      have : U.card ≤ S.card := hU_le.trans hu_le_S
      simpa [hU_eq] using this
    have h2 : ∑ _z ∈ S, 1 ≤ ∑ z ∈ S, (F z).card :=
      Finset.sum_le_sum fun z hz => (hz_prop z hz).2.2.2.2.2
    omega
  have hFz_card_one : ∀ z ∈ S, (F z).card = 1 := by
    intro z hz
    by_contra hne1
    have hge1 := (hz_prop z hz).2.2.2.2.2
    have hgt1 : 1 < (F z).card := by omega
    have hlt : ∑ _w ∈ S, 1 < ∑ w ∈ S, (F w).card := by
      refine Finset.sum_lt_sum (fun w hw => (hz_prop w hw).2.2.2.2.2) ⟨z, hz, hgt1⟩
    omega
  have hz_isSq : ∀ z ∈ S, z = 3 := by
    intro z hz
    obtain ⟨hz_prime, hz_pos, hsig_gt1, _, hFz_sub, _⟩ := hz_prop z hz
    obtain ⟨x, hx_eq⟩ := Finset.card_eq_one.mp (hFz_card_one z hz)
    have hx_mem : x ∈ F z := by rw [hx_eq]; exact Finset.mem_singleton_self x
    have hx_u : x ∈ u.primeFactors := hFz_sub hx_mem
    have hx_prime : x.Prime := Nat.prime_of_mem_primeFactors hx_u
    have hx_dvd_z : x ∣ sigma 1 (ordProj[z] (m ^ 2)) := Nat.dvd_of_mem_primeFactors hx_mem
    have hx_odd : Odd x := hu_odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hx_u)
    have hx_ndvd_other : ∀ p ∈ m.primeFactors, p ≠ z → ¬ x ∣ sigma 1 (ordProj[p] (m ^ 2)) := by
      intro p hp_m hp_ne hx_p
      exact h_nocoll ⟨x, hx_prime, hx_odd, z, Finset.mem_of_mem_erase hz, p, hp_m,
        hp_ne.symm, hx_dvd_z, hx_p⟩
    have hsig_other_fact :
        (∏ p ∈ m.primeFactors.erase z, sigma 1 (ordProj[p] (m ^ 2))).factorization x = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hdvd
      obtain ⟨p, hp_er, hx_p⟩ := (hx_prime.prime.dvd_finsetProd_iff _).mp hdvd
      exact hx_ndvd_other p (Finset.mem_of_mem_erase hp_er) (Finset.ne_of_mem_erase hp_er) hx_p
    have hprod_split :
        sigma 1 (m ^ 2) =
          sigma 1 (ordProj[z] (m ^ 2)) * ∏ p ∈ m.primeFactors.erase z, sigma 1 (ordProj[p] (m ^ 2)) := by
      rw [hsigm2_prod]
      exact (Finset.mul_prod_erase m.primeFactors _ (Finset.mem_of_mem_erase hz)).symm
    have hsigz_ne0 : sigma 1 (ordProj[z] (m ^ 2)) ≠ 0 := by omega
    have hprod_er_ne0 : (∏ p ∈ m.primeFactors.erase z, sigma 1 (ordProj[p] (m ^ 2))) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
      have hp_m : p ∈ m.primeFactors := Finset.mem_of_mem_erase hp
      have hp_prime := Nat.prime_of_mem_primeFactors hp_m
      exact (sigma_pos 1 _ (pow_ne_zero _ hp_prime.ne_zero)).ne'
    have hx_fact_eq : (sigma 1 (ordProj[z] (m ^ 2))).factorization x = 2 * u.factorization x := by
      have h1 : (sigma 1 (m ^ 2)).factorization x = (q * u ^ 2).factorization x := by
        rw [hsigm2_eq]
      rw [hprod_split, Nat.factorization_mul hsigz_ne0 hprod_er_ne0, Finsupp.add_apply,
        hsig_other_fact, add_zero] at h1
      have hx_ne_q : x ≠ q := fun hxq =>
        hqm (hxq ▸ (Nat.dvd_of_mem_primeFactors hx_u).trans ⟨h, by rw [hm_eq, mul_comm]⟩)
      have h2 : (q * u ^ 2).factorization x = 2 * u.factorization x := by
        have hx_ndvd_q : ¬ x ∣ q := fun hd =>
          hx_ne_q (((Nat.dvd_prime hq).mp hd).resolve_left hx_prime.ne_one)
        rw [Nat.factorization_mul hq.ne_zero hu20, Finsupp.add_apply,
          Nat.factorization_eq_zero_of_not_dvd hx_ndvd_q, zero_add,
          Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
      omega
    have hsigz_sq : IsSquare (sigma 1 (ordProj[z] (m ^ 2))) := by
      rw [Nat.isSquare_iff_even_factorization]
      intro r hr
      by_cases hrx : r = x
      · rw [hrx, hx_fact_eq]
        exact ⟨u.factorization x, by ring⟩
      · have hr_notin : r ∉ F z := by
          rw [hx_eq]
          simp [hrx]
        have hr_ndvd : ¬ r ∣ sigma 1 (ordProj[z] (m ^ 2)) := fun hd =>
          hr_notin (Nat.mem_primeFactors.mpr ⟨hr, hd, hsigz_ne0⟩)
        rw [Nat.factorization_eq_zero_of_not_dvd hr_ndvd]
        exact ⟨0, rfl⟩
    rw [ordProj_sq_eq_pow hm0] at hsigz_sq
    exact ((sigma_prime_pow_isSquare_iff_of_even hz_prime (by omega) ⟨m.factorization z, by ring⟩).mp hsigz_sq).1
  have hS_card_le1 : S.card ≤ 1 := by
    have hS_sub : S ⊆ ({3} : Finset ℕ) := fun z hz => Finset.mem_singleton.mpr (hz_isSq z hz)
    calc
      S.card ≤ ({3} : Finset ℕ).card := Finset.card_le_card hS_sub
      _ = 1 := Finset.card_singleton 3
  have hm_card_le2 : m.primeFactors.card ≤ 2 := by
    have := hS_card
    have hpos : 1 ≤ m.primeFactors.card := Finset.card_pos.mpr ⟨r₀, hr₀_m⟩
    omega
  have hN_pf_sub : N.primeFactors ⊆ insert q m.primeFactors := by
    rw [hform]
    intro p hp
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have hp_dvd := Nat.dvd_of_mem_primeFactors hp
    rcases hp_prime.dvd_mul.mp hp_dvd with hpq | hpm2
    · have heq : p = q := ((Nat.dvd_prime hq).mp hpq).resolve_left hp_prime.ne_one
      rw [heq]
      exact Finset.mem_insert_self q _
    · exact Finset.mem_insert_of_mem
        (Nat.mem_primeFactors.mpr ⟨hp_prime, hp_prime.dvd_of_dvd_pow hpm2, hm0⟩)
  have hN_card_le3 : N.primeFactors.card ≤ 3 := by
    calc
      N.primeFactors.card ≤ (insert q m.primeFactors).card := Finset.card_le_card hN_pf_sub
      _ ≤ m.primeFactors.card + 1 := Finset.card_insert_le q m.primeFactors
      _ ≤ 3 := by omega
  have hN_card_ge5 : 5 ≤ N.primeFactors.card := five_le_distinct_prime_factor_count ho hN
  omega

/-- **4. Unconditional Non-Trivial `σ`-Collision Dichotomy for Linear Euler Odd Perfect Numbers**:
Every linear Euler odd perfect number `N = q * m ^ 2` satisfies one of two non-vacuous structural
alternatives:
- Either `(q + 1) / 2` and `componentIndex N q` share an odd prime `s ∈ m.primeFactors` that
  simultaneously witnesses a `σ`-collision between the Euler component `q` (`s ∣ (q + 1) / 2`)
  and a distinct square component `p ∈ m.primeFactors` (`p ≠ s`, `s ∣ σ(ordProj[p] (m ^ 2))`);
- Or `Nat.Coprime ((q + 1) / 2) (componentIndex N q)`, forcing `(q + 1) / 2` and
  `componentIndex N q` to be coprime odd squares, `q % 8 = 1`, `¬ 3 ∣ N → q % 24 = 1 ∧ 97 ≤ q`,
  and an explicit odd-prime `σ`-collision between two distinct square components `p₁ ≠ p₂ ∈ m.primeFactors`. -/
theorem linear_euler_unconditional_nontrivial_sigma_collision {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2) :
    (∃ s ∈ m.primeFactors,
      s ∣ (q + 1) / 2 ∧
      s ∣ componentIndex N q ∧
      ∃ p ∈ m.primeFactors, p ≠ s ∧ s ∣ sigma 1 (ordProj[p] (m ^ 2))) ∨
    (Nat.Coprime ((q + 1) / 2) (componentIndex N q) ∧
      IsSquare ((q + 1) / 2) ∧
      IsSquare (componentIndex N q) ∧
      q % 8 = 1 ∧
      (¬ 3 ∣ N → q % 24 = 1 ∧ 97 ≤ q) ∧
      ∃ r' : ℕ, r'.Prime ∧
        ∃ p₁ ∈ m.primeFactors, ∃ p₂ ∈ m.primeFactors,
          p₁ ≠ p₂ ∧
          r' ∣ sigma 1 (ordProj[p₁] (m ^ 2)) ∧
          r' ∣ sigma 1 (ordProj[p₂] (m ^ 2))) := by
  by_cases hcop : Nat.Coprime ((q + 1) / 2) (componentIndex N q)
  · right
    obtain ⟨⟨h, u, _, _, _, _, _, _, hhalf_eq, _, hci_sq_eq, _, _⟩, hq_mod8, _, h3⟩ :=
      linear_euler_coprime_half_succ_index_square_split ho hN hq hqm hform hcop
    obtain ⟨r', hr', _, p₁, hp₁, p₂, hp₂, hp_ne, hd₁, hd₂⟩ :=
      linear_euler_coprime_half_succ_forces_square_collision ho hN hq hqm hform hcop
    exact ⟨hcop, ⟨h, by rw [hhalf_eq, pow_two]⟩, ⟨u, by rw [hci_sq_eq, pow_two]⟩,
      hq_mod8, h3, r', hr', p₁, hp₁, p₂, hp₂, hp_ne, hd₁, hd₂⟩
  · left
    obtain ⟨s, hs_m, p, hp_m, _, _, _, hp_ne_s, _, hs_half, _, _, hs_ci, _, hs_dvd_p⟩ :=
      linear_euler_half_succ_not_coprime_index_forces_euler_collision ho hN hq hqm hform hcop
    exact ⟨s, hs_m, hs_half, hs_ci, p, hp_m, hp_ne_s, hs_dvd_p⟩

end OddPerfect
