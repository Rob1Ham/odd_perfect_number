module

public import OddPerfect.LinearEulerUnitaryHalfSuccPeeling
public import OddPerfect.SixthPowerFreeHalfSuccPinch
import OddPerfect.PadicPadeQuadraticQuotient
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Linear Euler Coprime Half-Successor Quotient Obstruction

Deepens the analysis of the coprime half-successor branch
`Nat.Coprime ((q + 1) / 2) (componentIndex N q)` on linear Euler odd perfect numbers
`N = q * m ^ 2`, where `(q + 1) / 2 = h ^ 2`, `q = 2 * h ^ 2 - 1`,
`componentIndex N q = u ^ 2`, `m = h * u`, and `Nat.Coprime h u`:

1. `linear_euler_coprime_half_succ_unique_q_source_in_u`:
   Locates the unique `q`-source `r₀ ∈ u.primeFactors` (`¬ r₀ ∣ h`,
   `h < r₀ ^ (m.factorization r₀)`), proving `q ∣ σ(u ^ 2)`, `Nat.Coprime q (σ(h ^ 2))`,
   and `σ(h ^ 2) ∣ u ^ 2`.
2. `linear_euler_coprime_half_succ_quotient_system`:
   Introduces the odd cofactor quotient `W := σ(u ^ 2) / q`, establishing the coupled system
   `u ^ 2 = W * σ(h ^ 2)`, `σ(u ^ 2) = W * (2 * h ^ 2 - 1)`,
   `2 * u ^ 2 - σ(u ^ 2) = W * (2 * (σ(h ^ 2) - h ^ 2) + 1)`, `2 * h * W < 2 * u ^ 2 - σ(u ^ 2)`,
   and characterizes `W = 1` (`u = p ^ e`, `componentIndex N q = p ^ (2 * e)`,
   `2 ≤ h.primeFactors.card`).
3. `sixth_power_free_coprime_half_succ_quotient_bounds`:
   Specializes (2) to sixth-power-free odd perfect numbers, obtaining `59 ≤ h`, `6961 ≤ q`,
   `119 * W ≤ 2 * u ^ 2 - σ(u ^ 2)`, and eliminating `W = 1` via
   `even_prime_power_component_sharpened_pade_cap` (`128 ≤ e`, contradicting `¬ p ^ 6 ∣ N`)
   to prove `2 ≤ W` and hence `3 ≤ W`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma ordProj_sq_eq_pow_coprime {m p : ℕ} (hm0 : m ≠ 0) :
    ordProj[p] (m ^ 2) = p ^ (2 * m.factorization p) := by
  rw [pow_two, Nat.factorization_mul hm0 hm0, Finsupp.add_apply, ← two_mul]

/-- **1. Unique `q`-Source in `u` and Coprime Quotient Divisibility**:
In the coprime half-successor branch `Nat.Coprime ((q + 1) / 2) (componentIndex N q)` of a
linear Euler odd perfect number `N = q * m ^ 2`, the unique `q`-source `r₀ ∈ m.primeFactors`
must belong to `u.primeFactors` (`¬ r₀ ∣ h`, `h < r₀ ^ (m.factorization r₀)`), forcing
`q ∣ σ(u ^ 2)`, `Nat.Coprime q (σ(h ^ 2))`, and `σ(h ^ 2) ∣ u ^ 2`. -/
theorem linear_euler_coprime_half_succ_unique_q_source_in_u {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hcop : Nat.Coprime ((q + 1) / 2) (componentIndex N q)) :
    ∃ h u r₀ : ℕ,
      Odd h ∧ Odd u ∧ 3 ≤ h ∧ 3 ≤ u ∧ Nat.Coprime h u ∧
      m = h * u ∧
      (q + 1) / 2 = h ^ 2 ∧
      q = 2 * h ^ 2 - 1 ∧
      componentIndex N q = u ^ 2 ∧
      r₀ ∈ u.primeFactors ∧
      ¬ r₀ ∣ h ∧
      h < r₀ ^ (m.factorization r₀) ∧
      q ∣ sigma 1 (u ^ 2) ∧
      Nat.Coprime q (sigma 1 (h ^ 2)) ∧
      sigma 1 (h ^ 2) ∣ u ^ 2 := by
  have hm_odd : Odd m :=
    ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  obtain ⟨⟨h, u, hh_odd, hh_ge3, hu_odd, hu_gt1, hcop_hu, hm_eq, hhalf_eq, hq_eq,
    hci_sq_eq, hsigm2_eq, _⟩, _, _, _⟩ :=
    linear_euler_coprime_half_succ_index_square_split ho hN hq hqm hform hcop
  have hu_ge3 : 3 ≤ u := by
    obtain ⟨k, hk⟩ := hu_odd
    omega
  have hh0 : h ≠ 0 := hh_odd.pos.ne'
  have hu0 : u ≠ 0 := hu_odd.pos.ne'
  have hh20 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh0
  have hcop_h2_u2 : Nat.Coprime (h ^ 2) (u ^ 2) := (hcop_hu.pow_left 2).pow_right 2
  have hsig_split : sigma 1 (h ^ 2) * sigma 1 (u ^ 2) = q * u ^ 2 := by
    calc
      sigma 1 (h ^ 2) * sigma 1 (u ^ 2)
          = sigma 1 (h ^ 2 * u ^ 2) := (isMultiplicative_sigma.map_mul_of_coprime hcop_h2_u2).symm
      _ = sigma 1 (m ^ 2) := by rw [hm_eq, mul_pow]
      _ = q * u ^ 2 := hsigm2_eq
  obtain ⟨_, r₀, hr₀_m, hq_dvd_r₀, _, _, hbound_r₀, huniq_r₀⟩ :=
    linear_euler_unique_q_source_and_bound ho hN hq hqm hform
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀_m
  have hh_lt_r₀pow : h < r₀ ^ (m.factorization r₀) := by
    have hh2_ge9 : 9 ≤ h ^ 2 := by nlinarith
    have h2q : 2 * q = 4 * h ^ 2 - 2 := by omega
    have hpow_sq : r₀ ^ (2 * m.factorization r₀) = (r₀ ^ (m.factorization r₀)) ^ 2 := by
      rw [← pow_mul, mul_comm]
    rw [hpow_sq] at hbound_r₀
    have hsq_lt : h ^ 2 < (r₀ ^ (m.factorization r₀)) ^ 2 := by omega
    by_contra! hle
    have := Nat.pow_le_pow_left hle 2
    omega
  have hr₀_ndvd_h : ¬ r₀ ∣ h := by
    intro hdvd_h
    have hr₀_ndvd_u : ¬ r₀ ∣ u := fun hdvd_u =>
      hr₀_prime.not_dvd_one (hcop_hu ▸ Nat.dvd_gcd hdvd_h hdvd_u)
    have hm_fact : m.factorization r₀ = h.factorization r₀ := by
      rw [hm_eq, Nat.factorization_mul hh0 hu0, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hr₀_ndvd_u, add_zero]
    have hpow_dvd_h : r₀ ^ (m.factorization r₀) ∣ h := by
      rw [hm_fact]
      exact Nat.ordProj_dvd h r₀
    have hle : r₀ ^ (m.factorization r₀) ≤ h := Nat.le_of_dvd hh_odd.pos hpow_dvd_h
    omega
  have hr₀_u : r₀ ∈ u.primeFactors := by
    have hr₀_dvd_m : r₀ ∣ h * u := hm_eq ▸ Nat.dvd_of_mem_primeFactors hr₀_m
    have hr₀_dvd_u : r₀ ∣ u := (hr₀_prime.dvd_mul.mp hr₀_dvd_m).resolve_left hr₀_ndvd_h
    exact Nat.mem_primeFactors.mpr ⟨hr₀_prime, hr₀_dvd_u, hu0⟩
  have hsigh2_prod : sigma 1 (h ^ 2) = ∏ z ∈ h.primeFactors, sigma 1 (ordProj[z] (h ^ 2)) := by
    rw [isMultiplicative_sigma.multiplicative_factorization (sigma 1) hh20]
    exact Finset.prod_congr
      ((h ^ 2).support_factorization.trans (Nat.primeFactors_pow h (by decide : 2 ≠ 0)))
      fun _ _ => rfl
  have hq_ndvd_sigh2 : ¬ q ∣ sigma 1 (h ^ 2) := by
    intro hqd
    rw [hsigh2_prod] at hqd
    obtain ⟨z, hz_h, hqz⟩ := (hq.prime.dvd_finsetProd_iff _).mp hqd
    have hz_prime : z.Prime := Nat.prime_of_mem_primeFactors hz_h
    have hz_dvd_h : z ∣ h := Nat.dvd_of_mem_primeFactors hz_h
    have hz_dvd_m : z ∣ m := hm_eq ▸ hz_dvd_h.trans (dvd_mul_right h u)
    have hz_m : z ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hz_prime, hz_dvd_m, hm0⟩
    have hz_ndvd_u : ¬ z ∣ u := fun hzu =>
      hz_prime.not_dvd_one (hcop_hu ▸ Nat.dvd_gcd hz_dvd_h hzu)
    have hm_fact_z : m.factorization z = h.factorization z := by
      rw [hm_eq, Nat.factorization_mul hh0 hu0, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hz_ndvd_u, add_zero]
    rw [ordProj_sq_eq_pow_coprime hh0, ← hm_fact_z] at hqz
    have hzr₀ : z = r₀ := huniq_r₀ z hz_m hqz
    exact hr₀_ndvd_h (hzr₀ ▸ hz_dvd_h)
  have hcop_q_sigh2 : Nat.Coprime q (sigma 1 (h ^ 2)) :=
    hq.coprime_iff_not_dvd.mpr hq_ndvd_sigh2
  have hq_dvd_sigu2 : q ∣ sigma 1 (u ^ 2) :=
    hcop_q_sigh2.dvd_of_dvd_mul_left ⟨u ^ 2, hsig_split⟩
  have hsigh2_dvd_u2 : sigma 1 (h ^ 2) ∣ u ^ 2 :=
    hcop_q_sigh2.symm.dvd_of_dvd_mul_left ⟨sigma 1 (u ^ 2), hsig_split.symm⟩
  exact ⟨h, u, r₀, hh_odd, hu_odd, hh_ge3, hu_ge3, hcop_hu, hm_eq, hhalf_eq, hq_eq, hci_sq_eq,
    hr₀_u, hr₀_ndvd_h, hh_lt_r₀pow, hq_dvd_sigu2, hcop_q_sigh2, hsigh2_dvd_u2⟩

private lemma sq_add_self_add_one_le_sigma_sq {h : ℕ} (hh : 3 ≤ h) :
    h ^ 2 + h + 1 ≤ sigma 1 (h ^ 2) := by
  have hh0 : h ≠ 0 := by omega
  have hh2_ne0 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh0
  have h1_mem : 1 ∈ (h ^ 2).divisors := Nat.mem_divisors.mpr ⟨one_dvd _, hh2_ne0⟩
  have hh_mem : h ∈ (h ^ 2).divisors :=
    Nat.mem_divisors.mpr ⟨dvd_pow_self h (by decide : 2 ≠ 0), hh2_ne0⟩
  have hh2_mem : h ^ 2 ∈ (h ^ 2).divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, hh2_ne0⟩
  have hlt1 : 1 < h := by omega
  have hlt2 : h < h ^ 2 := by nlinarith
  have hsub : ({1, h, h ^ 2} : Finset ℕ) ⊆ (h ^ 2).divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact h1_mem
    · exact hh_mem
    · exact hh2_mem
  have hsum_le : ∑ d ∈ ({1, h, h ^ 2} : Finset ℕ), d ≤ sigma 1 (h ^ 2) := by
    rw [sigma_one_apply]
    exact Finset.sum_le_sum_of_subset hsub
  have h1_notin : (1 : ℕ) ∉ ({h, h ^ 2} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hh_notin : h ∉ ({h ^ 2} : Finset ℕ) := by
    simp only [Finset.mem_singleton]
    omega
  rw [Finset.sum_insert h1_notin, Finset.sum_insert hh_notin, Finset.sum_singleton] at hsum_le
  omega

private lemma prime_pow_of_primeFactors_eq_singleton {n p : ℕ}
    (hn0 : n ≠ 0) (hp_sing : n.primeFactors = {p}) :
    p.Prime ∧ 0 < n.factorization p ∧ n = p ^ (n.factorization p) := by
  have hp_mem : p ∈ n.primeFactors := by rw [hp_sing]; exact Finset.mem_singleton_self p
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  have he_pos : 0 < n.factorization p :=
    (hp_prime.dvd_iff_one_le_factorization hn0).mp (Nat.dvd_of_mem_primeFactors hp_mem)
  have hcompl_eq1 : ordCompl[p] n = 1 := by
    by_contra hne1
    obtain ⟨r, hr_prime, hr_dvd⟩ := Nat.exists_prime_and_dvd hne1
    have hr_mem : r ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hr_prime, hr_dvd.trans (Nat.ordCompl_dvd n p), hn0⟩
    rw [hp_sing, Finset.mem_singleton] at hr_mem
    exact Nat.not_dvd_ordCompl hp_prime hn0 (hr_mem ▸ hr_dvd)
  have hn_pow : n = p ^ (n.factorization p) := by
    have hmul := Nat.ordProj_mul_ordCompl_eq_self n p
    rw [hcompl_eq1, mul_one] at hmul
    exact hmul.symm
  exact ⟨hp_prime, he_pos, hn_pow⟩

private lemma coprime_half_succ_w_one_char {N q h u : ℕ}
    (hq : q.Prime) (hh_ge3 : 3 ≤ h) (hu_ge3 : 3 ≤ u)
    (hq_eq : q = 2 * h ^ 2 - 1) (hci_sq_eq : componentIndex N q = u ^ 2)
    (hsigu2_q : sigma 1 (u ^ 2) = q) (hu2_sigh2 : u ^ 2 = sigma 1 (h ^ 2)) :
    (∃ p e : ℕ, p.Prime ∧ 0 < e ∧ u = p ^ e ∧ componentIndex N q = p ^ (2 * e)) ∧
    2 ≤ h.primeFactors.card := by
  have hh0 : h ≠ 0 := by omega
  have hu0 : u ≠ 0 := by omega
  have hu_pf_le1 : u.primeFactors.card ≤ 1 := by
    by_contra! hgt1
    obtain ⟨p, hp_u⟩ := Finset.card_pos.mp (by omega : 0 < u.primeFactors.card)
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_u
    have hord_gt1 : 1 < ordProj[p] u := by
      have hpos : 0 < u.factorization p :=
        (hp_prime.dvd_iff_one_le_factorization hu0).mp (Nat.dvd_of_mem_primeFactors hp_u)
      exact Nat.one_lt_pow hpos.ne' hp_prime.one_lt
    have hcompl_gt1 : 1 < ordCompl[p] u := by
      by_contra! hle1
      have hcompl_pos : 0 < ordCompl[p] u := Nat.ordCompl_pos p hu0
      have hcompl_eq1 : ordCompl[p] u = 1 := by omega
      have hu_eq_proj : u = ordProj[p] u := by
        have hmul := Nat.ordProj_mul_ordCompl_eq_self u p
        rw [hcompl_eq1, mul_one] at hmul
        exact hmul.symm
      have hu_pf_sub : u.primeFactors ⊆ {p} := by
        rw [hu_eq_proj]
        intro r hr
        have hr_prime := Nat.prime_of_mem_primeFactors hr
        have hr_dvd := hr_prime.dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hr)
        exact Finset.mem_singleton.mpr (((Nat.dvd_prime hp_prime).mp hr_dvd).resolve_left hr_prime.ne_one)
      have : u.primeFactors.card ≤ 1 := (Finset.card_le_card hu_pf_sub).trans (Finset.card_singleton p).le
      omega
    have hcop_pc : Nat.Coprime (ordProj[p] u) (ordCompl[p] u) :=
      (Nat.coprime_ordCompl hp_prime hu0).pow_left _
    have hcop_sq : Nat.Coprime ((ordProj[p] u) ^ 2) ((ordCompl[p] u) ^ 2) :=
      (hcop_pc.pow_left 2).pow_right 2
    have hu2_split : u ^ 2 = (ordProj[p] u) ^ 2 * (ordCompl[p] u) ^ 2 := by
      rw [← mul_pow, Nat.ordProj_mul_ordCompl_eq_self u p]
    have hsig_u2_mul :
        sigma 1 (u ^ 2) = sigma 1 ((ordProj[p] u) ^ 2) * sigma 1 ((ordCompl[p] u) ^ 2) := by
      rw [hu2_split, isMultiplicative_sigma.map_mul_of_coprime hcop_sq]
    have ha_gt1 : 1 < sigma 1 ((ordProj[p] u) ^ 2) := by
      have hsq_gt1 : 1 < (ordProj[p] u) ^ 2 := by nlinarith
      exact hsq_gt1.trans (self_lt_sigma_of_one_lt hsq_gt1)
    have hb_gt1 : 1 < sigma 1 ((ordCompl[p] u) ^ 2) := by
      have hsq_gt1 : 1 < (ordCompl[p] u) ^ 2 := by nlinarith
      exact hsq_gt1.trans (self_lt_sigma_of_one_lt hsq_gt1)
    rw [hsigu2_q] at hsig_u2_mul
    rcases hq.eq_one_or_self_of_dvd _ ⟨sigma 1 ((ordCompl[p] u) ^ 2), hsig_u2_mul⟩ with h1 | hself
    · omega
    · have : sigma 1 ((ordCompl[p] u) ^ 2) = 1 := by nlinarith
      omega
  have hu_pf_pos : 1 ≤ u.primeFactors.card := by
    have hu_ne1 : u ≠ 1 := by omega
    obtain ⟨p, hp⟩ := Nat.exists_prime_and_dvd hu_ne1
    exact Finset.card_pos.mpr ⟨p, Nat.mem_primeFactors.mpr ⟨hp.1, hp.2, hu0⟩⟩
  have hu_pf_card1 : u.primeFactors.card = 1 := by omega
  obtain ⟨p, hp_singleton⟩ := Finset.card_eq_one.mp hu_pf_card1
  obtain ⟨hp_prime, he_pos, hu_pow⟩ := prime_pow_of_primeFactors_eq_singleton hu0 hp_singleton
  let e := u.factorization p
  have hu_pow_e : u = p ^ e := hu_pow
  have hci_pow : componentIndex N q = p ^ (2 * e) := by
    rw [hci_sq_eq, hu_pow_e, ← pow_mul, mul_comm]
  have hh_pf_ge2 : 2 ≤ h.primeFactors.card := by
    by_contra! hh_le1
    have hh_pf_pos : 1 ≤ h.primeFactors.card := by
      have hh_ne1 : h ≠ 1 := by omega
      obtain ⟨r, hr⟩ := Nat.exists_prime_and_dvd hh_ne1
      exact Finset.card_pos.mpr ⟨r, Nat.mem_primeFactors.mpr ⟨hr.1, hr.2, hh0⟩⟩
    have hh_pf_card1 : h.primeFactors.card = 1 := by omega
    obtain ⟨ph, hph_singleton⟩ := Finset.card_eq_one.mp hh_pf_card1
    obtain ⟨hph_prime, heh_pos, hh_pow⟩ := prime_pow_of_primeFactors_eq_singleton hh0 hph_singleton
    let eh := h.factorization ph
    have hh_pow_e : h = ph ^ eh := hh_pow
    have hh2_pow : h ^ 2 = ph ^ (2 * eh) := by
      rw [hh_pow_e, ← pow_mul, mul_comm]
    have hsig_sq : IsSquare (sigma 1 (ph ^ (2 * eh))) := by
      rw [← hh2_pow, ← hu2_sigh2]
      exact ⟨u, pow_two u⟩
    have h2eh_pos : 0 < 2 * eh := by omega
    have h2eh_even : Even (2 * eh) := even_two_mul eh
    obtain ⟨hph3, h2eh4⟩ :=
      (sigma_prime_pow_isSquare_iff_of_even hph_prime h2eh_pos h2eh_even).mp hsig_sq
    have heh2 : eh = 2 := by omega
    have hh9 : h = 9 := by
      rw [hh_pow_e, heh2, hph3]
      norm_num
    have hq161 : q = 161 := by
      rw [hq_eq, hh9]
      norm_num
    rw [hq161] at hq
    rcases hq.eq_one_or_self_of_dvd 7 (by decide) with h7 | h7 <;> omega
  exact ⟨⟨p, e, hp_prime, he_pos, hu_pow_e, hci_pow⟩, hh_pf_ge2⟩

/-- **2. Quotient System for the Coprime Half-Successor Branch**:
Defining `W := σ(u ^ 2) / q`, establishes the coupled system
`u ^ 2 = W * σ(h ^ 2)`, `σ(u ^ 2) = W * (2 * h ^ 2 - 1)`,
`2 * u ^ 2 - σ(u ^ 2) = W * (2 * (σ(h ^ 2) - h ^ 2) + 1)`, `2 * h * W < 2 * u ^ 2 - σ(u ^ 2)`,
and characterizes `W = 1` (`W = 1 ↔ σ(u ^ 2) = q ↔ u ^ 2 = σ(h ^ 2)`), showing `W = 1` forces
`u = p ^ e` (`componentIndex N q = p ^ (2 * e)`) and `2 ≤ h.primeFactors.card`. -/
theorem linear_euler_coprime_half_succ_quotient_system {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hcop : Nat.Coprime ((q + 1) / 2) (componentIndex N q)) :
    ∃ h u W : ℕ,
      W = sigma 1 (u ^ 2) / q ∧
      Odd h ∧ Odd u ∧ Odd W ∧ 3 ≤ h ∧ 3 ≤ u ∧ 1 ≤ W ∧
      Nat.Coprime h u ∧ Nat.Coprime h W ∧
      m = h * u ∧
      q = 2 * h ^ 2 - 1 ∧
      componentIndex N q = u ^ 2 ∧
      u ^ 2 = W * sigma 1 (h ^ 2) ∧
      sigma 1 (u ^ 2) = W * (2 * h ^ 2 - 1) ∧
      h ^ 2 + h + 1 ≤ sigma 1 (h ^ 2) ∧
      sigma 1 (u ^ 2) < 2 * u ^ 2 ∧
      2 * u ^ 2 - sigma 1 (u ^ 2) = W * (2 * (sigma 1 (h ^ 2) - h ^ 2) + 1) ∧
      2 * h * W < 2 * u ^ 2 - sigma 1 (u ^ 2) ∧
      (W = 1 ↔ sigma 1 (u ^ 2) = q) ∧
      (W = 1 ↔ u ^ 2 = sigma 1 (h ^ 2)) ∧
      (W = 1 →
        (∃ p e : ℕ, p.Prime ∧ 0 < e ∧ u = p ^ e ∧ componentIndex N q = p ^ (2 * e)) ∧
        2 ≤ h.primeFactors.card) := by
  obtain ⟨h, u, _, hh_odd, hu_odd, hh_ge3, hu_ge3, hcop_hu, hm_eq, _, hq_eq, hci_sq_eq,
    _, _, _, hq_dvd_sigu2, _, _⟩ :=
    linear_euler_coprime_half_succ_unique_q_source_in_u ho hN hq hqm hform hcop
  have hh0 : h ≠ 0 := hh_odd.pos.ne'
  have hu0 : u ≠ 0 := hu_odd.pos.ne'
  have hh20 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh0
  have hu20 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu0
  have hm0 : m ≠ 0 := by rw [hm_eq]; exact mul_ne_zero hh0 hu0
  have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hcop_h2_u2 : Nat.Coprime (h ^ 2) (u ^ 2) := (hcop_hu.pow_left 2).pow_right 2
  have hsigm2_eq : sigma 1 (m ^ 2) = q * u ^ 2 := by
    have hq_cop_m2 : q.Coprime (m ^ 2) := (hq.coprime_iff_not_dvd.mpr hqm).pow_right 2
    have hsig_N : sigma 1 N = 2 * N :=
      (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul ho.pos).mp hN)
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
      hq.coprime_iff_not_dvd.mpr fun hd => hq.not_dvd_one ((Nat.dvd_add_right (dvd_refl q)).mp hd)
    have hq_dvd_m2 : q ∣ sigma 1 (m ^ 2) :=
      hq_cop_q1.dvd_of_dvd_mul_left ⟨2 * m ^ 2, by rw [hsig_bal]; ring⟩
    have hfact_q : N.factorization q = 1 := by
      have hqm2 : ¬ q ∣ m ^ 2 := fun hd => hqm (hq.dvd_of_dvd_pow hd)
      rw [hform, Nat.factorization_mul hq.ne_zero hm20, Finsupp.add_apply,
        hq.factorization_self, Nat.factorization_eq_zero_of_not_dvd hqm2, add_zero]
    have hord_q : ordProj[q] N = q := by rw [hfact_q, pow_one]
    have hcompl_q : ordCompl[q] N = m ^ 2 := by
      rw [hfact_q, pow_one, hform, Nat.mul_div_cancel_left _ hq.pos]
    have hci_eq : componentIndex N q = sigma 1 (m ^ 2) / q := by
      rw [componentIndex, hcompl_q, hord_q]
    rw [← hci_sq_eq, hci_eq]
    exact (Nat.mul_div_cancel' hq_dvd_m2).symm
  have hsig_split : sigma 1 (h ^ 2) * sigma 1 (u ^ 2) = q * u ^ 2 := by
    calc
      sigma 1 (h ^ 2) * sigma 1 (u ^ 2)
          = sigma 1 (h ^ 2 * u ^ 2) := (isMultiplicative_sigma.map_mul_of_coprime hcop_h2_u2).symm
      _ = sigma 1 (m ^ 2) := by rw [hm_eq, mul_pow]
      _ = q * u ^ 2 := hsigm2_eq
  let W := sigma 1 (u ^ 2) / q
  have hsigu2_eq_Wq : sigma 1 (u ^ 2) = W * q := by
    have h1 := Nat.mul_div_cancel' hq_dvd_sigu2
    dsimp [W]
    linarith
  have hsigu2_eq : sigma 1 (u ^ 2) = W * (2 * h ^ 2 - 1) := by
    rwa [← hq_eq]
  have hsigu2_pos : 0 < sigma 1 (u ^ 2) := sigma_pos 1 (u ^ 2) hu20
  have hW_pos : 1 ≤ W := by
    by_contra! hW0
    have hWz : W = 0 := Nat.lt_one_iff.mp hW0
    rw [hWz, zero_mul] at hsigu2_eq_Wq
    exact hsigu2_pos.ne' hsigu2_eq_Wq
  have hsigu2_odd : Odd (sigma 1 (u ^ 2)) :=
    (odd_sigma_iff_square_of_odd hu_odd.pow).mpr ⟨u, pow_two u⟩
  have hW_odd : Odd W := hsigu2_odd.of_dvd_nat ⟨q, hsigu2_eq_Wq⟩
  have hu2_eq : u ^ 2 = W * sigma 1 (h ^ 2) := by
    apply Nat.mul_left_cancel hq.pos
    calc
      q * u ^ 2 = sigma 1 (h ^ 2) * sigma 1 (u ^ 2) := hsig_split.symm
      _ = sigma 1 (h ^ 2) * (W * q) := by rw [hsigu2_eq_Wq]
      _ = q * (W * sigma 1 (h ^ 2)) := by ring
  have hcop_hW : Nat.Coprime h W := by
    have hcop_hu2 : Nat.Coprime h (u ^ 2) := hcop_hu.pow_right 2
    exact hcop_hu2.coprime_dvd_right ⟨sigma 1 (h ^ 2), hu2_eq⟩
  have hsigh2_lb : h ^ 2 + h + 1 ≤ sigma 1 (h ^ 2) := sq_add_self_add_one_le_sigma_sq hh_ge3
  have hh2_ge9 : 9 ≤ h ^ 2 := by nlinarith
  have hsigu2_lt : sigma 1 (u ^ 2) < 2 * u ^ 2 := by
    rw [hsigu2_eq, hu2_eq]
    have h1 : 2 * h ^ 2 - 1 < 2 * sigma 1 (h ^ 2) := by omega
    nlinarith
  have hdiff_eq : 2 * u ^ 2 - sigma 1 (u ^ 2) = W * (2 * (sigma 1 (h ^ 2) - h ^ 2) + 1) := by
    zify [show sigma 1 (u ^ 2) ≤ 2 * u ^ 2 by omega,
          show h ^ 2 ≤ sigma 1 (h ^ 2) by omega,
          show 1 ≤ 2 * h ^ 2 by omega]
    have hu2_z : (u ^ 2 : ℤ) = (W : ℤ) * (sigma 1 (h ^ 2) : ℤ) := by exact_mod_cast hu2_eq
    have hsigu2_z : (sigma 1 (u ^ 2) : ℤ) = (W : ℤ) * (2 * (h ^ 2 : ℤ) - 1) := by
      have h1 : sigma 1 (u ^ 2) = W * (2 * h ^ 2 - 1) := hsigu2_eq
      zify [show 1 ≤ 2 * h ^ 2 by omega] at h1
      exact h1
    rw [hu2_z, hsigu2_z]
    ring
  have hdiff_gt : 2 * h * W < 2 * u ^ 2 - sigma 1 (u ^ 2) := by
    rw [hdiff_eq]
    have h1 : 2 * h < 2 * (sigma 1 (h ^ 2) - h ^ 2) + 1 := by omega
    nlinarith
  have hW_iff_sig : W = 1 ↔ sigma 1 (u ^ 2) = q := by
    constructor
    · intro hW1
      rw [hsigu2_eq_Wq, hW1, one_mul]
    · intro hsq
      rw [hsq, mul_comm] at hsigu2_eq_Wq
      have hq1 : q * 1 = q * W := by simpa [mul_one] using hsigu2_eq_Wq
      exact (Nat.mul_left_cancel hq.pos hq1).symm
  have hsigh2_pos : 0 < sigma 1 (h ^ 2) := sigma_pos 1 (h ^ 2) hh20
  have hW_iff_u2 : W = 1 ↔ u ^ 2 = sigma 1 (h ^ 2) := by
    constructor
    · intro hW1
      rw [hu2_eq, hW1, one_mul]
    · intro hu2s
      have h1 : 1 * sigma 1 (h ^ 2) = W * sigma 1 (h ^ 2) := by
        rw [one_mul, ← hu2_eq, hu2s]
      exact (Nat.mul_right_cancel hsigh2_pos h1).symm
  have hW1_imp :
      W = 1 →
        (∃ p e : ℕ, p.Prime ∧ 0 < e ∧ u = p ^ e ∧ componentIndex N q = p ^ (2 * e)) ∧
        2 ≤ h.primeFactors.card :=
    fun hW1 =>
      coprime_half_succ_w_one_char hq hh_ge3 hu_ge3 hq_eq hci_sq_eq
        (hW_iff_sig.mp hW1) (hW_iff_u2.mp hW1)
  exact ⟨h, u, W, rfl, hh_odd, hu_odd, hW_odd, hh_ge3, hu_ge3, hW_pos, hcop_hu, hcop_hW,
    hm_eq, hq_eq, hci_sq_eq, hu2_eq, hsigu2_eq, hsigh2_lb, hsigu2_lt, hdiff_eq, hdiff_gt,
    hW_iff_sig, hW_iff_u2, hW1_imp⟩

private lemma sixth_power_free_coprime_half_succ_w_ne_one {N q h u p e : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq_prime : q.Prime)
    (hfree : ∀ r : ℕ, r.Prime → ¬ r ^ 6 ∣ N)
    (hform : N = q * (h * u) ^ 2) (hqm : ¬ q ∣ h * u)
    (hhalf : (q + 1) / 2 = h ^ 2) (hci : componentIndex N q = u ^ 2)
    (hp_prime : p.Prime) (he_pos : 0 < e) (hu_pow : u = p ^ e) (hci_pow : componentIndex N q = p ^ (2 * e)) :
    False := by
  let m := h * u
  have hq_odd : Odd q := ho.of_dvd_nat (hform ▸ dvd_mul_right q (m ^ 2))
  have hq1_even : q + 1 = 2 * ((q + 1) / 2) := by
    have := Nat.odd_iff.mp hq_odd
    omega
  have hq1_eq : q + 1 = 2 * h ^ 2 := by rw [hq1_even, hhalf]
  have hqm2 : ¬ q ∣ m ^ 2 := fun hd => hqm (hq_prime.dvd_of_dvd_pow hd)
  have hform_pow : N = q ^ 1 * m ^ 2 := by simpa only [pow_one] using hform
  have hq_cop_m2 : q.Coprime (m ^ 2) := (hq_prime.coprime_iff_not_dvd.mpr hqm).pow_right 2
  have hsig_N : sigma 1 N = 2 * N :=
    (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul ho.pos).mp hN)
  have hsig_q : sigma 1 q = q + 1 := by
    rw [← pow_one q, sigma_one_apply_prime_pow hq_prime]
    simp [Finset.sum_range_succ]
    ring
  have hr_q : (q + 1) * componentIndex N q = 2 * m ^ 2 := by
    rw [hq1_eq, hci]
    change 2 * h ^ 2 * u ^ 2 = 2 * (h * u) ^ 2
    ring
  have hl_q : sigma 1 (m ^ 2) = q * componentIndex N q := by
    have hmul : sigma 1 (q * m ^ 2) = sigma 1 q * sigma 1 (m ^ 2) :=
      isMultiplicative_sigma.map_mul_of_coprime hq_cop_m2
    have hsig_bal : (q + 1) * sigma 1 (m ^ 2) = 2 * (q * m ^ 2) := by
      rw [← hsig_q, ← hmul, ← hform, hsig_N, hform]
    have hq1_pos : 0 < q + 1 := Nat.succ_pos q
    apply Nat.mul_left_cancel hq1_pos
    calc
      (q + 1) * sigma 1 (m ^ 2) = 2 * (q * m ^ 2) := hsig_bal
      _ = q * (2 * m ^ 2) := by ring
      _ = q * ((q + 1) * componentIndex N q) := by rw [hr_q]
      _ = (q + 1) * (q * componentIndex N q) := by ring
  have hl : sigma 1 (m ^ 2) = q ^ 1 * componentIndex N q := by
    simpa only [pow_one] using hl_q
  have hr : sigma 1 (q ^ 1) * componentIndex N q = 2 * m ^ 2 := by
    simpa only [pow_one, hsig_q] using hr_q
  obtain ⟨he_ge128, _, _⟩ :=
    even_prime_power_component_sharpened_pade_cap hN ho hq_prime (by decide : 0 < 1)
      hform_pow hqm2 hl hr hp_prime he_pos hci_pow
  have hp_dvd_N : p ^ (2 * e) ∣ N := by
    have hu2_dvd_m2 : u ^ 2 ∣ m ^ 2 := by
      change u ^ 2 ∣ (h * u) ^ 2
      rw [mul_pow]
      exact dvd_mul_left _ _
    have hu2_eq_p : u ^ 2 = p ^ (2 * e) := by rw [hu_pow, ← pow_mul, mul_comm]
    have hp_dvd_m2 : p ^ (2 * e) ∣ m ^ 2 := hu2_eq_p ▸ hu2_dvd_m2
    exact hp_dvd_m2.trans (hform ▸ dvd_mul_left _ _)
  exact hfree p hp_prime ((pow_dvd_pow p (by omega : 6 ≤ 2 * e)).trans hp_dvd_N)

private lemma three_le_of_odd_of_two_le {W : ℕ} (hodd : Odd W) (h2 : 2 ≤ W) : 3 ≤ W := by
  obtain ⟨k, rfl⟩ := hodd
  omega

/-- **3. Sixth-Power-Free Coprime Half-Successor Quotient Bounds (`3 ≤ W`)**:
Specializing `linear_euler_coprime_half_succ_quotient_system` to a sixth-power-free odd perfect
number `N` yields `59 ≤ h`, `6961 ≤ q`, `119 * W ≤ 2 * u ^ 2 - σ(u ^ 2)`, and eliminates
`W = 1` unconditionally via `even_prime_power_component_sharpened_pade_cap` (`128 ≤ e`,
contradicting `¬ p ^ 6 ∣ N`), proving `2 ≤ W` and hence `3 ≤ W` since `Odd W`. -/
theorem sixth_power_free_coprime_half_succ_quotient_bounds {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N)
    (hcop : Nat.Coprime ((q + 1) / 2) (componentIndex N q)) :
    ∃ h u W : ℕ,
      W = sigma 1 (u ^ 2) / q ∧
      Odd h ∧ Odd u ∧ Odd W ∧
      59 ≤ h ∧ 3 ≤ u ∧ 2 ≤ W ∧ 3 ≤ W ∧
      Nat.Coprime h u ∧ Nat.Coprime h W ∧
      N = q * (h * u) ^ 2 ∧
      ¬ q ∣ h * u ∧
      (q + 1) / 2 = h ^ 2 ∧
      q = 2 * h ^ 2 - 1 ∧
      6961 ≤ q ∧
      componentIndex N q = u ^ 2 ∧
      u ^ 2 = W * sigma 1 (h ^ 2) ∧
      sigma 1 (u ^ 2) = W * (2 * h ^ 2 - 1) ∧
      h ^ 2 + h + 1 ≤ sigma 1 (h ^ 2) ∧
      sigma 1 (u ^ 2) < 2 * u ^ 2 ∧
      2 * u ^ 2 - sigma 1 (u ^ 2) = W * (2 * (sigma 1 (h ^ 2) - h ^ 2) + 1) ∧
      119 * W ≤ 2 * u ^ 2 - sigma 1 (u ^ 2) := by
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  obtain ⟨⟨h₁, u₁, _, hh₁_ge59, _, _, _, hform₁, hqm₁, hhalf₁, _, _, _⟩,
    _, _, hq_ge6961, _, _, _, _⟩ :=
    sixth_power_free_coprime_half_succ_index_profile ho hN hq hq4 he hev hfree hcop
  obtain ⟨h, u, W, hW_def, hh_odd, hu_odd, hW_odd, _, hu_ge3, hW_ge1, hcop_hu, hcop_hW,
    hm_eq, hq_eq, hci_sq_eq, hu2_eq, hsigu2_eq, hsigh2_lb, hsigu2_lt, hdiff_eq, _,
    _, _, hW1_imp⟩ :=
    linear_euler_coprime_half_succ_quotient_system ho hN hq_prime hqm₁ hform₁ hcop
  have hh_sq_eq : h ^ 2 = h₁ ^ 2 := by
    have hq_odd : Odd q := ho.of_dvd_nat (hform₁ ▸ dvd_mul_right q ((h₁ * u₁) ^ 2))
    have hq1_even : q + 1 = 2 * ((q + 1) / 2) := by
      have hmod := Nat.odd_iff.mp hq_odd
      exact (Nat.mul_div_cancel' (by exact Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, hmod]))).symm
    have hh1_pos : 1 ≤ h ^ 2 := Nat.one_le_pow 2 h hh_odd.pos
    have hq1_eq : q + 1 = 2 * h ^ 2 := by
      have hge1 : 1 ≤ 2 * h ^ 2 := by linarith
      exact ((Nat.sub_eq_iff_eq_add hge1).mp hq_eq.symm).symm
    have h2 : 2 * h ^ 2 = 2 * h₁ ^ 2 := by
      calc
        2 * h ^ 2 = q + 1 := hq1_eq.symm
        _ = 2 * ((q + 1) / 2) := hq1_even
        _ = 2 * h₁ ^ 2 := by rw [hhalf₁]
    exact Nat.mul_left_cancel (by decide : 0 < 2) h2
  have hh_eq : h = h₁ := Nat.pow_left_injective (by decide : 2 ≠ 0) hh_sq_eq
  have hh_ge59 : 59 ≤ h := hh_eq ▸ hh₁_ge59
  have hhalf_eq : (q + 1) / 2 = h ^ 2 := hh_eq ▸ hhalf₁
  have hform_hu : N = q * (h * u) ^ 2 := by rwa [← hm_eq]
  have hqm_hu : ¬ q ∣ h * u := by rwa [← hm_eq]
  have hW_ne1 : W ≠ 1 := by
    intro hW1
    obtain ⟨⟨p, e, hp_prime, he_pos, hu_pow, hci_pow⟩, _⟩ := hW1_imp hW1
    exact sixth_power_free_coprime_half_succ_w_ne_one ho hN hq_prime hfree
      hform_hu hqm_hu hhalf_eq hci_sq_eq hp_prime he_pos hu_pow hci_pow
  have hW_ge2 : 2 ≤ W := Nat.lt_of_le_of_ne hW_ge1 (Ne.symm hW_ne1)
  have hW_ge3 : 3 ≤ W := three_le_of_odd_of_two_le hW_odd hW_ge2
  have h119_le : 119 * W ≤ 2 * u ^ 2 - sigma 1 (u ^ 2) := by
    rw [hdiff_eq]
    have hsub : h + 1 ≤ sigma 1 (h ^ 2) - h ^ 2 := Nat.le_sub_of_add_le' hsigh2_lb
    have h1 : 119 ≤ 2 * (sigma 1 (h ^ 2) - h ^ 2) + 1 := by linarith
    exact Nat.le_trans (Nat.mul_le_mul_right W h1) (by rw [mul_comm])
  exact ⟨h, u, W, hW_def, hh_odd, hu_odd, hW_odd, hh_ge59, hu_ge3, hW_ge2, hW_ge3,
    hcop_hu, hcop_hW, hform_hu, hqm_hu, hhalf_eq, hq_eq, hq_ge6961, hci_sq_eq,
    hu2_eq, hsigu2_eq, hsigh2_lb, hsigu2_lt, hdiff_eq, h119_le⟩

end OddPerfect
