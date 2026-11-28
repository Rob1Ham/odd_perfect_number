module

public import OddPerfect.LinearEulerCoprimeHalfSuccObstruction
public import OddPerfect.QuarticTargetCapacity
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Linear Euler Coprime Half-Successor `W`-Factor Obstruction

Deepens the analysis of the coprime half-successor branch
`Nat.Coprime ((q + 1) / 2) (componentIndex N q)` on linear Euler odd perfect numbers
`N = q * m ^ 2`, where `u ^ 2 = W * σ(h ^ 2)` and `σ(u ^ 2) = W * (2 * h ^ 2 - 1)`:

1. `linear_euler_coprime_half_succ_square_or_block_collision`:
   Establishes the odd-valuation inter-block `σ`-collision dichotomy:
   - Either `IsSquare (σ(h ^ 2)) ∧ IsSquare W ∧ 2 ≤ h.primeFactors.card`;
   - Or `¬ IsSquare (σ(h ^ 2)) ∧ ¬ IsSquare W` with an explicit odd prime `s ∈ u.primeFactors`
     (`3 ≤ s ≤ W`) having odd valuation in both `σ(h ^ 2)` and `W`, dividing `W`, `σ(h ^ 2)`,
     and `σ(u ^ 2)`, and dividing `σ(ordProj[p₁] (m ^ 2))` and `σ(ordProj[p₂] (m ^ 2))` for two
     distinct prime components `p₁ ∈ h.primeFactors` and `p₂ ∈ u.primeFactors`.
2. `sixth_power_free_coprime_half_succ_w_ge_61`:
   Lifts the sixth-power-free cofactor bound from `3 ≤ W` to `61 ≤ W` and
   `7259 ≤ 2 * u ^ 2 - σ(u ^ 2)`, locating a prime `s ∈ u.primeFactors` with `s ∣ W`,
   `s % 5 = 1 ∨ s % 3 = 1`, and `61 ≤ s`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

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

private lemma ordProj_sq_eq_pow {m p : ℕ} (hm0 : m ≠ 0) :
    ordProj[p] (m ^ 2) = p ^ (2 * m.factorization p) := by
  rw [pow_two, Nat.factorization_mul hm0 hm0, Finsupp.add_apply, ← two_mul]

/-- **1. Odd-Valuation Inter-Block `σ`-Collision Dichotomy**:
On the coprime half-successor branch `Nat.Coprime ((q + 1) / 2) (componentIndex N q)` of a linear
Euler odd perfect number `N = q * m ^ 2`, either `IsSquare (σ(h ^ 2)) ∧ IsSquare W ∧ 2 ≤ ω(h)`,
or `¬ IsSquare (σ(h ^ 2)) ∧ ¬ IsSquare W` and there is an explicit odd prime `s ∈ u.primeFactors`
(`3 ≤ s ≤ W`) with odd valuation in `σ(h ^ 2)` and `W` dividing `W`, `σ(h ^ 2)`, `σ(u ^ 2)`,
and two distinct prime-power blocks `ordProj[p₁] (m ^ 2)` (`p₁ ∈ h.primeFactors`) and
`ordProj[p₂] (m ^ 2)` (`p₂ ∈ u.primeFactors`). -/
theorem linear_euler_coprime_half_succ_square_or_block_collision {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hcop : Nat.Coprime ((q + 1) / 2) (componentIndex N q)) :
    ∃ h u W : ℕ,
      W = sigma 1 (u ^ 2) / q ∧
      Odd h ∧ Odd u ∧ Odd W ∧
      3 ≤ h ∧ 3 ≤ u ∧ 1 ≤ W ∧
      Nat.Coprime h u ∧ Nat.Coprime h W ∧
      m = h * u ∧
      q = 2 * h ^ 2 - 1 ∧
      componentIndex N q = u ^ 2 ∧
      u ^ 2 = W * sigma 1 (h ^ 2) ∧
      sigma 1 (u ^ 2) = W * (2 * h ^ 2 - 1) ∧
      ((IsSquare (sigma 1 (h ^ 2)) ∧ IsSquare W ∧ 2 ≤ h.primeFactors.card) ∨
       (¬ IsSquare (sigma 1 (h ^ 2)) ∧ ¬ IsSquare W ∧
        ∃ s ∈ u.primeFactors,
          Odd ((sigma 1 (h ^ 2)).factorization s) ∧
          Odd (W.factorization s) ∧
          s ∣ W ∧
          s ∣ sigma 1 (h ^ 2) ∧
          s ∣ sigma 1 (u ^ 2) ∧
          3 ≤ s ∧
          s ≤ W ∧
          ∃ p₁ ∈ h.primeFactors, ∃ p₂ ∈ u.primeFactors,
            p₁ ≠ p₂ ∧
            s ∣ sigma 1 (ordProj[p₁] (m ^ 2)) ∧
            s ∣ sigma 1 (ordProj[p₂] (m ^ 2)))) := by
  obtain ⟨h, u, W, hW_def, hh_odd, hu_odd, hW_odd, hh_ge3, hu_ge3, hW_ge1, hcop_hu, hcop_hW,
    hm_eq, hq_eq, hci_sq_eq, hu2_eq, hsigu2_eq, _, _, _, _, _, _, _⟩ :=
    linear_euler_coprime_half_succ_quotient_system ho hN hq hqm hform hcop
  have hh0 : h ≠ 0 := hh_odd.pos.ne'
  have hu0 : u ≠ 0 := hu_odd.pos.ne'
  have hm0 : m ≠ 0 := by rw [hm_eq]; exact mul_ne_zero hh0 hu0
  have hh20 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh0
  have hu20 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu0
  have hW0 : W ≠ 0 := by omega
  have hsigh2_ne0 : sigma 1 (h ^ 2) ≠ 0 := (sigma_pos 1 (h ^ 2) hh20).ne'
  have hfac_u2_sum : ∀ r : ℕ, 2 * u.factorization r = W.factorization r + (sigma 1 (h ^ 2)).factorization r := by
    intro r
    have h1 := congrArg (fun n => n.factorization r) hu2_eq
    rw [pow_two, Nat.factorization_mul hu0 hu0, Finsupp.add_apply, ← two_mul,
      Nat.factorization_mul hW0 hsigh2_ne0, Finsupp.add_apply] at h1
    exact h1
  refine ⟨h, u, W, hW_def, hh_odd, hu_odd, hW_odd, hh_ge3, hu_ge3, hW_ge1, hcop_hu, hcop_hW,
    hm_eq, hq_eq, hci_sq_eq, hu2_eq, hsigu2_eq, ?_⟩
  by_cases hsq : IsSquare (sigma 1 (h ^ 2))
  · left
    have hW_sq : IsSquare W := by
      rw [Nat.isSquare_iff_even_factorization]
      intro r hr
      have hs_even : Even ((sigma 1 (h ^ 2)).factorization r) :=
        (Nat.isSquare_iff_even_factorization.mp hsq) r hr
      obtain ⟨a, ha⟩ := hs_even
      have hsum := hfac_u2_sum r
      exact ⟨u.factorization r - a, by omega⟩
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
        rwa [← hh2_pow]
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
    exact ⟨hsq, hW_sq, hh_pf_ge2⟩
  · right
    have hW_nsq : ¬ IsSquare W := by
      intro hW_sq
      apply hsq
      rw [Nat.isSquare_iff_even_factorization]
      intro r hr
      have hW_even : Even (W.factorization r) :=
        (Nat.isSquare_iff_even_factorization.mp hW_sq) r hr
      obtain ⟨a, ha⟩ := hW_even
      have hsum := hfac_u2_sum r
      exact ⟨u.factorization r - a, by omega⟩
    have hex : ∃ s : ℕ, s.Prime ∧ ¬ Even ((sigma 1 (h ^ 2)).factorization s) := by
      by_contra! hall
      exact hsq (Nat.isSquare_iff_even_factorization.mpr hall)
    obtain ⟨s, hs_prime, hs_not_even⟩ := hex
    have hs_sigh2_odd : Odd ((sigma 1 (h ^ 2)).factorization s) :=
      Nat.not_even_iff_odd.mp hs_not_even
    have hs_W_odd : Odd (W.factorization s) := by
      have hsum := hfac_u2_sum s
      obtain ⟨k, hk⟩ := hs_sigh2_odd
      rw [Nat.odd_iff]
      omega
    have hs_sigh2_ge1 : 1 ≤ (sigma 1 (h ^ 2)).factorization s := by
      obtain ⟨k, hk⟩ := hs_sigh2_odd
      omega
    have hs_W_ge1 : 1 ≤ W.factorization s := by
      obtain ⟨k, hk⟩ := hs_W_odd
      omega
    have hs_dvd_sigh2 : s ∣ sigma 1 (h ^ 2) :=
      (hs_prime.dvd_iff_one_le_factorization hsigh2_ne0).mpr hs_sigh2_ge1
    have hs_dvd_W : s ∣ W :=
      (hs_prime.dvd_iff_one_le_factorization hW0).mpr hs_W_ge1
    have hs_dvd_sigu2 : s ∣ sigma 1 (u ^ 2) :=
      hsigu2_eq ▸ hs_dvd_W.trans (dvd_mul_right W _)
    have hs_dvd_u2 : s ∣ u ^ 2 :=
      hu2_eq ▸ hs_dvd_W.trans (dvd_mul_right W _)
    have hs_dvd_u : s ∣ u := hs_prime.dvd_of_dvd_pow hs_dvd_u2
    have hs_u : s ∈ u.primeFactors := Nat.mem_primeFactors.mpr ⟨hs_prime, hs_dvd_u, hu0⟩
    have hs_odd : Odd s := hu_odd.of_dvd_nat hs_dvd_u
    have hs_ge3 : 3 ≤ s := by
      have := hs_prime.two_le
      obtain ⟨k, hk⟩ := hs_odd
      omega
    have hs_le_W : s ≤ W := Nat.le_of_dvd hW_ge1 hs_dvd_W
    have hsigh2_prod : sigma 1 (h ^ 2) = ∏ z ∈ h.primeFactors, sigma 1 (ordProj[z] (h ^ 2)) := by
      rw [isMultiplicative_sigma.multiplicative_factorization (sigma 1) hh20]
      exact Finset.prod_congr
        ((h ^ 2).support_factorization.trans (Nat.primeFactors_pow h (by decide : 2 ≠ 0)))
        fun _ _ => rfl
    have hsigu2_prod : sigma 1 (u ^ 2) = ∏ z ∈ u.primeFactors, sigma 1 (ordProj[z] (u ^ 2)) := by
      rw [isMultiplicative_sigma.multiplicative_factorization (sigma 1) hu20]
      exact Finset.prod_congr
        ((u ^ 2).support_factorization.trans (Nat.primeFactors_pow u (by decide : 2 ≠ 0)))
        fun _ _ => rfl
    obtain ⟨p₁, hp₁_h, hs_dvd_p₁h⟩ :=
      (hs_prime.prime.dvd_finsetProd_iff _).mp (hsigh2_prod ▸ hs_dvd_sigh2)
    obtain ⟨p₂, hp₂_u, hs_dvd_p₂u⟩ :=
      (hs_prime.prime.dvd_finsetProd_iff _).mp (hsigu2_prod ▸ hs_dvd_sigu2)
    have hp₁_prime : p₁.Prime := Nat.prime_of_mem_primeFactors hp₁_h
    have hp₁_dvd_h : p₁ ∣ h := Nat.dvd_of_mem_primeFactors hp₁_h
    have hp₂_dvd_u : p₂ ∣ u := Nat.dvd_of_mem_primeFactors hp₂_u
    have hp_ne : p₁ ≠ p₂ := by
      intro hpeq
      subst p₂
      exact hp₁_prime.not_dvd_one (hcop_hu ▸ Nat.dvd_gcd hp₁_dvd_h hp₂_dvd_u)
    have hord₁ : ordProj[p₁] (h ^ 2) = ordProj[p₁] (m ^ 2) := by
      have hp₁_ndvd_u : ¬ p₁ ∣ u := fun hd =>
        hp₁_prime.not_dvd_one (hcop_hu ▸ Nat.dvd_gcd hp₁_dvd_h hd)
      have hm_fac : m.factorization p₁ = h.factorization p₁ := by
        rw [hm_eq, Nat.factorization_mul hh0 hu0, Finsupp.add_apply,
          Nat.factorization_eq_zero_of_not_dvd hp₁_ndvd_u, add_zero]
      rw [ordProj_sq_eq_pow hh0, ordProj_sq_eq_pow hm0, hm_fac]
    have hord₂ : ordProj[p₂] (u ^ 2) = ordProj[p₂] (m ^ 2) := by
      have hp₂_prime : p₂.Prime := Nat.prime_of_mem_primeFactors hp₂_u
      have hp₂_ndvd_h : ¬ p₂ ∣ h := fun hd =>
        hp₂_prime.not_dvd_one (hcop_hu ▸ Nat.dvd_gcd hd hp₂_dvd_u)
      have hm_fac : m.factorization p₂ = u.factorization p₂ := by
        rw [hm_eq, Nat.factorization_mul hh0 hu0, Finsupp.add_apply,
          Nat.factorization_eq_zero_of_not_dvd hp₂_ndvd_h, zero_add]
      rw [ordProj_sq_eq_pow hu0, ordProj_sq_eq_pow hm0, hm_fac]
    have hs_dvd_p₁ : s ∣ sigma 1 (ordProj[p₁] (m ^ 2)) := hord₁ ▸ hs_dvd_p₁h
    have hs_dvd_p₂ : s ∣ sigma 1 (ordProj[p₂] (m ^ 2)) := hord₂ ▸ hs_dvd_p₂u
    exact ⟨hsq, hW_nsq, s, hs_u, hs_sigh2_odd, hs_W_odd, hs_dvd_W, hs_dvd_sigh2, hs_dvd_sigu2,
      hs_ge3, hs_le_W, p₁, hp₁_h, p₂, hp₂_u, hp_ne, hs_dvd_p₁, hs_dvd_p₂⟩

/-- **2. Sixth-Power-Free Coprime Half-Successor Cofactor Bound (`61 ≤ W`)**:
On a sixth-power-free odd perfect number `N` in the coprime half-successor branch
`Nat.Coprime ((q + 1) / 2) (componentIndex N q)`, any prime factor `s ∣ W` lies in
`u.primeFactors` and divides `componentIndex N q = u ^ 2`, forcing `s % 5 = 1 ∨ s % 3 = 1` and
`61 ≤ s`, which lifts `3 ≤ W` to `61 ≤ W` and `7259 ≤ 2 * u ^ 2 - σ(u ^ 2)`. -/
theorem sixth_power_free_coprime_half_succ_w_ge_61 {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N)
    (hcop : Nat.Coprime ((q + 1) / 2) (componentIndex N q)) :
    ∃ h u W : ℕ,
      W = sigma 1 (u ^ 2) / q ∧
      Odd h ∧ Odd u ∧ Odd W ∧
      59 ≤ h ∧ 6961 ≤ q ∧ 61 ≤ W ∧
      Nat.Coprime h u ∧ Nat.Coprime h W ∧
      N = q * (h * u) ^ 2 ∧
      componentIndex N q = u ^ 2 ∧
      u ^ 2 = W * sigma 1 (h ^ 2) ∧
      sigma 1 (u ^ 2) = W * (2 * h ^ 2 - 1) ∧
      119 * W ≤ 2 * u ^ 2 - sigma 1 (u ^ 2) ∧
      7259 ≤ 2 * u ^ 2 - sigma 1 (u ^ 2) ∧
      ∃ s ∈ u.primeFactors, s ∣ W ∧ (s % 5 = 1 ∨ s % 3 = 1) ∧ 61 ≤ s := by
  obtain ⟨h, u, W, hW_def, hh_odd, hu_odd, hW_odd, hh_ge59, _, _, hW_ge3,
    hcop_hu, hcop_hW, hform_hu, _, _, _, hq_ge6961, hci_sq_eq, hu2_eq, hsigu2_eq,
    _, _, _, h119_le⟩ :=
    sixth_power_free_coprime_half_succ_quotient_bounds ho hN hq hq4 he hev hfree hcop
  have hu0 : u ≠ 0 := hu_odd.pos.ne'
  have hW_ne1 : W ≠ 1 := by omega
  obtain ⟨s, hs_prime, hs_dvd_W⟩ := Nat.exists_prime_and_dvd hW_ne1
  have hs_dvd_u2 : s ∣ u ^ 2 := hu2_eq ▸ hs_dvd_W.trans (dvd_mul_right W _)
  have hs_dvd_u : s ∣ u := hs_prime.dvd_of_dvd_pow hs_dvd_u2
  have hs_u : s ∈ u.primeFactors := Nat.mem_primeFactors.mpr ⟨hs_prime, hs_dvd_u, hu0⟩
  have hci_ne0 : componentIndex N q ≠ 0 := by
    rw [hci_sq_eq]
    exact pow_ne_zero 2 hu0
  have hs_ci_mem : s ∈ (componentIndex N q).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hs_prime, hci_sq_eq ▸ hs_dvd_u2, hci_ne0⟩
  have hs_mod : s % 5 = 1 ∨ s % 3 = 1 :=
    (sixth_power_free_euler_index_drop_and_support ho hN hq hq4 he hev hfree).2 s hs_ci_mem
  have hs_dvd_N : s ∣ N := by
    rw [hform_hu]
    exact (hs_dvd_u.trans (dvd_mul_left u h)).trans
      ((dvd_pow_self (h * u) (by decide : 2 ≠ 0)).trans (dvd_mul_left _ q))
  have hs_N : s ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hs_prime, hs_dvd_N, hN.2.ne'⟩
  have hs_ge53 : 53 ≤ s := sixth_power_free_min_prime_ge_53 ho hN hfree hs_N
  have hs_ge61 : 61 ≤ s := by
    by_contra! hlt
    have hs_cases : s = 54 ∨ s = 55 ∨ s = 56 ∨ s = 57 ∨ s = 58 ∨ s = 60 := by omega
    rcases hs_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (by decide : ¬ Nat.Prime _) hs_prime
  have hW_ge61 : 61 ≤ W := hs_ge61.trans (Nat.le_of_dvd (by omega : 0 < W) hs_dvd_W)
  have h7259_le : 7259 ≤ 2 * u ^ 2 - sigma 1 (u ^ 2) := by omega
  exact ⟨h, u, W, hW_def, hh_odd, hu_odd, hW_odd, hh_ge59, hq_ge6961, hW_ge61, hcop_hu, hcop_hW,
    hform_hu, hci_sq_eq, hu2_eq, hsigu2_eq, h119_le, h7259_le, s, hs_u, hs_dvd_W, hs_mod, hs_ge61⟩

end OddPerfect
