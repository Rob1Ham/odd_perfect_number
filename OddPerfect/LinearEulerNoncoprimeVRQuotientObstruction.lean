module

public import OddPerfect.LinearEulerSixthPowerFreeRightSourcePeeling
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Linear Euler Non-Coprime `V_R` Quotient and Reverse-Edge Obstruction

Establishes the peeled quotient `V_R := (g_L * g_R * U₀ ^ 2) / c₀` and forced incoming
reverse-edge witness `s ∈ (M_R * m_L).primeFactors` when the unique `q`-source `r₀` lies
in `m_R` without dividing `g_R`, together with the universal sixth-power-free lower bounds
`61 ≤ r₀`, `3721 ≤ r₀ ^ (2 * e₀)`, `c₀ = 1 ∨ (61 ≤ c₀.minFac ∧ 61 ≤ c₀)`, and
`61 ≤ g_L * g_R * (u₀ / r₀ ^ e₀)` when `1 < c₀`:

1. `OddPerfect.linear_euler_noncoprime_VR_quotient_and_reverse_edge`
2. `OddPerfect.sixth_power_free_universal_r0_and_c0_minFac_pinch`
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma prime_ge_61_of_ge_53_mod {s : ℕ} (hs_prime : s.Prime)
    (hs_ge53 : 53 ≤ s) (hs_mod : s % 5 = 1 ∨ s % 3 = 1) : 61 ≤ s := by
  by_contra! hlt
  have hs_cases : s = 54 ∨ s = 55 ∨ s = 56 ∨ s = 57 ∨ s = 58 ∨ s = 60 := by omega
  rcases hs_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact (by decide : ¬ Nat.Prime _) hs_prime

/-- **1. Non-Coprime `V_R` Quotient and Reverse-Edge Obstruction**:
On any linear Euler odd perfect number `N = q * m ^ 2`, refines `linear_euler_right_source_peeling_dichotomy`
in the `r₀ ∣ m_R`, `¬ r₀ ∣ g_R` regime by cancelling `c₀` into `V_R := (g_L * g_R * U₀ ^ 2) / c₀`,
giving `sigma 1 (M_R ^ 2) * sigma 1 (m_L ^ 2) = r₀ ^ (2 * e₀) * V_R`, `Nat.Coprime (r₀ ^ (2 * e₀)) V_R`,
and a reverse-edge prime `s ∈ (M_R * m_L).primeFactors` (`s ≠ r₀`, `s ≠ q`, `s ∣ M_R ∨ s ∣ m_L`)
satisfying `r₀ ∣ sigma 1 (s ^ (2 * m.factorization s))`. -/
theorem linear_euler_noncoprime_VR_quotient_and_reverse_edge {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2) :
    let A := (q + 1) / 2
    let I := componentIndex N q
    let L := Nat.factorizationLCMLeft A I
    let R := Nat.factorizationLCMRight A I
    let m_L := Nat.gcd m L
    let m_R := Nat.gcd m R
    ∃ h₀ u₀ g_L g_R r₀ : ℕ,
      A = g_L * g_R * h₀ ^ 2 ∧
      I = g_L * g_R * u₀ ^ 2 ∧
      m_L = g_L * h₀ ∧
      m_R = g_R * u₀ ∧
      m = m_L * m_R ∧
      Nat.Coprime m_L m_R ∧
      r₀ ∈ m.primeFactors ∧
      q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀)) ∧
      (r₀ ∣ m_R → ¬ r₀ ∣ g_R →
        let e₀ := m.factorization r₀
        let U₀ := u₀ / r₀ ^ e₀
        let M_R := ordCompl[r₀] m_R
        let c₀ := sigma 1 (r₀ ^ (2 * e₀)) / q
        let V_R := (g_L * g_R * U₀ ^ 2) / c₀
        u₀ = r₀ ^ e₀ * U₀ ∧
        ¬ r₀ ∣ U₀ ∧
        ¬ r₀ ∣ g_L * g_R * U₀ ^ 2 ∧
        M_R = g_R * U₀ ∧
        ordCompl[r₀] m = m_L * M_R ∧
        Nat.Coprime M_R m_L ∧
        1 ≤ V_R ∧
        Odd V_R ∧
        c₀ * V_R = g_L * g_R * U₀ ^ 2 ∧
        sigma 1 (M_R ^ 2) * sigma 1 (m_L ^ 2) = r₀ ^ (2 * e₀) * V_R ∧
        Nat.Coprime (r₀ ^ (2 * e₀)) V_R ∧
        (∃ s ∈ (M_R * m_L).primeFactors,
          s ≠ r₀ ∧ s ≠ q ∧ (s ∣ M_R ∨ s ∣ m_L) ∧
          r₀ ∣ sigma 1 (s ^ (2 * m.factorization s)))) := by
  intro A I L R m_L m_R
  obtain ⟨h₀, u₀, g_L, g_R, r₀, hA_eq, hI_eq, hmL_eq, hmR_eq, hr₀_m, hq_dvd_r0, hpeel⟩ :=
    linear_euler_right_source_peeling_dichotomy ho hN hq hqm hform
  obtain ⟨_, _, hm_cop, hm_split, _, _, _, _, _, _, _, _, _, _⟩ :=
    linear_euler_lcm_gcd_canonical_coprime_split ho hN hq hqm hform
  refine ⟨h₀, u₀, g_L, g_R, r₀, hA_eq, hI_eq, hmL_eq, hmR_eq, hm_split, hm_cop, hr₀_m, hq_dvd_r0, ?_⟩
  intro hr0_mR hr0_not_gR e₀ U₀ M_R c₀ V_R
  obtain ⟨_, hmR_split, hcop_r0_MR, _, hprod_eq, hbranch⟩ := hpeel hr0_mR
  have hr0_not_gR_branch :
      r₀ ^ e₀ ∣ u₀ ∧
      Nat.Coprime r₀ A ∧
      M_R = g_R * U₀ ∧
      r₀ ^ (2 * e₀) ∣ sigma 1 (M_R ^ 2) * sigma 1 (m_L ^ 2) ∧
      c₀ ∣ g_L * g_R * U₀ ^ 2 := by
    rcases hbranch with ⟨hr0_gR, _⟩ | ⟨_, hr0_pow_u0, hcop_r0_A, hMR_eq, hr0_pow_dvd, hc0_dvd⟩
    · exact absurd hr0_gR hr0_not_gR
    · exact ⟨hr0_pow_u0, hcop_r0_A, hMR_eq, hr0_pow_dvd, hc0_dvd⟩
  rcases hr0_not_gR_branch with ⟨hr0_pow_u0, hcop_r0_A, hMR_eq, _, hc0_dvd⟩
  have hr0_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀_m
  have hr0_dvd_m : r₀ ∣ m := Nat.dvd_of_mem_primeFactors hr₀_m
  have hm_odd : Odd m :=
    ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  have hmL_eq' : m_L = g_L * h₀ := hmL_eq
  have hmR_eq' : m_R = g_R * u₀ := hmR_eq
  have hm_cop' : Nat.Coprime m_L m_R := hm_cop
  have hm_split' : m = m_L * m_R := hm_split
  have hmR_split' : m_R = r₀ ^ e₀ * M_R := hmR_split
  have hcop_r0_MR' : Nat.Coprime r₀ M_R := hcop_r0_MR
  have hcop_r0_A' : Nat.Coprime r₀ A := hcop_r0_A
  have hmL_odd : Odd m_L := hm_odd.of_dvd_nat ⟨m_R, hm_split'⟩
  have hmR_odd : Odd m_R := hm_odd.of_dvd_nat ⟨m_L, by rw [hm_split', mul_comm]⟩
  have hgL_odd : Odd g_L := hmL_odd.of_dvd_nat (hmL_eq' ▸ dvd_mul_right g_L h₀)
  have hgR_odd : Odd g_R := hmR_odd.of_dvd_nat (hmR_eq' ▸ dvd_mul_right g_R u₀)
  have hu0_odd : Odd u₀ := hmR_odd.of_dvd_nat (hmR_eq' ▸ dvd_mul_left u₀ g_R)
  have hu0_split : u₀ = r₀ ^ e₀ * U₀ := (Nat.mul_div_cancel' hr0_pow_u0).symm
  have hU0_odd : Odd U₀ := hu0_odd.of_dvd_nat ⟨r₀ ^ e₀, by rw [hu0_split, mul_comm]⟩
  have hrhs_odd : Odd (g_L * g_R * U₀ ^ 2) := (hgL_odd.mul hgR_odd).mul hU0_odd.pow
  have hr0_not_U0 : ¬ r₀ ∣ U₀ := by
    intro hd
    have hd_MR : r₀ ∣ M_R := by
      rw [hMR_eq]
      exact hd.trans (dvd_mul_left U₀ g_R)
    exact hr0_prime.not_dvd_one (hcop_r0_MR' ▸ Nat.dvd_gcd (dvd_refl r₀) hd_MR)
  have hr0_not_gL : ¬ r₀ ∣ g_L := by
    intro hd
    have hd_A : r₀ ∣ A := by
      change r₀ ∣ (q + 1) / 2
      rw [hA_eq]
      exact hd.trans ((dvd_mul_right g_L g_R).trans (dvd_mul_right _ (h₀ ^ 2)))
    exact hr0_prime.not_dvd_one (hcop_r0_A' ▸ Nat.dvd_gcd (dvd_refl r₀) hd_A)
  have hr0_not_rhs : ¬ r₀ ∣ g_L * g_R * U₀ ^ 2 := by
    intro hd
    rcases hr0_prime.dvd_mul.mp hd with hgg | hU2
    · rcases hr0_prime.dvd_mul.mp hgg with hgL | hgR
      · exact hr0_not_gL hgL
      · exact hr0_not_gR hgR
    · exact hr0_not_U0 (hr0_prime.dvd_of_dvd_pow hU2)
  have hordCompl_eq : ordCompl[r₀] m = m_L * M_R := by
    have hm_decomp : m = r₀ ^ e₀ * ordCompl[r₀] m := by
      have h := (Nat.ordProj_mul_ordCompl_eq_self m r₀).symm
      simpa [e₀] using h
    have hm_alt : m = r₀ ^ e₀ * (m_L * M_R) := by
      calc
        m = m_L * m_R := hm_split'
        _ = m_L * (r₀ ^ e₀ * M_R) := by rw [hmR_split']
        _ = r₀ ^ e₀ * (m_L * M_R) := by ring
    exact Nat.mul_left_cancel (pow_pos hr0_prime.pos e₀) (hm_decomp.symm.trans hm_alt)
  have hcop_MR_mL : Nat.Coprime M_R m_L := by
    have hMR_dvd_mR : M_R ∣ m_R := ⟨r₀ ^ e₀, by rw [hmR_split', mul_comm]⟩
    exact (hm_cop'.coprime_dvd_right hMR_dvd_mR).symm
  have hc0_VR_eq : c₀ * V_R = g_L * g_R * U₀ ^ 2 := Nat.mul_div_cancel' hc0_dvd
  have hVR_odd : Odd V_R := hrhs_odd.of_dvd_nat ⟨c₀, by rw [← hc0_VR_eq, mul_comm]⟩
  have hVR_ge1 : 1 ≤ V_R := hVR_odd.pos
  have hc0_pos : 0 < c₀ := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_mul] at hc0_VR_eq
    exact hrhs_odd.pos.ne' hc0_VR_eq.symm
  have hsig_eq : sigma 1 (M_R ^ 2) * sigma 1 (m_L ^ 2) = r₀ ^ (2 * e₀) * V_R := by
    apply Nat.mul_left_cancel hc0_pos
    calc
      c₀ * (sigma 1 (M_R ^ 2) * sigma 1 (m_L ^ 2))
          = c₀ * sigma 1 (M_R ^ 2) * sigma 1 (m_L ^ 2) := by ring
      _ = g_L * g_R * u₀ ^ 2 := hprod_eq
      _ = g_L * g_R * (r₀ ^ e₀ * U₀) ^ 2 := by rw [hu0_split]
      _ = (g_L * g_R * U₀ ^ 2) * r₀ ^ (2 * e₀) := by ring
      _ = (c₀ * V_R) * r₀ ^ (2 * e₀) := by rw [hc0_VR_eq]
      _ = c₀ * (r₀ ^ (2 * e₀) * V_R) := by ring
  have hr0_not_VR : ¬ r₀ ∣ V_R := fun hd =>
    hr0_not_rhs (hd.trans ⟨c₀, by rw [← hc0_VR_eq, mul_comm]⟩)
  have hcop_pow_VR : Nat.Coprime (r₀ ^ (2 * e₀)) V_R :=
    (hr0_prime.coprime_iff_not_dvd.mpr hr0_not_VR).pow_left (2 * e₀)
  refine ⟨hu0_split, hr0_not_U0, hr0_not_rhs, hMR_eq, hordCompl_eq, hcop_MR_mL,
    hVR_ge1, hVR_odd, hc0_VR_eq, hsig_eq, hcop_pow_VR, ?_⟩
  have he0_pos : 1 ≤ e₀ := (hr0_prime.dvd_iff_one_le_factorization hm0).mp hr0_dvd_m
  have hr0_dvd_pow : r₀ ∣ r₀ ^ (2 * e₀) := dvd_pow_self r₀ (by omega)
  have hr0_dvd_sig_prod : r₀ ∣ sigma 1 (M_R ^ 2) * sigma 1 (m_L ^ 2) :=
    hr0_dvd_pow.trans ⟨V_R, hsig_eq⟩
  have hcop_sq : Nat.Coprime (M_R ^ 2) (m_L ^ 2) := (hcop_MR_mL.pow_left 2).pow_right 2
  have hsig_sq_eq : sigma 1 ((M_R * m_L) ^ 2) = sigma 1 (M_R ^ 2) * sigma 1 (m_L ^ 2) := by
    rw [mul_pow, isMultiplicative_sigma.map_mul_of_coprime hcop_sq]
  have hMR_odd : Odd M_R := hmR_odd.of_dvd_nat ⟨r₀ ^ e₀, by rw [hmR_split', mul_comm]⟩
  have hprod_ne0 : M_R * m_L ≠ 0 := (hMR_odd.mul hmL_odd).pos.ne'
  have hsq_ne0 : (M_R * m_L) ^ 2 ≠ 0 := pow_ne_zero 2 hprod_ne0
  have hsig_factor :
      sigma 1 ((M_R * m_L) ^ 2) =
        ∏ s ∈ ((M_R * m_L) ^ 2).primeFactors, sigma 1 (ordProj[s] ((M_R * m_L) ^ 2)) := by
    rw [isMultiplicative_sigma.multiplicative_factorization (sigma 1) hsq_ne0]
    exact Finset.prod_congr ((M_R * m_L) ^ 2).support_factorization fun _ _ => rfl
  have hr0_dvd_finprod :
      r₀ ∣ ∏ s ∈ ((M_R * m_L) ^ 2).primeFactors, sigma 1 (ordProj[s] ((M_R * m_L) ^ 2)) := by
    rw [← hsig_factor, hsig_sq_eq]
    exact hr0_dvd_sig_prod
  obtain ⟨s, hs_mem_sq, hs_dvd_sig⟩ := (hr0_prime.prime.dvd_finsetProd_iff _).mp hr0_dvd_finprod
  have hs_mem : s ∈ (M_R * m_L).primeFactors := by
    rwa [Nat.primeFactors_pow (M_R * m_L) (by decide : 2 ≠ 0)] at hs_mem_sq
  have hs_prime : s.Prime := Nat.prime_of_mem_primeFactors hs_mem
  have hs_dvd_prod : s ∣ M_R * m_L := Nat.dvd_of_mem_primeFactors hs_mem
  have hr0_not_mL : ¬ r₀ ∣ m_L := fun hd =>
    hr0_prime.not_dvd_one (hm_cop' ▸ Nat.dvd_gcd hd hr0_mR)
  have hr0_not_MR : ¬ r₀ ∣ M_R := fun hd =>
    hr0_prime.not_dvd_one (hcop_r0_MR' ▸ Nat.dvd_gcd (dvd_refl r₀) hd)
  have hs_ne_r0 : s ≠ r₀ := by
    intro hsr0
    subst hsr0
    rcases hr0_prime.dvd_mul.mp hs_dvd_prod with hMR | hmL
    · exact hr0_not_MR hMR
    · exact hr0_not_mL hmL
  have hm_prod_eq : m = r₀ ^ e₀ * (M_R * m_L) := by
    calc
      m = r₀ ^ e₀ * ordCompl[r₀] m := by
        have h := (Nat.ordProj_mul_ordCompl_eq_self m r₀).symm
        simpa [e₀] using h
      _ = r₀ ^ e₀ * (m_L * M_R) := by rw [hordCompl_eq]
      _ = r₀ ^ e₀ * (M_R * m_L) := by ring
  have hs_dvd_m : s ∣ m := hs_dvd_prod.trans ⟨r₀ ^ e₀, by rw [hm_prod_eq, mul_comm]⟩
  have hs_ne_q : s ≠ q := fun hsq => hqm (hsq ▸ hs_dvd_m)
  have hs_branch : s ∣ M_R ∨ s ∣ m_L := hs_prime.dvd_mul.mp hs_dvd_prod
  have hs_not_pow : ¬ s ∣ r₀ ^ e₀ := fun hd =>
    hs_ne_r0 ((Nat.prime_dvd_prime_iff_eq hs_prime hr0_prime).mp (hs_prime.dvd_of_dvd_pow hd))
  have hm_fact_s : m.factorization s = (M_R * m_L).factorization s := by
    rw [hm_prod_eq, Nat.factorization_mul (pow_ne_zero e₀ hr0_prime.ne_zero) hprod_ne0,
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hs_not_pow, zero_add]
  have hordProj_eq : ordProj[s] ((M_R * m_L) ^ 2) = s ^ (2 * m.factorization s) := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hm_fact_s]
  rw [hordProj_eq] at hs_dvd_sig
  exact ⟨s, hs_mem, hs_ne_r0, hs_ne_q, hs_branch, hs_dvd_sig⟩

/-- **2. Universal `r₀ ≥ 61` and `c₀.minFac ≥ 61` Pinch**:
On any sixth-power-free odd perfect number `N = q * m ^ 2`, proves unconditionally that the unique
`q`-source `r₀` satisfies `61 ≤ r₀` and `3721 ≤ r₀ ^ (2 * e₀)`, its cofactor
`c₀ := sigma 1 (r₀ ^ (2 * e₀)) / q` satisfies `c₀ = 1 ∨ (61 ≤ c₀.minFac ∧ 61 ≤ c₀)`, and in the
non-`g_R` right branch (`r₀ ∣ m_R`, `¬ r₀ ∣ g_R`) with `1 < c₀` we have
`61 ≤ g_L * g_R * (u₀ / r₀ ^ e₀)`. -/
theorem sixth_power_free_universal_r0_and_c0_minFac_pinch {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    ∃ m h₀ u₀ g_L g_R r₀ : ℕ,
      Odd m ∧ ¬ q ∣ m ∧ N = q * m ^ 2 ∧
      r₀ ∈ m.primeFactors ∧
      q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀)) ∧
      (q + 1) / 2 = g_L * g_R * h₀ ^ 2 ∧
      componentIndex N q = g_L * g_R * u₀ ^ 2 ∧
      let e₀ := m.factorization r₀
      let c₀ := sigma 1 (r₀ ^ (2 * e₀)) / q
      let m_R := Nat.gcd m (Nat.factorizationLCMRight ((q + 1) / 2) (componentIndex N q))
      61 ≤ r₀ ∧
      3721 ≤ r₀ ^ (2 * e₀) ∧
      (c₀ = 1 ∨ (61 ≤ c₀.minFac ∧ 61 ≤ c₀)) ∧
      (r₀ ∣ m_R → ¬ r₀ ∣ g_R → 1 < c₀ → 61 ≤ g_L * g_R * (u₀ / r₀ ^ e₀)) := by
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  obtain ⟨m, r₀, hm_odd, hqm, hform, hr₀_m, hmul_c0, hnq_c0, hc0_odd, _, hc0_dvd_B,
      hiq_eq, huniq, hm_dich⟩ :=
    sixth_power_free_unique_q_source_mirror_dichotomy ho hN hq hq4 he hev hfree
  obtain ⟨h₀, u₀, g_L, g_R, r₁, hA_eq, hI_eq, _, _, hr₁_m, hq_dvd_r1, hpeel⟩ :=
    linear_euler_right_source_peeling_dichotomy ho hN hq_prime hqm hform
  have hr1_eq : r₁ = r₀ := huniq r₁ hr₁_m hq_dvd_r1
  rw [hr1_eq] at hq_dvd_r1 hpeel
  have hq_dvd_r0 : q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀)) := hq_dvd_r1
  let e₀ := m.factorization r₀
  let c₀ := sigma 1 (r₀ ^ (2 * e₀)) / q
  let m_R := Nat.gcd m (Nat.factorizationLCMRight ((q + 1) / 2) (componentIndex N q))
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  have hr0_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀_m
  have hr0_dvd_m : r₀ ∣ m := Nat.dvd_of_mem_primeFactors hr₀_m
  have hr0_dvd_N : r₀ ∣ N :=
    hform ▸ hr0_dvd_m.trans ((dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
  have hr0_N : r₀ ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hr0_prime, hr0_dvd_N, hN.2.ne'⟩
  have hr0_ge53 : 53 ≤ r₀ := sixth_power_free_min_prime_ge_53 ho hN hfree hr0_N
  have hr0_mod : r₀ % 5 = 1 ∨ r₀ % 3 = 1 := by
    rcases hm_dich with ⟨_, hmod5, _⟩ | ⟨_, hmod3, _⟩
    · exact Or.inl hmod5
    · exact Or.inr hmod3
  have hr0_ge61 : 61 ≤ r₀ := prime_ge_61_of_ge_53_mod hr0_prime hr0_ge53 hr0_mod
  have he0_pos : 1 ≤ e₀ := (hr0_prime.dvd_iff_one_le_factorization hm0).mp hr0_dvd_m
  have hr0_pow_ge : 3721 ≤ r₀ ^ (2 * e₀) := by
    have h1 : 61 ^ 2 ≤ r₀ ^ 2 := Nat.pow_le_pow_left hr0_ge61 2
    have h2 : r₀ ^ 2 ≤ r₀ ^ (2 * e₀) := Nat.pow_le_pow_right hr0_prime.pos (by omega)
    omega
  have hc0_or : c₀ = 1 ∨ (61 ≤ c₀.minFac ∧ 61 ≤ c₀) := by
    by_cases hc0_1 : c₀ = 1
    · exact Or.inl hc0_1
    · right
      let t := c₀.minFac
      have ht_prime : t.Prime := Nat.minFac_prime hc0_1
      have ht_dvd_c0 : t ∣ c₀ := Nat.minFac_dvd c₀
      have ht_ne_q : t ≠ q := fun htq => hnq_c0 (by
        change q ∣ c₀
        conv_lhs => rw [← htq]
        exact ht_dvd_c0)
      have ht_dvd_B : t ∣ ordCompl[r₀] (m ^ 2) := ht_dvd_c0.trans hc0_dvd_B
      have ht_dvd_m2 : t ∣ m ^ 2 := ht_dvd_B.trans (Nat.ordCompl_dvd (m ^ 2) r₀)
      have ht_dvd_N : t ∣ N := hform ▸ ht_dvd_m2.trans (dvd_mul_left (m ^ 2) q)
      have ht_N : t ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨ht_prime, ht_dvd_N, hN.2.ne'⟩
      have ht_ge53 : 53 ≤ t := sixth_power_free_min_prime_ge_53 ho hN hfree ht_N
      have hI_pos : 0 < componentIndex N q := (componentIndex_mul_eq_two_mul hN hq).2
      have hc0_dvd_I : c₀ ∣ componentIndex N q := by
        have hcomp_eq : componentIndex N q = sigma 1 (m ^ 2) / q := by
          have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
          have hq_ndvd_m2 : ¬ q ∣ m ^ 2 := fun h => hqm (hq_prime.dvd_of_dvd_pow h)
          have hfact_q : N.factorization q = 1 := by
            rw [hform, Nat.factorization_mul hq_prime.ne_zero hm20, Finsupp.add_apply,
              hq_prime.factorization_self, Nat.factorization_eq_zero_of_not_dvd hq_ndvd_m2, add_zero]
          have hord : ordProj[q] N = q := by rw [hfact_q, pow_one]
          have hcompl : ordCompl[q] N = m ^ 2 := by
            rw [hfact_q, pow_one, hform, Nat.mul_div_cancel_left _ hq_prime.pos]
          rw [componentIndex, hcompl, hord]
        rw [hcomp_eq]
        exact ⟨sigma 1 (ordCompl[r₀] (m ^ 2)), hiq_eq⟩
      have ht_dvd_I : t ∣ componentIndex N q := ht_dvd_c0.trans hc0_dvd_I
      have ht_I : t ∈ (componentIndex N q).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨ht_prime, ht_dvd_I, hI_pos.ne'⟩
      have ht_mod : t % 5 = 1 ∨ t % 3 = 1 :=
        (sixth_power_free_euler_index_drop_and_support ho hN hq hq4 he hev hfree).2 t ht_I
      have ht_ge61 : 61 ≤ t := prime_ge_61_of_ge_53_mod ht_prime ht_ge53 ht_mod
      have hc0_pos : 0 < c₀ := hc0_odd.pos
      have ht_le_c0 : t ≤ c₀ := Nat.le_of_dvd hc0_pos ht_dvd_c0
      exact ⟨ht_ge61, le_trans ht_ge61 ht_le_c0⟩
  refine ⟨m, h₀, u₀, g_L, g_R, r₀, hm_odd, hqm, hform, hr₀_m, hq_dvd_r0, hA_eq, hI_eq,
    hr0_ge61, hr0_pow_ge, hc0_or, ?_⟩
  intro hr0_mR hr0_not_gR hc0_gt1
  have hc0_gt1' : 1 < c₀ := hc0_gt1
  have hc0_ne1 : c₀ ≠ 1 := ne_of_gt hc0_gt1'
  have ht_ge61 : 61 ≤ c₀.minFac := (hc0_or.resolve_left hc0_ne1).1
  have ht_prime : c₀.minFac.Prime := Nat.minFac_prime hc0_ne1
  have ht_dvd_c0 : c₀.minFac ∣ c₀ := Nat.minFac_dvd c₀
  obtain ⟨_, _, _, _, _, hbranch⟩ := hpeel hr0_mR
  have hc0_dvd_rhs : c₀ ∣ g_L * g_R * (u₀ / r₀ ^ e₀) ^ 2 := by
    rcases hbranch with ⟨hr0_gR, _⟩ | ⟨_, _, _, _, _, hc0_dvd⟩
    · exact absurd hr0_gR hr0_not_gR
    · exact hc0_dvd
  have ht_dvd_rhs : c₀.minFac ∣ g_L * g_R * (u₀ / r₀ ^ e₀) ^ 2 := ht_dvd_c0.trans hc0_dvd_rhs
  have ht_dvd_lin : c₀.minFac ∣ g_L * g_R * (u₀ / r₀ ^ e₀) := by
    rcases ht_prime.dvd_mul.mp ht_dvd_rhs with hgg | hU2
    · exact hgg.trans (dvd_mul_right _ _)
    · exact (ht_prime.dvd_of_dvd_pow hU2).trans (dvd_mul_left _ _)
  have hI_pos : 0 < componentIndex N q := (componentIndex_mul_eq_two_mul hN hq).2
  have hgLgR_pos : 0 < g_L * g_R := Nat.pos_of_ne_zero fun h0 =>
    hI_pos.ne' (by rw [hI_eq, h0, zero_mul])
  have hu0_ne0 : u₀ ≠ 0 := fun h0 =>
    hI_pos.ne' (by rw [hI_eq, h0, zero_pow (by decide : 2 ≠ 0), mul_zero])
  have hr0_pow_u0 : r₀ ^ e₀ ∣ u₀ := by
    rcases hbranch with ⟨hr0_gR, _⟩ | ⟨_, hr0_pow_u0, _⟩
    · exact absurd hr0_gR hr0_not_gR
    · exact hr0_pow_u0
  have hU0_pos : 0 < u₀ / r₀ ^ e₀ := Nat.pos_of_ne_zero fun h0 => by
    have hu0_split : r₀ ^ e₀ * (u₀ / r₀ ^ e₀) = u₀ := Nat.mul_div_cancel' hr0_pow_u0
    rw [h0, mul_zero] at hu0_split
    exact hu0_ne0 hu0_split.symm
  have hlin_pos : 0 < g_L * g_R * (u₀ / r₀ ^ e₀) := mul_pos hgLgR_pos hU0_pos
  exact le_trans ht_ge61 (Nat.le_of_dvd hlin_pos ht_dvd_lin)

end OddPerfect
