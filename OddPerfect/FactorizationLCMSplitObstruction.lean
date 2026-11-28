module

public import OddPerfect.LinearEulerSquareDescent
public import OddPerfect.LinearEulerUnitaryHalfSuccPeeling
public import Mathlib.Data.Nat.Factorization.LCM
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Factorization LCM Split Obstruction

Establishes the universal `gcd` / `factorizationLCMLeft` / `factorizationLCMRight` square
parametrization of `((q + 1) / 2, componentIndex N q)` on the linear Euler branch `N = q * m ^ 2`,
together with the prime-collision profile when `¬ Nat.Coprime ((q + 1) / 2) (componentIndex N q)`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma componentIndex_linear_euler_eq' {N q m : ℕ}
    (ho : Odd N) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2) :
    ordProj[q] N = q ∧
    ordCompl[q] N = m ^ 2 ∧
    componentIndex N q = sigma 1 (m ^ 2) / q := by
  have hm_odd : Odd m :=
    ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
  have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm_odd.pos.ne'
  have hq_ndvd_m2 : ¬ q ∣ m ^ 2 := fun h => hqm (hq.dvd_of_dvd_pow h)
  have hfact_q : N.factorization q = 1 := by
    rw [hform, Nat.factorization_mul hq.ne_zero hm20, Finsupp.add_apply,
      hq.factorization_self, Nat.factorization_eq_zero_of_not_dvd hq_ndvd_m2, add_zero]
  have hord : ordProj[q] N = q := by rw [hfact_q, pow_one]
  have hcompl : ordCompl[q] N = m ^ 2 := by
    rw [hfact_q, pow_one, hform, Nat.mul_div_cancel_left _ hq.pos]
  exact ⟨hord, hcompl, by rw [componentIndex, hcompl, hord]⟩

private lemma isSquare_of_coprime_mul_eq_sq' {a b m : ℕ}
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
  exact ⟨Nat.isSquare_iff_even_factorization.mpr fun p hp => (h_even_both p hp).1,
    Nat.isSquare_iff_even_factorization.mpr fun p hp => (h_even_both p hp).2⟩

private lemma q_dvd_sigma_sq' {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2) :
    q ∣ sigma 1 (m ^ 2) := by
  have hq_cop_m2 : q.Coprime (m ^ 2) := (hq.coprime_iff_not_dvd.mpr hqm).pow_right 2
  have hsig_N : sigma 1 N = 2 * N :=
    (sigma_one_apply N).trans ((Nat.perfect_iff_sum_divisors_eq_two_mul ho.pos).mp hN)
  have hsig_q : sigma 1 q = q + 1 := by
    rw [← pow_one q, sigma_one_apply_prime_pow hq]
    simp [Finset.sum_range_succ]
    ring
  have hsig_bal : (q + 1) * sigma 1 (m ^ 2) = 2 * (q * m ^ 2) := by
    calc
      (q + 1) * sigma 1 (m ^ 2)
          = sigma 1 q * sigma 1 (m ^ 2) := by rw [hsig_q]
      _ = sigma 1 (q * m ^ 2) := (isMultiplicative_sigma.map_mul_of_coprime hq_cop_m2).symm
      _ = sigma 1 N := by rw [← hform]
      _ = 2 * N := hsig_N
      _ = 2 * (q * m ^ 2) := by rw [hform]
  have hq_cop_q1 : q.Coprime (q + 1) :=
    hq.coprime_iff_not_dvd.mpr (fun hd => hq.not_dvd_one ((Nat.dvd_add_right (dvd_refl q)).mp hd))
  exact hq_cop_q1.dvd_of_dvd_mul_left ⟨2 * m ^ 2, by rw [hsig_bal]; ring⟩

/-- **1. Universal Half-Successor and Index GCD/LCM Square Parametrization**:
For any linear Euler odd perfect number `N = q * m ^ 2`, letting `A := (q + 1) / 2`,
`I := componentIndex N q`, `g := Nat.gcd A I`, `L := Nat.factorizationLCMLeft A I`, and
`R := Nat.factorizationLCMRight A I`, proves `Odd g`, `g ∣ m`, coprime LCM factorization
`L * R = Nat.lcm A I`, and coprime odd `h₀, u₀ ≥ 1` with `A = g * h₀ ^ 2`, `I = g * u₀ ^ 2`,
`m = g * h₀ * u₀`, `q = 2 * g * h₀ ^ 2 - 1`, `L * R = g * h₀ ^ 2 * u₀ ^ 2`, and
`sigma 1 ((g * h₀ * u₀) ^ 2) = g * (2 * g * h₀ ^ 2 - 1) * u₀ ^ 2`. -/
theorem universal_half_succ_index_gcd_square_parametrization {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2) :
    let A := (q + 1) / 2
    let I := componentIndex N q
    let g := Nat.gcd A I
    let L := Nat.factorizationLCMLeft A I
    let R := Nat.factorizationLCMRight A I
    Odd g ∧ 1 ≤ g ∧ g ∣ m ∧
    Nat.Coprime L R ∧ L ∣ A ∧ R ∣ I ∧ L * R = Nat.lcm A I ∧
    ∃ h₀ u₀ : ℕ,
      Odd h₀ ∧ Odd u₀ ∧ 1 ≤ h₀ ∧ 1 ≤ u₀ ∧
      Nat.Coprime h₀ u₀ ∧
      A = g * h₀ ^ 2 ∧
      I = g * u₀ ^ 2 ∧
      m = g * h₀ * u₀ ∧
      q = 2 * g * h₀ ^ 2 - 1 ∧
      L * R = g * h₀ ^ 2 * u₀ ^ 2 ∧
      sigma 1 ((g * h₀ * u₀) ^ 2) = g * (2 * g * h₀ ^ 2 - 1) * u₀ ^ 2 ∧
      (g = 1 ↔ Nat.Coprime A I) := by
  intro A I g L R
  have hq_odd : Odd q := ho.of_dvd_nat (hform ▸ dvd_mul_right q (m ^ 2))
  have hm_odd : Odd m :=
    ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
  have hm2_odd : Odd (m ^ 2) := hm_odd.pow
  obtain ⟨_, _, hci_eq⟩ := componentIndex_linear_euler_eq' ho hq hqm hform
  obtain ⟨h_half_mul, _, _⟩ := linear_euler_half_succ_mul_index_and_deficient_square ho hN hq hqm hform
  have hAI : A * I = m ^ 2 := by
    dsimp [A, I]
    rw [hci_eq]
    exact h_half_mul
  have hA_odd : Odd A := hm2_odd.of_dvd_nat ⟨I, hAI.symm⟩
  have hI_odd : Odd I := hm2_odd.of_dvd_nat ⟨A, by rw [← hAI, mul_comm]⟩
  have hA0 : A ≠ 0 := hA_odd.pos.ne'
  have hI0 : I ≠ 0 := hI_odd.pos.ne'
  have hg_dvd_A : g ∣ A := Nat.gcd_dvd_left A I
  have hg_dvd_I : g ∣ I := Nat.gcd_dvd_right A I
  have hg_odd : Odd g := hA_odd.of_dvd_nat hg_dvd_A
  have hg_pos : 0 < g := hg_odd.pos
  have hg_ge1 : 1 ≤ g := hg_pos
  have hLR_cop : Nat.Coprime L R := Nat.coprime_factorizationLCMLeft_factorizationLCMRight A I
  have hL_dvd : L ∣ A := Nat.factorizationLCMLeft_dvd_left A I
  have hR_dvd : R ∣ I := Nat.factorizationLCMRight_dvd_right A I
  have hLR_lcm : L * R = Nat.lcm A I := Nat.factorizationLCMLeft_mul_factorizationLCMRight hA0 hI0
  let A' := A / g
  let I' := I / g
  have hA_eq : A = g * A' := (Nat.mul_div_cancel' hg_dvd_A).symm
  have hI_eq : I = g * I' := (Nat.mul_div_cancel' hg_dvd_I).symm
  have hcop' : Nat.Coprime A' I' := Nat.coprime_div_gcd_div_gcd hg_pos
  have hg2_mul : g ^ 2 * (A' * I') = m ^ 2 := by
    calc
      g ^ 2 * (A' * I') = (g * A') * (g * I') := by ring
      _ = A * I := by rw [← hA_eq, ← hI_eq]
      _ = m ^ 2 := hAI
  have hg_dvd_m : g ∣ m :=
    (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp ⟨A' * I', hg2_mul.symm⟩
  let m' := m / g
  have hm_eq : m = g * m' := (Nat.mul_div_cancel' hg_dvd_m).symm
  have hm'_odd : Odd m' := hm_odd.of_dvd_nat ⟨g, by rw [hm_eq, mul_comm]⟩
  have hm'0 : m' ≠ 0 := hm'_odd.pos.ne'
  have hAI' : A' * I' = m' ^ 2 := by
    apply Nat.mul_left_cancel (pow_pos hg_pos 2)
    calc
      g ^ 2 * (A' * I') = m ^ 2 := hg2_mul
      _ = (g * m') ^ 2 := by rw [hm_eq]
      _ = g ^ 2 * m' ^ 2 := by ring
  obtain ⟨⟨h₀, hh₀⟩, ⟨u₀, hu₀⟩⟩ := isSquare_of_coprime_mul_eq_sq' hm'0 hcop' hAI'
  have hA'_sq : A' = h₀ ^ 2 := by rw [hh₀, pow_two]
  have hI'_sq : I' = u₀ ^ 2 := by rw [hu₀, pow_two]
  have hA'_odd : Odd A' := hA_odd.of_dvd_nat ⟨g, by rw [hA_eq, mul_comm]⟩
  have hI'_odd : Odd I' := hI_odd.of_dvd_nat ⟨g, by rw [hI_eq, mul_comm]⟩
  have hh0_odd : Odd h₀ := hA'_odd.of_dvd_nat ⟨h₀, hh₀⟩
  have hu0_odd : Odd u₀ := hI'_odd.of_dvd_nat ⟨u₀, hu₀⟩
  have hh0_ge1 : 1 ≤ h₀ := hh0_odd.pos
  have hu0_ge1 : 1 ≤ u₀ := hu0_odd.pos
  have hcop_h0u0 : Nat.Coprime h₀ u₀ := by
    have h1 : Nat.Coprime (h₀ ^ 2) (u₀ ^ 2) := by rwa [← hA'_sq, ← hI'_sq]
    exact (Nat.coprime_pow_left_iff (by decide : 0 < 2) h₀ _).mp
      ((Nat.coprime_pow_right_iff (by decide : 0 < 2) _ u₀).mp h1)
  have hA_h0 : A = g * h₀ ^ 2 := by rw [hA_eq, hA'_sq]
  have hI_u0 : I = g * u₀ ^ 2 := by rw [hI_eq, hI'_sq]
  have hm'_eq : h₀ * u₀ = m' := by
    apply Nat.pow_left_injective (by decide : 2 ≠ 0)
    calc
      (h₀ * u₀) ^ 2 = h₀ ^ 2 * u₀ ^ 2 := by ring
      _ = A' * I' := by rw [hA'_sq, hI'_sq]
      _ = m' ^ 2 := hAI'
  have hm_gh0u0 : m = g * h₀ * u₀ := by
    calc
      m = g * m' := hm_eq
      _ = g * (h₀ * u₀) := by rw [hm'_eq]
      _ = g * h₀ * u₀ := by ring
  have hq1_even : q + 1 = 2 * A := by
    dsimp [A]
    have := Nat.odd_iff.mp hq_odd
    omega
  have hq_eq : q = 2 * g * h₀ ^ 2 - 1 := by
    have h2 : q + 1 = 2 * g * h₀ ^ 2 := by
      rw [hq1_even, hA_h0]
      ring
    omega
  have hLR_eq : L * R = g * h₀ ^ 2 * u₀ ^ 2 := by
    apply Nat.mul_left_cancel hg_pos
    calc
      g * (L * R) = Nat.gcd A I * Nat.lcm A I := by rw [hLR_lcm]
      _ = A * I := Nat.gcd_mul_lcm A I
      _ = (g * h₀ ^ 2) * (g * u₀ ^ 2) := by rw [hA_h0, hI_u0]
      _ = g * (g * h₀ ^ 2 * u₀ ^ 2) := by ring
  have hq_dvd_sigm2 : q ∣ sigma 1 (m ^ 2) := q_dvd_sigma_sq' ho hN hq hqm hform
  have hsig_eq : sigma 1 ((g * h₀ * u₀) ^ 2) = g * (2 * g * h₀ ^ 2 - 1) * u₀ ^ 2 := by
    calc
      sigma 1 ((g * h₀ * u₀) ^ 2) = sigma 1 (m ^ 2) := by rw [← hm_gh0u0]
      _ = q * I := by dsimp [I]; rw [hci_eq]; exact (Nat.mul_div_cancel' hq_dvd_sigm2).symm
      _ = (2 * g * h₀ ^ 2 - 1) * (g * u₀ ^ 2) := by rw [hq_eq, hI_u0]
      _ = g * (2 * g * h₀ ^ 2 - 1) * u₀ ^ 2 := by ring
  refine ⟨hg_odd, hg_ge1, hg_dvd_m, hLR_cop, hL_dvd, hR_dvd, hLR_lcm, ?_⟩
  refine ⟨h₀, u₀, hh0_odd, hu0_odd, hh0_ge1, hu0_ge1, hcop_h0u0, hA_h0, hI_u0, hm_gh0u0, hq_eq,
    hLR_eq, hsig_eq, Iff.rfl⟩

/-- **2. Non-Coprime Half-Successor & Index GCD Prime Collision Profile**:
When `¬ Nat.Coprime ((q + 1) / 2) (componentIndex N q)`, `g := Nat.gcd ((q + 1) / 2) (componentIndex N q)`
satisfies `3 ≤ g`, and every prime factor `s` of `g` is an odd prime dividing `(q + 1) / 2`,
`componentIndex N q`, and `m`, and collides with some distinct prime component `p ∈ m.primeFactors`
(`p ≠ s`) via `s ∣ sigma 1 (p ^ (2 * m.factorization p))`. -/
theorem noncoprime_half_succ_gcd_prime_collision_profile {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hncop : ¬ Nat.Coprime ((q + 1) / 2) (componentIndex N q)) :
    let g := Nat.gcd ((q + 1) / 2) (componentIndex N q)
    3 ≤ g ∧
    ∀ s ∈ g.primeFactors,
      s.Prime ∧ Odd s ∧ 2 * s ∣ q + 1 ∧ s ∣ componentIndex N q ∧ s ∣ m ∧
      ∃ p ∈ m.primeFactors, p ≠ s ∧ s ∣ sigma 1 (p ^ (2 * m.factorization p)) := by
  intro g
  obtain ⟨hg_odd, _, hg_dvd_m, _, _, _, _, _⟩ :=
    universal_half_succ_index_gcd_square_parametrization ho hN hq hqm hform
  have hg_ne1 : g ≠ 1 := hncop
  have hg_ge3 : 3 ≤ g := by
    obtain ⟨k, hk⟩ := hg_odd
    omega
  refine ⟨hg_ge3, ?_⟩
  have hq_odd : Odd q := ho.of_dvd_nat (hform ▸ dvd_mul_right q (m ^ 2))
  have hm_odd : Odd m :=
    ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  obtain ⟨_, _, hci_eq⟩ := componentIndex_linear_euler_eq' ho hq hqm hform
  have hq_dvd_sigm2 : q ∣ sigma 1 (m ^ 2) := q_dvd_sigma_sq' ho hN hq hqm hform
  have hsigm2_eq : sigma 1 (m ^ 2) = q * componentIndex N q := by
    rw [hci_eq]
    exact (Nat.mul_div_cancel' hq_dvd_sigm2).symm
  have hsigm2_prod :
      sigma 1 (m ^ 2) = ∏ p ∈ m.primeFactors, sigma 1 (p ^ (2 * m.factorization p)) := by
    rw [isMultiplicative_sigma.multiplicative_factorization (sigma 1) hm20]
    refine Finset.prod_congr
      ((m ^ 2).support_factorization.trans (Nat.primeFactors_pow m (by decide : 2 ≠ 0)))
      fun p _ => ?_
    rw [pow_two, Nat.factorization_mul hm0 hm0, Finsupp.add_apply, ← two_mul]
  intro s hs
  have hs_prime : s.Prime := Nat.prime_of_mem_primeFactors hs
  have hs_dvd_g : s ∣ g := Nat.dvd_of_mem_primeFactors hs
  have hs_odd : Odd s := hg_odd.of_dvd_nat hs_dvd_g
  have hs_half : s ∣ (q + 1) / 2 := hs_dvd_g.trans (Nat.gcd_dvd_left _ _)
  have hq1_even : q + 1 = 2 * ((q + 1) / 2) := by
    have := Nat.odd_iff.mp hq_odd
    omega
  have hs_2_q1 : 2 * s ∣ q + 1 := by
    rw [hq1_even]
    exact Nat.mul_dvd_mul_left 2 hs_half
  have hs_ci : s ∣ componentIndex N q := hs_dvd_g.trans (Nat.gcd_dvd_right _ _)
  have hs_m : s ∣ m := hs_dvd_g.trans hg_dvd_m
  have hs_sigm2 : s ∣ sigma 1 (m ^ 2) := by
    rw [hsigm2_eq]
    exact hs_ci.trans (dvd_mul_left _ _)
  obtain ⟨p, hp_mem, hs_dvd_p⟩ := by
    rw [hsigm2_prod] at hs_sigm2
    exact (hs_prime.prime.dvd_finsetProd_iff _).mp hs_sigm2
  have hp_ne_s : p ≠ s := by
    intro hps
    subst hps
    rw [Nat.dvd_iff_mod_eq_zero, sigma_prime_pow_mod_self hs_prime] at hs_dvd_p
    have := hs_prime.two_le
    omega
  exact ⟨hs_prime, hs_odd, hs_2_q1, hs_ci, hs_m, p, hp_mem, hp_ne_s, hs_dvd_p⟩

end OddPerfect
