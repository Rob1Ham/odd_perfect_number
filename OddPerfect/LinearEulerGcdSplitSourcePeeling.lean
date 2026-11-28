module

public import OddPerfect.LinearEulerNoncoprimeHalfSuccQuotientDuality
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Linear Euler GCD Split Source Peeling

Unconditionally establishes the fourth-power law on the right-side GCD block `g_R` and the
`ordCompl`-peeled right-branch dichotomy for the unique `q`-source `r₀` on any linear Euler odd
perfect number `N = q * m ^ 2`:

1. `OddPerfect.linear_euler_gR_fourth_power_law`:
   Every prime divisor `p ∈ g_R.primeFactors` satisfies `1 ≤ A.factorization p`,
   `A.factorization p + 2 ≤ I.factorization p`, `3 ≤ I.factorization p`, `2 ≤ m.factorization p`,
   `p ^ 4 ∣ N`, `2 * p ∣ q + 1`, and `p ≠ 3 → p ∈ largeSources N q`.
2. `OddPerfect.linear_euler_right_source_peeling_dichotomy`:
   Whenever the unique `q`-source `r₀` lies in `m_R = g_R * u₀`, peeling `r₀ ^ e₀` via
   `M_R := ordCompl[r₀] m_R` and `c₀ := sigma 1 (r₀ ^ (2 * e₀)) / q` gives
   `W_R = c₀ * sigma 1 (M_R ^ 2)` and `c₀ * sigma 1 (M_R ^ 2) * sigma 1 (m_L ^ 2) = g_L * g_R * u₀ ^ 2`,
   splitting into either `r₀ ∣ g_R` (triggering the fourth-power law above) or `¬ r₀ ∣ g_R`
   (forcing `r₀ ^ e₀ ∣ u₀`, `Nat.Coprime r₀ A`, `M_R = g_R * (u₀ / r₀ ^ e₀)`,
   `r₀ ^ (2 * e₀) ∣ sigma 1 (M_R ^ 2) * sigma 1 (m_L ^ 2)`, and `c₀ ∣ g_L * g_R * (u₀ / r₀ ^ e₀) ^ 2`).
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma gR_primeFactors_fourth_power_aux {N q m h₀ u₀ g_L g_R : ℕ}
    (ho : Odd N) (hN : N.Perfect) (_hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hh0_odd : Odd h₀) (hu0_odd : Odd u₀) (hgL_odd : Odd g_L) (hgR_odd : Odd g_R)
    (hcop_gLgR : Nat.Coprime g_L g_R) (hcop_gRh0 : Nat.Coprime g_R h₀)
    (hR_eq : Nat.factorizationLCMRight ((q + 1) / 2) (componentIndex N q) = g_R * u₀ ^ 2)
    (hA_eq : (q + 1) / 2 = g_L * g_R * h₀ ^ 2)
    (hI_eq : componentIndex N q = g_L * g_R * u₀ ^ 2)
    (hm_eq : m = g_L * g_R * h₀ * u₀) :
    let A := (q + 1) / 2
    let I := componentIndex N q
    ∀ p ∈ g_R.primeFactors,
      1 ≤ A.factorization p ∧
      A.factorization p + 2 ≤ I.factorization p ∧
      3 ≤ I.factorization p ∧
      2 ≤ m.factorization p ∧
      p ^ 4 ∣ N ∧
      2 * p ∣ q + 1 ∧
      (p ≠ 3 → p ∈ largeSources N q) := by
  intro A I p hp_mem
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  have hp_dvd_gR : p ∣ g_R := Nat.dvd_of_mem_primeFactors hp_mem
  have hgL0 : g_L ≠ 0 := hgL_odd.pos.ne'
  have hgR0 : g_R ≠ 0 := hgR_odd.pos.ne'
  have hh00 : h₀ ≠ 0 := hh0_odd.pos.ne'
  have hu00 : u₀ ≠ 0 := hu0_odd.pos.ne'
  have hA0 : A ≠ 0 := by
    change (q + 1) / 2 ≠ 0
    rw [hA_eq]
    exact mul_ne_zero (mul_ne_zero hgL0 hgR0) (pow_ne_zero 2 hh00)
  have hm0 : m ≠ 0 := by
    rw [hm_eq]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hgL0 hgR0) hh00) hu00
  have hq_odd : Odd q := ho.of_dvd_nat (hform ▸ dvd_mul_right q (m ^ 2))
  have hq1_eq : q + 1 = 2 * A := (Nat.mul_div_cancel' (hq_odd.add_odd odd_one).two_dvd).symm
  have hp_dvd_A : p ∣ A := by
    change p ∣ (q + 1) / 2
    rw [hA_eq]
    exact hp_dvd_gR.trans ((dvd_mul_left g_R g_L).trans (dvd_mul_right _ (h₀ ^ 2)))
  have hA_pos : 1 ≤ A.factorization p := (hp.dvd_iff_one_le_factorization hA0).mp hp_dvd_A
  have h2p_dvd : 2 * p ∣ q + 1 := by
    rw [hq1_eq]
    exact Nat.mul_dvd_mul_left 2 hp_dvd_A
  have hp_ndvd_gL : ¬ p ∣ g_L := fun hp_gL =>
    hp.not_dvd_one (hcop_gLgR ▸ Nat.dvd_gcd hp_gL hp_dvd_gR)
  have hp_ndvd_h0 : ¬ p ∣ h₀ := fun hp_h0 =>
    hp.not_dvd_one (hcop_gRh0 ▸ Nat.dvd_gcd hp_dvd_gR hp_h0)
  have hgL_zero : g_L.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hp_ndvd_gL
  have hh0_zero : h₀.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hp_ndvd_h0
  have hA_fact : A.factorization p = g_R.factorization p := by
    change ((q + 1) / 2).factorization p = g_R.factorization p
    rw [hA_eq, Nat.factorization_mul (mul_ne_zero hgL0 hgR0) (pow_ne_zero 2 hh00),
      Finsupp.add_apply, Nat.factorization_mul hgL0 hgR0, Finsupp.add_apply, hgL_zero, zero_add,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hh0_zero, mul_zero, add_zero]
  have hI_fact : I.factorization p = g_R.factorization p + 2 * u₀.factorization p := by
    change (componentIndex N q).factorization p = g_R.factorization p + 2 * u₀.factorization p
    rw [hI_eq, Nat.factorization_mul (mul_ne_zero hgL0 hgR0) (pow_ne_zero 2 hu00),
      Finsupp.add_apply, Nat.factorization_mul hgL0 hgR0, Finsupp.add_apply, hgL_zero, zero_add,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have hp_dvd_R : p ∣ Nat.factorizationLCMRight A I := by
    change p ∣ Nat.factorizationLCMRight ((q + 1) / 2) (componentIndex N q)
    rw [hR_eq]
    exact hp_dvd_gR.trans (dvd_mul_right g_R (u₀ ^ 2))
  have hA_lt_I_fact : A.factorization p < I.factorization p := by
    by_contra hle
    have hI_le_A : I.factorization p ≤ A.factorization p := not_lt.mp hle
    have hp_dvd_prod : p ∣ (Nat.lcm A I).factorization.prod fun r n =>
        if I.factorization r ≤ A.factorization r then 1 else r ^ n := hp_dvd_R
    rw [Finsupp.prod, hp.prime.dvd_finsetProd_iff] at hp_dvd_prod
    obtain ⟨r, hr_mem, hr_dvd⟩ := hp_dvd_prod
    have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr_mem
    by_cases hrp : r = p
    · subst hrp
      simp only [hI_le_A, ↓reduceIte] at hr_dvd
      exact hp.not_dvd_one hr_dvd
    · split_ifs at hr_dvd with hcond
      · exact hp.not_dvd_one hr_dvd
      · exact hrp ((Nat.prime_dvd_prime_iff_eq hp hr_prime).mp (hp.dvd_of_dvd_pow hr_dvd)).symm
  have hu0_pos : 1 ≤ u₀.factorization p := by omega
  have hA_add_2_le_I : A.factorization p + 2 ≤ I.factorization p := by omega
  have h3_le_I : 3 ≤ I.factorization p := by omega
  have hgR_pos : 1 ≤ g_R.factorization p := (hp.dvd_iff_one_le_factorization hgR0).mp hp_dvd_gR
  have hm_fact : m.factorization p = g_R.factorization p + u₀.factorization p := by
    rw [hm_eq, Nat.factorization_mul (mul_ne_zero (mul_ne_zero hgL0 hgR0) hh00) hu00,
      Finsupp.add_apply, Nat.factorization_mul (mul_ne_zero hgL0 hgR0) hh00,
      Finsupp.add_apply, Nat.factorization_mul hgL0 hgR0, Finsupp.add_apply,
      hgL_zero, zero_add, hh0_zero, add_zero]
  have hm_ge2 : 2 ≤ m.factorization p := by omega
  have hp2_dvd_m : p ^ 2 ∣ m := (hp.pow_dvd_iff_le_factorization hm0).mpr hm_ge2
  have hp4_dvd_N : p ^ 4 ∣ N := by
    have hpow : p ^ 4 ∣ m ^ 2 := by
      have h1 : (p ^ 2) ^ 2 ∣ m ^ 2 := pow_dvd_pow_of_dvd hp2_dvd_m 2
      rwa [← pow_mul] at h1
    exact hform ▸ hpow.trans (dvd_mul_left (m ^ 2) q)
  have hN_ge4 : 4 ≤ N.factorization p := (hp.pow_dvd_iff_le_factorization hN.2.ne').mp hp4_dvd_N
  have hp_dvd_m : p ∣ m := (hp.dvd_iff_one_le_factorization hm0).mpr (by omega)
  have hp_ne_q : p ≠ q := fun hpq => hqm (hpq ▸ hp_dvd_m)
  have hp_dvd_N : p ∣ N := hp_dvd_m.trans (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans
    (dvd_mul_left (m ^ 2) q))
  have hp_mem_N : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hp_dvd_N, hN.2.ne'⟩
  refine ⟨hA_pos, hA_add_2_le_I, h3_le_I, hm_ge2, hp4_dvd_N, h2p_dvd, fun hp3 => ?_⟩
  exact Finset.mem_filter.mpr ⟨hp_mem_N, hp3, hp_ne_q, hN_ge4⟩

/-- **1. `g_R` Fourth-Power Law**:
On any linear Euler odd perfect number `N = q * m ^ 2`, every prime divisor `p ∈ g_R.primeFactors`
of the right-side GCD factor `g_R` satisfies `1 ≤ A.factorization p`,
`A.factorization p + 2 ≤ I.factorization p`, `3 ≤ I.factorization p`, `2 ≤ m.factorization p`,
`p ^ 4 ∣ N`, `2 * p ∣ q + 1`, and `p ≠ 3 → p ∈ largeSources N q`. -/
theorem linear_euler_gR_fourth_power_law {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2) :
    let A := (q + 1) / 2
    let I := componentIndex N q
    let L := Nat.factorizationLCMLeft A I
    let R := Nat.factorizationLCMRight A I
    let m_R := Nat.gcd m R
    ∃ h₀ u₀ g_L g_R : ℕ,
      Nat.gcd A I = g_L * g_R ∧
      Nat.Coprime g_L g_R ∧
      Nat.Coprime g_L u₀ ∧
      Nat.Coprime g_R h₀ ∧
      Nat.Coprime h₀ u₀ ∧
      A = g_L * g_R * h₀ ^ 2 ∧
      I = g_L * g_R * u₀ ^ 2 ∧
      L = g_L * h₀ ^ 2 ∧
      R = g_R * u₀ ^ 2 ∧
      m_R = g_R * u₀ ∧
      (∀ p ∈ g_R.primeFactors,
        1 ≤ A.factorization p ∧
        A.factorization p + 2 ≤ I.factorization p ∧
        3 ≤ I.factorization p ∧
        2 ≤ m.factorization p ∧
        p ^ 4 ∣ N ∧
        2 * p ∣ q + 1 ∧
        (p ≠ 3 → p ∈ largeSources N q)) := by
  intro A I L R m_R
  obtain ⟨h₀, u₀, g_L, g_R, hh0_odd, hu0_odd, hgL_odd, hgR_odd, _, _, _, _, _,
    hcop_h0u0, hcop_gLgR, hcop_gLu0, hcop_gRh0, hg_eq, _, hmR_eq, hL_eq, hR_eq,
    hA_eq, hI_eq, hm_eq, _⟩ :=
    linear_euler_gcd_coprime_split_and_quotient_duality ho hN hq hqm hform
  refine ⟨h₀, u₀, g_L, g_R, hg_eq, hcop_gLgR, hcop_gLu0, hcop_gRh0, hcop_h0u0,
    hA_eq, hI_eq, hL_eq, hR_eq, hmR_eq, ?_⟩
  exact gR_primeFactors_fourth_power_aux ho hN hq hqm hform
    hh0_odd hu0_odd hgL_odd hgR_odd hcop_gLgR hcop_gRh0 hR_eq hA_eq hI_eq hm_eq

/-- **2. Right-Source `ordCompl` Peeling Dichotomy**:
On any linear Euler odd perfect number `N = q * m ^ 2`, whenever the unique `q`-source `r₀`
lies in `m_R = g_R * u₀`, peeling `r₀ ^ e₀` (`e₀ := m.factorization r₀`, `M_R := ordCompl[r₀] m_R`,
`c₀ := sigma 1 (r₀ ^ (2 * e₀)) / q`, `W_R := sigma 1 (m_R ^ 2) / q`) gives
`W_R = c₀ * sigma 1 (M_R ^ 2)` and `c₀ * sigma 1 (M_R ^ 2) * sigma 1 (m_L ^ 2) = g_L * g_R * u₀ ^ 2`,
and splits on `r₀ ∣ g_R`:
- if `r₀ ∣ g_R`, then `2 ≤ e₀`, `3 ≤ I.factorization r₀`, `r₀ ^ 4 ∣ N`, `2 * r₀ ∣ q + 1`, and
  `r₀ ≠ 3 → r₀ ∈ largeSources N q`;
- if `¬ r₀ ∣ g_R`, then `r₀ ^ e₀ ∣ u₀`, `Nat.Coprime r₀ A`, `M_R = g_R * (u₀ / r₀ ^ e₀)`,
  `r₀ ^ (2 * e₀) ∣ sigma 1 (M_R ^ 2) * sigma 1 (m_L ^ 2)`, and
  `c₀ ∣ g_L * g_R * (u₀ / r₀ ^ e₀) ^ 2`. -/
theorem linear_euler_right_source_peeling_dichotomy {N q m : ℕ}
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
      r₀ ∈ m.primeFactors ∧
      q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀)) ∧
      (r₀ ∣ m_R →
        let e₀ := m.factorization r₀
        let M_R := ordCompl[r₀] m_R
        let c₀ := sigma 1 (r₀ ^ (2 * e₀)) / q
        let W_R := sigma 1 (m_R ^ 2) / q
        m_R.factorization r₀ = e₀ ∧
        m_R = r₀ ^ e₀ * M_R ∧
        Nat.Coprime r₀ M_R ∧
        W_R = c₀ * sigma 1 (M_R ^ 2) ∧
        c₀ * sigma 1 (M_R ^ 2) * sigma 1 (m_L ^ 2) = g_L * g_R * u₀ ^ 2 ∧
        ((r₀ ∣ g_R ∧
            2 ≤ e₀ ∧
            3 ≤ I.factorization r₀ ∧
            r₀ ^ 4 ∣ N ∧
            2 * r₀ ∣ q + 1 ∧
            (r₀ ≠ 3 → r₀ ∈ largeSources N q)) ∨
         (¬ r₀ ∣ g_R ∧
            r₀ ^ e₀ ∣ u₀ ∧
            Nat.Coprime r₀ A ∧
            M_R = g_R * (u₀ / r₀ ^ e₀) ∧
            r₀ ^ (2 * e₀) ∣ sigma 1 (M_R ^ 2) * sigma 1 (m_L ^ 2) ∧
            c₀ ∣ g_L * g_R * (u₀ / r₀ ^ e₀) ^ 2))) := by
  intro A I L R m_L m_R
  obtain ⟨h₀, u₀, g_L, g_R, hh0_odd, hu0_odd, hgL_odd, hgR_odd, _, _, _, _, _,
    _, hcop_gLgR, _, hcop_gRh0, _, hmL_eq, hmR_eq, _, hR_eq,
    hA_eq, hI_eq, hm_eq, r₀, hr₀_m, hq_dvd_r0, hbranch, _⟩ :=
    linear_euler_gcd_coprime_split_and_quotient_duality ho hN hq hqm hform
  refine ⟨h₀, u₀, g_L, g_R, r₀, hA_eq, hI_eq, hmL_eq, hmR_eq, hr₀_m, hq_dvd_r0, ?_⟩
  intro hr0_mR e₀ M_R c₀ W_R
  have hRight : ¬ r₀ ∣ m_L ∧ W_R * sigma 1 (m_L ^ 2) = g_L * g_R * u₀ ^ 2 := by
    rcases hbranch with ⟨_, hr0_not_mR, _⟩ | ⟨_, hr0_not_mL, _, _, hWR_sigL, _⟩
    · exact absurd hr0_mR hr0_not_mR
    · exact ⟨hr0_not_mL, hWR_sigL⟩
  rcases hRight with ⟨hr0_not_mL, hWR_sigL⟩
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀_m
  have hmL_eq' : m_L = g_L * h₀ := hmL_eq
  have hmR_eq' : m_R = g_R * u₀ := hmR_eq
  have hmL0 : m_L ≠ 0 := by rw [hmL_eq']; exact (hgL_odd.mul hh0_odd).pos.ne'
  have hmR0 : m_R ≠ 0 := by rw [hmR_eq']; exact (hgR_odd.mul hu0_odd).pos.ne'
  have hm_split : m = m_L * m_R := by
    rw [hm_eq, hmL_eq', hmR_eq']
    ring
  have hmR_fact : m_R.factorization r₀ = e₀ := by
    dsimp [e₀]
    rw [hm_split, Nat.factorization_mul hmL0 hmR0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hr0_not_mL, zero_add]
  have hmR_eq_split : m_R = r₀ ^ e₀ * M_R := by
    have hsplit := (Nat.ordProj_mul_ordCompl_eq_self m_R r₀).symm
    change m_R = r₀ ^ (m_R.factorization r₀) * M_R at hsplit
    rwa [hmR_fact] at hsplit
  have hcop_r0_MR : Nat.Coprime r₀ M_R := Nat.coprime_ordCompl hr₀_prime hmR0
  have hsig_r0_eq : sigma 1 (r₀ ^ (2 * e₀)) = q * c₀ := (Nat.mul_div_cancel' hq_dvd_r0).symm
  have hsig_mR2 : sigma 1 (m_R ^ 2) = q * (c₀ * sigma 1 (M_R ^ 2)) := by
    have hmR2_eq : m_R ^ 2 = r₀ ^ (2 * e₀) * M_R ^ 2 := by
      conv_lhs => rw [hmR_eq_split]
      ring
    have hcop_sq : Nat.Coprime (r₀ ^ (2 * e₀)) (M_R ^ 2) :=
      (hcop_r0_MR.pow_left (2 * e₀)).pow_right 2
    rw [hmR2_eq, isMultiplicative_sigma.map_mul_of_coprime hcop_sq, hsig_r0_eq]
    ring
  have hWR_eq : W_R = c₀ * sigma 1 (M_R ^ 2) := by
    dsimp [W_R]
    rw [hsig_mR2, Nat.mul_div_cancel_left _ hq.pos]
  have hprod_eq : c₀ * sigma 1 (M_R ^ 2) * sigma 1 (m_L ^ 2) = g_L * g_R * u₀ ^ 2 := by
    rw [← hWR_eq]
    exact hWR_sigL
  refine ⟨hmR_fact, hmR_eq_split, hcop_r0_MR, hWR_eq, hprod_eq, ?_⟩
  by_cases hr0_gR : r₀ ∣ g_R
  · left
    have hr0_mem_gR : r₀ ∈ g_R.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hr₀_prime, hr0_gR, hgR_odd.pos.ne'⟩
    have hfourth := gR_primeFactors_fourth_power_aux ho hN hq hqm hform
      hh0_odd hu0_odd hgL_odd hgR_odd hcop_gLgR hcop_gRh0 hR_eq hA_eq hI_eq hm_eq r₀ hr0_mem_gR
    exact ⟨hr0_gR, hfourth.2.2.2.1, hfourth.2.2.1, hfourth.2.2.2.2.1,
      hfourth.2.2.2.2.2.1, hfourth.2.2.2.2.2.2⟩
  · right
    have hcop_pow_gR : Nat.Coprime (r₀ ^ e₀) g_R :=
      (hr₀_prime.coprime_iff_not_dvd.mpr hr0_gR).pow_left e₀
    have hr0_pow_dvd_mR : r₀ ^ e₀ ∣ m_R := ⟨M_R, hmR_eq_split⟩
    have hr0_pow_dvd_u0 : r₀ ^ e₀ ∣ u₀ :=
      hcop_pow_gR.dvd_of_dvd_mul_left (hmR_eq' ▸ hr0_pow_dvd_mR)
    have hr0_ndvd_gL : ¬ r₀ ∣ g_L := fun hd =>
      hr0_not_mL (hmL_eq' ▸ hd.trans (dvd_mul_right g_L h₀))
    have hr0_ndvd_h0 : ¬ r₀ ∣ h₀ := fun hd =>
      hr0_not_mL (hmL_eq' ▸ hd.trans (dvd_mul_left h₀ g_L))
    have hr0_ndvd_A : ¬ r₀ ∣ A := by
      intro hd
      change r₀ ∣ (q + 1) / 2 at hd
      rw [hA_eq] at hd
      rcases hr₀_prime.dvd_mul.mp hd with hgg | hh2
      · rcases hr₀_prime.dvd_mul.mp hgg with hgL | hgR
        · exact hr0_ndvd_gL hgL
        · exact hr0_gR hgR
      · exact hr0_ndvd_h0 (hr₀_prime.dvd_of_dvd_pow hh2)
    have hcop_r0_A : Nat.Coprime r₀ A := hr₀_prime.coprime_iff_not_dvd.mpr hr0_ndvd_A
    let U₀ := u₀ / r₀ ^ e₀
    have hu0_split : u₀ = r₀ ^ e₀ * U₀ := (Nat.mul_div_cancel' hr0_pow_dvd_u0).symm
    have hMR_eq : M_R = g_R * U₀ := by
      apply Nat.mul_left_cancel (pow_pos hr₀_prime.pos e₀)
      calc
        r₀ ^ e₀ * M_R = m_R := hmR_eq_split.symm
        _ = g_R * u₀ := hmR_eq'
        _ = g_R * (r₀ ^ e₀ * U₀) := by rw [hu0_split]
        _ = r₀ ^ e₀ * (g_R * U₀) := by ring
    have hbal : c₀ * (sigma 1 (M_R ^ 2) * sigma 1 (m_L ^ 2)) =
        (g_L * g_R * U₀ ^ 2) * r₀ ^ (2 * e₀) := by
      calc
        c₀ * (sigma 1 (M_R ^ 2) * sigma 1 (m_L ^ 2))
            = c₀ * sigma 1 (M_R ^ 2) * sigma 1 (m_L ^ 2) := by ring
        _ = g_L * g_R * u₀ ^ 2 := hprod_eq
        _ = g_L * g_R * (r₀ ^ e₀ * U₀) ^ 2 := by rw [hu0_split]
        _ = (g_L * g_R * U₀ ^ 2) * r₀ ^ (2 * e₀) := by ring
    have hcop_pow_c0 : Nat.Coprime (r₀ ^ (2 * e₀)) c₀ := by
      have hmod1 : sigma 1 (r₀ ^ (2 * e₀)) % r₀ = 1 :=
        sigma_prime_pow_mod_self hr₀_prime (2 * e₀)
      have hr0_ndvd_sig : ¬ r₀ ∣ sigma 1 (r₀ ^ (2 * e₀)) := by
        intro hd
        have hmod0 : sigma 1 (r₀ ^ (2 * e₀)) % r₀ = 0 := Nat.mod_eq_zero_of_dvd hd
        have hr0_gt1 : 1 < r₀ := hr₀_prime.one_lt
        omega
      have hr0_ndvd_c0 : ¬ r₀ ∣ c₀ := fun hd =>
        hr0_ndvd_sig (hd.trans ⟨q, by rw [hsig_r0_eq, mul_comm]⟩)
      exact (hr₀_prime.coprime_iff_not_dvd.mpr hr0_ndvd_c0).pow_left (2 * e₀)
    have hr0_pow_dvd_sig : r₀ ^ (2 * e₀) ∣ sigma 1 (M_R ^ 2) * sigma 1 (m_L ^ 2) :=
      hcop_pow_c0.dvd_of_dvd_mul_left ⟨g_L * g_R * U₀ ^ 2, by rw [hbal, mul_comm]⟩
    have hc0_dvd_rhs : c₀ ∣ g_L * g_R * U₀ ^ 2 :=
      hcop_pow_c0.symm.dvd_of_dvd_mul_right ⟨sigma 1 (M_R ^ 2) * sigma 1 (m_L ^ 2), hbal.symm⟩
    exact ⟨hr0_gR, hr0_pow_dvd_u0, hcop_r0_A, hMR_eq, hr0_pow_dvd_sig, hc0_dvd_rhs⟩

end OddPerfect
