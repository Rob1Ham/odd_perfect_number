module

public import OddPerfect.LinearEulerLCMGcdTothObstruction
public import OddPerfect.SixthPowerFreeHalfSuccPinch
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Linear Euler Non-Coprime Half-Successor Quotient Duality

Couples the coprime LCM-GCD split `m = m_L * m_R` with the universal square parametrization
`A = g * h₀ ^ 2`, `I = g * u₀ ^ 2`, `m = g * h₀ * u₀` (`g = Nat.gcd A I`), splitting `g = g_L * g_R`
into coprime parts aligned with `L` and `R`:

1. `OddPerfect.linear_euler_gcd_coprime_split_and_quotient_duality`:
   Establishes `g = g_L * g_R`, `m_L = g_L * h₀`, `m_R = g_R * u₀`, `L = g_L * h₀ ^ 2`,
   `R = g_R * u₀ ^ 2`, and the quotient duality for the unique `q`-source `r₀ ∈ m.primeFactors`,
   forcing `g_R * W_L < g_L`, `3 ≤ g_L`, `3 ≤ g`, and `¬ Nat.Coprime A I` whenever `r₀ ∣ m_L`,
   and forcing `r₀ ∣ m_R` whenever `g_L = 1`.
2. `OddPerfect.sixth_power_free_gcd_coprime_split_gL_pinch`:
   Specializes Theorem 1 to sixth-power-free odd perfect numbers, pinching `61 ≤ g_L`,
   `61 ≤ g_L * h₀`, `3783 ≤ σ((g_L * h₀) ^ 2)`, `m.factorization r₀ = 2`, `r₀ ∈ largeSources N q`,
   and `61 ≤ r₀` in the `r₀ ∣ g_L * h₀` branch, and `r₀ ∣ g_R * u₀` unconditionally when `g_L = 1`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma sigma_sq_lower_bound {x : ℕ} (hx : 3 ≤ x) :
    1 + x + x ^ 2 ≤ sigma 1 (x ^ 2) := by
  have hx0 : x ≠ 0 := by omega
  have hx20 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx0
  have hx_lt_x2 : x < x ^ 2 := by nlinarith only [hx]
  let s : Finset ℕ := {1, x, x ^ 2}
  have hsub : s ⊆ (x ^ 2).divisors := by
    intro d hd
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hd
    rw [Nat.mem_divisors]
    rcases hd with hd1 | hdx | hdx2
    · rw [hd1]; exact ⟨one_dvd _, hx20⟩
    · rw [hdx]; exact ⟨⟨x, by ring⟩, hx20⟩
    · rw [hdx2]; exact ⟨dvd_refl _, hx20⟩
  have hsum_le : ∑ d ∈ s, d ≤ sigma 1 (x ^ 2) := by
    rw [sigma_one_apply]
    exact Finset.sum_le_sum_of_subset hsub
  have hx_notin : x ∉ ({x ^ 2} : Finset ℕ) := by
    simp only [Finset.mem_singleton]
    omega
  have h1_notin : (1 : ℕ) ∉ ({x, x ^ 2} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hsum_s : ∑ d ∈ s, d = 1 + x + x ^ 2 := by
    dsimp [s]
    rw [Finset.sum_insert h1_notin, Finset.sum_insert hx_notin, Finset.sum_singleton]
    ring
  linarith

private lemma prime_ge_61_of_ge_53_mod {s : ℕ} (hs_prime : s.Prime)
    (hs_ge53 : 53 ≤ s) (hs_mod : s % 5 = 1 ∨ s % 3 = 1) : 61 ≤ s := by
  by_contra! hlt
  have hs_cases : s = 54 ∨ s = 55 ∨ s = 56 ∨ s = 57 ∨ s = 58 ∨ s = 60 := by omega
  rcases hs_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact (by decide : ¬ Nat.Prime _) hs_prime

private lemma eq_two_of_pos_ne_one_two_mul_lt_six {e : ℕ}
    (he_pos : 1 ≤ e) (he_ne1 : e ≠ 1) (h2e_lt6 : 2 * e < 6) : e = 2 := by
  omega

/-- **1. Universal GCD Coprime Split and Quotient Duality**:
On any linear Euler odd perfect number `N = q * m ^ 2`, refines `g := Nat.gcd A I` into coprime
odd factors `g = g_L * g_R` aligned with `L = g_L * h₀ ^ 2` and `R = g_R * u₀ ^ 2`, giving
`m_L = g_L * h₀`, `m_R = g_R * u₀`, and the quotient duality for the unique `q`-source
`r₀ ∈ m.primeFactors`. Whenever `r₀ ∣ m_L`, `g_R * W_L < g_L` forces `3 ≤ g_L`, `3 ≤ g`, and
`¬ Nat.Coprime A I`; consequently `g_L = 1 → r₀ ∣ m_R ∧ ¬ r₀ ∣ m_L`. -/
theorem linear_euler_gcd_coprime_split_and_quotient_duality {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2) :
    let A := (q + 1) / 2
    let I := componentIndex N q
    let g := Nat.gcd A I
    let L := Nat.factorizationLCMLeft A I
    let R := Nat.factorizationLCMRight A I
    let m_L := Nat.gcd m L
    let m_R := Nat.gcd m R
    ∃ h₀ u₀ g_L g_R : ℕ,
      Odd h₀ ∧ Odd u₀ ∧ Odd g_L ∧ Odd g_R ∧
      1 ≤ h₀ ∧ 3 ≤ u₀ ∧ h₀ + 2 ≤ u₀ ∧ 1 ≤ g_L ∧ 1 ≤ g_R ∧
      Nat.Coprime h₀ u₀ ∧ Nat.Coprime g_L g_R ∧ Nat.Coprime g_L u₀ ∧ Nat.Coprime g_R h₀ ∧
      g = g_L * g_R ∧
      m_L = g_L * h₀ ∧ m_R = g_R * u₀ ∧
      L = g_L * h₀ ^ 2 ∧ R = g_R * u₀ ^ 2 ∧
      A = g_L * g_R * h₀ ^ 2 ∧ I = g_L * g_R * u₀ ^ 2 ∧ m = g_L * g_R * h₀ * u₀ ∧
      ∃ r₀ ∈ m.primeFactors,
        q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀)) ∧
        ((r₀ ∣ m_L ∧ ¬ r₀ ∣ m_R ∧
            let W_L := sigma 1 (m_L ^ 2) / q
            1 ≤ W_L ∧ Odd W_L ∧
            W_L * sigma 1 (m_R ^ 2) = g_L * g_R * u₀ ^ 2 ∧
            g_R * W_L * sigma 1 (m_R ^ 2) = g_L * m_R ^ 2 ∧
            (q + 1) * W_L * sigma 1 (m_R ^ 2) = 2 * m_L ^ 2 * m_R ^ 2 ∧
            g_R * W_L < g_L ∧ 3 ≤ g_L ∧ 3 ≤ g ∧ ¬ Nat.Coprime A I) ∨
         (r₀ ∣ m_R ∧ ¬ r₀ ∣ m_L ∧
            let W_R := sigma 1 (m_R ^ 2) / q
            1 ≤ W_R ∧ Odd W_R ∧
            W_R * sigma 1 (m_L ^ 2) = g_L * g_R * u₀ ^ 2 ∧
            (q + 1) * W_R * sigma 1 (m_L ^ 2) = 2 * m_L ^ 2 * m_R ^ 2)) ∧
        (g_L = 1 → r₀ ∣ m_R ∧ ¬ r₀ ∣ m_L) := by
  intro A I g L R m_L m_R
  obtain ⟨_, _, _, _, _, h₀, u₀, hh0_odd, hu0_odd, hh0_ge1, hu0_ge3, hh0_lt_u0,
    hcop_h0u0, hA_eq, hI_eq, hm_eq⟩ :=
    linear_euler_half_succ_lt_index_and_h0_lt_u0 ho hN hq hqm hform
  obtain ⟨hg_odd, _, _, hLR_cop, hL_dvd_A, hR_dvd_I, hLR_lcm, _, _, _, _, _, _,
    _, _, _, _, _, _, hg_cop_iff⟩ :=
    universal_half_succ_index_gcd_square_parametrization ho hN hq hqm hform
  obtain ⟨hmL_odd, hmR_odd, hm_cop, hm_eq_mul, hmL_dvd_L, _, _, _, hmR_dvd_R, _,
    hmR_ge3, _, _, _⟩ :=
    linear_euler_lcm_gcd_canonical_coprime_split ho hN hq hqm hform
  obtain ⟨_, _, _, r₀, hr₀_m, _, hq_dvd_r0, hbranch⟩ :=
    linear_euler_mL_eq_one_iff_and_r0_split_dichotomy ho hN hq hqm hform
  have hA_eq0 : A = g * h₀ ^ 2 := hA_eq
  have hI_eq0 : I = g * u₀ ^ 2 := hI_eq
  have hm_eq0 : m = g * h₀ * u₀ := hm_eq
  have hm_eq_mul0 : m = m_L * m_R := hm_eq_mul
  have hq_odd : Odd q := ho.of_dvd_nat (hform ▸ dvd_mul_right q (m ^ 2))
  have hm_odd : Odd m :=
    ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
  have hA_odd : Odd A := by rw [hA_eq0]; exact hg_odd.mul hh0_odd.pow
  have hI_odd : Odd I := by rw [hI_eq0]; exact hg_odd.mul hu0_odd.pow
  have hg0 : g ≠ 0 := hg_odd.pos.ne'
  have hh00 : h₀ ≠ 0 := hh0_odd.pos.ne'
  have hu00 : u₀ ≠ 0 := hu0_odd.pos.ne'
  have hA0 : A ≠ 0 := hA_odd.pos.ne'
  have hI0 : I ≠ 0 := hI_odd.pos.ne'
  have hL0 : L ≠ 0 := (Nat.factorizationLCMLeft_pos A I).ne'
  have hR0 : R ≠ 0 := (Nat.factorizationLCMRight_pos A I).ne'
  have hLR_fact : ∀ p : ℕ, A.factorization p ≤ L.factorization p + R.factorization p ∧
      I.factorization p ≤ L.factorization p + R.factorization p := by
    intro p
    have hsum : L.factorization p + R.factorization p = max (A.factorization p) (I.factorization p) := by
      calc
        L.factorization p + R.factorization p = (L * R).factorization p := by
          rw [← Finsupp.add_apply, ← Nat.factorization_mul hL0 hR0]
        _ = (Nat.lcm A I).factorization p := by rw [hLR_lcm]
        _ = max (A.factorization p) (I.factorization p) := by
          rw [Nat.factorization_lcm hA0 hI0, Finsupp.sup_apply]
    exact ⟨hsum ▸ le_max_left _ _, hsum ▸ le_max_right _ _⟩
  have hcop_h0_R : Nat.Coprime h₀ R := by
    by_contra hncop
    have hgcd_ne1 : Nat.gcd h₀ R ≠ 1 := hncop
    obtain ⟨p, hp, hp_gcd⟩ := Nat.exists_prime_and_dvd hgcd_ne1
    have hp_h0 : p ∣ h₀ := hp_gcd.trans (Nat.gcd_dvd_left h₀ R)
    have hp_R : p ∣ R := hp_gcd.trans (Nat.gcd_dvd_right h₀ R)
    have hp_not_u0 : ¬ p ∣ u₀ := fun hp_u0 =>
      hp.not_dvd_one (hcop_h0u0 ▸ Nat.dvd_gcd hp_h0 hp_u0)
    have hu0_zero : u₀.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hp_not_u0
    have hh0_pos : 1 ≤ h₀.factorization p := (hp.dvd_iff_one_le_factorization hh00).mp hp_h0
    have hI_fact : I.factorization p = g.factorization p := by
      rw [hI_eq0, Nat.factorization_mul hg0 (pow_ne_zero 2 hu00), Finsupp.add_apply,
        Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hu0_zero, mul_zero, add_zero]
    have hA_fact : A.factorization p = g.factorization p + 2 * h₀.factorization p := by
      rw [hA_eq0, Nat.factorization_mul hg0 (pow_ne_zero 2 hh00), Finsupp.add_apply,
        Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    have hR_le_I : R.factorization p ≤ I.factorization p :=
      (Nat.factorization_le_iff_dvd hR0 hI0).mpr hR_dvd_I p
    have hA_le := (hLR_fact p).1
    have hL_pos : 0 < L.factorization p := by
      linarith only [hh0_pos, hI_fact, hA_fact, hR_le_I, hA_le]
    have hp_L : p ∣ L := (hp.dvd_iff_one_le_factorization hL0).mpr hL_pos
    exact hp.not_dvd_one (hLR_cop ▸ Nat.dvd_gcd hp_L hp_R)
  have hcop_u0_L : Nat.Coprime u₀ L := by
    by_contra hncop
    have hgcd_ne1 : Nat.gcd u₀ L ≠ 1 := hncop
    obtain ⟨p, hp, hp_gcd⟩ := Nat.exists_prime_and_dvd hgcd_ne1
    have hp_u0 : p ∣ u₀ := hp_gcd.trans (Nat.gcd_dvd_left u₀ L)
    have hp_L : p ∣ L := hp_gcd.trans (Nat.gcd_dvd_right u₀ L)
    have hp_not_h0 : ¬ p ∣ h₀ := fun hp_h0 =>
      hp.not_dvd_one (hcop_h0u0 ▸ Nat.dvd_gcd hp_h0 hp_u0)
    have hh0_zero : h₀.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hp_not_h0
    have hu0_pos : 1 ≤ u₀.factorization p := (hp.dvd_iff_one_le_factorization hu00).mp hp_u0
    have hA_fact : A.factorization p = g.factorization p := by
      rw [hA_eq0, Nat.factorization_mul hg0 (pow_ne_zero 2 hh00), Finsupp.add_apply,
        Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hh0_zero, mul_zero, add_zero]
    have hI_fact : I.factorization p = g.factorization p + 2 * u₀.factorization p := by
      rw [hI_eq0, Nat.factorization_mul hg0 (pow_ne_zero 2 hu00), Finsupp.add_apply,
        Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    have hL_le_A : L.factorization p ≤ A.factorization p :=
      (Nat.factorization_le_iff_dvd hL0 hA0).mpr hL_dvd_A p
    have hI_le := (hLR_fact p).2
    have hR_pos : 0 < R.factorization p := by
      linarith only [hu0_pos, hA_fact, hI_fact, hL_le_A, hI_le]
    have hp_R : p ∣ R := (hp.dvd_iff_one_le_factorization hR0).mpr hR_pos
    exact hp.not_dvd_one (hLR_cop ▸ Nat.dvd_gcd hp_L hp_R)
  have hcop_h0_mR : Nat.Coprime h₀ m_R := hcop_h0_R.coprime_dvd_right hmR_dvd_R
  have hcop_u0_mL : Nat.Coprime u₀ m_L := hcop_u0_L.coprime_dvd_right hmL_dvd_L
  have hh0_dvd_mL : h₀ ∣ m_L := by
    have hh0_dvd_m : h₀ ∣ m_L * m_R := by
      rw [← hm_eq_mul0, hm_eq0]
      exact ⟨g * u₀, by ring⟩
    exact hcop_h0_mR.dvd_of_dvd_mul_right hh0_dvd_m
  have hu0_dvd_mR : u₀ ∣ m_R := by
    have hu0_dvd_m : u₀ ∣ m_L * m_R := by
      rw [← hm_eq_mul0, hm_eq0]
      exact ⟨g * h₀, by ring⟩
    exact hcop_u0_mL.dvd_of_dvd_mul_left hu0_dvd_m
  let g_L := m_L / h₀
  let g_R := m_R / u₀
  have hmL_eq : m_L = g_L * h₀ := (Nat.div_mul_cancel hh0_dvd_mL).symm
  have hmR_eq : m_R = g_R * u₀ := (Nat.div_mul_cancel hu0_dvd_mR).symm
  have hgL_odd : Odd g_L := hmL_odd.of_dvd_nat ⟨h₀, hmL_eq⟩
  have hgR_odd : Odd g_R := hmR_odd.of_dvd_nat ⟨u₀, hmR_eq⟩
  have hgL_ge1 : 1 ≤ g_L := hgL_odd.pos
  have hgR_ge1 : 1 ≤ g_R := hgR_odd.pos
  have hg_eq : g = g_L * g_R := by
    apply Nat.mul_right_cancel (mul_pos hh0_odd.pos hu0_odd.pos)
    calc
      g * (h₀ * u₀) = g * h₀ * u₀ := by ring
      _ = m := hm_eq0.symm
      _ = m_L * m_R := hm_eq_mul0
      _ = (g_L * h₀) * (g_R * u₀) := by rw [hmL_eq, hmR_eq]
      _ = (g_L * g_R) * (h₀ * u₀) := by ring
  have hm_cop_prod : Nat.Coprime (g_L * h₀) (g_R * u₀) := by
    rw [← hmL_eq, ← hmR_eq]
    exact hm_cop
  have hcop_gLgR : Nat.Coprime g_L g_R :=
    (hm_cop_prod.coprime_dvd_left (dvd_mul_right g_L h₀)).coprime_dvd_right (dvd_mul_right g_R u₀)
  have hcop_gLu0 : Nat.Coprime g_L u₀ :=
    (hm_cop_prod.coprime_dvd_left (dvd_mul_right g_L h₀)).coprime_dvd_right (dvd_mul_left u₀ g_R)
  have hcop_gRh0 : Nat.Coprime g_R h₀ :=
    ((hm_cop_prod.coprime_dvd_left (dvd_mul_left h₀ g_L)).coprime_dvd_right (dvd_mul_right g_R u₀)).symm
  have hA_eq' : A = g_L * g_R * h₀ ^ 2 := by rw [hA_eq0, hg_eq]
  have hI_eq' : I = g_L * g_R * u₀ ^ 2 := by rw [hI_eq0, hg_eq]
  have hm_eq' : m = g_L * g_R * h₀ * u₀ := by rw [hm_eq0, hg_eq]
  have hgR_dvd_R : g_R ∣ R := (dvd_mul_right g_R u₀).trans (hmR_eq ▸ hmR_dvd_R)
  have hgL_dvd_L : g_L ∣ L := (dvd_mul_right g_L h₀).trans (hmL_eq ▸ hmL_dvd_L)
  have hcop_L_gR : Nat.Coprime L g_R := hLR_cop.coprime_dvd_right hgR_dvd_R
  have hcop_R_gL : Nat.Coprime R g_L := hLR_cop.symm.coprime_dvd_right hgL_dvd_L
  have hL_dvd_target : L ∣ g_L * h₀ ^ 2 := by
    have hL_dvd' : L ∣ (g_L * h₀ ^ 2) * g_R := by
      have : g_L * g_R * h₀ ^ 2 = (g_L * h₀ ^ 2) * g_R := by ring
      rwa [← this, ← hA_eq']
    exact hcop_L_gR.dvd_of_dvd_mul_right hL_dvd'
  have hR_dvd_target : R ∣ g_R * u₀ ^ 2 := by
    have hR_dvd' : R ∣ (g_R * u₀ ^ 2) * g_L := by
      have : g_L * g_R * u₀ ^ 2 = (g_R * u₀ ^ 2) * g_L := by ring
      rwa [← this, ← hI_eq']
    exact hcop_R_gL.dvd_of_dvd_mul_right hR_dvd'
  have hLR_prod_eq : L * R = (g_L * h₀ ^ 2) * (g_R * u₀ ^ 2) := by
    have hAI : A * I = m ^ 2 := by rw [hA_eq', hI_eq', hm_eq']; ring
    have hgcd_lcm : g * Nat.lcm A I = A * I := Nat.gcd_mul_lcm A I
    have hLCM_eq : Nat.lcm A I = g * h₀ ^ 2 * u₀ ^ 2 := by
      apply Nat.mul_left_cancel hg_odd.pos
      calc
        g * Nat.lcm A I = A * I := hgcd_lcm
        _ = m ^ 2 := hAI
        _ = (g * h₀ * u₀) ^ 2 := by rw [hm_eq0]
        _ = g * (g * h₀ ^ 2 * u₀ ^ 2) := by ring
    calc
      L * R = Nat.lcm A I := hLR_lcm
      _ = g * h₀ ^ 2 * u₀ ^ 2 := hLCM_eq
      _ = (g_L * g_R) * h₀ ^ 2 * u₀ ^ 2 := by rw [hg_eq]
      _ = (g_L * h₀ ^ 2) * (g_R * u₀ ^ 2) := by ring
  obtain ⟨a, ha⟩ := hL_dvd_target
  obtain ⟨b, hb⟩ := hR_dvd_target
  have hab : a * b = 1 := by
    apply Nat.mul_left_cancel
      (mul_pos (Nat.factorizationLCMLeft_pos A I) (Nat.factorizationLCMRight_pos A I))
    calc
      L * R * (a * b) = (L * a) * (R * b) := by ring
      _ = (g_L * h₀ ^ 2) * (g_R * u₀ ^ 2) := by rw [← ha, ← hb]
      _ = L * R := hLR_prod_eq.symm
      _ = L * R * 1 := by ring
  have ha1 : a = 1 := Nat.eq_one_of_dvd_one ⟨b, hab.symm⟩
  have hb1 : b = 1 := Nat.eq_one_of_dvd_one ⟨a, by rw [← hab, mul_comm]⟩
  have hL_eq : L = g_L * h₀ ^ 2 := by rw [ha, ha1, mul_one]
  have hR_eq : R = g_R * u₀ ^ 2 := by rw [hb, hb1, mul_one]
  have hq1_eq : q + 1 = 2 * A := (Nat.mul_div_cancel' (hq_odd.add_odd odd_one).two_dvd).symm
  have hAI_m : A * I = m_L ^ 2 * m_R ^ 2 := by
    calc
      A * I = m ^ 2 := by rw [hA_eq', hI_eq', hm_eq']; ring
      _ = (m_L * m_R) ^ 2 := by rw [hm_eq_mul0]
      _ = m_L ^ 2 * m_R ^ 2 := by ring
  refine ⟨h₀, u₀, g_L, g_R, hh0_odd, hu0_odd, hgL_odd, hgR_odd, hh0_ge1, hu0_ge3, hh0_lt_u0,
    hgL_ge1, hgR_ge1, hcop_h0u0, hcop_gLgR, hcop_gLu0, hcop_gRh0, hg_eq, hmL_eq, hmR_eq,
    hL_eq, hR_eq, hA_eq', hI_eq', hm_eq', r₀, hr₀_m, hq_dvd_r0, ?_, ?_⟩
  · rcases hbranch with
      ⟨hr0_L, hr0_not_R, _, _, _, _, _, _, _, hdiv_eq⟩ |
      ⟨hr0_R, hr0_not_L, _, _, _, hdiv_eq⟩
    · left
      let W_L := sigma 1 (m_L ^ 2) / q
      have hdiv_eq' : W_L * sigma 1 (m_R ^ 2) = I := hdiv_eq
      have hWL_sigR : W_L * sigma 1 (m_R ^ 2) = g_L * g_R * u₀ ^ 2 := by
        rw [hdiv_eq', hI_eq']
      have hWL_dvd_I : W_L ∣ I := ⟨sigma 1 (m_R ^ 2), hdiv_eq'.symm⟩
      have hWL_odd : Odd W_L := hI_odd.of_dvd_nat hWL_dvd_I
      have hWL_ge1 : 1 ≤ W_L := hWL_odd.pos
      have hgR_WL_eq : g_R * W_L * sigma 1 (m_R ^ 2) = g_L * m_R ^ 2 := by
        calc
          g_R * W_L * sigma 1 (m_R ^ 2) = g_R * (W_L * sigma 1 (m_R ^ 2)) := by ring
          _ = g_R * (g_L * g_R * u₀ ^ 2) := by rw [hWL_sigR]
          _ = g_L * (g_R * u₀) ^ 2 := by ring
          _ = g_L * m_R ^ 2 := by rw [hmR_eq]
      have hq1_WL_eq : (q + 1) * W_L * sigma 1 (m_R ^ 2) = 2 * m_L ^ 2 * m_R ^ 2 := by
        calc
          (q + 1) * W_L * sigma 1 (m_R ^ 2)
              = (2 * A) * (W_L * sigma 1 (m_R ^ 2)) := by rw [hq1_eq]; ring
          _ = 2 * (A * I) := by rw [hWL_sigR, hI_eq']; ring
          _ = 2 * m_L ^ 2 * m_R ^ 2 := by rw [hAI_m]; ring
      have hmR_sq_lt_sig : m_R ^ 2 < sigma 1 (m_R ^ 2) := by
        have hlb := sigma_sq_lower_bound hmR_ge3
        linarith only [hlb, hmR_ge3]
      have hgR_WL_lt_gL : g_R * W_L < g_L := by
        have hgR_WL_pos : 0 < g_R * W_L := mul_pos hgR_odd.pos hWL_odd.pos
        have hmul_lt : g_R * W_L * m_R ^ 2 < g_L * m_R ^ 2 := by
          calc
            g_R * W_L * m_R ^ 2 < g_R * W_L * sigma 1 (m_R ^ 2) :=
              Nat.mul_lt_mul_of_pos_left hmR_sq_lt_sig hgR_WL_pos
            _ = g_L * m_R ^ 2 := hgR_WL_eq
        exact Nat.lt_of_mul_lt_mul_right hmul_lt
      have hgL_ge2 : 2 ≤ g_L := by
        have h1 : 1 ≤ g_R * W_L := mul_pos hgR_odd.pos hWL_odd.pos
        linarith only [h1, hgR_WL_lt_gL]
      have hgL_ge3 : 3 ≤ g_L := by
        obtain ⟨k, hk⟩ := hgL_odd
        rcases k with _ | k <;> linarith only [hk, hgL_ge2]
      have hg_ge3 : 3 ≤ g := by
        calc
          3 ≤ g_L := hgL_ge3
          _ = g_L * 1 := (mul_one g_L).symm
          _ ≤ g_L * g_R := Nat.mul_le_mul_left g_L hgR_ge1
          _ = g := hg_eq.symm
      have hncop_AI : ¬ Nat.Coprime A I := by
        intro hcop_AI
        have hg1 : g = 1 := hg_cop_iff.2.mpr hcop_AI
        linarith only [hg_ge3, hg1]
      exact ⟨hr0_L, hr0_not_R, hWL_ge1, hWL_odd, hWL_sigR, hgR_WL_eq, hq1_WL_eq,
        hgR_WL_lt_gL, hgL_ge3, hg_ge3, hncop_AI⟩
    · right
      let W_R := sigma 1 (m_R ^ 2) / q
      have hdiv_eq' : W_R * sigma 1 (m_L ^ 2) = I := hdiv_eq
      have hWR_sigL : W_R * sigma 1 (m_L ^ 2) = g_L * g_R * u₀ ^ 2 := by
        rw [hdiv_eq', hI_eq']
      have hWR_dvd_I : W_R ∣ I := ⟨sigma 1 (m_L ^ 2), hdiv_eq'.symm⟩
      have hWR_odd : Odd W_R := hI_odd.of_dvd_nat hWR_dvd_I
      have hWR_ge1 : 1 ≤ W_R := hWR_odd.pos
      have hq1_WR_eq : (q + 1) * W_R * sigma 1 (m_L ^ 2) = 2 * m_L ^ 2 * m_R ^ 2 := by
        calc
          (q + 1) * W_R * sigma 1 (m_L ^ 2)
              = (2 * A) * (W_R * sigma 1 (m_L ^ 2)) := by rw [hq1_eq]; ring
          _ = 2 * (A * I) := by rw [hWR_sigL, hI_eq']; ring
          _ = 2 * m_L ^ 2 * m_R ^ 2 := by rw [hAI_m]; ring
      exact ⟨hr0_R, hr0_not_L, hWR_ge1, hWR_odd, hWR_sigL, hq1_WR_eq⟩
  · intro hgL1
    rcases hbranch with ⟨hr0_L, hr0_not_R, _, _, _, _, _, _, _, hdiv_eq⟩ | ⟨hr0_R, hr0_not_L, _⟩
    · exfalso
      let W_L := sigma 1 (m_L ^ 2) / q
      have hdiv_eq' : W_L * sigma 1 (m_R ^ 2) = I := hdiv_eq
      have hWL_dvd_I : W_L ∣ I := ⟨sigma 1 (m_R ^ 2), hdiv_eq'.symm⟩
      have hWL_odd : Odd W_L := hI_odd.of_dvd_nat hWL_dvd_I
      have hWL_sigR : W_L * sigma 1 (m_R ^ 2) = g_L * g_R * u₀ ^ 2 := by
        rw [hdiv_eq', hI_eq']
      have hgR_WL_eq : g_R * W_L * sigma 1 (m_R ^ 2) = g_L * m_R ^ 2 := by
        calc
          g_R * W_L * sigma 1 (m_R ^ 2) = g_R * (W_L * sigma 1 (m_R ^ 2)) := by ring
          _ = g_R * (g_L * g_R * u₀ ^ 2) := by rw [hWL_sigR]
          _ = g_L * (g_R * u₀) ^ 2 := by ring
          _ = g_L * m_R ^ 2 := by rw [hmR_eq]
      have hmR_sq_lt_sig : m_R ^ 2 < sigma 1 (m_R ^ 2) := by
        have hlb := sigma_sq_lower_bound hmR_ge3
        linarith only [hlb, hmR_ge3]
      have hgR_WL_pos : 0 < g_R * W_L := mul_pos hgR_odd.pos hWL_odd.pos
      have hmul_lt : g_R * W_L * m_R ^ 2 < g_L * m_R ^ 2 := by
        calc
          g_R * W_L * m_R ^ 2 < g_R * W_L * sigma 1 (m_R ^ 2) :=
            Nat.mul_lt_mul_of_pos_left hmR_sq_lt_sig hgR_WL_pos
          _ = g_L * m_R ^ 2 := hgR_WL_eq
      have hgR_WL_lt_gL : g_R * W_L < g_L := Nat.lt_of_mul_lt_mul_right hmul_lt
      have h1 : 1 ≤ g_R * W_L := mul_pos hgR_odd.pos hWL_odd.pos
      linarith only [h1, hgR_WL_lt_gL, hgL1]
    · exact ⟨hr0_R, hr0_not_L⟩

/-- **2. Sixth-Power-Free GCD Coprime Split `g_L` Pinch**:
Specializes `linear_euler_gcd_coprime_split_and_quotient_duality` to sixth-power-free odd perfect
numbers. Whenever the unique `q`-source `r₀` lies in `m_L = g_L * h₀`, any prime divisor
`s ∣ g_L ∣ Nat.gcd A I` satisfies `61 ≤ s` via `sixth_power_free_min_prime_ge_53` and
`sixth_power_free_euler_index_drop_and_support`, pinching `61 ≤ g_L`, `61 ≤ g_L * h₀`,
`3783 ≤ σ((g_L * h₀) ^ 2)`, `m.factorization r₀ = 2`, `r₀ ∈ largeSources N q`, and `61 ≤ r₀`;
whenever `g_L = 1`, `r₀ ∣ g_R * u₀` holds unconditionally. -/
theorem sixth_power_free_gcd_coprime_split_gL_pinch {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    ∃ m h₀ u₀ g_L g_R r₀ : ℕ,
      let A := (q + 1) / 2
      let I := componentIndex N q
      let L := Nat.factorizationLCMLeft A I
      let R := Nat.factorizationLCMRight A I
      Odd m ∧ ¬ q ∣ m ∧ N = q * m ^ 2 ∧
      Odd h₀ ∧ Odd u₀ ∧ Odd g_L ∧ Odd g_R ∧
      1 ≤ h₀ ∧ 3 ≤ u₀ ∧ h₀ + 2 ≤ u₀ ∧ 1 ≤ g_L ∧ 1 ≤ g_R ∧
      Nat.Coprime h₀ u₀ ∧ Nat.Coprime g_L g_R ∧ Nat.Coprime g_L u₀ ∧ Nat.Coprime g_R h₀ ∧
      g_L * g_R = Nat.gcd A I ∧
      Nat.gcd m L = g_L * h₀ ∧
      Nat.gcd m R = g_R * u₀ ∧
      r₀ ∈ m.primeFactors ∧
      q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀)) ∧
      ((r₀ ∣ g_L * h₀ ∧ ¬ r₀ ∣ g_R * u₀ ∧
          61 ≤ g_L ∧ 61 ≤ g_L * h₀ ∧ 3783 ≤ sigma 1 ((g_L * h₀) ^ 2) ∧
          m.factorization r₀ = 2 ∧ r₀ ∈ largeSources N q ∧ 61 ≤ r₀) ∨
       (r₀ ∣ g_R * u₀ ∧ ¬ r₀ ∣ g_L * h₀)) ∧
      (g_L = 1 → r₀ ∣ g_R * u₀ ∧ ¬ r₀ ∣ g_L * h₀) := by
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  obtain ⟨m, _, hm_odd, hqm, hform, _⟩ :=
    sixth_power_free_unique_q_source_mirror_dichotomy ho hN hq hq4 he hev hfree
  obtain ⟨h₀, u₀, g_L, g_R, hh0_odd, hu0_odd, hgL_odd, hgR_odd, hh0_ge1, hu0_ge3, hh0_lt_u0,
    hgL_ge1, hgR_ge1, hcop_h0u0, hcop_gLgR, hcop_gLu0, hcop_gRh0, hg_eq, hmL_eq, hmR_eq,
    _, _, _, hI_eq', hm_eq', r₀, hr₀_m, hq_dvd_r0, hbranch, hgL1_branch⟩ :=
    linear_euler_gcd_coprime_split_and_quotient_duality ho hN hq_prime hqm hform
  let A := (q + 1) / 2
  let I := componentIndex N q
  let L := Nat.factorizationLCMLeft A I
  let R := Nat.factorizationLCMRight A I
  have hI_eq'' : I = g_L * g_R * u₀ ^ 2 := hI_eq'
  have hsig_split_all := linear_euler_lcm_gcd_canonical_coprime_split ho hN hq_prime hqm hform
  have hsig_eq_I : I = sigma 1 (m ^ 2) / q := by
    have hsigm2_eq_qI : sigma 1 (m ^ 2) = q * I :=
      hsig_split_all.2.2.2.2.2.2.2.2.2.2.2.2.1.trans hsig_split_all.2.2.2.2.2.2.2.2.2.2.2.2.2
    change I = sigma 1 (m ^ 2) / q
    rw [hsigm2_eq_qI, Nat.mul_div_cancel_left I hq_prime.pos]
  have hI_pos : 0 < I := (componentIndex_mul_eq_two_mul hN hq).2
  have hdrop := (sixth_power_free_euler_index_drop_and_support ho hN hq hq4 he hev hfree).2
  refine ⟨m, h₀, u₀, g_L, g_R, r₀, hm_odd, hqm, hform, hh0_odd, hu0_odd, hgL_odd, hgR_odd,
    hh0_ge1, hu0_ge3, hh0_lt_u0, hgL_ge1, hgR_ge1, hcop_h0u0, hcop_gLgR, hcop_gLu0, hcop_gRh0,
    hg_eq.symm, hmL_eq, hmR_eq, hr₀_m, hq_dvd_r0, ?_, ?_⟩
  · rcases hbranch with
      ⟨hr0_L, hr0_not_R, _, _, _, _, _, _, hgL_ge3, _, _⟩ |
      ⟨hr0_R, hr0_not_L, _⟩
    · left
      have hr0_L' : r₀ ∣ g_L * h₀ := by rwa [← hmL_eq]
      have hr0_not_R' : ¬ r₀ ∣ g_R * u₀ := by rwa [← hmR_eq]
      have hgL_ne1 : g_L ≠ 1 := by
        intro h1
        linarith only [hgL_ge3, h1]
      obtain ⟨s, hs_prime, hs_dvd_gL⟩ := Nat.exists_prime_and_dvd hgL_ne1
      have hs_dvd_I : s ∣ I := by
        have : g_L ∣ I := by rw [hI_eq'']; exact ⟨g_R * u₀ ^ 2, by ring⟩
        exact hs_dvd_gL.trans this
      have hs_dvd_m : s ∣ m := by
        have : g_L ∣ m := by rw [hm_eq']; exact ⟨g_R * h₀ * u₀, by ring⟩
        exact hs_dvd_gL.trans this
      have hs_dvd_N : s ∣ N :=
        hform ▸ hs_dvd_m.trans ((dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left _ q))
      have hs_N : s ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hs_prime, hs_dvd_N, hN.2.ne'⟩
      have hs_ge53 : 53 ≤ s := sixth_power_free_min_prime_ge_53 ho hN hfree hs_N
      have hs_I_mem : s ∈ I.primeFactors := Nat.mem_primeFactors.mpr ⟨hs_prime, hs_dvd_I, hI_pos.ne'⟩
      have hs_mod : s % 5 = 1 ∨ s % 3 = 1 := hdrop s hs_I_mem
      have hs_ge61 : 61 ≤ s := prime_ge_61_of_ge_53_mod hs_prime hs_ge53 hs_mod
      have hgL_ge61 : 61 ≤ g_L := hs_ge61.trans (Nat.le_of_dvd hgL_odd.pos hs_dvd_gL)
      have hgLh0_ge61 : 61 ≤ g_L * h₀ := by
        calc
          61 ≤ g_L := hgL_ge61
          _ = g_L * 1 := (mul_one g_L).symm
          _ ≤ g_L * h₀ := Nat.mul_le_mul_left g_L hh0_ge1
      have hsig_ge3783 : 3783 ≤ sigma 1 ((g_L * h₀) ^ 2) := by
        have hgLh0_ge3 : 3 ≤ g_L * h₀ := by linarith only [hgLh0_ge61]
        have hlb := sigma_sq_lower_bound hgLh0_ge3
        nlinarith only [hgLh0_ge61, hlb]
      have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀_m
      have hr₀_dvd_m : r₀ ∣ m := Nat.dvd_of_mem_primeFactors hr₀_m
      have hr₀_dvd_A : r₀ ∣ A := hr0_L.trans (Nat.gcd_dvd_right m L |>.trans
        (Nat.factorizationLCMLeft_dvd_left A I))
      have hm0 : m ≠ 0 := hm_odd.pos.ne'
      have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
      have he0_pos : 1 ≤ m.factorization r₀ :=
        (hr₀_prime.dvd_iff_one_le_factorization hm0).mp hr₀_dvd_m
      have he0_ne1 : m.factorization r₀ ≠ 1 := by
        intro he1
        have hndvd :=
          (linear_euler_square_source_coprime_half_succ ho hN hq_prime hqm hform hr₀_m hq_dvd_r0 he1).2.1
        exact hndvd hr₀_dvd_A
      have hr₀_neq : r₀ ≠ q := fun h => hqm (h ▸ hr₀_dvd_m)
      have hr₀_not_q : ¬ r₀ ∣ q := fun hd =>
        hr₀_neq (((Nat.dvd_prime hq_prime).mp hd).resolve_left hr₀_prime.ne_one)
      have hN_fact_r0 : N.factorization r₀ = 2 * m.factorization r₀ := by
        rw [hform, Nat.factorization_mul hq_prime.ne_zero hm20, Finsupp.add_apply,
          Nat.factorization_eq_zero_of_not_dvd hr₀_not_q, zero_add,
          Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
      have hr₀_not_6_N : N.factorization r₀ < 6 := by
        by_contra! hge6
        exact hfree r₀ hr₀_prime ((hr₀_prime.pow_dvd_iff_le_factorization hN.2.ne').mpr hge6)
      have h2e0_lt6 : 2 * m.factorization r₀ < 6 := by linarith only [hN_fact_r0, hr₀_not_6_N]
      have he0_eq2 : m.factorization r₀ = 2 :=
        eq_two_of_pos_ne_one_two_mul_lt_six he0_pos he0_ne1 h2e0_lt6
      have hr₀_dvd_N : r₀ ∣ N :=
        hform ▸ hr₀_dvd_m.trans ((dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left _ q))
      have hr₀_N : r₀ ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hr₀_prime, hr₀_dvd_N, hN.2.ne'⟩
      have hr₀_ge53 : 53 ≤ r₀ := sixth_power_free_min_prime_ge_53 ho hN hfree hr₀_N
      have hr₀_ne3 : r₀ ≠ 3 := by linarith only [hr₀_ge53]
      have hN_fact_ge4 : 4 ≤ N.factorization r₀ := by linarith only [hN_fact_r0, he0_eq2]
      have hr₀_large : r₀ ∈ largeSources N q :=
        Finset.mem_filter.mpr ⟨hr₀_N, hr₀_ne3, hr₀_neq, hN_fact_ge4⟩
      have hr₀_mem_I : r₀ ∈ I.primeFactors := by
        have hmem :=
          (linear_euler_unique_source_dvd_sigma_B_and_index_of_source
            ho hN hq_prime hqm hform hr₀_m hq_dvd_r0).2.2.2.2.1
        rwa [← hsig_eq_I] at hmem
      have hr₀_mod : r₀ % 5 = 1 ∨ r₀ % 3 = 1 := hdrop r₀ hr₀_mem_I
      have hr₀_ge61 : 61 ≤ r₀ := prime_ge_61_of_ge_53_mod hr₀_prime hr₀_ge53 hr₀_mod
      exact ⟨hr0_L', hr0_not_R', hgL_ge61, hgLh0_ge61, hsig_ge3783, he0_eq2, hr₀_large, hr₀_ge61⟩
    · right
      rw [hmR_eq] at hr0_R
      rw [hmL_eq] at hr0_not_L
      exact ⟨hr0_R, hr0_not_L⟩
  · intro hgL1
    obtain ⟨hr0_R, hr0_not_L⟩ := hgL1_branch hgL1
    rw [hmR_eq] at hr0_R
    rw [hmL_eq] at hr0_not_L
    exact ⟨hr0_R, hr0_not_L⟩

end OddPerfect
