module

public import OddPerfect.LinearEulerGcdSplitSourcePeeling
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Linear Euler Right-Source Forcing

BRANCH_MAP: A1
Closure: Eliminates the entire r₀ ∣ m_L half of the A1 noncoprime quotient dichotomy unconditionally across all g ≥ 1, shrinking A1 to the single r₀ ∣ m_R system W_R σ(m_L²) = g u₀².

Unconditionally eliminates the `r₀ ∣ m_L` branch of the noncoprime quotient duality on any
linear Euler odd perfect number `N = q * m ^ 2`, forcing the unique `q`-source `r₀` to satisfy
`¬ r₀ ∣ m_L`, `r₀ ∣ m_R`, `r₀ ∣ u₀`, `A.factorization r₀ < m.factorization r₀`, and
`A.factorization r₀ < I.factorization r₀`, and discharging the `r₀ ∣ m_R →` guard of
`linear_euler_right_source_peeling_dichotomy`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma r0_not_dvd_mL_aux {N q m h₀ u₀ g_L g_R m_R r₀ : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hh0_odd : Odd h₀) (hu0_odd : Odd u₀) (hgL_odd : Odd g_L) (hgR_odd : Odd g_R)
    (hmR_eq : m_R = g_R * u₀)
    (hA_eq : (q + 1) / 2 = g_L * g_R * h₀ ^ 2)
    (hm_eq : m = g_L * g_R * h₀ * u₀)
    (hr₀_m : r₀ ∈ m.primeFactors)
    (hq_dvd_r0 : q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀)))
    (hr0_not_mR : ¬ r₀ ∣ m_R) :
    False := by
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀_m
  have hm_odd : Odd m :=
    ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
  have hr₀_odd : Odd r₀ := hm_odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr₀_m)
  have hr₀_ge3 : 3 ≤ r₀ := by
    obtain ⟨u, hu⟩ := hr₀_odd
    have := hr₀_prime.two_le
    omega
  have hq_odd : Odd q := ho.of_dvd_nat (hform ▸ dvd_mul_right q (m ^ 2))
  have hq1_eq : q + 1 = 2 * ((q + 1) / 2) := by
    have := Nat.odd_iff.mp hq_odd
    omega
  have hr0_ndvd_gR : ¬ r₀ ∣ g_R := fun hd =>
    hr0_not_mR (hmR_eq ▸ hd.trans (dvd_mul_right g_R u₀))
  have hr0_ndvd_u0 : ¬ r₀ ∣ u₀ := fun hd =>
    hr0_not_mR (hmR_eq ▸ hd.trans (dvd_mul_left u₀ g_R))
  have hgR_zero : g_R.factorization r₀ = 0 := Nat.factorization_eq_zero_of_not_dvd hr0_ndvd_gR
  have hu0_zero : u₀.factorization r₀ = 0 := Nat.factorization_eq_zero_of_not_dvd hr0_ndvd_u0
  have hgL0 : g_L ≠ 0 := hgL_odd.pos.ne'
  have hgR0 : g_R ≠ 0 := hgR_odd.pos.ne'
  have hh00 : h₀ ≠ 0 := hh0_odd.pos.ne'
  have hu00 : u₀ ≠ 0 := hu0_odd.pos.ne'
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  let k := g_L.factorization r₀
  let a := h₀.factorization r₀
  let e₀ := m.factorization r₀
  let M := ((q + 1) / 2).factorization r₀
  have he0_eq : e₀ = k + a := by
    dsimp [e₀, k, a]
    rw [hm_eq, Nat.factorization_mul (mul_ne_zero (mul_ne_zero hgL0 hgR0) hh00) hu00,
      Finsupp.add_apply, Nat.factorization_mul (mul_ne_zero hgL0 hgR0) hh00,
      Finsupp.add_apply, Nat.factorization_mul hgL0 hgR0, Finsupp.add_apply]
    simp only [hgR_zero, hu0_zero, add_zero]
  have hM_eq : M = k + 2 * a := by
    dsimp [M, k, a]
    rw [hA_eq, Nat.factorization_mul (mul_ne_zero hgL0 hgR0) (pow_ne_zero 2 hh00),
      Finsupp.add_apply, Nat.factorization_mul hgL0 hgR0, Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hgR_zero, add_zero]
  have he0_pos : 1 ≤ e₀ :=
    (hr₀_prime.dvd_iff_one_le_factorization hm0).mp (Nat.dvd_of_mem_primeFactors hr₀_m)
  have hr0_pow_dvd_A : r₀ ^ M ∣ (q + 1) / 2 := Nat.ordProj_dvd ((q + 1) / 2) r₀
  by_cases hk0 : k = 0
  · have hM_2e0 : M = 2 * e₀ := by omega
    have hpow_dvd : r₀ ^ (2 * e₀) ∣ (q + 1) / 2 := hM_2e0 ▸ hr0_pow_dvd_A
    have hndvd :=
      (linear_euler_unique_source_dvd_sigma_B_and_index_of_source
        ho hN hq hqm hform hr₀_m hq_dvd_r0).1
    exact hndvd hpow_dvd
  · have hk_pos : 1 ≤ k := by omega
    have hM_pos : 1 ≤ M := by omega
    have hM_le_2e0 : M ≤ 2 * e₀ := by omega
    have h2e0_le_2M : 2 * e₀ ≤ 2 * M := by omega
    let X := r₀ ^ M
    have hX_ge_r0 : r₀ ≤ X := by
      calc
        r₀ = r₀ ^ 1 := (pow_one r₀).symm
        _ ≤ r₀ ^ M := Nat.pow_le_pow_right hr₀_prime.pos hM_pos
    have hX_ge3 : 3 ≤ X := by omega
    have hA_odd : Odd ((q + 1) / 2) := by
      rw [hA_eq]
      exact (hgL_odd.mul hgR_odd).mul hh0_odd.pow
    obtain ⟨C, hA_C⟩ := hr0_pow_dvd_A
    have hC_odd : Odd C := hA_odd.of_dvd_nat ⟨X, by rw [hA_C, mul_comm]⟩
    have hC_pos : 1 ≤ C := hC_odd.pos
    have hq1_eq_C : q + 1 = 2 * C * X := by
      rw [hq1_eq, hA_C]
      ring
    let c₀ := sigma 1 (r₀ ^ (2 * e₀)) / q
    obtain ⟨hsig_eq, _, hc0_odd, _⟩ :=
      linear_euler_cofactor_quotient_structure_of_source ho hN hq hqm hform hr₀_m hq_dvd_r0
    have hsig_eq' : sigma 1 (r₀ ^ (2 * e₀)) = q * c₀ := hsig_eq
    have hc0_pos : 1 ≤ c₀ := hc0_odd.pos
    have hgeom : (r₀ - 1) * sigma 1 (r₀ ^ (2 * e₀)) + 1 = r₀ ^ (2 * e₀ + 1) := by
      rw [sigma_one_apply_prime_pow hr₀_prime, mul_comm]
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ r₀)] using
        geom_sum_mul_add (r₀ - 1) (2 * e₀ + 1)
    have hq_c0_pow : (r₀ - 1) * q * c₀ + 1 = r₀ ^ (2 * e₀ + 1) := by
      rw [← hgeom, hsig_eq']
      ring
    have hq1_c0_pow : (r₀ - 1) * (q + 1) * c₀ + 1 = r₀ ^ (2 * e₀ + 1) + (r₀ - 1) * c₀ := by
      calc
        (r₀ - 1) * (q + 1) * c₀ + 1
            = ((r₀ - 1) * q * c₀ + 1) + (r₀ - 1) * c₀ := by ring
        _ = r₀ ^ (2 * e₀ + 1) + (r₀ - 1) * c₀ := by rw [hq_c0_pow]
    have hX_dvd_pow : X ∣ r₀ ^ (2 * e₀ + 1) :=
      pow_dvd_pow r₀ (by omega : M ≤ 2 * e₀ + 1)
    obtain ⟨P, hP⟩ := hX_dvd_pow
    have hmod_eq : X * ((r₀ - 1) * 2 * C * c₀) + 1 = X * P + (r₀ - 1) * c₀ := by
      calc
        X * ((r₀ - 1) * 2 * C * c₀) + 1
            = (r₀ - 1) * (2 * C * X) * c₀ + 1 := by ring
        _ = (r₀ - 1) * (q + 1) * c₀ + 1 := by rw [← hq1_eq_C]
        _ = r₀ ^ (2 * e₀ + 1) + (r₀ - 1) * c₀ := hq1_c0_pow
        _ = X * P + (r₀ - 1) * c₀ := by rw [hP]
    have hmod1 : 1 ≡ (r₀ - 1) * c₀ [MOD X] := by
      have h1 : X * ((r₀ - 1) * 2 * C * c₀) + 1 ≡ 1 [MOD X] := Nat.ModEq.modulus_mul_add
      have h2 : X * P + (r₀ - 1) * c₀ ≡ (r₀ - 1) * c₀ [MOD X] := Nat.ModEq.modulus_mul_add
      rw [hmod_eq] at h1
      exact h1.symm.trans h2
    have h1_le : 1 ≤ (r₀ - 1) * c₀ := Nat.mul_pos (by omega) hc0_pos
    obtain ⟨t, ht⟩ := (Nat.modEq_iff_exists_eq_add h1_le).mp hmod1
    have hr0_cases : r₀ = 3 ∨ 5 ≤ r₀ := by
      obtain ⟨u, hu⟩ := hr₀_odd
      omega
    rcases hr0_cases with hr0_eq3 | hr0_ge5
    · subst hr0_eq3
      have ht' : 2 * c₀ = 1 + X * t := by
        change 2 * c₀ = 1 + X * t at ht
        exact ht
      have hX_odd : Odd X := (by decide : Odd 3).pow
      have ht_mod : t % 2 = 1 := by
        have hX_mod : X % 2 = 1 := Nat.odd_iff.mp hX_odd
        have hmul_mod : (X * t) % 2 = t % 2 := by
          rw [Nat.mul_mod, hX_mod, one_mul, Nat.mod_mod]
        have h_lhs : (2 * c₀) % 2 = 0 := by omega
        have h_rhs : (1 + X * t) % 2 = (1 + t % 2) % 2 := by
          rw [Nat.add_mod, hmul_mod, Nat.mod_eq_of_lt (by decide : 1 < 2)]
        rw [ht'] at h_lhs
        omega
      have ht_cases : t = 1 ∨ 3 ≤ t := by omega
      have hC_mod : C % 2 = 1 := Nat.odd_iff.mp hC_odd
      have hC_cases : C = 1 ∨ 3 ≤ C := by omega
      have hq_c0_pow3 : q * (2 * c₀) + 1 = 3 ^ (2 * e₀ + 1) := by
        have hq_c0_pow' : 2 * q * c₀ + 1 = 3 ^ (2 * e₀ + 1) := hq_c0_pow
        calc
          q * (2 * c₀) + 1 = 2 * q * c₀ + 1 := by ring
          _ = 3 ^ (2 * e₀ + 1) := hq_c0_pow'
      rcases ht_cases with rfl | ht_ge3
      · rcases hC_cases with rfl | hC_ge3
        · have h2c0 : 2 * c₀ = X + 1 := by omega
          have hq_eq : q + 1 = 2 * X := by linarith only [hq1_eq_C]
          have hprod_eq : 3 ^ (2 * e₀ + 1) = X * (2 * X + 1) := by
            have h1 : 3 ^ (2 * e₀ + 1) + (X + 1) = 2 * X * (X + 1) + 1 := by
              calc
                3 ^ (2 * e₀ + 1) + (X + 1)
                    = (q * (2 * c₀) + 1) + 2 * c₀ := by rw [hq_c0_pow3, h2c0]
                _ = (q + 1) * (2 * c₀) + 1 := by ring
                _ = 2 * X * (X + 1) + 1 := by rw [hq_eq, h2c0]
            have h2 : 2 * X * (X + 1) + 1 = X * (2 * X + 1) + (X + 1) := by ring
            omega
          have hpow_dvd : 3 ^ (M + 1) ∣ 3 ^ (2 * e₀ + 1) :=
            pow_dvd_pow 3 (by omega : M + 1 ≤ 2 * e₀ + 1)
          have hX3_dvd : X * 3 ∣ X * (2 * X + 1) := by
            rw [Nat.pow_succ, hprod_eq] at hpow_dvd
            exact hpow_dvd
          have h3_dvd : 3 ∣ 2 * X + 1 :=
            (mul_dvd_mul_iff_left (by omega : X ≠ 0)).mp hX3_dvd
          have h3_dvd_X : 3 ∣ X := dvd_pow_self 3 (by omega : M ≠ 0)
          obtain ⟨u, hu⟩ := h3_dvd_X
          obtain ⟨v, hv⟩ := h3_dvd
          rw [hu] at hv
          omega
        · let X' := X - 3
          let C' := C - 3
          have hX' : X = X' + 3 := by omega
          have hC' : C = C' + 3 := by omega
          have hq_ge : 6 * X' + 17 ≤ q := by
            have h1 : q + 1 = 2 * C' * (X' + 3) + (6 * X' + 17) + 1 := by
              rw [hq1_eq_C, hC', hX']
              ring
            omega
          have hc0_ge : X' + 4 ≤ 2 * c₀ := by
            rw [ht', mul_one, hX']
            omega
          have hmul_le : (6 * X' + 17) * (X' + 4) ≤ q * (2 * c₀) :=
            (Nat.mul_le_mul_right _ hq_ge).trans (Nat.mul_le_mul_left _ hc0_ge)
          have hpow_le : 3 ^ (2 * e₀ + 1) ≤ 3 * (X' + 3) ^ 2 := by
            calc
              3 ^ (2 * e₀ + 1) ≤ 3 ^ (2 * M + 1) :=
                Nat.pow_le_pow_right (by decide : 0 < 3) (by omega)
              _ = 3 * (3 ^ M) ^ 2 := by ring
              _ = 3 * (X' + 3) ^ 2 := by change 3 * X ^ 2 = _; rw [hX']
          have hlhs : (6 * X' + 17) * (X' + 4) + 1 =
              3 * (X' + 3) ^ 2 + (3 * X' ^ 2 + 23 * X' + 42) := by ring
          omega
      · let X' := X - 3
        let C' := C - 1
        let t' := t - 3
        have hX' : X = X' + 3 := by omega
        have hC' : C = C' + 1 := by omega
        have ht'' : t = t' + 3 := by omega
        have hq_ge : 2 * X' + 5 ≤ q := by
          have h1 : q + 1 = 2 * C' * (X' + 3) + (2 * X' + 5) + 1 := by
            rw [hq1_eq_C, hC', hX']
            ring
          omega
        have hc0_ge : 3 * X' + 10 ≤ 2 * c₀ := by
          have h2 : 2 * c₀ = (X' + 3) * t' + (3 * X' + 10) := by
            rw [ht', hX', ht'']
            ring
          omega
        have hmul_le : (2 * X' + 5) * (3 * X' + 10) ≤ q * (2 * c₀) :=
          (Nat.mul_le_mul_right _ hq_ge).trans (Nat.mul_le_mul_left _ hc0_ge)
        have hpow_le : 3 ^ (2 * e₀ + 1) ≤ 3 * (X' + 3) ^ 2 := by
          calc
            3 ^ (2 * e₀ + 1) ≤ 3 ^ (2 * M + 1) :=
              Nat.pow_le_pow_right (by decide : 0 < 3) (by omega)
            _ = 3 * (3 ^ M) ^ 2 := by ring
            _ = 3 * (X' + 3) ^ 2 := by change 3 * X ^ 2 = _; rw [hX']
        have hlhs : (2 * X' + 5) * (3 * X' + 10) + 1 =
            3 * (X' + 3) ^ 2 + (3 * X' ^ 2 + 17 * X' + 24) := by ring
        omega
    · have hr0_sub_mod : X ≡ 1 [MOD r₀ - 1] := by
        have hsub : r₀ ≡ 1 [MOD r₀ - 1] := Nat.modEq_sub (by omega : 1 ≤ r₀)
        simpa only [one_pow] using hsub.pow M
      have h1t_mod : 1 + X * t ≡ 1 + t [MOD r₀ - 1] := by
        have hXt := hr0_sub_mod.mul_right t
        rw [one_mul] at hXt
        exact hXt.add_left 1
      have hc0_mod_zero : 0 ≡ (r₀ - 1) * c₀ [MOD r₀ - 1] :=
        (Nat.modEq_zero_iff_dvd.mpr ⟨c₀, rfl⟩).symm
      have h0_mod_1t : 0 ≡ 1 + t [MOD r₀ - 1] := by
        rw [← ht] at h1t_mod
        exact hc0_mod_zero.trans h1t_mod
      have hdvd_1t : r₀ - 1 ∣ 1 + t := Nat.modEq_zero_iff_dvd.mp h0_mod_1t.symm
      have hle_1t : r₀ - 1 ≤ 1 + t := Nat.le_of_dvd (by omega : 0 < 1 + t) hdvd_1t
      have ht_ge : r₀ - 2 ≤ t := by omega
      have hX_ge5 : 5 ≤ X := le_trans hr0_ge5 hX_ge_r0
      let r' := r₀ - 5
      let X' := X - 5
      let C' := C - 1
      let t' := t - (r₀ - 2)
      have hr' : r₀ = r' + 5 := by omega
      have hX' : X = X' + 5 := by omega
      have hC' : C = C' + 1 := by omega
      have ht' : t = t' + (r' + 3) := by omega
      have hq_ge : 2 * X' + 9 ≤ q := by
        have h1 : q + 1 = 2 * C' * (X' + 5) + (2 * X' + 9) + 1 := by
          rw [hq1_eq_C, hC', hX']
          ring
        omega
      have hc0_lb : 1 + (X' + 5) * (r' + 3) ≤ (r₀ - 1) * c₀ := by
        have h1 : (r₀ - 1) * c₀ = (X' + 5) * t' + (1 + (X' + 5) * (r' + 3)) := by
          rw [ht, hX', ht']
          ring
        omega
      have hmul_le : (2 * X' + 9) * (1 + (X' + 5) * (r' + 3)) ≤ q * ((r₀ - 1) * c₀) :=
        (Nat.mul_le_mul_right _ hq_ge).trans (Nat.mul_le_mul_left _ hc0_lb)
      have hq_c0_eq : q * ((r₀ - 1) * c₀) + 1 = r₀ ^ (2 * e₀ + 1) := by
        rw [← hq_c0_pow]
        ring
      have hpow_le : r₀ ^ (2 * e₀ + 1) ≤ (r' + 5) * (X' + 5) ^ 2 := by
        calc
          r₀ ^ (2 * e₀ + 1) ≤ r₀ ^ (2 * M + 1) := Nat.pow_le_pow_right hr₀_prime.pos (by omega)
          _ = r₀ * (r₀ ^ M) ^ 2 := by ring
          _ = (r' + 5) * (X' + 5) ^ 2 := by change r₀ * X ^ 2 = _; rw [hr', hX']
      have hlhs : (2 * X' + 9) * (1 + (X' + 5) * (r' + 3)) + 1 =
          (r' + 5) * (X' + 5) ^ 2 +
            (X' ^ 2 * r' + X' ^ 2 + 9 * X' * r' + 9 * X' + 20 * r' + 20) := by ring
      omega

/-- **1. Unconditional Right-Source Forcing**:
On any linear Euler odd perfect number `N = q * m ^ 2`, eliminates the `r₀ ∣ m_L` half of
`linear_euler_gcd_coprime_split_and_quotient_duality`, forcing `¬ r₀ ∣ m_L`, `r₀ ∣ m_R`,
`r₀ ∣ u₀`, `A.factorization r₀ < m.factorization r₀`, `A.factorization r₀ < I.factorization r₀`,
and `W_R * sigma 1 (m_L ^ 2) = g_L * g_R * u₀ ^ 2`. -/
theorem linear_euler_unique_source_right_forcing {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2) :
    let A := (q + 1) / 2
    let I := componentIndex N q
    let L := Nat.factorizationLCMLeft A I
    let R := Nat.factorizationLCMRight A I
    let m_L := Nat.gcd m L
    let m_R := Nat.gcd m R
    let W_R := sigma 1 (m_R ^ 2) / q
    ∃ h₀ u₀ g_L g_R r₀ : ℕ,
      Odd h₀ ∧ Odd u₀ ∧ Odd g_L ∧ Odd g_R ∧
      1 ≤ h₀ ∧ 1 ≤ u₀ ∧ 1 ≤ g_L ∧ 1 ≤ g_R ∧
      Nat.Coprime h₀ u₀ ∧ Nat.Coprime g_L g_R ∧ Nat.Coprime g_L u₀ ∧ Nat.Coprime g_R h₀ ∧
      Nat.Coprime m_L m_R ∧
      Nat.gcd A I = g_L * g_R ∧
      m_L = g_L * h₀ ∧ m_R = g_R * u₀ ∧
      A = g_L * g_R * h₀ ^ 2 ∧ I = g_L * g_R * u₀ ^ 2 ∧ m = g_L * g_R * h₀ * u₀ ∧
      r₀ ∈ m.primeFactors ∧
      q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀)) ∧
      ¬ r₀ ∣ m_L ∧
      r₀ ∣ m_R ∧
      r₀ ∣ u₀ ∧
      A.factorization r₀ < m.factorization r₀ ∧
      A.factorization r₀ < I.factorization r₀ ∧
      1 ≤ W_R ∧ Odd W_R ∧
      W_R * sigma 1 (m_L ^ 2) = g_L * g_R * u₀ ^ 2 ∧
      sigma 1 (m_L ^ 2) ∣ g_L * g_R * u₀ ^ 2 ∧
      (q + 1) * W_R * sigma 1 (m_L ^ 2) = 2 * m_L ^ 2 * m_R ^ 2 := by
  intro A I L R m_L m_R W_R
  obtain ⟨h₀, u₀, g_L, g_R, hh0_odd, hu0_odd, hgL_odd, hgR_odd, hh0_ge1, hu0_ge3, _,
    hgL_ge1, hgR_ge1, hcop_h0u0, hcop_gLgR, hcop_gLu0, hcop_gRh0, hg_eq, hmL_eq, hmR_eq,
    _, _, hA_eq, hI_eq, hm_eq, r₀, hr₀_m, hq_dvd_r0, hbranch, _⟩ :=
    linear_euler_gcd_coprime_split_and_quotient_duality ho hN hq hqm hform
  have hRight : r₀ ∣ m_R ∧ ¬ r₀ ∣ m_L ∧ 1 ≤ W_R ∧ Odd W_R ∧
      W_R * sigma 1 (m_L ^ 2) = g_L * g_R * u₀ ^ 2 ∧
      (q + 1) * W_R * sigma 1 (m_L ^ 2) = 2 * m_L ^ 2 * m_R ^ 2 := by
    rcases hbranch with ⟨_, hr0_not_mR, _⟩ | ⟨hr0_mR, hr0_not_mL, hWR_ge1, hWR_odd, hWR_sigL, hq1⟩
    · exact absurd
        (r0_not_dvd_mL_aux ho hN hq hqm hform hh0_odd hu0_odd hgL_odd hgR_odd
          hmR_eq hA_eq hm_eq hr₀_m hq_dvd_r0 hr0_not_mR)
        False.elim
    · exact ⟨hr0_mR, hr0_not_mL, hWR_ge1, hWR_odd, hWR_sigL, hq1⟩
  rcases hRight with ⟨hr0_mR, hr0_not_mL, hWR_ge1, hWR_odd, hWR_sigL, hq1⟩
  have hmL_eq' : m_L = g_L * h₀ := hmL_eq
  have hmR_eq' : m_R = g_R * u₀ := hmR_eq
  have hcop_mLmR : Nat.Coprime m_L m_R := by
    rw [hmL_eq', hmR_eq']
    exact (hcop_gLgR.mul_right hcop_gLu0).mul_left (hcop_gRh0.symm.mul_right hcop_h0u0)
  have hu0_ge1 : 1 ≤ u₀ := by omega
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀_m
  have hr0_dvd_R : r₀ ∣ R := hr0_mR.trans (Nat.gcd_dvd_right m R)
  have hA_lt_I : A.factorization r₀ < I.factorization r₀ := by
    by_contra hle
    have hI_le_A : I.factorization r₀ ≤ A.factorization r₀ := not_lt.mp hle
    have hr0_dvd_prod : r₀ ∣ (Nat.lcm A I).factorization.prod fun r n =>
        if I.factorization r ≤ A.factorization r then 1 else r ^ n := hr0_dvd_R
    rw [Finsupp.prod, hr₀_prime.prime.dvd_finsetProd_iff] at hr0_dvd_prod
    obtain ⟨r, hr_mem, hr_dvd⟩ := hr0_dvd_prod
    have hr_prime : r.Prime := Nat.prime_of_mem_primeFactors hr_mem
    by_cases hrp : r = r₀
    · subst hrp
      simp only [hI_le_A, ↓reduceIte] at hr_dvd
      exact hr₀_prime.not_dvd_one hr_dvd
    · split_ifs at hr_dvd with hcond
      · exact hr₀_prime.not_dvd_one hr_dvd
      · exact hrp ((Nat.prime_dvd_prime_iff_eq hr₀_prime hr_prime).mp
          (hr₀_prime.dvd_of_dvd_pow hr_dvd)).symm
  have hr0_ndvd_gL : ¬ r₀ ∣ g_L := fun hd =>
    hr0_not_mL (hmL_eq' ▸ hd.trans (dvd_mul_right g_L h₀))
  have hr0_ndvd_h0 : ¬ r₀ ∣ h₀ := fun hd =>
    hr0_not_mL (hmL_eq' ▸ hd.trans (dvd_mul_left h₀ g_L))
  have hgL_zero : g_L.factorization r₀ = 0 := Nat.factorization_eq_zero_of_not_dvd hr0_ndvd_gL
  have hh0_zero : h₀.factorization r₀ = 0 := Nat.factorization_eq_zero_of_not_dvd hr0_ndvd_h0
  have hgL0 : g_L ≠ 0 := hgL_odd.pos.ne'
  have hgR0 : g_R ≠ 0 := hgR_odd.pos.ne'
  have hh00 : h₀ ≠ 0 := hh0_odd.pos.ne'
  have hu00 : u₀ ≠ 0 := hu0_odd.pos.ne'
  have hA_fact : A.factorization r₀ = g_R.factorization r₀ := by
    change ((q + 1) / 2).factorization r₀ = g_R.factorization r₀
    rw [hA_eq, Nat.factorization_mul (mul_ne_zero hgL0 hgR0) (pow_ne_zero 2 hh00),
      Finsupp.add_apply, Nat.factorization_mul hgL0 hgR0, Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hgL_zero, zero_add,
      hh0_zero, mul_zero, add_zero]
  have hI_fact : I.factorization r₀ = g_R.factorization r₀ + 2 * u₀.factorization r₀ := by
    change (componentIndex N q).factorization r₀ = g_R.factorization r₀ + 2 * u₀.factorization r₀
    rw [hI_eq, Nat.factorization_mul (mul_ne_zero hgL0 hgR0) (pow_ne_zero 2 hu00),
      Finsupp.add_apply, Nat.factorization_mul hgL0 hgR0, Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hgL_zero, zero_add]
  have hm_fact : m.factorization r₀ = g_R.factorization r₀ + u₀.factorization r₀ := by
    rw [hm_eq, Nat.factorization_mul (mul_ne_zero (mul_ne_zero hgL0 hgR0) hh00) hu00,
      Finsupp.add_apply, Nat.factorization_mul (mul_ne_zero hgL0 hgR0) hh00,
      Finsupp.add_apply, Nat.factorization_mul hgL0 hgR0, Finsupp.add_apply,
      hgL_zero, zero_add, hh0_zero, add_zero]
  have hu0_fact_pos : 1 ≤ u₀.factorization r₀ := by omega
  have hr0_u0 : r₀ ∣ u₀ := (hr₀_prime.dvd_iff_one_le_factorization hu00).mpr hu0_fact_pos
  have hA_lt_m : A.factorization r₀ < m.factorization r₀ := by omega
  have hsig_dvd : sigma 1 (m_L ^ 2) ∣ g_L * g_R * u₀ ^ 2 :=
    ⟨W_R, by rw [← hWR_sigL, mul_comm]⟩
  exact ⟨h₀, u₀, g_L, g_R, r₀,
    hh0_odd, hu0_odd, hgL_odd, hgR_odd,
    hh0_ge1, hu0_ge1, hgL_ge1, hgR_ge1,
    hcop_h0u0, hcop_gLgR, hcop_gLu0, hcop_gRh0,
    hcop_mLmR, hg_eq, hmL_eq, hmR_eq, hA_eq, hI_eq, hm_eq,
    hr₀_m, hq_dvd_r0, hr0_not_mL, hr0_mR, hr0_u0, hA_lt_m, hA_lt_I,
    hWR_ge1, hWR_odd, hWR_sigL, hsig_dvd, hq1⟩

/-- **2. Unconditional Right-Source `ordCompl` Peeling**:
Discharges the `r₀ ∣ m_R →` guard of `linear_euler_right_source_peeling_dichotomy` via
`linear_euler_unique_source_right_forcing` and `linear_euler_unique_q_source_and_bound`. -/
theorem linear_euler_unconditional_right_source_peeling {N q m : ℕ}
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
      ¬ r₀ ∣ m_L ∧
      r₀ ∣ m_R ∧
      r₀ ∣ u₀ ∧
      (let e₀ := m.factorization r₀
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
  obtain ⟨h₀, u₀, g_L, g_R, r₀,
    _, _, _, _,
    hh0_ge1, hu0_ge1, hgL_ge1, hgR_ge1,
    _, _, _, _, _, _, _, _,
    hA_eq, hI_eq, _,
    hr₀_m, hq_dvd_r0, hr0_not_mL, hr0_mR, _, _, hA_lt_I, _⟩ :=
    linear_euler_unique_source_right_forcing ho hN hq hqm hform
  obtain ⟨h₀', u₀', g_L', g_R', r₀', hA_eq', hI_eq', hmL_eq', hmR_eq',
    hr₀'_m, hq_dvd_r0', hpeel⟩ :=
    linear_euler_right_source_peeling_dichotomy ho hN hq hqm hform
  obtain ⟨_, r₁, _, _, _, _, _, huniq⟩ :=
    linear_euler_unique_q_source_and_bound ho hN hq hqm hform
  have hr_eq : r₀' = r₀ := (huniq r₀' hr₀'_m hq_dvd_r0').trans (huniq r₀ hr₀_m hq_dvd_r0).symm
  rw [hr_eq] at hr₀'_m hq_dvd_r0' hpeel
  have hA0 : A ≠ 0 := by
    change (q + 1) / 2 ≠ 0
    rw [hA_eq]
    exact mul_ne_zero (mul_ne_zero (by omega) (by omega)) (pow_ne_zero 2 (by omega))
  have hI0 : I ≠ 0 := by
    change componentIndex N q ≠ 0
    rw [hI_eq]
    exact mul_ne_zero (mul_ne_zero (by omega) (by omega)) (pow_ne_zero 2 (by omega))
  have hA_eq'' : A = g_L' * g_R' * h₀' ^ 2 := hA_eq'
  have hI_eq'' : I = g_L' * g_R' * u₀' ^ 2 := hI_eq'
  have hgL'0 : g_L' ≠ 0 := fun h0 => hA0 (by rw [hA_eq'', h0]; ring)
  have hgR'0 : g_R' ≠ 0 := fun h0 => hA0 (by rw [hA_eq'', h0]; ring)
  have hh0'0 : h₀' ≠ 0 := fun h0 => hA0 (by rw [hA_eq'', h0]; ring)
  have hu0'0 : u₀' ≠ 0 := fun h0 => hI0 (by rw [hI_eq'', h0]; ring)
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀_m
  have hr0_ndvd_gL' : ¬ r₀ ∣ g_L' := fun hd =>
    hr0_not_mL (hmL_eq' ▸ hd.trans (dvd_mul_right g_L' h₀'))
  have hr0_ndvd_h0' : ¬ r₀ ∣ h₀' := fun hd =>
    hr0_not_mL (hmL_eq' ▸ hd.trans (dvd_mul_left h₀' g_L'))
  have hgL'_zero : g_L'.factorization r₀ = 0 := Nat.factorization_eq_zero_of_not_dvd hr0_ndvd_gL'
  have hh0'_zero : h₀'.factorization r₀ = 0 := Nat.factorization_eq_zero_of_not_dvd hr0_ndvd_h0'
  have hA'_fact : A.factorization r₀ = g_R'.factorization r₀ := by
    change ((q + 1) / 2).factorization r₀ = g_R'.factorization r₀
    rw [hA_eq', Nat.factorization_mul (mul_ne_zero hgL'0 hgR'0) (pow_ne_zero 2 hh0'0),
      Finsupp.add_apply, Nat.factorization_mul hgL'0 hgR'0, Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hgL'_zero, zero_add,
      hh0'_zero, mul_zero, add_zero]
  have hI'_fact : I.factorization r₀ = g_R'.factorization r₀ + 2 * u₀'.factorization r₀ := by
    change (componentIndex N q).factorization r₀ =
      g_R'.factorization r₀ + 2 * u₀'.factorization r₀
    rw [hI_eq', Nat.factorization_mul (mul_ne_zero hgL'0 hgR'0) (pow_ne_zero 2 hu0'0),
      Finsupp.add_apply, Nat.factorization_mul hgL'0 hgR'0, Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hgL'_zero, zero_add]
  have hA_lt_I' : A.factorization r₀ < I.factorization r₀ := hA_lt_I
  have hr0_u0' : r₀ ∣ u₀' :=
    (hr₀_prime.dvd_iff_one_le_factorization hu0'0).mpr (by omega)
  exact ⟨h₀', u₀', g_L', g_R', r₀, hA_eq', hI_eq', hmL_eq', hmR_eq',
    hr₀'_m, hq_dvd_r0', hr0_not_mL, hr0_mR, hr0_u0', hpeel hr0_mR⟩

end OddPerfect
