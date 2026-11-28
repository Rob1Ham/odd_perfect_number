module

public import OddPerfect.LinearEulerGcdSplitSourcePeeling
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Linear Euler Sixth-Power-Free Right-Source Peeling

Specializes `OddPerfect.linear_euler_gR_fourth_power_law` and
`OddPerfect.linear_euler_right_source_peeling_dichotomy` to sixth-power-free odd perfect numbers
`N = q * m ^ 2`:

1. `OddPerfect.sixth_power_free_gR_squarefree_and_valuation_pinch`:
   Every prime `p ∈ g_R.primeFactors` satisfies `m.factorization p = 2` and `N.factorization p = 4`
   (by sixth-power-freeness combined with `2 ≤ m.factorization p`), forcing exact valuations
   `g_R.factorization p = 1`, `u₀.factorization p = 1`, `A.factorization p = 1`,
   `I.factorization p = 3`, `p ∈ largeSources N q`, and `61 ≤ p`. Consequently `Squarefree g_R`,
   `g_R ∣ u₀`, and `g_R ^ 3 ∣ R = Nat.factorizationLCMRight A I`, while every `p ∈ g_L.primeFactors`
   satisfies `1 ≤ g_L.factorization p ≤ 2` and `61 ≤ p`.
2. `OddPerfect.sixth_power_free_right_source_peeling_profile`:
   Specializes the `ordCompl[r₀]` peeling dichotomy on `m_R = g_R * u₀` to sixth-power-free
   candidates, giving exact valuation/support pinning (`e₀ = 2`, `N.factorization r₀ = 4`,
   `A.factorization r₀ = 1`, `I.factorization r₀ = 3`, `r₀ ∈ largeSources N q`, `61 ≤ r₀`) when
   `r₀ ∣ g_R`, and `e₀ = 1 ∨ e₀ = 2` together with the peeled divisibility laws when `¬ r₀ ∣ g_R`.
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

private lemma sixth_power_free_m_factorization_le_two {N q m p : ℕ}
    (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hfree : ∀ r : ℕ, r.Prime → ¬ r ^ 6 ∣ N)
    (hm0 : m ≠ 0) (hp : p.Prime) (hp_dvd_m : p ∣ m) :
    m.factorization p ≤ 2 ∧ N.factorization p = 2 * m.factorization p := by
  have hp_neq : p ≠ q := fun hpq => hqm (hpq ▸ hp_dvd_m)
  have hp_ndvd_q : ¬ p ∣ q := fun hd =>
    hp_neq (((Nat.dvd_prime hq).mp hd).resolve_left hp.ne_one)
  have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hN_fact : N.factorization p = 2 * m.factorization p := by
    rw [hform, Nat.factorization_mul hq.ne_zero hm20, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hp_ndvd_q, zero_add,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have hN_lt6 : N.factorization p < 6 := by
    by_contra! hge6
    exact hfree p hp ((hp.pow_dvd_iff_le_factorization hN.2.ne').mpr hge6)
  exact ⟨by omega, hN_fact⟩

private lemma sixth_power_free_prime_ge_61_of_dvd_m_and_I {N q m p : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ r : ℕ, r.Prime → ¬ r ^ 6 ∣ N)
    (hform : N = q * m ^ 2) (hp : p.Prime)
    (hp_dvd_m : p ∣ m) (hp_dvd_I : p ∣ componentIndex N q) :
    61 ≤ p := by
  have hI_pos : 0 < componentIndex N q := (componentIndex_mul_eq_two_mul hN hq).2
  have hp_dvd_N : p ∣ N :=
    hform ▸ hp_dvd_m.trans ((dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left _ q))
  have hp_N : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hp_dvd_N, hN.2.ne'⟩
  have hp_ge53 : 53 ≤ p := sixth_power_free_min_prime_ge_53 ho hN hfree hp_N
  have hp_I : p ∈ (componentIndex N q).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hp_dvd_I, hI_pos.ne'⟩
  have hp_mod : p % 5 = 1 ∨ p % 3 = 1 :=
    (sixth_power_free_euler_index_drop_and_support ho hN hq hq4 he hev hfree).2 p hp_I
  exact prime_ge_61_of_ge_53_mod hp hp_ge53 hp_mod

private lemma factorizationLCMRight_lt_factorization {A I p : ℕ}
    (hp : p.Prime) (hp_dvd_R : p ∣ Nat.factorizationLCMRight A I) :
    A.factorization p < I.factorization p := by
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

private lemma gR_squarefree_and_valuations_of_split {N q m h₀ u₀ g_L g_R : ℕ}
    (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2)
    (hfree : ∀ r : ℕ, r.Prime → ¬ r ^ 6 ∣ N)
    (hm0 : m ≠ 0) (hgL0 : g_L ≠ 0) (hgR0 : g_R ≠ 0) (hh00 : h₀ ≠ 0) (hu00 : u₀ ≠ 0)
    (hcop_gLgR : Nat.Coprime g_L g_R) (hcop_gRh0 : Nat.Coprime g_R h₀)
    (hA_eq : (q + 1) / 2 = g_L * g_R * h₀ ^ 2)
    (hI_eq : componentIndex N q = g_L * g_R * u₀ ^ 2)
    (hmR_eq : Nat.gcd m (Nat.factorizationLCMRight ((q + 1) / 2) (componentIndex N q)) = g_R * u₀)
    (hmR_dvd_R : Nat.gcd m (Nat.factorizationLCMRight ((q + 1) / 2) (componentIndex N q)) ∣
        Nat.factorizationLCMRight ((q + 1) / 2) (componentIndex N q)) :
    Squarefree g_R ∧ g_R ∣ u₀ ∧
    ∀ p ∈ g_R.primeFactors,
      g_R.factorization p = 1 ∧
      u₀.factorization p = 1 ∧
      ((q + 1) / 2).factorization p = 1 ∧
      (componentIndex N q).factorization p = 3 := by
  let A := (q + 1) / 2
  let I := componentIndex N q
  let m_R := Nat.gcd m (Nat.factorizationLCMRight A I)
  have hmR0 : m_R ≠ 0 := by
    change Nat.gcd m (Nat.factorizationLCMRight A I) ≠ 0
    rw [hmR_eq]
    exact mul_ne_zero hgR0 hu00
  have hp_val : ∀ p ∈ g_R.primeFactors,
      g_R.factorization p = 1 ∧
      u₀.factorization p = 1 ∧
      A.factorization p = 1 ∧
      I.factorization p = 3 := by
    intro p hp_mem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have hp_dvd_gR : p ∣ g_R := Nat.dvd_of_mem_primeFactors hp_mem
    have hp_dvd_mR : p ∣ m_R := by
      change p ∣ Nat.gcd m (Nat.factorizationLCMRight A I)
      rw [hmR_eq]
      exact hp_dvd_gR.trans (dvd_mul_right g_R u₀)
    have hp_dvd_m : p ∣ m := hp_dvd_mR.trans (Nat.gcd_dvd_left m _)
    have hp_dvd_R : p ∣ Nat.factorizationLCMRight A I := hp_dvd_mR.trans hmR_dvd_R
    have hm_le2 : m.factorization p ≤ 2 :=
      (sixth_power_free_m_factorization_le_two hN hq hqm hform hfree hm0 hp hp_dvd_m).1
    have hmR_le_m : m_R.factorization p ≤ m.factorization p :=
      (Nat.factorization_le_iff_dvd hmR0 hm0).mpr (Nat.gcd_dvd_left m _) p
    have hmR_fact : m_R.factorization p = g_R.factorization p + u₀.factorization p := by
      change (Nat.gcd m (Nat.factorizationLCMRight A I)).factorization p =
        g_R.factorization p + u₀.factorization p
      rw [hmR_eq, Nat.factorization_mul hgR0 hu00, Finsupp.add_apply]
    have hp_ndvd_gL : ¬ p ∣ g_L := fun hd =>
      hp.not_dvd_one (hcop_gLgR ▸ Nat.dvd_gcd hd hp_dvd_gR)
    have hp_ndvd_h0 : ¬ p ∣ h₀ := fun hd =>
      hp.not_dvd_one (hcop_gRh0 ▸ Nat.dvd_gcd hp_dvd_gR hd)
    have hgL_zero : g_L.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hp_ndvd_gL
    have hh0_zero : h₀.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hp_ndvd_h0
    have hA_fact : A.factorization p = g_R.factorization p := by
      change ((q + 1) / 2).factorization p = g_R.factorization p
      rw [hA_eq, Nat.factorization_mul (mul_ne_zero hgL0 hgR0) (pow_ne_zero 2 hh00),
        Finsupp.add_apply, Nat.factorization_mul hgL0 hgR0, Finsupp.add_apply,
        hgL_zero, zero_add, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
        hh0_zero, mul_zero, add_zero]
    have hI_fact : I.factorization p = g_R.factorization p + 2 * u₀.factorization p := by
      change (componentIndex N q).factorization p = g_R.factorization p + 2 * u₀.factorization p
      rw [hI_eq, Nat.factorization_mul (mul_ne_zero hgL0 hgR0) (pow_ne_zero 2 hu00),
        Finsupp.add_apply, Nat.factorization_mul hgL0 hgR0, Finsupp.add_apply,
        hgL_zero, zero_add, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    have hA_lt_I : A.factorization p < I.factorization p :=
      factorizationLCMRight_lt_factorization hp hp_dvd_R
    have hgR_pos : 1 ≤ g_R.factorization p := (hp.dvd_iff_one_le_factorization hgR0).mp hp_dvd_gR
    have hu0_pos : 1 ≤ u₀.factorization p := by omega
    have hgR_eq1 : g_R.factorization p = 1 := by omega
    have hu0_eq1 : u₀.factorization p = 1 := by omega
    exact ⟨hgR_eq1, hu0_eq1, by omega, by omega⟩
  have hsq_gR : Squarefree g_R := by
    rw [Nat.squarefree_iff_factorization_le_one hgR0]
    intro p
    by_cases hp_mem : p ∈ g_R.primeFactors
    · exact (hp_val p hp_mem).1.le
    · have hp_zero : g_R.factorization p = 0 := by
        rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
        exact hp_mem
      omega
  have hgR_dvd_u0 : g_R ∣ u₀ := by
    rw [← Nat.factorization_le_iff_dvd hgR0 hu00]
    intro p
    by_cases hp_mem : p ∈ g_R.primeFactors
    · rw [(hp_val p hp_mem).1, (hp_val p hp_mem).2.1]
    · have hp_zero : g_R.factorization p = 0 := by
        rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
        exact hp_mem
      omega
  exact ⟨hsq_gR, hgR_dvd_u0, hp_val⟩

/-- **1. Sixth-Power-Free `g_R` Squarefree and Valuation Pinch**:
On any sixth-power-free odd perfect number `N = q * m ^ 2`, every prime factor `p ∈ g_R.primeFactors`
satisfies `g_R.factorization p = 1`, `u₀.factorization p = 1`, `A.factorization p = 1`,
`I.factorization p = 3`, `m.factorization p = 2`, `N.factorization p = 4`, `p ∈ largeSources N q`,
and `61 ≤ p`. Consequently `Squarefree g_R`, `g_R ∣ u₀`, and `g_R ^ 3 ∣ R`, while every
`p ∈ g_L.primeFactors` satisfies `1 ≤ g_L.factorization p ≤ 2` and `61 ≤ p`. -/
theorem sixth_power_free_gR_squarefree_and_valuation_pinch {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    ∃ m h₀ u₀ g_L g_R : ℕ,
      let A := (q + 1) / 2
      let I := componentIndex N q
      let R := Nat.factorizationLCMRight A I
      Odd m ∧ ¬ q ∣ m ∧ N = q * m ^ 2 ∧
      Nat.gcd A I = g_L * g_R ∧
      Nat.Coprime g_L g_R ∧ Nat.Coprime g_L u₀ ∧ Nat.Coprime g_R h₀ ∧ Nat.Coprime h₀ u₀ ∧
      A = g_L * g_R * h₀ ^ 2 ∧ I = g_L * g_R * u₀ ^ 2 ∧ R = g_R * u₀ ^ 2 ∧
      Squarefree g_R ∧
      g_R ∣ u₀ ∧
      g_R ^ 3 ∣ R ∧
      (∀ p ∈ g_R.primeFactors,
        g_R.factorization p = 1 ∧
        u₀.factorization p = 1 ∧
        A.factorization p = 1 ∧
        I.factorization p = 3 ∧
        m.factorization p = 2 ∧
        N.factorization p = 4 ∧
        p ∈ largeSources N q ∧
        61 ≤ p) ∧
      (∀ p ∈ g_L.primeFactors,
        1 ≤ g_L.factorization p ∧
        g_L.factorization p ≤ 2 ∧
        61 ≤ p) := by
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  obtain ⟨m, _, hm_odd, hqm, hform, _⟩ :=
    sixth_power_free_unique_q_source_mirror_dichotomy ho hN hq hq4 he hev hfree
  obtain ⟨h₀, u₀, g_L, g_R, hh0_odd, hu0_odd, hgL_odd, hgR_odd, _, _, _, _, _,
    hcop_h0u0, hcop_gLgR, hcop_gLu0, hcop_gRh0, hg_eq, _, hmR_eq, _, hR_eq,
    hA_eq, hI_eq, hm_eq, _⟩ :=
    linear_euler_gcd_coprime_split_and_quotient_duality ho hN hq_prime hqm hform
  let A := (q + 1) / 2
  let I := componentIndex N q
  let R := Nat.factorizationLCMRight A I
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  have hh00 : h₀ ≠ 0 := hh0_odd.pos.ne'
  have hu00 : u₀ ≠ 0 := hu0_odd.pos.ne'
  have hgL0 : g_L ≠ 0 := hgL_odd.pos.ne'
  have hgR0 : g_R ≠ 0 := hgR_odd.pos.ne'
  have hgL_dvd_m : g_L ∣ m := by
    rw [hm_eq]
    exact ⟨g_R * h₀ * u₀, by ring⟩
  have hgR_dvd_m : g_R ∣ m := by
    rw [hm_eq]
    exact ⟨g_L * h₀ * u₀, by ring⟩
  have hcore := gR_squarefree_and_valuations_of_split hN hq_prime hqm hform hfree
    hm0 hgL0 hgR0 hh00 hu00 hcop_gLgR hcop_gRh0 hA_eq hI_eq hmR_eq
    (Nat.gcd_dvd_right m R)
  rcases hcore with ⟨hsq_gR, hgR_dvd_u0, hgR_vals⟩
  have hgR3_dvd_R : g_R ^ 3 ∣ R := by
    have hpow2 : g_R ^ 2 ∣ u₀ ^ 2 := pow_dvd_pow_of_dvd hgR_dvd_u0 2
    have hpow3 : g_R * g_R ^ 2 ∣ g_R * u₀ ^ 2 := Nat.mul_dvd_mul_left g_R hpow2
    have hpow_eq : g_R ^ 3 = g_R * g_R ^ 2 := by ring
    change g_R ^ 3 ∣ ((q + 1) / 2).factorizationLCMRight (componentIndex N q)
    rw [hpow_eq, hR_eq]
    exact hpow3
  -- Re-prove the fourth-power law on the exact `g_R` from `linear_euler_gcd_coprime_split_and_quotient_duality`
  -- via `g_R.primeFactors` valuation bounds + `sixth_power_free_three_not_dvd`.
  have h3_ndvd : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  refine ⟨m, h₀, u₀, g_L, g_R, hm_odd, hqm, hform, hg_eq, hcop_gLgR, hcop_gLu0, hcop_gRh0,
    hcop_h0u0, hA_eq, hI_eq, hR_eq, hsq_gR, hgR_dvd_u0, hgR3_dvd_R, ?_, ?_⟩
  · intro p hp_mem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have hp_dvd_gR : p ∣ g_R := Nat.dvd_of_mem_primeFactors hp_mem
    have hp_dvd_m : p ∣ m := hp_dvd_gR.trans hgR_dvd_m
    have hp_dvd_I : p ∣ I := by
      change p ∣ componentIndex N q
      rw [hI_eq]
      exact hp_dvd_gR.trans ((dvd_mul_left g_R g_L).trans (dvd_mul_right _ (u₀ ^ 2)))
    have hp_dvd_N : p ∣ N :=
      hform ▸ hp_dvd_m.trans ((dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left _ q))
    have hp_N : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hp_dvd_N, hN.2.ne'⟩
    have hp_neq : p ≠ q := fun hpq => hqm (hpq ▸ hp_dvd_m)
    have hp_ne3 : p ≠ 3 := fun hp3 => h3_ndvd (hp3 ▸ hp_dvd_N)
    have hvals := hgR_vals p hp_mem
    have hm_fact : m.factorization p = g_R.factorization p + u₀.factorization p := by
      have hp_ndvd_gL : ¬ p ∣ g_L := fun hd =>
        hp.not_dvd_one (hcop_gLgR ▸ Nat.dvd_gcd hd hp_dvd_gR)
      have hp_ndvd_h0 : ¬ p ∣ h₀ := fun hd =>
        hp.not_dvd_one (hcop_gRh0 ▸ Nat.dvd_gcd hp_dvd_gR hd)
      rw [hm_eq, Nat.factorization_mul (mul_ne_zero (mul_ne_zero hgL0 hgR0) hh00) hu00,
        Finsupp.add_apply, Nat.factorization_mul (mul_ne_zero hgL0 hgR0) hh00,
        Finsupp.add_apply, Nat.factorization_mul hgL0 hgR0, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hp_ndvd_gL, zero_add,
        Nat.factorization_eq_zero_of_not_dvd hp_ndvd_h0, add_zero]
    have hm_eq2 : m.factorization p = 2 := by
      rw [hm_fact, hvals.1, hvals.2.1]
    have hN_eq4 : N.factorization p = 4 := by
      have hN_fact := (sixth_power_free_m_factorization_le_two hN hq_prime hqm hform hfree
        hm0 hp hp_dvd_m).2
      omega
    have hp_large : p ∈ largeSources N q :=
      Finset.mem_filter.mpr ⟨hp_N, hp_ne3, hp_neq, by omega⟩
    have hp_ge61 : 61 ≤ p :=
      sixth_power_free_prime_ge_61_of_dvd_m_and_I ho hN hq hq4 he hev hfree hform hp
        hp_dvd_m hp_dvd_I
    exact ⟨hvals.1, hvals.2.1, hvals.2.2.1, hvals.2.2.2, hm_eq2, hN_eq4, hp_large, hp_ge61⟩
  · intro p hp_mem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have hp_dvd_gL : p ∣ g_L := Nat.dvd_of_mem_primeFactors hp_mem
    have hgL_pos : 1 ≤ g_L.factorization p := (hp.dvd_iff_one_le_factorization hgL0).mp hp_dvd_gL
    have hp_dvd_m : p ∣ m := hp_dvd_gL.trans hgL_dvd_m
    have hgL_le_m : g_L.factorization p ≤ m.factorization p :=
      (Nat.factorization_le_iff_dvd hgL0 hm0).mpr hgL_dvd_m p
    have hm_le2 : m.factorization p ≤ 2 :=
      (sixth_power_free_m_factorization_le_two hN hq_prime hqm hform hfree hm0 hp hp_dvd_m).1
    have hp_dvd_I : p ∣ I := by
      change p ∣ componentIndex N q
      rw [hI_eq]
      exact hp_dvd_gL.trans ((dvd_mul_right g_L g_R).trans (dvd_mul_right _ (u₀ ^ 2)))
    have hp_ge61 : 61 ≤ p :=
      sixth_power_free_prime_ge_61_of_dvd_m_and_I ho hN hq hq4 he hev hfree hform hp
        hp_dvd_m hp_dvd_I
    exact ⟨hgL_pos, le_trans hgL_le_m hm_le2, hp_ge61⟩

/-- **2. Sixth-Power-Free Right-Source `ordCompl` Peeling Profile**:
Specializes `OddPerfect.linear_euler_right_source_peeling_dichotomy` to sixth-power-free odd
perfect numbers `N = q * m ^ 2`. Whenever the unique `q`-source `r₀` lies in `m_R = g_R * u₀`:
- If `r₀ ∣ g_R`, then `e₀ = 2`, `N.factorization r₀ = 4`, `A.factorization r₀ = 1`,
  `I.factorization r₀ = 3`, `r₀ ∈ largeSources N q`, and `61 ≤ r₀`;
- If `¬ r₀ ∣ g_R`, then `e₀ = 1 ∨ e₀ = 2`, `r₀ ^ e₀ ∣ u₀`, `Nat.Coprime r₀ A`,
  `M_R = g_R * (u₀ / r₀ ^ e₀)`, `r₀ ^ (2 * e₀) ∣ sigma 1 (M_R ^ 2) * sigma 1 (m_L ^ 2)`, and
  `c₀ ∣ g_L * g_R * (u₀ / r₀ ^ e₀) ^ 2`. -/
theorem sixth_power_free_right_source_peeling_profile {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    ∃ m h₀ u₀ g_L g_R r₀ : ℕ,
      let A := (q + 1) / 2
      let I := componentIndex N q
      let L := Nat.factorizationLCMLeft A I
      let R := Nat.factorizationLCMRight A I
      let m_L := Nat.gcd m L
      let m_R := Nat.gcd m R
      Odd m ∧ ¬ q ∣ m ∧ N = q * m ^ 2 ∧
      A = g_L * g_R * h₀ ^ 2 ∧
      I = g_L * g_R * u₀ ^ 2 ∧
      Squarefree g_R ∧
      g_R ∣ u₀ ∧
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
            e₀ = 2 ∧
            N.factorization r₀ = 4 ∧
            A.factorization r₀ = 1 ∧
            I.factorization r₀ = 3 ∧
            r₀ ∈ largeSources N q ∧
            61 ≤ r₀) ∨
         (¬ r₀ ∣ g_R ∧
            (e₀ = 1 ∨ e₀ = 2) ∧
            r₀ ^ e₀ ∣ u₀ ∧
            Nat.Coprime r₀ A ∧
            M_R = g_R * (u₀ / r₀ ^ e₀) ∧
            r₀ ^ (2 * e₀) ∣ sigma 1 (M_R ^ 2) * sigma 1 (m_L ^ 2) ∧
            c₀ ∣ g_L * g_R * (u₀ / r₀ ^ e₀) ^ 2))) := by
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  obtain ⟨m, _, hm_odd, hqm, hform, _⟩ :=
    sixth_power_free_unique_q_source_mirror_dichotomy ho hN hq hq4 he hev hfree
  obtain ⟨h₀, u₀, g_L, g_R, r₀, hA_eq, hI_eq, hmL_eq, hmR_eq, hr₀_m, hq_dvd_r0, hpeel⟩ :=
    linear_euler_right_source_peeling_dichotomy ho hN hq_prime hqm hform
  obtain ⟨_, _, hm_cop, _, _, _, _, _, hmR_dvd_R, _⟩ :=
    linear_euler_lcm_gcd_canonical_coprime_split ho hN hq_prime hqm hform
  let A := (q + 1) / 2
  let I := componentIndex N q
  let L := Nat.factorizationLCMLeft A I
  let R := Nat.factorizationLCMRight A I
  let m_L := Nat.gcd m L
  let m_R := Nat.gcd m R
  have hI_pos : 0 < I := (componentIndex_mul_eq_two_mul hN hq).2
  have hq_odd : Odd q := ho.of_dvd_nat (hform ▸ dvd_mul_right q (m ^ 2))
  have hA_pos : 0 < A := by
    change 0 < (q + 1) / 2
    have hq_ge1 : 1 ≤ q := hq_odd.pos
    omega
  have hgL0 : g_L ≠ 0 := by
    intro h0
    have hI0 : I = 0 := by
      change componentIndex N q = 0
      rw [hI_eq, h0, zero_mul, zero_mul]
    exact hI_pos.ne' hI0
  have hgR0 : g_R ≠ 0 := by
    intro h0
    have hI0 : I = 0 := by
      change componentIndex N q = 0
      rw [hI_eq, h0, mul_zero, zero_mul]
    exact hI_pos.ne' hI0
  have hu00 : u₀ ≠ 0 := by
    intro h0
    have hI0 : I = 0 := by
      change componentIndex N q = 0
      rw [hI_eq, h0, zero_pow (by decide : 2 ≠ 0), mul_zero]
    exact hI_pos.ne' hI0
  have hh00 : h₀ ≠ 0 := by
    intro h0
    have hA0 : A = 0 := by
      change (q + 1) / 2 = 0
      rw [hA_eq, h0, zero_pow (by decide : 2 ≠ 0), mul_zero]
    exact hA_pos.ne' hA0
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  have hm_cop_prod : Nat.Coprime (g_L * h₀) (g_R * u₀) := by
    rw [← hmL_eq, ← hmR_eq]
    exact hm_cop
  have hcop_gLgR : Nat.Coprime g_L g_R :=
    (hm_cop_prod.coprime_dvd_left (dvd_mul_right g_L h₀)).coprime_dvd_right (dvd_mul_right g_R u₀)
  have hcop_gRh0 : Nat.Coprime g_R h₀ :=
    ((hm_cop_prod.coprime_dvd_left (dvd_mul_left h₀ g_L)).coprime_dvd_right (dvd_mul_right g_R u₀)).symm
  have hcore := gR_squarefree_and_valuations_of_split hN hq_prime hqm hform hfree
    hm0 hgL0 hgR0 hh00 hu00 hcop_gLgR hcop_gRh0 hA_eq hI_eq hmR_eq
    hmR_dvd_R
  rcases hcore with ⟨hsq_gR, hgR_dvd_u0, hgR_vals⟩
  refine ⟨m, h₀, u₀, g_L, g_R, r₀, hm_odd, hqm, hform, hA_eq, hI_eq, hsq_gR, hgR_dvd_u0,
    hmL_eq, hmR_eq, hr₀_m, hq_dvd_r0, ?_⟩
  intro hr0_mR e₀ M_R c₀ W_R
  obtain ⟨hmR_fact, hmR_split, hcop_r0_MR, hWR_eq, hprod_eq, hbranch⟩ := hpeel hr0_mR
  refine ⟨hmR_fact, hmR_split, hcop_r0_MR, hWR_eq, hprod_eq, ?_⟩
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀_m
  have hr₀_dvd_m : r₀ ∣ m := Nat.dvd_of_mem_primeFactors hr₀_m
  have he0_pos : 1 ≤ e₀ := (hr₀_prime.dvd_iff_one_le_factorization hm0).mp hr₀_dvd_m
  have hm_le2_and_N := sixth_power_free_m_factorization_le_two hN hq_prime hqm hform hfree
    hm0 hr₀_prime hr₀_dvd_m
  have he0_le2 : e₀ ≤ 2 := hm_le2_and_N.1
  rcases hbranch with
    ⟨hr0_gR, he0_ge2, _, _, _, hr0_large_imp⟩ |
    ⟨hr0_not_gR, hr0_pow_u0, hcop_r0_A, hMR_eq, hr0_pow_dvd_sig, hc0_dvd⟩
  · left
    have he0_eq2 : e₀ = 2 := by omega
    have hN_eq4 : N.factorization r₀ = 4 := by
      have hN_fact := hm_le2_and_N.2
      change N.factorization r₀ = 2 * e₀ at hN_fact
      omega
    have hr0_mem_gR : r₀ ∈ g_R.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hr₀_prime, hr0_gR, hgR0⟩
    have hvals := hgR_vals r₀ hr0_mem_gR
    have hr0_dvd_I : r₀ ∣ I := by
      change r₀ ∣ componentIndex N q
      rw [hI_eq]
      exact hr0_gR.trans ((dvd_mul_left g_R g_L).trans (dvd_mul_right _ (u₀ ^ 2)))
    have hr0_ge61 : 61 ≤ r₀ :=
      sixth_power_free_prime_ge_61_of_dvd_m_and_I ho hN hq hq4 he hev hfree hform hr₀_prime
        hr₀_dvd_m hr0_dvd_I
    have hr0_ne3 : r₀ ≠ 3 := by omega
    exact ⟨hr0_gR, he0_eq2, hN_eq4, hvals.2.2.1, hvals.2.2.2, hr0_large_imp hr0_ne3, hr0_ge61⟩
  · right
    have he0_cases : e₀ = 1 ∨ e₀ = 2 := by omega
    exact ⟨hr0_not_gR, he0_cases, hr0_pow_u0, hcop_r0_A, hMR_eq, hr0_pow_dvd_sig, hc0_dvd⟩

end OddPerfect
