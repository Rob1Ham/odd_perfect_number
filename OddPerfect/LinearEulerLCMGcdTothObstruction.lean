module

public import OddPerfect.FactorizationLCMSplitCoprimeBalance
public import OddPerfect.LinearEulerTothObstruction
public import OddPerfect.LinearEulerIteratedPeeling
public import OddPerfect.SixthPowerFreeHalfSuccPinch
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Linear Euler LCM-GCD Tóth Obstruction

Couples the canonical coprime LCM-GCD split `m = m_L * m_R` from
`OddPerfect.FactorizationLCMSplitCoprimeBalance` (`linear_euler_lcm_gcd_canonical_coprime_split`)
with the unique `q`-source `r₀ ∈ m.primeFactors` (`OddPerfect.LinearEulerTothObstruction`,
`OddPerfect.LinearEulerIteratedPeeling`) to prove two unconditional theorems on `N = q * m ^ 2`:

1. `linear_euler_mL_eq_one_iff_and_r0_split_dichotomy`:
   Establishes `m_L = 1 ↔ L = 1`, `m_L ≠ 1 → 3 ≤ m_L ∧ 13 ≤ sigma 1 (m_L ^ 2)`,
   `13 ≤ sigma 1 (m_R ^ 2)`, and the exact split dichotomy for the unique `q`-source `r₀`
   between `r₀ ∣ m_L` (forcing `2 ≤ m.factorization r₀`, `r₀ ^ 4 ∣ N`, `2 * r₀ ∣ q + 1`) and
   `r₀ ∣ m_R`.
2. `sixth_power_free_lcm_gcd_coprime_split_profile`:
   Specializes Theorem 1 to sixth-power-free odd perfect numbers, establishing
   `53 ≤ m_R`, `2863 ≤ sigma 1 (m_R ^ 2)`, and in the `r₀ ∣ m_L` branch forcing
   `m.factorization r₀ = 2`, `r₀ ∈ largeSources N q`, and `61 ≤ r₀`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma sigma_sq_lower_bound {x : ℕ} (hx : 3 ≤ x) :
    1 + x + x ^ 2 ≤ sigma 1 (x ^ 2) := by
  have hx0 : x ≠ 0 := by omega
  have hx20 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx0
  have h1_lt_x : 1 < x := by omega
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

private lemma sigma_ordProj_dvd_sigma_of_coprime_left {A B C p : ℕ}
    (hp : p.Prime) (hAB : A = B * C) (hcop : B.Coprime C) (hpB : p ∈ B.primeFactors) :
    sigma 1 (ordProj[p] A) ∣ sigma 1 B := by
  have hB0 : B ≠ 0 := by
    intro h0
    subst h0
    simp at hpB
  have hp_dvd_B : p ∣ B := Nat.dvd_of_mem_primeFactors hpB
  have hC0 : C ≠ 0 := by
    intro h0
    rw [h0, Nat.coprime_zero_right] at hcop
    rw [hcop] at hp_dvd_B
    exact hp.not_dvd_one hp_dvd_B
  have hp_ndvd_C : ¬ p ∣ C := fun hpC =>
    hp.not_dvd_one (hcop ▸ Nat.dvd_gcd hp_dvd_B hpC)
  have hA_fact : A.factorization p = B.factorization p := by
    rw [hAB, Nat.factorization_mul hB0 hC0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hp_ndvd_C, add_zero]
  have hB_split : B = ordProj[p] B * ordCompl[p] B :=
    (Nat.ordProj_mul_ordCompl_eq_self B p).symm
  have hB_cop : (ordProj[p] B).Coprime (ordCompl[p] B) :=
    (Nat.coprime_ordCompl hp hB0).pow_left _
  have hord_eq : ordProj[p] A = ordProj[p] B := by rw [hA_fact]
  rw [hord_eq]
  conv_rhs => rw [hB_split, isMultiplicative_sigma.map_mul_of_coprime hB_cop]
  exact dvd_mul_right _ _

/-- **1. Canonical `m_L = 1 ↔ L = 1` Equivalence and `r₀` Split Dichotomy**:
On any linear Euler odd perfect number `N = q * m ^ 2`, letting `A := (q + 1) / 2`,
`I := componentIndex N q`, `L := Nat.factorizationLCMLeft A I`,
`R := Nat.factorizationLCMRight A I`, `m_L := Nat.gcd m L`, and `m_R := Nat.gcd m R`,
proves `m_L = 1 ↔ L = 1`, the lower bounds `13 ≤ σ(m_L^2)` (when `m_L ≠ 1`) and
`13 ≤ σ(m_R^2)`, and the exact dichotomy locating the unique `q`-source `r₀ ∈ m.primeFactors`
in either `m_L` (forcing `2 ≤ m.factorization r₀`, `r₀ ^ 4 ∣ N`, `2 * r₀ ∣ q + 1`) or `m_R`. -/
theorem linear_euler_mL_eq_one_iff_and_r0_split_dichotomy {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2) :
    let A := (q + 1) / 2
    let I := componentIndex N q
    let L := Nat.factorizationLCMLeft A I
    let R := Nat.factorizationLCMRight A I
    let m_L := Nat.gcd m L
    let m_R := Nat.gcd m R
    (m_L = 1 ↔ L = 1) ∧
    (m_L ≠ 1 → 3 ≤ m_L ∧ 13 ≤ sigma 1 (m_L ^ 2)) ∧
    13 ≤ sigma 1 (m_R ^ 2) ∧
    ∃ r₀ ∈ m.primeFactors,
      let e₀ := m.factorization r₀
      (sigma 1 (m ^ 2)).factorization q = 1 ∧
      q ∣ sigma 1 (r₀ ^ (2 * e₀)) ∧
      ((r₀ ∣ m_L ∧ ¬ r₀ ∣ m_R ∧
          r₀ ∣ A ∧ 2 * r₀ ∣ q + 1 ∧ 2 ≤ e₀ ∧ r₀ ^ 4 ∣ N ∧
          q ∣ sigma 1 (m_L ^ 2) ∧ ¬ q ∣ sigma 1 (m_R ^ 2) ∧
          sigma 1 (m_R ^ 2) ∣ I ∧
          (sigma 1 (m_L ^ 2) / q) * sigma 1 (m_R ^ 2) = I) ∨
       (r₀ ∣ m_R ∧ ¬ r₀ ∣ m_L ∧
          q ∣ sigma 1 (m_R ^ 2) ∧ ¬ q ∣ sigma 1 (m_L ^ 2) ∧
          sigma 1 (m_L ^ 2) ∣ I ∧
          (sigma 1 (m_R ^ 2) / q) * sigma 1 (m_L ^ 2) = I)) := by
  intro A I L R m_L m_R
  obtain ⟨hmL_odd, hmR_odd, hm_cop, hm_eq_mul, hmL_dvd_L, hmL_dvd_A, _, _,
    _, _, hmR_ge3, _, hsig_split, hsig_eq_qI⟩ :=
    linear_euler_lcm_gcd_canonical_coprime_split ho hN hq hqm hform
  obtain ⟨_, _, _, _, hL_dvd_A, _, _, h₀, u₀, _, _, _, _, _, hA_eq, hI_eq, hm_gh0u0, _, _, _, _⟩ :=
    universal_half_succ_index_gcd_square_parametrization ho hN hq hqm hform
  have hAI : A * I = m ^ 2 := by
    dsimp [A, I]
    rw [congrArg₂ (· * ·) hA_eq hI_eq, hm_gh0u0]
    ring
  have hmL_iff : m_L = 1 ↔ L = 1 := by
    constructor
    · intro hmL1
      by_contra hL1
      obtain ⟨p, hp, hp_dvd_L⟩ := Nat.exists_prime_and_dvd hL1
      have hp_dvd_A : p ∣ A := hp_dvd_L.trans hL_dvd_A
      have hp_dvd_m2 : p ∣ m ^ 2 := hAI ▸ hp_dvd_A.trans (dvd_mul_right A I)
      have hp_dvd_m : p ∣ m := hp.dvd_of_dvd_pow hp_dvd_m2
      have hp_dvd_mL : p ∣ m_L := Nat.dvd_gcd hp_dvd_m hp_dvd_L
      rw [hmL1] at hp_dvd_mL
      exact hp.not_dvd_one hp_dvd_mL
    · intro hL1
      dsimp [m_L]
      rw [hL1, Nat.gcd_one_right]
  have hmL_bounds : m_L ≠ 1 → 3 ≤ m_L ∧ 13 ≤ sigma 1 (m_L ^ 2) := by
    intro hmL_ne1
    have hmL_ge3 : 3 ≤ m_L := by
      obtain ⟨k, hk⟩ := hmL_odd
      have hmL_eq : m_L = 2 * k + 1 := hk
      omega
    have hsig_ge13 : 13 ≤ sigma 1 (m_L ^ 2) := by
      have h1 := sigma_sq_lower_bound hmL_ge3
      nlinarith only [hmL_ge3, h1]
    exact ⟨hmL_ge3, hsig_ge13⟩
  have hmR_sig_ge13 : 13 ≤ sigma 1 (m_R ^ 2) := by
    have h1 := sigma_sq_lower_bound hmR_ge3
    nlinarith only [hmR_ge3, h1]
  obtain ⟨hsigm2_fact_q, r₀, hr₀_m, hq_dvd_r0, _, _, _, _⟩ :=
    linear_euler_unique_q_source_and_bound ho hN hq hqm hform
  have hq_odd : Odd q := ho.of_dvd_nat (hform ▸ dvd_mul_right q (m ^ 2))
  have hmodd : Odd m :=
    ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
  have hm0 : m ≠ 0 := hmodd.pos.ne'
  have hmL0 : m_L ≠ 0 := hmL_odd.pos.ne'
  have hmR0 : m_R ≠ 0 := hmR_odd.pos.ne'
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀_m
  have hr₀_dvd_m : r₀ ∣ m := Nat.dvd_of_mem_primeFactors hr₀_m
  have hm2_split : m ^ 2 = m_L ^ 2 * m_R ^ 2 := by
    rw [hm_eq_mul]
    ring
  have hm2_cop : (m_L ^ 2).Coprime (m_R ^ 2) := hm_cop.pow 2 2
  have hord_r0 : ordProj[r₀] (m ^ 2) = r₀ ^ (2 * m.factorization r₀) := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have hsigm2_ne0 : sigma 1 (m ^ 2) ≠ 0 := (sigma_pos 1 (m ^ 2) (pow_ne_zero 2 hm0)).ne'
  have hsig_mL_ne0 : sigma 1 (m_L ^ 2) ≠ 0 := (sigma_pos 1 (m_L ^ 2) (pow_ne_zero 2 hmL0)).ne'
  have hsig_mR_ne0 : sigma 1 (m_R ^ 2) ≠ 0 := (sigma_pos 1 (m_R ^ 2) (pow_ne_zero 2 hmR0)).ne'
  have hq_not_both : ¬ (q ∣ sigma 1 (m_L ^ 2) ∧ q ∣ sigma 1 (m_R ^ 2)) := by
    rintro ⟨hqL, hqR⟩
    have hq2_dvd : q ^ 2 ∣ sigma 1 (m ^ 2) := by
      rw [hsig_split, pow_two]
      exact Nat.mul_dvd_mul hqL hqR
    have hle2 : 2 ≤ (sigma 1 (m ^ 2)).factorization q :=
      (hq.pow_dvd_iff_le_factorization hsigm2_ne0).mp hq2_dvd
    omega
  refine ⟨hmL_iff, hmL_bounds, hmR_sig_ge13, r₀, hr₀_m, hsigm2_fact_q, hq_dvd_r0, ?_⟩
  rcases hr₀_prime.dvd_mul.mp (hm_eq_mul ▸ hr₀_dvd_m) with hr0_L | hr0_R
  · left
    have hr0_not_R : ¬ r₀ ∣ m_R := fun hr0_R =>
      hr₀_prime.not_dvd_one (hm_cop ▸ Nat.dvd_gcd hr0_L hr0_R)
    have hr0_A : r₀ ∣ A := hr0_L.trans hmL_dvd_A
    have hq1_even : q + 1 = 2 * A := by
      dsimp [A]
      have := Nat.odd_iff.mp hq_odd
      omega
    have h2r0_q1 : 2 * r₀ ∣ q + 1 := by
      rw [hq1_even]
      exact Nat.mul_dvd_mul_left 2 hr0_A
    have he0_pos : 1 ≤ m.factorization r₀ :=
      (hr₀_prime.dvd_iff_one_le_factorization hm0).mp hr₀_dvd_m
    have he0_ne1 : m.factorization r₀ ≠ 1 := by
      intro he1
      have hndvd :=
        (linear_euler_square_source_coprime_half_succ ho hN hq hqm hform hr₀_m hq_dvd_r0 he1).2.1
      exact hndvd hr0_A
    have he0_ge2 : 2 ≤ m.factorization r₀ := by omega
    have hr0_sq_m : r₀ ^ 2 ∣ m :=
      (hr₀_prime.pow_dvd_iff_le_factorization hm0).mpr he0_ge2
    have hr0_4_N : r₀ ^ 4 ∣ N := by
      have h1 : r₀ ^ 4 ∣ m ^ 2 := by
        have hpow : (r₀ ^ 2) ^ 2 ∣ m ^ 2 := pow_dvd_pow_of_dvd hr0_sq_m 2
        rwa [← pow_mul] at hpow
      exact hform ▸ h1.trans (dvd_mul_left _ _)
    have hr0_mem_L2 : r₀ ∈ (m_L ^ 2).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hr₀_prime, hr0_L.trans (dvd_pow_self m_L (by decide : 2 ≠ 0)),
        pow_ne_zero 2 hmL0⟩
    have hq_sigL : q ∣ sigma 1 (m_L ^ 2) := by
      have hdvd := sigma_ordProj_dvd_sigma_of_coprime_left hr₀_prime hm2_split hm2_cop hr0_mem_L2
      rw [hord_r0] at hdvd
      exact hq_dvd_r0.trans hdvd
    have hq_not_sigR : ¬ q ∣ sigma 1 (m_R ^ 2) := fun hqR => hq_not_both ⟨hq_sigL, hqR⟩
    have hdiv_eq : (sigma 1 (m_L ^ 2) / q) * sigma 1 (m_R ^ 2) = I := by
      apply Nat.mul_left_cancel hq.pos
      calc
        q * ((sigma 1 (m_L ^ 2) / q) * sigma 1 (m_R ^ 2))
            = (q * (sigma 1 (m_L ^ 2) / q)) * sigma 1 (m_R ^ 2) := by ring
        _ = sigma 1 (m_L ^ 2) * sigma 1 (m_R ^ 2) := by rw [Nat.mul_div_cancel' hq_sigL]
        _ = q * I := hsig_eq_qI
    have hsigR_dvd_I : sigma 1 (m_R ^ 2) ∣ I :=
      ⟨sigma 1 (m_L ^ 2) / q, by rw [← hdiv_eq, mul_comm]⟩
    exact ⟨hr0_L, hr0_not_R, hr0_A, h2r0_q1, he0_ge2, hr0_4_N, hq_sigL, hq_not_sigR,
      hsigR_dvd_I, hdiv_eq⟩
  · right
    have hr0_not_L : ¬ r₀ ∣ m_L := fun hr0_L =>
      hr₀_prime.not_dvd_one (hm_cop ▸ Nat.dvd_gcd hr0_L hr0_R)
    have hm2_split' : m ^ 2 = m_R ^ 2 * m_L ^ 2 := by
      rw [hm_eq_mul]
      ring
    have hr0_mem_R2 : r₀ ∈ (m_R ^ 2).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hr₀_prime, hr0_R.trans (dvd_pow_self m_R (by decide : 2 ≠ 0)),
        pow_ne_zero 2 hmR0⟩
    have hq_sigR : q ∣ sigma 1 (m_R ^ 2) := by
      have hdvd :=
        sigma_ordProj_dvd_sigma_of_coprime_left hr₀_prime hm2_split' hm2_cop.symm hr0_mem_R2
      rw [hord_r0] at hdvd
      exact hq_dvd_r0.trans hdvd
    have hq_not_sigL : ¬ q ∣ sigma 1 (m_L ^ 2) := fun hqL => hq_not_both ⟨hqL, hq_sigR⟩
    have hdiv_eq : (sigma 1 (m_R ^ 2) / q) * sigma 1 (m_L ^ 2) = I := by
      apply Nat.mul_left_cancel hq.pos
      calc
        q * ((sigma 1 (m_R ^ 2) / q) * sigma 1 (m_L ^ 2))
            = sigma 1 (m_L ^ 2) * (q * (sigma 1 (m_R ^ 2) / q)) := by ring
        _ = sigma 1 (m_L ^ 2) * sigma 1 (m_R ^ 2) := by rw [Nat.mul_div_cancel' hq_sigR]
        _ = q * I := hsig_eq_qI
    have hsigL_dvd_I : sigma 1 (m_L ^ 2) ∣ I :=
      ⟨sigma 1 (m_R ^ 2) / q, by rw [← hdiv_eq, mul_comm]⟩
    exact ⟨hr0_R, hr0_not_L, hq_sigR, hq_not_sigL, hsigL_dvd_I, hdiv_eq⟩

/-- **2. Sixth-Power-Free LCM-GCD Coprime Split Profile**:
Specializes `linear_euler_mL_eq_one_iff_and_r0_split_dichotomy` to sixth-power-free odd perfect
numbers (`∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N`), proving `53 ≤ m_R`, `2863 ≤ sigma 1 (m_R ^ 2)`,
and in the `r₀ ∣ m_L` branch forcing `m.factorization r₀ = 2`, `r₀ ∈ largeSources N q`, and
`61 ≤ r₀` (`2 * r₀ ∣ q + 1`). -/
theorem sixth_power_free_lcm_gcd_coprime_split_profile {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q ∈ N.primeFactors)
    (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    ∃ m : ℕ,
      let A := (q + 1) / 2
      let I := componentIndex N q
      let L := Nat.factorizationLCMLeft A I
      let R := Nat.factorizationLCMRight A I
      let m_L := Nat.gcd m L
      let m_R := Nat.gcd m R
      Odd m ∧ ¬ q ∣ m ∧ N = q * m ^ 2 ∧
      53 ≤ m_R ∧ 2863 ≤ sigma 1 (m_R ^ 2) ∧
      ∃ r₀ ∈ m.primeFactors,
        q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀)) ∧
        ((r₀ ∣ m_L ∧ ¬ r₀ ∣ m_R ∧
            m.factorization r₀ = 2 ∧ r₀ ∈ largeSources N q ∧
            61 ≤ r₀ ∧ 2 * r₀ ∣ q + 1 ∧
            sigma 1 (m_R ^ 2) ∣ I ∧
            (sigma 1 (m_L ^ 2) / q) * sigma 1 (m_R ^ 2) = I) ∨
         (r₀ ∣ m_R ∧ ¬ r₀ ∣ m_L ∧
            sigma 1 (m_L ^ 2) ∣ I ∧
            (sigma 1 (m_R ^ 2) / q) * sigma 1 (m_L ^ 2) = I)) := by
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  obtain ⟨m, _, hm_odd, hqm, hform, _⟩ :=
    sixth_power_free_unique_q_source_mirror_dichotomy ho hN hq hq4 he hev hfree
  let A := (q + 1) / 2
  let I := componentIndex N q
  let L := Nat.factorizationLCMLeft A I
  let R := Nat.factorizationLCMRight A I
  let m_L := Nat.gcd m L
  let m_R := Nat.gcd m R
  obtain ⟨_, hmR_odd, _, _, _, _, _, _, _, _, hmR_ge3, _, hsig_split, hsig_eq_qI⟩ :=
    linear_euler_lcm_gcd_canonical_coprime_split ho hN hq_prime hqm hform
  obtain ⟨_, _, _, r₀, hr₀_m, _, hq_dvd_r0, hbranch⟩ :=
    linear_euler_mL_eq_one_iff_and_r0_split_dichotomy ho hN hq_prime hqm hform
  have hmR_ge3' : 3 ≤ m_R := hmR_ge3
  have hmR_ne1 : m_R ≠ 1 := by omega
  obtain ⟨p, hp_prime, hp_dvd_mR⟩ := Nat.exists_prime_and_dvd hmR_ne1
  have hp_dvd_m : p ∣ m := hp_dvd_mR.trans (Nat.gcd_dvd_left m R)
  have hp_dvd_N : p ∣ N :=
    hform ▸ hp_dvd_m.trans ((dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left _ q))
  have hp_N : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd_N, hN.2.ne'⟩
  have hp_ge53 : 53 ≤ p := sixth_power_free_min_prime_ge_53 ho hN hfree hp_N
  have hp_le_mR : p ≤ m_R := Nat.le_of_dvd hmR_odd.pos hp_dvd_mR
  have hmR_ge53 : 53 ≤ m_R := hp_ge53.trans hp_le_mR
  have hmR_sig_ge2863 : 2863 ≤ sigma 1 (m_R ^ 2) := by
    have h1 := sigma_sq_lower_bound (by omega : 3 ≤ m_R)
    nlinarith only [hmR_ge53, h1]
  refine ⟨m, hm_odd, hqm, hform, hmR_ge53, hmR_sig_ge2863, r₀, hr₀_m, hq_dvd_r0, ?_⟩
  rcases hbranch with
    ⟨hr0_L, hr0_not_R, _, h2r0_q1, he0_ge2, hr0_4_N, _, _, hsigR_dvd_I, hdiv_eq⟩ |
    ⟨hr0_R, hr0_not_L, _, _, hsigL_dvd_I, hdiv_eq⟩
  · left
    have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀_m
    have hr₀_dvd_m : r₀ ∣ m := Nat.dvd_of_mem_primeFactors hr₀_m
    have hr₀_dvd_N : r₀ ∣ N :=
      hform ▸ hr₀_dvd_m.trans ((dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left _ q))
    have hr₀_N : r₀ ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hr₀_prime, hr₀_dvd_N, hN.2.ne'⟩
    have hr₀_ge53 : 53 ≤ r₀ := sixth_power_free_min_prime_ge_53 ho hN hfree hr₀_N
    have hr₀_ne3 : r₀ ≠ 3 := by omega
    have hr₀_neq : r₀ ≠ q := fun h => hqm (h ▸ hr₀_dvd_m)
    have hr₀_not_6_N : N.factorization r₀ < 6 := by
      by_contra! hge6
      exact hfree r₀ hr₀_prime ((hr₀_prime.pow_dvd_iff_le_factorization hN.2.ne').mpr hge6)
    have hm0 : m ≠ 0 := hm_odd.pos.ne'
    have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
    have hr₀_not_q : ¬ r₀ ∣ q := fun hd =>
      hr₀_neq (((Nat.dvd_prime hq_prime).mp hd).resolve_left hr₀_prime.ne_one)
    have hN_fact_r0 : N.factorization r₀ = 2 * m.factorization r₀ := by
      rw [hform, Nat.factorization_mul hq_prime.ne_zero hm20, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hr₀_not_q, zero_add,
        Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    have he0_eq2 : m.factorization r₀ = 2 := by omega
    have hN_fact_ge4 : 4 ≤ N.factorization r₀ := by omega
    have hr₀_large : r₀ ∈ largeSources N q :=
      Finset.mem_filter.mpr ⟨hr₀_N, hr₀_ne3, hr₀_neq, hN_fact_ge4⟩
    have hI_eq_sig : I = sigma 1 (m ^ 2) / q := by
      have hsigm2_eq_qI : sigma 1 (m ^ 2) = q * I := hsig_split.trans hsig_eq_qI
      change I = sigma 1 (m ^ 2) / q
      rw [hsigm2_eq_qI, Nat.mul_div_cancel_left I hq_prime.pos]
    have hr₀_mem_I : r₀ ∈ I.primeFactors := by
      have hmem :=
        (linear_euler_unique_source_dvd_sigma_B_and_index_of_source
          ho hN hq_prime hqm hform hr₀_m hq_dvd_r0).2.2.2.2.1
      rwa [← hI_eq_sig] at hmem
    have hr₀_mod : r₀ % 5 = 1 ∨ r₀ % 3 = 1 :=
      (sixth_power_free_euler_index_drop_and_support ho hN hq hq4 he hev hfree).2 r₀ hr₀_mem_I
    have hr₀_ge61 : 61 ≤ r₀ := by
      by_contra! hlt
      have hr₀_cases : r₀ = 54 ∨ r₀ = 55 ∨ r₀ = 56 ∨ r₀ = 57 ∨ r₀ = 58 ∨ r₀ = 60 := by omega
      rcases hr₀_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact (by decide : ¬ Nat.Prime _) hr₀_prime
    exact ⟨hr0_L, hr0_not_R, he0_eq2, hr₀_large, hr₀_ge61, h2r0_q1, hsigR_dvd_I, hdiv_eq⟩
  · right
    exact ⟨hr0_R, hr0_not_L, hsigL_dvd_I, hdiv_eq⟩

end OddPerfect
