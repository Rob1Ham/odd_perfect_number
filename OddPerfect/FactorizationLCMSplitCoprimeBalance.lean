module

public import OddPerfect.FactorizationLCMSplitObstruction
public import OddPerfect.AcquaahKonyagin

/-!
# Factorization LCM Split Coprime Balance

Unconditional linear Euler (`N = q * m ^ 2`) inequalities and canonical coprime splitting
`m = m_L * m_R` separating genuine odd perfect numbers from Descartes's spoof
`198585576189 = 22021 * 3003 ^ 2`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- **1. Universal Half-Successor Strictly Below Index (`A < I`) and `h₀ < u₀`**:
For any linear Euler odd perfect number `N = q * m ^ 2`, letting `A := (q + 1) / 2`,
`I := componentIndex N q`, `g := Nat.gcd A I`, and `R := Nat.factorizationLCMRight A I`,
proves `q ^ 2 < 3 * m ^ 2`, `A < I`, `q + 3 ≤ 2 * I`, `¬ (I ∣ A)`, `1 < R`, and the
ordered coprime odd square parametrization `h₀ + 2 ≤ u₀` (`3 ≤ u₀`). -/
theorem linear_euler_half_succ_lt_index_and_h0_lt_u0 {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2) :
    let A := (q + 1) / 2
    let I := componentIndex N q
    let g := Nat.gcd A I
    let R := Nat.factorizationLCMRight A I
    q ^ 2 < 3 * m ^ 2 ∧
    A < I ∧
    q + 3 ≤ 2 * I ∧
    ¬ (I ∣ A) ∧
    1 < R ∧
    ∃ h₀ u₀ : ℕ,
      Odd h₀ ∧ Odd u₀ ∧ 1 ≤ h₀ ∧ 3 ≤ u₀ ∧ h₀ + 2 ≤ u₀ ∧
      Nat.Coprime h₀ u₀ ∧
      A = g * h₀ ^ 2 ∧ I = g * u₀ ^ 2 ∧ m = g * h₀ * u₀ := by
  intro A I g R
  have hqN : q ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq, ⟨m ^ 2, hform⟩, hN.2.ne'⟩
  have hq3_lt : q ^ 3 < 3 * N := prime_cube_lt_three_mul hN ho hqN
  have hq2_lt : q ^ 2 < 3 * m ^ 2 := by
    apply Nat.lt_of_mul_lt_mul_left (a := q)
    calc
      q * q ^ 2 = q ^ 3 := by ring
      _ < 3 * N := hq3_lt
      _ = q * (3 * m ^ 2) := by rw [hform]; ring
  let L := Nat.factorizationLCMLeft A I
  obtain ⟨hg_odd, hg_ge1, _, _, hL_dvd, _, hLR_lcm,
      h₀, u₀, hh0_odd, hu0_odd, hh0_ge1, hu0_ge1, hcop_h0u0,
      hA_eq, hI_eq, hm_eq, _, _, _, _⟩ :=
    universal_half_succ_index_gcd_square_parametrization ho hN hq hqm hform
  have hg_odd' : Odd g := hg_odd
  have hA_eq' : A = g * h₀ ^ 2 := hA_eq
  have hI_eq' : I = g * u₀ ^ 2 := hI_eq
  have hm_eq' : m = g * h₀ * u₀ := hm_eq
  have hL_dvd' : L ∣ A := hL_dvd
  have hLR_lcm' : L * R = Nat.lcm A I := hLR_lcm
  have hAI : A * I = m ^ 2 := by
    rw [hA_eq', hI_eq', hm_eq']
    ring
  have hq_odd : Odd q := ho.of_dvd_nat ⟨m ^ 2, hform⟩
  have hq1_eq : q + 1 = 2 * A := by
    dsimp [A]
    have := Nat.odd_iff.mp hq_odd
    omega
  have hA_odd : Odd A := by rw [hA_eq']; exact hg_odd'.mul hh0_odd.pow
  have hI_odd : Odd I := by rw [hI_eq']; exact hg_odd'.mul hu0_odd.pow
  have hA_pos : 0 < A := hA_odd.pos
  have hI_pos : 0 < I := hI_odd.pos
  have hA_lt_I : A < I := by
    by_cases hA4 : 4 ≤ A
    · have h3A2_lt_q2 : 3 * A ^ 2 < q ^ 2 := by nlinarith only [hA4, hq1_eq]
      apply Nat.lt_of_mul_lt_mul_left (a := 3 * A)
      calc
        3 * A * A = 3 * A ^ 2 := by ring
        _ < q ^ 2 := h3A2_lt_q2
        _ < 3 * m ^ 2 := hq2_lt
        _ = 3 * A * I := by rw [← hAI]; ring
    · have hA_eq3 : A = 3 := by
        obtain ⟨k, hk⟩ := hA_odd
        have hq2 := hq.two_le
        omega
      have hq5 : q = 5 := by omega
      have hm2_eq : m ^ 2 = 3 * I := by rw [← hAI, hA_eq3]
      by_cases hI1 : I = 1
      · rw [hI1, mul_one] at hm2_eq
        have : m ≤ 1 ∨ 2 ≤ m := by omega
        rcases this with hm1 | hm2
        · nlinarith only [hm2_eq, hm1]
        · nlinarith only [hm2_eq, hm2]
      · by_cases hI3 : I = 3
        · rw [hI3] at hm2_eq
          have hm3 : m = 3 := by nlinarith only [hm2_eq]
          have hN45 : N = 45 := by rw [hform, hq5, hm3]; norm_num
          have hsum : ∑ i ∈ Nat.divisors 45, i = 2 * 45 :=
            (Nat.perfect_iff_sum_divisors_eq_two_mul (by decide : 0 < 45)).mp (hN45 ▸ hN)
          have hfalse : ∑ i ∈ Nat.divisors 45, i ≠ 2 * 45 := by decide
          exact absurd hsum hfalse
        · obtain ⟨k, hk⟩ := hI_odd
          omega
  have hq3_le : q + 3 ≤ 2 * I := by omega
  have hI_ndvd_A : ¬ (I ∣ A) := fun hd => by
    have := Nat.le_of_dvd hA_pos hd
    omega
  have hR_gt1 : 1 < R := by
    have hR_pos : 0 < R := Nat.factorizationLCMRight_pos A I
    by_contra hR_le
    have hR1 : R = 1 := by omega
    have hlcm_le : Nat.lcm A I ≤ A := by
      rw [← hLR_lcm', hR1, mul_one]
      exact Nat.le_of_dvd hA_pos hL_dvd'
    have hlcm_pos : 0 < Nat.lcm A I :=
      Nat.pos_of_ne_zero (Nat.lcm_ne_zero hA_pos.ne' hI_pos.ne')
    have hI_le_lcm : I ≤ Nat.lcm A I := Nat.le_of_dvd hlcm_pos (Nat.dvd_lcm_right A I)
    omega
  have hh0_sq_lt : h₀ ^ 2 < u₀ ^ 2 := by
    apply Nat.lt_of_mul_lt_mul_left (a := g)
    rw [← hA_eq', ← hI_eq']
    exact hA_lt_I
  have hh0_lt_u0 : h₀ < u₀ := by
    by_contra hle
    exact absurd (Nat.pow_le_pow_left (not_lt.mp hle) 2) (not_le.mpr hh0_sq_lt)
  have hh0_add2 : h₀ + 2 ≤ u₀ := by
    obtain ⟨k₁, hk₁⟩ := hh0_odd
    obtain ⟨k₂, hk₂⟩ := hu0_odd
    omega
  have hu0_ge3 : 3 ≤ u₀ := by omega
  exact ⟨hq2_lt, hA_lt_I, hq3_le, hI_ndvd_A, hR_gt1,
    h₀, u₀, hh0_odd, hu0_odd, hh0_ge1, hu0_ge3, hh0_add2, hcop_h0u0, hA_eq', hI_eq', hm_eq'⟩

/-- **2. Canonical Coprime LCM-GCD Split of `m`**:
For any linear Euler odd perfect number `N = q * m ^ 2`, letting `A := (q + 1) / 2`,
`I := componentIndex N q`, `L := Nat.factorizationLCMLeft A I`, `R := Nat.factorizationLCMRight A I`,
`m_L := Nat.gcd m L`, and `m_R := Nat.gcd m R`, proves `m = m_L * m_R` with `Nat.Coprime m_L m_R`,
`2 * m_L ≤ q + 1`, `m_L < q`, `3 ≤ m_R`, `m_R < R`, and the coprime divisor-sum identity
`sigma 1 (m_L ^ 2) * sigma 1 (m_R ^ 2) = q * I`. -/
theorem linear_euler_lcm_gcd_canonical_coprime_split {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2) :
    let A := (q + 1) / 2
    let I := componentIndex N q
    let L := Nat.factorizationLCMLeft A I
    let R := Nat.factorizationLCMRight A I
    let m_L := Nat.gcd m L
    let m_R := Nat.gcd m R
    Odd m_L ∧ Odd m_R ∧
    Nat.Coprime m_L m_R ∧
    m = m_L * m_R ∧
    m_L ∣ L ∧ m_L ∣ A ∧ 2 * m_L ≤ q + 1 ∧ m_L < q ∧
    m_R ∣ R ∧ m_R ∣ I ∧ 3 ≤ m_R ∧ m_R < R ∧
    sigma 1 (m ^ 2) = sigma 1 (m_L ^ 2) * sigma 1 (m_R ^ 2) ∧
    sigma 1 (m_L ^ 2) * sigma 1 (m_R ^ 2) = q * I := by
  intro A I L R m_L m_R
  obtain ⟨_, hA_lt_I, _, hI_ndvd_A, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    linear_euler_half_succ_lt_index_and_h0_lt_u0 ho hN hq hqm hform
  obtain ⟨_, _, _, hLR_cop, hL_dvd, hR_dvd, hLR_lcm,
      h₀, u₀, _, _, _, _, _, hA_eq, hI_eq, hm_gh0u0, hq_eq, _, hsig_eq, _⟩ :=
    universal_half_succ_index_gcd_square_parametrization ho hN hq hqm hform
  let g := Nat.gcd A I
  have hA_lt_I' : A < I := hA_lt_I
  have hI_ndvd_A' : ¬ (I ∣ A) := hI_ndvd_A
  have hLR_cop' : Nat.Coprime L R := hLR_cop
  have hL_dvd' : L ∣ A := hL_dvd
  have hR_dvd' : R ∣ I := hR_dvd
  have hLR_lcm' : L * R = Nat.lcm A I := hLR_lcm
  have hA_eq' : A = g * h₀ ^ 2 := hA_eq
  have hI_eq' : I = g * u₀ ^ 2 := hI_eq
  have hm_gh0u0' : m = g * h₀ * u₀ := hm_gh0u0
  have hq_eq' : q = 2 * g * h₀ ^ 2 - 1 := hq_eq
  have hsig_eq' : sigma 1 ((g * h₀ * u₀) ^ 2) = g * (2 * g * h₀ ^ 2 - 1) * u₀ ^ 2 := hsig_eq
  have hq_odd : Odd q := ho.of_dvd_nat ⟨m ^ 2, hform⟩
  have hm_odd : Odd m :=
    ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  have hA_pos : 0 < A := by
    have : 1 ≤ q := hq.pos
    have := Nat.odd_iff.mp hq_odd
    dsimp [A]
    omega
  have hI_pos : 0 < I := lt_trans hA_pos hA_lt_I'
  have hA0 : A ≠ 0 := hA_pos.ne'
  have hI0 : I ≠ 0 := hI_pos.ne'
  have hL0 : L ≠ 0 := (Nat.factorizationLCMLeft_pos A I).ne'
  have hR0 : R ≠ 0 := (Nat.factorizationLCMRight_pos A I).ne'
  have hmL_dvd_m : m_L ∣ m := Nat.gcd_dvd_left m L
  have hmR_dvd_m : m_R ∣ m := Nat.gcd_dvd_left m R
  have hmL_odd : Odd m_L := hm_odd.of_dvd_nat hmL_dvd_m
  have hmR_odd : Odd m_R := hm_odd.of_dvd_nat hmR_dvd_m
  have hmL0 : m_L ≠ 0 := hmL_odd.pos.ne'
  have hmR0 : m_R ≠ 0 := hmR_odd.pos.ne'
  have hmL_dvd_L : m_L ∣ L := Nat.gcd_dvd_right m L
  have hmR_dvd_R : m_R ∣ R := Nat.gcd_dvd_right m R
  have hmL_dvd_A : m_L ∣ A := hmL_dvd_L.trans hL_dvd'
  have hmR_dvd_I : m_R ∣ I := hmR_dvd_R.trans hR_dvd'
  have hm_cop : Nat.Coprime m_L m_R :=
    (hLR_cop'.coprime_dvd_left hmL_dvd_L).coprime_dvd_right hmR_dvd_R
  have hAI : A * I = m ^ 2 := by
    rw [hA_eq', hI_eq', hm_gh0u0']
    ring
  have hm_eq_mul : m = m_L * m_R := by
    apply Nat.eq_of_factorization_eq hm0 (mul_ne_zero hmL0 hmR0)
    intro p
    have h2m : 2 * m.factorization p = A.factorization p + I.factorization p := by
      calc
        2 * m.factorization p = (m ^ 2).factorization p := by
          rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
        _ = (A * I).factorization p := by rw [hAI]
        _ = A.factorization p + I.factorization p := by
          rw [Nat.factorization_mul hA0 hI0, Finsupp.add_apply]
    have hLR_fact : L.factorization p + R.factorization p =
        max (A.factorization p) (I.factorization p) := by
      calc
        L.factorization p + R.factorization p = (L * R).factorization p := by
          rw [← Finsupp.add_apply, ← Nat.factorization_mul hL0 hR0]
        _ = (Nat.lcm A I).factorization p := by rw [hLR_lcm']
        _ = max (A.factorization p) (I.factorization p) := by
          rw [Nat.factorization_lcm hA0 hI0, Finsupp.sup_apply]
    have hmL_fact : m_L.factorization p = min (m.factorization p) (L.factorization p) := by
      change (Nat.gcd m L).factorization p = _
      rw [Nat.factorization_gcd hm0 hL0, Finsupp.inf_apply]
    have hmR_fact : m_R.factorization p = min (m.factorization p) (R.factorization p) := by
      change (Nat.gcd m R).factorization p = _
      rw [Nat.factorization_gcd hm0 hR0, Finsupp.inf_apply]
    have hLR_zero : L.factorization p = 0 ∨ R.factorization p = 0 := by
      by_cases hLz : L.factorization p = 0
      · exact Or.inl hLz
      · right
        have hp_mem : p ∈ L.primeFactors := Finsupp.mem_support_iff.mpr hLz
        have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
        have hpL : p ∣ L := Nat.dvd_of_mem_primeFactors hp_mem
        have hpR : ¬ p ∣ R := fun hpR => hp.not_dvd_one (hLR_cop' ▸ Nat.dvd_gcd hpL hpR)
        exact Nat.factorization_eq_zero_of_not_dvd hpR
    rw [Nat.factorization_mul hmL0 hmR0, Finsupp.add_apply, hmL_fact, hmR_fact]
    rcases hLR_zero with hLz | hRz
    · rw [hLz, Nat.min_zero, zero_add]
      rw [hLz, zero_add] at hLR_fact
      have hm_le_R : m.factorization p ≤ R.factorization p := by omega
      exact (min_eq_left hm_le_R).symm
    · rw [hRz, Nat.min_zero, add_zero]
      rw [hRz, add_zero] at hLR_fact
      have hm_le_L : m.factorization p ≤ L.factorization p := by omega
      exact (min_eq_left hm_le_L).symm
  have hq1_eq : q + 1 = 2 * A := by
    dsimp [A]
    have := Nat.odd_iff.mp hq_odd
    omega
  have hmL_le_A : m_L ≤ A := Nat.le_of_dvd hA_pos hmL_dvd_A
  have h2mL_le : 2 * m_L ≤ q + 1 := by omega
  have hmL_lt_q : m_L < q := by
    have := hq.two_le
    omega
  have hmR_ne1 : m_R ≠ 1 := by
    intro hmR1
    have hm_dvd_A : m ∣ A := by
      rw [hm_eq_mul, hmR1, mul_one]
      exact hmL_dvd_A
    have hm2_dvd_A2 : A * I ∣ A * A := by
      rw [hAI, ← pow_two]
      exact pow_dvd_pow_of_dvd hm_dvd_A 2
    exact hI_ndvd_A' ((Nat.mul_dvd_mul_iff_left hA_pos).mp hm2_dvd_A2)
  have hmR_ge3 : 3 ≤ m_R := by
    obtain ⟨k, hk⟩ := hmR_odd
    omega
  have hmR_lt_R : m_R < R := by
    obtain ⟨p, hp, hp_dvd_mR⟩ := Nat.exists_prime_and_dvd hmR_ne1
    have hp_dvd_R : p ∣ R := hp_dvd_mR.trans hmR_dvd_R
    have hp_ndvd_L : ¬ p ∣ L := fun hpL => hp.not_dvd_one (hLR_cop' ▸ Nat.dvd_gcd hpL hp_dvd_R)
    have hL_zero : L.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hp_ndvd_L
    have hA_lt_I_fact : A.factorization p < I.factorization p := by
      by_contra hle
      have hI_le_A : I.factorization p ≤ A.factorization p := not_lt.mp hle
      have hp_dvd_prod : p ∣ (Nat.lcm A I).factorization.prod fun q n =>
          if I.factorization q ≤ A.factorization q then 1 else q ^ n := hp_dvd_R
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
    have hLR_fact : L.factorization p + R.factorization p =
        max (A.factorization p) (I.factorization p) := by
      calc
        L.factorization p + R.factorization p = (L * R).factorization p := by
          rw [← Finsupp.add_apply, ← Nat.factorization_mul hL0 hR0]
        _ = (Nat.lcm A I).factorization p := by rw [hLR_lcm']
        _ = max (A.factorization p) (I.factorization p) := by
          rw [Nat.factorization_lcm hA0 hI0, Finsupp.sup_apply]
    have hR_eq_I : R.factorization p = I.factorization p := by
      rw [hL_zero, zero_add, max_eq_right hA_lt_I_fact.le] at hLR_fact
      exact hLR_fact
    have h2m : 2 * m.factorization p = A.factorization p + I.factorization p := by
      calc
        2 * m.factorization p = (m ^ 2).factorization p := by
          rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
        _ = (A * I).factorization p := by rw [hAI]
        _ = A.factorization p + I.factorization p := by
          rw [Nat.factorization_mul hA0 hI0, Finsupp.add_apply]
    have hm_lt_R : m.factorization p < R.factorization p := by omega
    have hmR_le_m : m_R.factorization p ≤ m.factorization p := by
      change (Nat.gcd m R).factorization p ≤ m.factorization p
      rw [Nat.factorization_gcd hm0 hR0, Finsupp.inf_apply]
      exact min_le_left _ _
    have hmR_ne_R : m_R ≠ R := by
      intro hEq
      rw [hEq] at hmR_le_m
      omega
    exact lt_of_le_of_ne (Nat.le_of_dvd (Nat.factorizationLCMRight_pos A I) hmR_dvd_R) hmR_ne_R
  have hsig_split : sigma 1 (m ^ 2) = sigma 1 (m_L ^ 2) * sigma 1 (m_R ^ 2) := by
    have hm2_eq : m ^ 2 = m_L ^ 2 * m_R ^ 2 := by
      rw [hm_eq_mul]
      ring
    rw [hm2_eq]
    exact isMultiplicative_sigma.map_mul_of_coprime (hm_cop.pow 2 2)
  have hsig_eq_qI : sigma 1 (m_L ^ 2) * sigma 1 (m_R ^ 2) = q * I := by
    calc
      sigma 1 (m_L ^ 2) * sigma 1 (m_R ^ 2) = sigma 1 (m ^ 2) := hsig_split.symm
      _ = sigma 1 ((g * h₀ * u₀) ^ 2) := by rw [hm_gh0u0']
      _ = g * (2 * g * h₀ ^ 2 - 1) * u₀ ^ 2 := hsig_eq'
      _ = (2 * g * h₀ ^ 2 - 1) * (g * u₀ ^ 2) := by ring
      _ = q * I := by rw [← hq_eq', ← hI_eq']
  exact ⟨hmL_odd, hmR_odd, hm_cop, hm_eq_mul, hmL_dvd_L, hmL_dvd_A, h2mL_le, hmL_lt_q,
    hmR_dvd_R, hmR_dvd_I, hmR_ge3, hmR_lt_R, hsig_split, hsig_eq_qI⟩

end OddPerfect
