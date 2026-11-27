module

public import OddPerfect.HarmonicSupportFinite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-!
## 1. Exact 2-Adic Valuation Conservation and Odd Harmonic Mean
-/

/-- For every odd Ore harmonic number, the 2-adic valuation of each local
`sigma 1 (p ^ e_p)` equals the 2-adic valuation of `e_p + 1`, and globally
`v_2(σ(N)) = v_2(τ(N))`. -/
theorem odd_oreHarmonic_component_two_valuation_eq {N : ℕ} (ho : Odd N) (hh : OreHarmonic N) :
    (∀ p ∈ N.primeFactors,
      (sigma 1 (p ^ N.factorization p)).factorization 2 = (N.factorization p + 1).factorization 2) ∧
    (sigma 1 N).factorization 2 = N.divisors.card.factorization 2 := by
  have hσ_pos : 0 < sigma 1 N := sigma_pos_iff.mpr ho.pos
  have hτ_pos : 0 < N.divisors.card :=
    Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr ho.pos.ne'⟩
  have hσ_prod : sigma 1 N = ∏ p ∈ N.primeFactors, sigma 1 (p ^ N.factorization p) := by
    rw [isMultiplicative_sigma.multiplicative_factorization _ ho.pos.ne',
      Finsupp.prod, Nat.support_factorization]
  have hτ_prod : N.divisors.card = ∏ p ∈ N.primeFactors, (N.factorization p + 1) :=
    Nat.card_divisors ho.pos.ne'
  have h_le_glob : (sigma 1 N).factorization 2 ≤ N.divisors.card.factorization 2 := by
    have hle := (Nat.factorization_le_iff_dvd hσ_pos.ne' (Nat.mul_pos ho.pos hτ_pos).ne').mpr hh.2 2
    rw [Nat.factorization_mul ho.pos.ne' hτ_pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd ho.not_two_dvd_nat, zero_add] at hle
    exact hle
  have hσ_sum : (sigma 1 N).factorization 2 =
      ∑ p ∈ N.primeFactors, (sigma 1 (p ^ N.factorization p)).factorization 2 := by
    rw [hσ_prod]
    exact Nat.factorization_prod_apply (fun p hp =>
      (sigma_pos_iff.mpr (pow_pos (Nat.prime_of_mem_primeFactors hp).pos _)).ne')
  have hτ_sum : N.divisors.card.factorization 2 =
      ∑ p ∈ N.primeFactors, (N.factorization p + 1).factorization 2 := by
    rw [hτ_prod]
    exact Nat.factorization_prod_apply (fun p _ => Nat.succ_ne_zero _)
  have h_local_le : ∀ p ∈ N.primeFactors,
      (N.factorization p + 1).factorization 2 ≤ (sigma 1 (p ^ N.factorization p)).factorization 2 := by
    intro p hp
    have hp_pr := Nat.prime_of_mem_primeFactors hp
    have hp_odd := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
    rw [sigma_one_apply_prime_pow hp_pr]
    exact two_valuation_length_le_geometric (N.factorization p + 1) (Nat.succ_pos _) p hp_odd
  have h_sum_le : ∑ p ∈ N.primeFactors, (sigma 1 (p ^ N.factorization p)).factorization 2 ≤
      ∑ p ∈ N.primeFactors, (N.factorization p + 1).factorization 2 := by
    rw [← hσ_sum, ← hτ_sum]
    exact h_le_glob
  have h_local_eq : ∀ p ∈ N.primeFactors,
      (sigma 1 (p ^ N.factorization p)).factorization 2 = (N.factorization p + 1).factorization 2 := by
    intro p hp
    by_contra hne
    have hlt : (N.factorization p + 1).factorization 2 <
        (sigma 1 (p ^ N.factorization p)).factorization 2 :=
      lt_of_le_of_ne (h_local_le p hp) (Ne.symm hne)
    have hsum_lt := Finset.sum_lt_sum h_local_le ⟨p, hp, hlt⟩
    omega
  refine ⟨h_local_eq, ?_⟩
  rw [hσ_sum, hτ_sum]
  exact Finset.sum_congr rfl h_local_eq

/-- For any odd Ore harmonic number `N`, its harmonic mean `M = N * τ(N) / σ(N)`
is an odd integer satisfying `3 ≤ M`. -/
theorem odd_oreHarmonic_odd_harmonic_mean {N : ℕ} (ho : Odd N) (hh : OreHarmonic N) :
    let M := N * N.divisors.card / sigma 1 N
    M * sigma 1 N = N * N.divisors.card ∧ Odd M ∧ 3 ≤ M := by
  intro M
  have hM_eq : M * sigma 1 N = N * N.divisors.card := Nat.div_mul_cancel hh.2
  have hσ_pos : 0 < sigma 1 N := sigma_pos_iff.mpr ho.pos
  have hτ_pos : 0 < N.divisors.card :=
    Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr ho.pos.ne'⟩
  have hM_pos : 0 < M := by
    by_cases hM0 : M = 0
    · rw [hM0, zero_mul] at hM_eq
      exact ((mul_pos ho.pos hτ_pos).ne' hM_eq.symm).elim
    · exact Nat.pos_of_ne_zero hM0
  have hfact_eq : (M * sigma 1 N).factorization 2 = (N * N.divisors.card).factorization 2 := by
    rw [hM_eq]
  rw [Nat.factorization_mul hM_pos.ne' hσ_pos.ne', Nat.factorization_mul ho.pos.ne' hτ_pos.ne',
    Finsupp.add_apply, Finsupp.add_apply,
    (odd_oreHarmonic_component_two_valuation_eq ho hh).2,
    Nat.factorization_eq_zero_of_not_dvd ho.not_two_dvd_nat, zero_add] at hfact_eq
  have hM_v2 : M.factorization 2 = 0 := by omega
  have hM_not_two : ¬ 2 ∣ M := by
    intro hd
    have h1 := (Nat.prime_two.dvd_iff_one_le_factorization hM_pos.ne').mp hd
    omega
  have hM_odd : Odd M := Nat.odd_iff.mpr (by omega)
  have hM_ne_one : M ≠ 1 := by
    intro hM1
    rw [hM1, one_mul] at hM_eq
    have h1_mem : 1 ∈ N.divisors := Nat.one_mem_divisors.mpr ho.pos.ne'
    have hlt : sigma 1 N < N.divisors.card * N := by
      rw [sigma_one_apply, ← smul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_lt_sum
        (fun d hd => Nat.le_of_dvd ho.pos (Nat.dvd_of_mem_divisors hd))
        ⟨1, h1_mem, hh.1⟩
    rw [mul_comm] at hM_eq
    omega
  refine ⟨hM_eq, hM_odd, ?_⟩
  obtain ⟨k, hk⟩ := hM_odd
  omega

/-!
## 2. Unconditional Nonexistence of Cube-Free Odd `OreHarmonic` with `ω(N) ≤ 3`
-/

private lemma lt_sigma_one_of_one_lt'' {a : ℕ} (ha : 1 < a) : a < sigma 1 a := by
  rw [sigma_one_apply]
  have hsub : ({1, a} : Finset ℕ) ⊆ a.divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Nat.one_mem_divisors.mpr (by omega)
    · exact Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩
  have hsum := Finset.sum_le_sum_of_subset (f := fun x : ℕ => x) hsub
  rw [Finset.sum_pair ha.ne] at hsum
  omega

private lemma exists_three_sorted_of_card_eq_three {s : Finset ℕ} (hs : s.card = 3) :
    ∃ p₁ p₂ p₃, p₁ < p₂ ∧ p₂ < p₃ ∧ s = {p₁, p₂, p₃} := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs
  rcases lt_or_gt_of_ne hab with h1 | h1 <;>
  rcases lt_or_gt_of_ne hac with h2 | h2 <;>
  rcases lt_or_gt_of_ne hbc with h3 | h3
  · exact ⟨a, b, c, h1, h3, rfl⟩
  · exact ⟨a, c, b, h2, h3, by ext x; simp; tauto⟩
  · omega
  · exact ⟨c, a, b, h2, h1, by ext x; simp; tauto⟩
  · exact ⟨b, a, c, h1, h2, by ext x; simp; tauto⟩
  · omega
  · exact ⟨b, c, a, h3, h2, by ext x; simp; tauto⟩
  · exact ⟨c, b, a, h3, h1, by ext x; simp; tauto⟩

private lemma card_four_subset_lt {s : Finset ℕ} (hs : s.card = 3)
    {a b c d : ℕ} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s) : False := by
  have hsub : ({a, b, c, d} : Finset ℕ) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hcard : ({a, b, c, d} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hcd]
    · simp [hbc, hbd]
    · simp [hab, hac, had]
  have hle := Finset.card_le_card hsub
  omega

private lemma sigma_prime_pow_one_two_bound {p e a b : ℕ} (hp : p.Prime)
    (he1 : 1 ≤ e) (he2 : e ≤ 2)
    (h1 : a * (p + 1) ≤ b * p) (h2 : a * (p ^ 2 + p + 1) ≤ b * p ^ 2) :
    a * sigma 1 (p ^ e) ≤ b * p ^ e := by
  rcases (show e = 1 ∨ e = 2 by omega) with rfl | rfl
  · rw [sigma_one_apply_prime_pow hp]
    simp only [sum_range_succ, sum_range_zero, zero_add, pow_zero, pow_one]
    linarith
  · rw [sigma_one_apply_prime_pow hp]
    simp only [sum_range_succ, sum_range_zero, zero_add, pow_zero, pow_one]
    linarith

private lemma sigma_bound_5 {p e : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (he1 : 1 ≤ e) (he2 : e ≤ 2) :
    25 * sigma 1 (p ^ e) ≤ 31 * p ^ e :=
  sigma_prime_pow_one_two_bound hp he1 he2 (by omega) (by nlinarith)

private lemma sigma_bound_7 {p e : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (he1 : 1 ≤ e) (he2 : e ≤ 2) :
    49 * sigma 1 (p ^ e) ≤ 57 * p ^ e :=
  sigma_prime_pow_one_two_bound hp he1 he2 (by omega) (by nlinarith)

private lemma sigma_bound_11 {p e : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) (he1 : 1 ≤ e) (he2 : e ≤ 2) :
    121 * sigma 1 (p ^ e) ≤ 133 * p ^ e :=
  sigma_prime_pow_one_two_bound hp he1 he2 (by omega) (by nlinarith)

private lemma prime_mem_of_dvd_sigma_cubeFree {N p q : ℕ} (ho : Odd N) (hh : OreHarmonic N)
    (hcf : ∀ r, N.factorization r ≤ 2)
    (hp : p ∈ N.primeFactors) (hq : q.Prime) (hq3 : 3 < q)
    (hdvd : q ∣ sigma 1 (p ^ N.factorization p)) :
    q ∈ N.primeFactors := by
  have hσ_dvd : sigma 1 (p ^ N.factorization p) ∣ sigma 1 N := by
    rw [isMultiplicative_sigma.multiplicative_factorization _ ho.pos.ne']
    exact Finset.dvd_prod_of_mem _ hp
  have hq_Nτ : q ∣ N * N.divisors.card := hdvd.trans (hσ_dvd.trans hh.2)
  have hq_ndvd_τ : ¬ q ∣ N.divisors.card := by
    intro hqτ
    rw [Nat.card_divisors ho.pos.ne'] at hqτ
    obtain ⟨r, _, hqr⟩ := (Nat.prime_iff.mp hq).dvd_finsetProd_iff _ |>.mp hqτ
    have hle := Nat.le_of_dvd (Nat.succ_pos _) hqr
    have := hcf r
    omega
  have hq_N : q ∣ N := (hq.dvd_mul.mp hq_Nτ).resolve_right hq_ndvd_τ
  exact Nat.mem_primeFactors.mpr ⟨hq, hq_N, ho.pos.ne'⟩

private lemma factorization_eq_two_of_mod_four_eq_three {N p : ℕ} (ho : Odd N) (hh : OreHarmonic N)
    (hcf : ∀ r, N.factorization r ≤ 2) (hp : p ∈ N.primeFactors) (hp3 : p % 4 = 3) :
    N.factorization p = 2 := by
  have hp_pr := Nat.prime_of_mem_primeFactors hp
  have he_pos : 0 < N.factorization p :=
    hp_pr.factorization_pos_of_dvd ho.pos.ne' (Nat.dvd_of_mem_primeFactors hp)
  have he_le : N.factorization p ≤ 2 := hcf p
  have hmod := odd_harmonic_component_one_mod_four ho hh hp
  rcases (show N.factorization p = 1 ∨ N.factorization p = 2 by omega) with h1 | h2
  · rw [h1, pow_one] at hmod
    omega
  · exact h2

/-- No cube-free odd Ore harmonic number has three or fewer distinct prime factors. -/
theorem odd_oreHarmonic_four_le_primeFactors_of_cubeFree {N : ℕ}
    (ho : Odd N) (hh : OreHarmonic N) (hcf : ∀ p, N.factorization p ≤ 2) :
    4 ≤ N.primeFactors.card := by
  have h3_le : 3 ≤ N.primeFactors.card := odd_oreHarmonic_three_le_primeFactors ho hh
  by_contra! hlt
  have hcard3 : N.primeFactors.card = 3 := by omega
  obtain ⟨p₁, p₂, p₃, hp12, hp23, hPF⟩ := exists_three_sorted_of_card_eq_three hcard3
  have hp₁_mem : p₁ ∈ N.primeFactors := by rw [hPF]; simp
  have hp₂_mem : p₂ ∈ N.primeFactors := by rw [hPF]; simp
  have hp₃_mem : p₃ ∈ N.primeFactors := by rw [hPF]; simp
  have hp₁ : p₁.Prime := Nat.prime_of_mem_primeFactors hp₁_mem
  have hp₂ : p₂.Prime := Nat.prime_of_mem_primeFactors hp₂_mem
  have hp₃ : p₃.Prime := Nat.prime_of_mem_primeFactors hp₃_mem
  have h_odd_p : ∀ p ∈ N.primeFactors, 3 ≤ p := fun p hp => by
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hpo := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
    have := hpr.two_le
    rcases eq_or_ne p 2 with rfl | hne
    · exact (hpo.not_two_dvd_nat dvd_rfl).elim
    · omega
  have he_bounds : ∀ p ∈ N.primeFactors, N.factorization p = 1 ∨ N.factorization p = 2 := by
    intro p hp
    have h1 := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd ho.pos.ne'
      (Nat.dvd_of_mem_primeFactors hp)
    have h2 := hcf p
    omega
  have hτ_eq : N.divisors.card =
      (N.factorization p₁ + 1) * (N.factorization p₂ + 1) * (N.factorization p₃ + 1) := by
    rw [Nat.card_divisors ho.pos.ne', hPF,
      Finset.prod_insert (by simp [hp12.ne, (hp12.trans hp23).ne]),
      Finset.prod_pair hp23.ne]
    ring
  have hτ_cases : N.divisors.card = 12 ∨ N.divisors.card = 18 ∨ N.divisors.card = 27 := by
    rcases he_bounds p₁ hp₁_mem with h1 | h1 <;>
    rcases he_bounds p₂ hp₂_mem with h2 | h2 <;>
    rcases he_bounds p₃ hp₃_mem with h3 | h3
    · exfalso
      have h8 : N.divisors.card = 2 ^ 3 := by rw [hτ_eq, h1, h2, h3]; norm_num
      exact odd_oreHarmonic_divisor_count_not_pow_two ho hh 3 h8
    · left; rw [hτ_eq, h1, h2, h3]
    · left; rw [hτ_eq, h1, h2, h3]
    · right; left; rw [hτ_eq, h1, h2, h3]
    · left; rw [hτ_eq, h1, h2, h3]
    · right; left; rw [hτ_eq, h1, h2, h3]
    · right; left; rw [hτ_eq, h1, h2, h3]
    · right; right; rw [hτ_eq, h1, h2, h3]
  have hN_eq3 : ∀ a b c : ℕ, a ≠ b → a ≠ c → b ≠ c →
      a ∈ N.primeFactors → b ∈ N.primeFactors → c ∈ N.primeFactors →
      N.primeFactors = {a, b, c} ∧
      N = a ^ N.factorization a * b ^ N.factorization b * c ^ N.factorization c ∧
      sigma 1 N = sigma 1 (a ^ N.factorization a) * sigma 1 (b ^ N.factorization b) *
        sigma 1 (c ^ N.factorization c) := by
    intro a b c hab hac hbc ha hb hc
    have hsub : ({a, b, c} : Finset ℕ) ⊆ N.primeFactors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have hcard_abc : ({a, b, c} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
    have hset : N.primeFactors = {a, b, c} :=
      (Finset.eq_of_subset_of_card_le hsub (by rw [hcard3, hcard_abc])).symm
    refine ⟨hset, ?_, ?_⟩
    · conv_lhs => rw [Nat.prod_primeFactors_pow_factorization ho.pos.ne', hset,
        Finset.prod_insert (by simp [hab, hac]), Finset.prod_pair hbc]
      ring
    · conv_lhs => rw [isMultiplicative_sigma.multiplicative_factorization _ ho.pos.ne',
        Finsupp.prod, Nat.support_factorization, hset,
        Finset.prod_insert (by simp [hab, hac]), Finset.prod_pair hbc]
      ring
  -- Step A: rule out 3 ∣ N
  have h3_not_mem : 3 ∉ N.primeFactors := by
    intro h3_mem
    have he3 : N.factorization 3 = 2 :=
      factorization_eq_two_of_mod_four_eq_three ho hh hcf h3_mem (by decide)
    have hσ3 : sigma 1 (3 ^ N.factorization 3) = 13 := by
      rw [he3, sigma_one_apply_prime_pow (by decide : Nat.Prime 3)]
      norm_num [sum_range_succ]
    have h13_mem : 13 ∈ N.primeFactors :=
      prime_mem_of_dvd_sigma_cubeFree ho hh hcf h3_mem (by norm_num) (by decide)
        (by rw [hσ3])
    rcases he_bounds 13 h13_mem with he13 | he13
    · have hσ13 : sigma 1 (13 ^ N.factorization 13) = 2 * 7 := by
        rw [he13, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
        norm_num [sum_range_succ]
      have h7_mem : 7 ∈ N.primeFactors :=
        prime_mem_of_dvd_sigma_cubeFree ho hh hcf h13_mem (by norm_num) (by decide)
          (by rw [hσ13]; exact dvd_mul_left 7 2)
      have he7 : N.factorization 7 = 2 :=
        factorization_eq_two_of_mod_four_eq_three ho hh hcf h7_mem (by decide)
      have hσ7 : sigma 1 (7 ^ N.factorization 7) = 3 * 19 := by
        rw [he7, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
        norm_num [sum_range_succ]
      have h19_mem : 19 ∈ N.primeFactors :=
        prime_mem_of_dvd_sigma_cubeFree ho hh hcf h7_mem (by norm_num) (by decide)
          (by rw [hσ7]; exact dvd_mul_left 19 3)
      exact card_four_subset_lt hcard3 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) h3_mem h7_mem h13_mem h19_mem
    · have hσ13 : sigma 1 (13 ^ N.factorization 13) = 3 * 61 := by
        rw [he13, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
        norm_num [sum_range_succ]
      have h61_mem : 61 ∈ N.primeFactors :=
        prime_mem_of_dvd_sigma_cubeFree ho hh hcf h13_mem (by norm_num) (by decide)
          (by rw [hσ13]; exact dvd_mul_left 61 3)
      rcases he_bounds 61 h61_mem with he61 | he61
      · have hσ61 : sigma 1 (61 ^ N.factorization 61) = 2 * 31 := by
          rw [he61, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 61)]
          norm_num [sum_range_succ]
        have h31_mem : 31 ∈ N.primeFactors :=
          prime_mem_of_dvd_sigma_cubeFree ho hh hcf h61_mem (by norm_num) (by decide)
            (by rw [hσ61]; exact dvd_mul_left 31 2)
        exact card_four_subset_lt hcard3 (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) h3_mem h13_mem h31_mem h61_mem
      · have hσ61 : sigma 1 (61 ^ N.factorization 61) = 3 * 13 * 97 := by
          rw [he61, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 61)]
          norm_num [sum_range_succ]
        have h97_mem : 97 ∈ N.primeFactors :=
          prime_mem_of_dvd_sigma_cubeFree ho hh hcf h61_mem (by norm_num) (by decide)
            (by rw [hσ61]; exact dvd_mul_left 97 (3 * 13))
        exact card_four_subset_lt hcard3 (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) h3_mem h13_mem h61_mem h97_mem
  -- Step B: 5 ≤ p₁, 7 ≤ p₂, 11 ≤ p₃
  have hp₁_5 : 5 ≤ p₁ := by
    have hpo₁ := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp₁_mem)
    have h2 : p₁ % 2 = 1 := Nat.odd_iff.mp hpo₁
    have := h_odd_p p₁ hp₁_mem
    rcases eq_or_ne p₁ 3 with rfl | hne
    · exact (h3_not_mem hp₁_mem).elim
    · omega
  have hp₂_7 : 7 ≤ p₂ := by
    have hpo₂ := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp₂_mem)
    have h2 : p₂ % 2 = 1 := Nat.odd_iff.mp hpo₂
    omega
  have hp₃_11 : 11 ≤ p₃ := by
    have hpo₃ := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp₃_mem)
    have h2 : p₃ % 2 = 1 := Nat.odd_iff.mp hpo₃
    rcases (show p₃ = 9 ∨ 11 ≤ p₃ by omega) with rfl | h11
    · exfalso
      norm_num at hp₃
    · exact h11
  obtain ⟨_, hN_p, hσ_p⟩ := hN_eq3 p₁ p₂ p₃ hp12.ne (hp12.trans hp23).ne hp23.ne
    hp₁_mem hp₂_mem hp₃_mem
  have hσ_bound : 148225 * sigma 1 N ≤ 235011 * N := by
    have hb1 := sigma_bound_5 hp₁ hp₁_5
      (hp₁.factorization_pos_of_dvd ho.pos.ne' (Nat.dvd_of_mem_primeFactors hp₁_mem)) (hcf p₁)
    have hb2 := sigma_bound_7 hp₂ hp₂_7
      (hp₂.factorization_pos_of_dvd ho.pos.ne' (Nat.dvd_of_mem_primeFactors hp₂_mem)) (hcf p₂)
    have hb3 := sigma_bound_11 hp₃ hp₃_11
      (hp₃.factorization_pos_of_dvd ho.pos.ne' (Nat.dvd_of_mem_primeFactors hp₃_mem)) (hcf p₃)
    have hmul := Nat.mul_le_mul (Nat.mul_le_mul hb1 hb2) hb3
    have h_rhs : (31 * p₁ ^ N.factorization p₁ * (57 * p₂ ^ N.factorization p₂)) *
        (133 * p₃ ^ N.factorization p₃) = 235011 * N := by
      calc (31 * p₁ ^ N.factorization p₁ * (57 * p₂ ^ N.factorization p₂)) *
            (133 * p₃ ^ N.factorization p₃)
          = 235011 * (p₁ ^ N.factorization p₁ * p₂ ^ N.factorization p₂ *
              p₃ ^ N.factorization p₃) := by ring
        _ = 235011 * N := by rw [← hN_p]
    calc 148225 * sigma 1 N
        = (25 * sigma 1 (p₁ ^ N.factorization p₁) *
            (49 * sigma 1 (p₂ ^ N.factorization p₂))) *
            (121 * sigma 1 (p₃ ^ N.factorization p₃)) := by rw [hσ_p]; ring
      _ ≤ (31 * p₁ ^ N.factorization p₁ * (57 * p₂ ^ N.factorization p₂)) *
            (133 * p₃ ^ N.factorization p₃) := hmul
      _ = 235011 * N := h_rhs
  obtain ⟨hM_eq, hM_odd, hM_3⟩ := odd_oreHarmonic_odd_harmonic_mean ho hh
  set M := N * N.divisors.card / sigma 1 N
  change M * sigma 1 N = N * N.divisors.card at hM_eq
  change Odd M at hM_odd
  change 3 ≤ M at hM_3
  have hσ_gt : N < sigma 1 N := lt_sigma_one_of_one_lt'' hh.1
  have hM_lt_τ : M < N.divisors.card := by
    by_contra! hle
    have hmul : N * N.divisors.card < M * sigma 1 N := by
      calc N * N.divisors.card
          ≤ N * M := Nat.mul_le_mul_left N hle
        _ < sigma 1 N * M := Nat.mul_lt_mul_of_pos_right hσ_gt (by omega)
        _ = M * sigma 1 N := mul_comm _ _
    omega
  have hM_lower : 148225 * N.divisors.card ≤ 235011 * M := by
    have hmul : N * (148225 * N.divisors.card) ≤ N * (235011 * M) := by
      calc N * (148225 * N.divisors.card)
          = 148225 * (N * N.divisors.card) := by ring
        _ = 148225 * (M * sigma 1 N) := by rw [hM_eq]
        _ = M * (148225 * sigma 1 N) := by ring
        _ ≤ M * (235011 * N) := Nat.mul_le_mul_left M hσ_bound
        _ = N * (235011 * M) := by ring
    exact Nat.le_of_mul_le_mul_left hmul ho.pos
  have hM_mod2 : M % 2 = 1 := Nat.odd_iff.mp hM_odd
  -- Check the 9 candidate pairs (τ, M)
  rcases hτ_cases with hτ | hτ | hτ
  · -- τ = 12, M ∈ {9, 11}
    rw [hτ] at hM_eq hM_lt_τ hM_lower
    rcases (show M = 9 ∨ M = 11 by omega) with hM | hM
    · rw [hM] at hM_eq
      have h3σ : 3 * sigma 1 N = 4 * N := by omega
      have h3_dvd : 3 ∣ 4 * N := ⟨sigma 1 N, by omega⟩
      have h3_N : 3 ∣ N := (by decide : Nat.Coprime 3 4).dvd_of_dvd_mul_left h3_dvd
      exact h3_not_mem (Nat.mem_primeFactors.mpr ⟨by decide, h3_N, ho.pos.ne'⟩)
    · rw [hM] at hM_eq
      have h11_dvd : 11 ∣ 12 * N := ⟨sigma 1 N, by omega⟩
      have h11_N : 11 ∣ N := (by decide : Nat.Coprime 11 12).dvd_of_dvd_mul_left h11_dvd
      have h11_mem : 11 ∈ N.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨by norm_num, h11_N, ho.pos.ne'⟩
      have he11 : N.factorization 11 = 2 :=
        factorization_eq_two_of_mod_four_eq_three ho hh hcf h11_mem (by decide)
      have hσ11 : sigma 1 (11 ^ N.factorization 11) = 7 * 19 := by
        rw [he11, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
        norm_num [sum_range_succ]
      have h7_mem : 7 ∈ N.primeFactors :=
        prime_mem_of_dvd_sigma_cubeFree ho hh hcf h11_mem (by norm_num) (by decide)
          (by rw [hσ11]; exact dvd_mul_right 7 19)
      have h19_mem : 19 ∈ N.primeFactors :=
        prime_mem_of_dvd_sigma_cubeFree ho hh hcf h11_mem (by norm_num) (by decide)
          (by rw [hσ11]; exact dvd_mul_left 19 7)
      have he7 : N.factorization 7 = 2 :=
        factorization_eq_two_of_mod_four_eq_three ho hh hcf h7_mem (by decide)
      have he19 : N.factorization 19 = 2 :=
        factorization_eq_two_of_mod_four_eq_three ho hh hcf h19_mem (by decide)
      obtain ⟨hset, _, _⟩ := hN_eq3 7 11 19 (by decide) (by decide) (by decide)
        h7_mem h11_mem h19_mem
      have hτ27 : N.divisors.card = 27 := by
        rw [Nat.card_divisors ho.pos.ne', hset,
          Finset.prod_insert (by decide), Finset.prod_pair (by decide), he7, he11, he19]
        norm_num
      omega
  · -- τ = 18, M ∈ {13, 15, 17}
    rw [hτ] at hM_eq hM_lt_τ hM_lower
    rcases (show M = 13 ∨ M = 15 ∨ M = 17 by omega) with hM | hM | hM
    · rw [hM] at hM_eq
      have h13_dvd : 13 ∣ 18 * N := ⟨sigma 1 N, by omega⟩
      have h13_N : 13 ∣ N := (by decide : Nat.Coprime 13 18).dvd_of_dvd_mul_left h13_dvd
      have h13_mem : 13 ∈ N.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨by norm_num, h13_N, ho.pos.ne'⟩
      rcases he_bounds 13 h13_mem with he13 | he13
      · have hσ13 : sigma 1 (13 ^ N.factorization 13) = 2 * 7 := by
          rw [he13, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
          norm_num [sum_range_succ]
        have h7_mem : 7 ∈ N.primeFactors :=
          prime_mem_of_dvd_sigma_cubeFree ho hh hcf h13_mem (by norm_num) (by decide)
            (by rw [hσ13]; exact dvd_mul_left 7 2)
        have he7 : N.factorization 7 = 2 :=
          factorization_eq_two_of_mod_four_eq_three ho hh hcf h7_mem (by decide)
        have hσ7 : sigma 1 (7 ^ N.factorization 7) = 3 * 19 := by
          rw [he7, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
          norm_num [sum_range_succ]
        have h19_mem : 19 ∈ N.primeFactors :=
          prime_mem_of_dvd_sigma_cubeFree ho hh hcf h7_mem (by norm_num) (by decide)
            (by rw [hσ7]; exact dvd_mul_left 19 3)
        have he19 : N.factorization 19 = 2 :=
          factorization_eq_two_of_mod_four_eq_three ho hh hcf h19_mem (by decide)
        obtain ⟨_, hN_val, hσ_val⟩ := hN_eq3 7 13 19 (by decide) (by decide) (by decide)
          h7_mem h13_mem h19_mem
        rw [he7, he13, he19,
          sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7),
          sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13),
          sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19)] at hσ_val
        rw [he7, he13, he19] at hN_val
        simp only [sum_range_succ, sum_range_zero, zero_add] at hσ_val
        rw [hσ_val, hN_val] at hM_eq
        norm_num at hM_eq
      · have hσ13 : sigma 1 (13 ^ N.factorization 13) = 3 * 61 := by
          rw [he13, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
          norm_num [sum_range_succ]
        have h61_mem : 61 ∈ N.primeFactors :=
          prime_mem_of_dvd_sigma_cubeFree ho hh hcf h13_mem (by norm_num) (by decide)
            (by rw [hσ13]; exact dvd_mul_left 61 3)
        rcases he_bounds 61 h61_mem with he61 | he61
        · have hσ61 : sigma 1 (61 ^ N.factorization 61) = 2 * 31 := by
            rw [he61, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 61)]
            norm_num [sum_range_succ]
          have h31_mem : 31 ∈ N.primeFactors :=
            prime_mem_of_dvd_sigma_cubeFree ho hh hcf h61_mem (by norm_num) (by decide)
              (by rw [hσ61]; exact dvd_mul_left 31 2)
          have he31 : N.factorization 31 = 2 :=
            factorization_eq_two_of_mod_four_eq_three ho hh hcf h31_mem (by decide)
          obtain ⟨_, hN_val, hσ_val⟩ := hN_eq3 13 31 61 (by decide) (by decide) (by decide)
            h13_mem h31_mem h61_mem
          rw [he13, he31, he61,
            sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13),
            sigma_one_apply_prime_pow (by norm_num : Nat.Prime 31),
            sigma_one_apply_prime_pow (by norm_num : Nat.Prime 61)] at hσ_val
          rw [he13, he31, he61] at hN_val
          simp only [sum_range_succ, sum_range_zero, zero_add] at hσ_val
          rw [hσ_val, hN_val] at hM_eq
          norm_num at hM_eq
        · have hσ61 : sigma 1 (61 ^ N.factorization 61) = 3 * 13 * 97 := by
            rw [he61, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 61)]
            norm_num [sum_range_succ]
          have h97_mem : 97 ∈ N.primeFactors :=
            prime_mem_of_dvd_sigma_cubeFree ho hh hcf h61_mem (by norm_num) (by decide)
              (by rw [hσ61]; exact dvd_mul_left 97 (3 * 13))
          obtain ⟨hset, _, _⟩ := hN_eq3 13 61 97 (by decide) (by decide) (by decide)
            h13_mem h61_mem h97_mem
          have hτ_prod : 18 = 3 * 3 * (N.factorization 97 + 1) := by
            have h18 := hτ
            rw [Nat.card_divisors ho.pos.ne', hset,
              Finset.prod_insert (by decide), Finset.prod_pair (by decide), he13, he61] at h18
            linarith
          have he97 : N.factorization 97 = 1 := by omega
          have hσ97 : sigma 1 (97 ^ N.factorization 97) = 2 * 7 ^ 2 := by
            rw [he97, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 97)]
            norm_num [sum_range_succ]
          have h7_mem : 7 ∈ N.primeFactors :=
            prime_mem_of_dvd_sigma_cubeFree ho hh hcf h97_mem (by norm_num) (by decide)
              (by rw [hσ97]; exact (dvd_pow_self 7 (by decide : 2 ≠ 0)).trans (dvd_mul_left _ 2))
          exact card_four_subset_lt hcard3 (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) h7_mem h13_mem h61_mem h97_mem
    · rw [hM] at hM_eq
      have h5σ : 5 * sigma 1 N = 6 * N := by omega
      have h5_dvd : 5 ∣ 6 * N := ⟨sigma 1 N, by omega⟩
      have h5_N : 5 ∣ N := (by decide : Nat.Coprime 5 6).dvd_of_dvd_mul_left h5_dvd
      have h5_mem : 5 ∈ N.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨by norm_num, h5_N, ho.pos.ne'⟩
      have hp₁_eq5 : p₁ = 5 := by
        rw [hPF] at h5_mem
        simp only [Finset.mem_insert, Finset.mem_singleton] at h5_mem
        rcases h5_mem with rfl | rfl | rfl <;> omega
      subst hp₁_eq5
      let B := p₂ ^ N.factorization p₂ * p₃ ^ N.factorization p₃
      have hB_gt1 : 1 < B := by
        have hp2_pow : 1 < p₂ ^ N.factorization p₂ :=
          one_lt_pow₀ hp₂.one_lt (hp₂.factorization_pos_of_dvd ho.pos.ne'
            (Nat.dvd_of_mem_primeFactors hp₂_mem)).ne'
        have hp3_pow : 1 < p₃ ^ N.factorization p₃ :=
          one_lt_pow₀ hp₃.one_lt (hp₃.factorization_pos_of_dvd ho.pos.ne'
            (Nat.dvd_of_mem_primeFactors hp₃_mem)).ne'
        dsimp [B]
        nlinarith
      have hcop5B : Nat.Coprime (5 ^ N.factorization 5) B := by
        refine Nat.Coprime.pow_left _ (Nat.Coprime.mul_right ?_ ?_)
        · exact ((by norm_num : Nat.Prime 5).coprime_iff_not_dvd.mpr fun hd =>
            hp12.ne ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp₂).mp hd)).pow_right _
        · exact ((by norm_num : Nat.Prime 5).coprime_iff_not_dvd.mpr fun hd =>
            (hp12.trans hp23).ne ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp₃).mp hd)).pow_right _
      have hN_split : N = 5 ^ N.factorization 5 * B := by
        calc N = 5 ^ N.factorization 5 * p₂ ^ N.factorization p₂ * p₃ ^ N.factorization p₃ := hN_p
          _ = 5 ^ N.factorization 5 * B := by ring
      have hσ_split : sigma 1 N = sigma 1 (5 ^ N.factorization 5) * sigma 1 B := by
        conv_lhs => rw [hN_split]
        exact isMultiplicative_sigma.map_mul_of_coprime hcop5B
      have h5_ge6 : 6 * 5 ^ N.factorization 5 ≤ 5 * sigma 1 (5 ^ N.factorization 5) := by
        rcases he_bounds 5 hp₁_mem with he5 | he5 <;>
          rw [he5, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)] <;>
          norm_num [sum_range_succ]
      have hB_lt := lt_sigma_one_of_one_lt'' hB_gt1
      have hlt_5σ : 6 * N < 5 * sigma 1 N := by
        calc 6 * N = (6 * 5 ^ N.factorization 5) * B := by
              conv_lhs => rw [hN_split]
              ring
          _ < (6 * 5 ^ N.factorization 5) * sigma 1 B :=
              Nat.mul_lt_mul_of_pos_left hB_lt (by positivity)
          _ ≤ (5 * sigma 1 (5 ^ N.factorization 5)) * sigma 1 B :=
              Nat.mul_le_mul_right _ h5_ge6
          _ = 5 * sigma 1 N := by rw [hσ_split]; ring
      omega
    · rw [hM] at hM_eq
      have h17_dvd : 17 ∣ 18 * N := ⟨sigma 1 N, by omega⟩
      have h17_N : 17 ∣ N := (by decide : Nat.Coprime 17 18).dvd_of_dvd_mul_left h17_dvd
      have h17_mem : 17 ∈ N.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨by norm_num, h17_N, ho.pos.ne'⟩
      rcases he_bounds 17 h17_mem with he17 | he17
      · let B := ∏ p ∈ N.primeFactors.erase 17, p ^ N.factorization p
        have hcop : Nat.Coprime (17 ^ N.factorization 17) B := by
          refine Nat.Coprime.pow_left _ (Nat.Coprime.prod_right fun p hp => ?_)
          have hp_ne : 17 ≠ p := (Finset.mem_erase.mp hp).1.symm
          have hp_pr := Nat.prime_of_mem_primeFactors (Finset.mem_erase.mp hp).2
          exact ((by norm_num : Nat.Prime 17).coprime_iff_not_dvd.mpr fun hd =>
            hp_ne ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp_pr).mp hd)).pow_right _
        have hN_split : N = 17 * B := by
          conv_lhs => rw [Nat.prod_primeFactors_pow_factorization ho.pos.ne',
            ← Finset.mul_prod_erase N.primeFactors (fun p => p ^ N.factorization p) h17_mem,
            he17, pow_one]
        have hB_gt1 : 1 < B := by
          have h_er_card : (N.primeFactors.erase 17).card = 2 := by
            rw [Finset.card_erase_of_mem h17_mem, hcard3]
          obtain ⟨q, hq_er⟩ := Finset.card_pos.mp (by omega : 0 < (N.primeFactors.erase 17).card)
          have hq_mem := (Finset.mem_erase.mp hq_er).2
          have hq_pr := Nat.prime_of_mem_primeFactors hq_mem
          have hq_pow_gt1 : 1 < q ^ N.factorization q :=
            one_lt_pow₀ hq_pr.one_lt (hq_pr.factorization_pos_of_dvd ho.pos.ne'
              (Nat.dvd_of_mem_primeFactors hq_mem)).ne'
          have hq_dvd_B : q ^ N.factorization q ∣ B := Finset.dvd_prod_of_mem _ hq_er
          have hB_pos : 0 < B := Finset.prod_pos fun p hp =>
            pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_erase.mp hp).2).pos _
          exact hq_pow_gt1.trans_le (Nat.le_of_dvd hB_pos hq_dvd_B)
        have hσ_split : sigma 1 N = 18 * sigma 1 B := by
          conv_lhs => rw [hN_split]
          have hcop' : Nat.Coprime 17 B := by simpa [he17] using hcop
          have hσ17_1 : sigma 1 (17 ^ 1) = 18 := by
            rw [sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17)]
            norm_num [sum_range_succ]
          rw [isMultiplicative_sigma.map_mul_of_coprime hcop', ← pow_one 17, hσ17_1]
        rw [hσ_split, hN_split] at hM_eq
        have hB_eq : sigma 1 B = B := by omega
        have := lt_sigma_one_of_one_lt'' hB_gt1
        omega
      · have hσ17 : sigma 1 (17 ^ N.factorization 17) = 307 := by
          rw [he17, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17)]
          norm_num [sum_range_succ]
        have h307_mem : 307 ∈ N.primeFactors :=
          prime_mem_of_dvd_sigma_cubeFree ho hh hcf h17_mem (by norm_num) (by decide)
            (by rw [hσ17])
        have he307 : N.factorization 307 = 2 :=
          factorization_eq_two_of_mod_four_eq_three ho hh hcf h307_mem (by decide)
        have hσ307 : sigma 1 (307 ^ N.factorization 307) = 3 * 43 * 733 := by
          rw [he307, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 307)]
          norm_num [sum_range_succ]
        have h43_mem : 43 ∈ N.primeFactors :=
          prime_mem_of_dvd_sigma_cubeFree ho hh hcf h307_mem (by norm_num) (by decide)
            (by rw [hσ307]; exact dvd_mul_of_dvd_left (dvd_mul_left 43 3) 733)
        have h733_mem : 733 ∈ N.primeFactors :=
          prime_mem_of_dvd_sigma_cubeFree ho hh hcf h307_mem (by norm_num) (by decide)
            (by rw [hσ307]; exact dvd_mul_left 733 (3 * 43))
        exact card_four_subset_lt hcard3 (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) h17_mem h43_mem h307_mem h733_mem
  · -- τ = 27, so e_p = 2 for all p ∈ N.primeFactors; M ∈ {19, 21, 23, 25}
    have he_all2 : ∀ p ∈ N.primeFactors, N.factorization p = 2 := by
      have h27 : (N.factorization p₁ + 1) * (N.factorization p₂ + 1) * (N.factorization p₃ + 1) = 27 :=
        hτ_eq.symm.trans hτ
      have he1 : N.factorization p₁ = 2 := by
        rcases he_bounds p₁ hp₁_mem with h1 | h1 <;>
        rcases he_bounds p₂ hp₂_mem with h2 | h2 <;>
        rcases he_bounds p₃ hp₃_mem with h3 | h3 <;>
        · rw [h1, h2, h3] at h27; omega
      have he2 : N.factorization p₂ = 2 := by
        rcases he_bounds p₂ hp₂_mem with h2 | h2 <;>
        rcases he_bounds p₃ hp₃_mem with h3 | h3 <;>
        · rw [he1, h2, h3] at h27; omega
      have he3 : N.factorization p₃ = 2 := by
        rcases he_bounds p₃ hp₃_mem with h3 | h3 <;>
        · rw [he1, he2, h3] at h27; omega
      intro p hp
      rw [hPF] at hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;> assumption
    rw [hτ] at hM_eq hM_lt_τ hM_lower
    rcases (show M = 19 ∨ M = 21 ∨ M = 23 ∨ M = 25 by omega) with hM | hM | hM | hM
    · rw [hM] at hM_eq
      have h19_dvd : 19 ∣ 27 * N := ⟨sigma 1 N, by omega⟩
      have h19_N : 19 ∣ N := (by decide : Nat.Coprime 19 27).dvd_of_dvd_mul_left h19_dvd
      have h19_mem : 19 ∈ N.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨by norm_num, h19_N, ho.pos.ne'⟩
      have he19 := he_all2 19 h19_mem
      have hσ19 : sigma 1 (19 ^ N.factorization 19) = 3 * 127 := by
        rw [he19, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19)]
        norm_num [sum_range_succ]
      have h127_mem : 127 ∈ N.primeFactors :=
        prime_mem_of_dvd_sigma_cubeFree ho hh hcf h19_mem (by norm_num) (by decide)
          (by rw [hσ19]; exact dvd_mul_left 127 3)
      have he127 := he_all2 127 h127_mem
      have hσ127 : sigma 1 (127 ^ N.factorization 127) = 3 * 5419 := by
        rw [he127, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 127)]
        norm_num [sum_range_succ]
      have h5419_mem : 5419 ∈ N.primeFactors :=
        prime_mem_of_dvd_sigma_cubeFree ho hh hcf h127_mem (by norm_num) (by decide)
          (by rw [hσ127]; exact dvd_mul_left 5419 3)
      have he5419 := he_all2 5419 h5419_mem
      obtain ⟨_, hN_val, hσ_val⟩ := hN_eq3 19 127 5419 (by decide) (by decide) (by decide)
        h19_mem h127_mem h5419_mem
      rw [he19, he127, he5419,
        sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19),
        sigma_one_apply_prime_pow (by norm_num : Nat.Prime 127),
        sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5419)] at hσ_val
      rw [he19, he127, he5419] at hN_val
      simp only [sum_range_succ, sum_range_zero, zero_add] at hσ_val
      rw [hσ_val, hN_val] at hM_eq
      norm_num at hM_eq
    · rw [hM] at hM_eq
      have h7σ : 7 * sigma 1 N = 9 * N := by omega
      have h7_dvd : 7 ∣ 9 * N := ⟨sigma 1 N, by omega⟩
      have h7_N : 7 ∣ N := (by decide : Nat.Coprime 7 9).dvd_of_dvd_mul_left h7_dvd
      have h7_mem : 7 ∈ N.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨by norm_num, h7_N, ho.pos.ne'⟩
      have he7 := he_all2 7 h7_mem
      have hσ7 : sigma 1 (7 ^ N.factorization 7) = 3 * 19 := by
        rw [he7, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
        norm_num [sum_range_succ]
      have h19_mem : 19 ∈ N.primeFactors :=
        prime_mem_of_dvd_sigma_cubeFree ho hh hcf h7_mem (by norm_num) (by decide)
          (by rw [hσ7]; exact dvd_mul_left 19 3)
      have he19 := he_all2 19 h19_mem
      have hσ19 : sigma 1 (19 ^ N.factorization 19) = 3 * 127 := by
        rw [he19, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19)]
        norm_num [sum_range_succ]
      have h127_mem : 127 ∈ N.primeFactors :=
        prime_mem_of_dvd_sigma_cubeFree ho hh hcf h19_mem (by norm_num) (by decide)
          (by rw [hσ19]; exact dvd_mul_left 127 3)
      have he127 := he_all2 127 h127_mem
      obtain ⟨_, hN_val, hσ_val⟩ := hN_eq3 7 19 127 (by decide) (by decide) (by decide)
        h7_mem h19_mem h127_mem
      rw [he7, he19, he127,
        sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7),
        sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19),
        sigma_one_apply_prime_pow (by norm_num : Nat.Prime 127)] at hσ_val
      rw [he7, he19, he127] at hN_val
      simp only [sum_range_succ, sum_range_zero, zero_add] at hσ_val
      rw [hσ_val, hN_val] at h7σ
      norm_num at h7σ
    · rw [hM] at hM_eq
      have h23_dvd : 23 ∣ 27 * N := ⟨sigma 1 N, by omega⟩
      have h23_N : 23 ∣ N := (by decide : Nat.Coprime 23 27).dvd_of_dvd_mul_left h23_dvd
      have h23_mem : 23 ∈ N.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨by norm_num, h23_N, ho.pos.ne'⟩
      have he23 := he_all2 23 h23_mem
      have hσ23 : sigma 1 (23 ^ N.factorization 23) = 7 * 79 := by
        rw [he23, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 23)]
        norm_num [sum_range_succ]
      have h7_mem : 7 ∈ N.primeFactors :=
        prime_mem_of_dvd_sigma_cubeFree ho hh hcf h23_mem (by norm_num) (by decide)
          (by rw [hσ23]; exact dvd_mul_right 7 79)
      have h79_mem : 79 ∈ N.primeFactors :=
        prime_mem_of_dvd_sigma_cubeFree ho hh hcf h23_mem (by norm_num) (by decide)
          (by rw [hσ23]; exact dvd_mul_left 79 7)
      have he7 := he_all2 7 h7_mem
      have he79 := he_all2 79 h79_mem
      obtain ⟨_, hN_val, hσ_val⟩ := hN_eq3 7 23 79 (by decide) (by decide) (by decide)
        h7_mem h23_mem h79_mem
      rw [he7, he23, he79,
        sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7),
        sigma_one_apply_prime_pow (by norm_num : Nat.Prime 23),
        sigma_one_apply_prime_pow (by norm_num : Nat.Prime 79)] at hσ_val
      rw [he7, he23, he79] at hN_val
      simp only [sum_range_succ, sum_range_zero, zero_add] at hσ_val
      rw [hσ_val, hN_val] at hM_eq
      norm_num at hM_eq
    · rw [hM] at hM_eq
      have h5_dvd : 5 ∣ 27 * N := (by decide : 5 ∣ 25).trans ⟨sigma 1 N, by omega⟩
      have h5_N : 5 ∣ N := (by decide : Nat.Coprime 5 27).dvd_of_dvd_mul_left h5_dvd
      have h5_mem : 5 ∈ N.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨by norm_num, h5_N, ho.pos.ne'⟩
      have he5 := he_all2 5 h5_mem
      have hσ5 : sigma 1 (5 ^ N.factorization 5) = 31 := by
        rw [he5, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
        norm_num [sum_range_succ]
      have h31_mem : 31 ∈ N.primeFactors :=
        prime_mem_of_dvd_sigma_cubeFree ho hh hcf h5_mem (by norm_num) (by decide)
          (by rw [hσ5])
      have he31 := he_all2 31 h31_mem
      have hσ31 : sigma 1 (31 ^ N.factorization 31) = 3 * 331 := by
        rw [he31, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 31)]
        norm_num [sum_range_succ]
      have h331_mem : 331 ∈ N.primeFactors :=
        prime_mem_of_dvd_sigma_cubeFree ho hh hcf h31_mem (by norm_num) (by decide)
          (by rw [hσ31]; exact dvd_mul_left 331 3)
      have he331 := he_all2 331 h331_mem
      obtain ⟨_, hN_val, hσ_val⟩ := hN_eq3 5 31 331 (by decide) (by decide) (by decide)
        h5_mem h31_mem h331_mem
      rw [he5, he31, he331,
        sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5),
        sigma_one_apply_prime_pow (by norm_num : Nat.Prime 31),
        sigma_one_apply_prime_pow (by norm_num : Nat.Prime 331)] at hσ_val
      rw [he5, he31, he331] at hN_val
      simp only [sum_range_succ, sum_range_zero, zero_add] at hσ_val
      rw [hσ_val, hN_val] at hM_eq
      norm_num at hM_eq

end OddPerfect
