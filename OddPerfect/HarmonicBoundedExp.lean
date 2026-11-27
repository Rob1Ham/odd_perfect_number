module

public import OddPerfect.HarmonicCubeFree
public import OddPerfect.FewPrimes
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-!
## 1. Local Arithmetic Helpers
-/

private lemma lt_sigma_one_of_one_lt_hb {a : ℕ} (ha : 1 < a) : a < sigma 1 a := by
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

private lemma mul_sum_range_add_one (p e : ℕ) (hp : 1 ≤ p) :
    (p - 1) * (∑ i ∈ range (e + 1), p ^ i) + 1 = p ^ (e + 1) := by
  induction e with
  | zero =>
    simp only [zero_add, sum_range_one, pow_zero, mul_one, pow_one]
    omega
  | succ e ih =>
    rw [sum_range_succ, mul_add, add_assoc, add_comm ((p - 1) * p ^ (e + 1)) 1, ← add_assoc, ih]
    have hmul : p ^ (e + 1) + (p - 1) * p ^ (e + 1) = p * p ^ (e + 1) := by
      calc p ^ (e + 1) + (p - 1) * p ^ (e + 1)
          = (1 + (p - 1)) * p ^ (e + 1) := by ring
        _ = p * p ^ (e + 1) := by rw [Nat.add_sub_of_le hp]
    rw [hmul, ← pow_succ']

private lemma nat_mul_lt_mul {a b c d : ℕ} (h1 : a < b) (h2 : c < d) : a * c < b * d := by
  nlinarith

private lemma mul_sub_lt_two_mul_of_sq_lt {p num den : ℕ} (hp : 1 ≤ p) (hden : den < num)
    (hsq : (p - 1) ^ 2 * num < p ^ 2 * den) :
    p * (num - den) < 2 * num := by
  have hmul : p * (p * (num - den)) < p * (2 * num) := by
    zify [hp, hden.le] at hsq ⊢
    nlinarith
  exact Nat.lt_of_mul_lt_mul_left hmul

private lemma prime_pred_mul_sigma_lt {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (p - 1) * sigma 1 (p ^ e) < p * p ^ e := by
  rw [sigma_one_apply_prime_pow hp]
  have h := mul_sum_range_add_one p e hp.one_lt.le
  rw [pow_succ'] at h
  omega

private lemma sigma_bound_of_le {p k : ℕ} (hp : p.Prime) (hk : k ≤ p) (hk1 : 1 ≤ k) (e : ℕ) :
    (k - 1) * sigma 1 (p ^ e) < k * p ^ e := by
  have h1 : (k - 1) * p ≤ k * (p - 1) := by
    zify [hk1, hp.one_lt.le]
    nlinarith
  have h2 := prime_pred_mul_sigma_lt hp e
  have hmul : p * ((k - 1) * sigma 1 (p ^ e)) < p * (k * p ^ e) := by
    calc p * ((k - 1) * sigma 1 (p ^ e))
        = ((k - 1) * p) * sigma 1 (p ^ e) := by ring
      _ ≤ (k * (p - 1)) * sigma 1 (p ^ e) := Nat.mul_le_mul_right _ h1
      _ = k * ((p - 1) * sigma 1 (p ^ e)) := by ring
      _ < k * (p * p ^ e) := Nat.mul_lt_mul_of_pos_left h2 (by omega)
      _ = p * (k * p ^ e) := by ring
  exact Nat.lt_of_mul_lt_mul_left hmul

private lemma exists_three_sorted_of_card_eq_three_hb {s : Finset ℕ} (hs : s.card = 3) :
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

private lemma card_four_subset_lt_hb {s : Finset ℕ} (hs : s.card = 3)
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

private lemma N_sigma_eq_three {N : ℕ} (ho : Odd N) (hcard3 : N.primeFactors.card = 3)
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∈ N.primeFactors) (hb : b ∈ N.primeFactors) (hc : c ∈ N.primeFactors) :
    N.primeFactors = {a, b, c} ∧
    N = a ^ N.factorization a * b ^ N.factorization b * c ^ N.factorization c ∧
    sigma 1 N = sigma 1 (a ^ N.factorization a) * sigma 1 (b ^ N.factorization b) *
      sigma 1 (c ^ N.factorization c) := by
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

/-!
## 2. Unbounded-Exponent Structural Link (`M ∤ τ(N)` when `ω(N) ≤ 3`)
-/

/-- For any odd Ore harmonic number with at most three distinct prime factors,
its harmonic mean `M = N * τ(N) / σ(N)` does not divide `τ(N)`. -/
theorem odd_oreHarmonic_card_three_not_dvd_divisor_count {N : ℕ}
    (ho : Odd N) (hh : OreHarmonic N) (hcard : N.primeFactors.card ≤ 3) :
    ¬ (N * N.divisors.card / sigma 1 N ∣ N.divisors.card) := by
  have h3_le : 3 ≤ N.primeFactors.card := odd_oreHarmonic_three_le_primeFactors ho hh
  have hcard3 : N.primeFactors.card = 3 := by omega
  obtain ⟨p₁, p₂, p₃, hp12, hp23, hPF⟩ := exists_three_sorted_of_card_eq_three_hb hcard3
  have hp₁_mem : p₁ ∈ N.primeFactors := by rw [hPF]; simp
  have hp₂_mem : p₂ ∈ N.primeFactors := by rw [hPF]; simp
  have hp₃_mem : p₃ ∈ N.primeFactors := by rw [hPF]; simp
  have hp₁ : p₁.Prime := Nat.prime_of_mem_primeFactors hp₁_mem
  have hp₂ : p₂.Prime := Nat.prime_of_mem_primeFactors hp₂_mem
  have hp₃ : p₃.Prime := Nat.prime_of_mem_primeFactors hp₃_mem
  have h_odd_p : ∀ p ∈ N.primeFactors, 3 ≤ p ∧ p % 2 = 1 := fun p hp => by
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hpo := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
    have hmod : p % 2 = 1 := Nat.odd_iff.mp hpo
    have h2 : 2 ≤ p := hpr.two_le
    exact ⟨by omega, hmod⟩
  have hp₁_ge3 : 3 ≤ p₁ := (h_odd_p p₁ hp₁_mem).1
  have hp₂_ge5 : 5 ≤ p₂ := by
    have := h_odd_p p₂ hp₂_mem
    omega
  have hp₃_ge7 : 7 ≤ p₃ := by
    have := h_odd_p p₃ hp₃_mem
    omega
  obtain ⟨_, hN_p, hσ_p⟩ := N_sigma_eq_three ho hcard3 hp12.ne (hp12.trans hp23).ne hp23.ne
    hp₁_mem hp₂_mem hp₃_mem
  have hb1 := sigma_bound_of_le hp₁ hp₁_ge3 (by decide) (N.factorization p₁)
  have hb2 := sigma_bound_of_le hp₂ hp₂_ge5 (by decide) (N.factorization p₂)
  have hb3 := sigma_bound_of_le hp₃ hp₃_ge7 (by decide) (N.factorization p₃)
  have hσ_lt_3N : sigma 1 N < 3 * N := by
    have hmul :
        (2 * sigma 1 (p₁ ^ N.factorization p₁)) *
        (4 * sigma 1 (p₂ ^ N.factorization p₂)) *
        (6 * sigma 1 (p₃ ^ N.factorization p₃)) <
        (3 * p₁ ^ N.factorization p₁) *
        (5 * p₂ ^ N.factorization p₂) *
        (7 * p₃ ^ N.factorization p₃) :=
      nat_mul_lt_mul (nat_mul_lt_mul hb1 hb2) hb3
    have h48 : 48 * sigma 1 N < 105 * N := by
      calc 48 * sigma 1 N
          = (2 * sigma 1 (p₁ ^ N.factorization p₁)) *
            (4 * sigma 1 (p₂ ^ N.factorization p₂)) *
            (6 * sigma 1 (p₃ ^ N.factorization p₃)) := by rw [hσ_p]; ring
        _ < (3 * p₁ ^ N.factorization p₁) *
            (5 * p₂ ^ N.factorization p₂) *
            (7 * p₃ ^ N.factorization p₃) := hmul
        _ = 105 * (p₁ ^ N.factorization p₁ * p₂ ^ N.factorization p₂ * p₃ ^ N.factorization p₃) := by ring
        _ = 105 * N := by rw [← hN_p]
    omega
  obtain ⟨hM_eq, _, hM_3⟩ := odd_oreHarmonic_odd_harmonic_mean ho hh
  set M := N * N.divisors.card / sigma 1 N
  change M * sigma 1 N = N * N.divisors.card at hM_eq
  change 3 ≤ M at hM_3
  have hσ_gt : N < sigma 1 N := lt_sigma_one_of_one_lt_hb hh.1
  have hM_lt_τ : M < N.divisors.card := by
    by_contra! hle
    have hmul : N * N.divisors.card < M * sigma 1 N := by
      calc N * N.divisors.card
          ≤ N * M := Nat.mul_le_mul_left N hle
        _ < sigma 1 N * M := Nat.mul_lt_mul_of_pos_right hσ_gt (by omega)
        _ = M * sigma 1 N := mul_comm _ _
    omega
  intro hMdvd
  obtain ⟨V, hV⟩ := hMdvd
  have hV_ge2 : 2 ≤ V := by
    by_contra! hV_lt
    have : M * V ≤ M * 1 := Nat.mul_le_mul_left M (by omega)
    omega
  have hσ_eq_VN : sigma 1 N = V * N := by
    have hmul : M * sigma 1 N = M * (V * N) := by
      calc M * sigma 1 N = N * N.divisors.card := hM_eq
        _ = N * (M * V) := by rw [hV]
        _ = M * (V * N) := by ring
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < M) hmul
  have hV_lt3 : V < 3 := by
    rw [hσ_eq_VN] at hσ_lt_3N
    exact Nat.lt_of_mul_lt_mul_right hσ_lt_3N
  have hV2 : V = 2 := by omega
  have hPerf : N.Perfect := by
    rw [Nat.perfect_iff_sum_divisors_eq_two_mul ho.pos, ← sigma_one_apply, hσ_eq_VN, hV2]
  have h5_le := five_le_distinct_prime_factor_count ho hPerf
  omega

/-!
## 3. Fifth-Power-Free Rank-3 Prime-Chain Exclusions (`3 ∤ N` and `v_5(N) ≤ 1`)
-/

private lemma prime_mem_of_dvd_sigma_fifthPowerFree {N p q : ℕ} (ho : Odd N) (hh : OreHarmonic N)
    (hfpf : ∀ r, N.factorization r ≤ 4)
    (hp : p ∈ N.primeFactors) (hq : q.Prime) (hq5 : 5 < q)
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
    have := hfpf r
    omega
  have hq_N : q ∣ N := (hq.dvd_mul.mp hq_Nτ).resolve_right hq_ndvd_τ
  exact Nat.mem_primeFactors.mpr ⟨hq, hq_N, ho.pos.ne'⟩

private lemma factorization_even_of_mod_four_eq_three_fpf {N p : ℕ} (ho : Odd N) (hh : OreHarmonic N)
    (hfpf : ∀ r, N.factorization r ≤ 4) (hp : p ∈ N.primeFactors) (hp3 : p % 4 = 3) :
    N.factorization p = 2 ∨ N.factorization p = 4 := by
  have hp_pr := Nat.prime_of_mem_primeFactors hp
  have he_pos : 0 < N.factorization p :=
    hp_pr.factorization_pos_of_dvd ho.pos.ne' (Nat.dvd_of_mem_primeFactors hp)
  have he_le : N.factorization p ≤ 4 := hfpf p
  have hmod := odd_harmonic_component_one_mod_four ho hh hp
  rcases (show N.factorization p = 1 ∨ N.factorization p = 2 ∨
      N.factorization p = 3 ∨ N.factorization p = 4 by omega) with h1 | h2 | h3 | h4
  · rw [h1, pow_one] at hmod; omega
  · exact Or.inl h2
  · have h3mod : p ^ 3 % 4 = 3 := by
      rw [Nat.pow_mod, hp3]
    rw [h3] at hmod
    omega
  · exact Or.inr h4

private lemma factorization_cases_fpf {N p : ℕ} (ho : Odd N)
    (hfpf : ∀ r, N.factorization r ≤ 4) (hp : p ∈ N.primeFactors) :
    N.factorization p = 1 ∨ N.factorization p = 2 ∨
    N.factorization p = 3 ∨ N.factorization p = 4 := by
  have hp_pr := Nat.prime_of_mem_primeFactors hp
  have he_pos : 0 < N.factorization p :=
    hp_pr.factorization_pos_of_dvd ho.pos.ne' (Nat.dvd_of_mem_primeFactors hp)
  have he_le : N.factorization p ≤ 4 := hfpf p
  omega

private lemma sigma_prime_pow_coprime_pow {p : ℕ} (hp : p.Prime) (e k : ℕ) :
    Nat.Coprime (sigma 1 (p ^ e)) (p ^ k) := by
  have hmod : sigma 1 (p ^ e) % p = 1 := by
    rw [sigma_one_apply_prime_pow hp, sum_range_succ', pow_zero, add_comm]
    have hd : p ∣ ∑ x ∈ range e, p ^ (x + 1) := by
      apply Finset.dvd_sum
      intro x _
      rw [pow_succ']
      exact dvd_mul_right _ _
    obtain ⟨t, ht⟩ := hd
    rw [ht, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hp.one_lt
  have hcop : Nat.Coprime (sigma 1 (p ^ e)) p := by
    rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr fun hd => by
      have h0 : sigma 1 (p ^ e) % p = 0 := Nat.mod_eq_zero_of_dvd hd
      omega
  exact hcop.pow_right k

private lemma sigma_prime_pow_ge_sq {p e : ℕ} (hp : p.Prime) (he : 2 ≤ e) :
    p ^ 2 < sigma 1 (p ^ e) := by
  rw [sigma_one_apply_prime_pow hp]
  have hsub : ({0, 2} : Finset ℕ) ⊆ range (e + 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_range] at hx ⊢
    omega
  have hsum := Finset.sum_le_sum_of_subset (f := fun i : ℕ => p ^ i) hsub
  rw [Finset.sum_pair (by decide), pow_zero] at hsum
  omega

private lemma thirteen_chain_fpf {N a : ℕ} (ho : Odd N) (hh : OreHarmonic N)
    (hfpf : ∀ r, N.factorization r ≤ 4) (hcard3 : N.primeFactors.card = 3)
    (ha_mem : a ∈ N.primeFactors) (ha3 : a = 3 ∨ a = 5)
    (h13_mem : 13 ∈ N.primeFactors) :
    N.factorization 13 = 4 ∧ 30941 ∈ N.primeFactors ∧ 2 ≤ N.factorization 30941 := by
  have ha_ne_7 : a ≠ 7 := by rcases ha3 with rfl | rfl <;> decide
  have ha_ne_13 : a ≠ 13 := by rcases ha3 with rfl | rfl <;> decide
  have ha_ne_17 : a ≠ 17 := by rcases ha3 with rfl | rfl <;> decide
  have ha_ne_19 : a ≠ 19 := by rcases ha3 with rfl | rfl <;> decide
  have ha_ne_31 : a ≠ 31 := by rcases ha3 with rfl | rfl <;> decide
  have ha_ne_61 : a ≠ 61 := by rcases ha3 with rfl | rfl <;> decide
  have ha_ne_97 : a ≠ 97 := by rcases ha3 with rfl | rfl <;> decide
  have ha_ne_131 : a ≠ 131 := by rcases ha3 with rfl | rfl <;> decide
  have ha_ne_191 : a ≠ 191 := by rcases ha3 with rfl | rfl <;> decide
  have ha_ne_2801 : a ≠ 2801 := by rcases ha3 with rfl | rfl <;> decide
  have ha_ne_30941 : a ≠ 30941 := by rcases ha3 with rfl | rfl <;> decide
  rcases factorization_cases_fpf ho hfpf h13_mem with he13 | he13 | he13 | he13
  · exfalso
    have hσ13 : sigma 1 (13 ^ N.factorization 13) = 2 * 7 := by
      rw [he13, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
      norm_num [sum_range_succ]
    have h7_mem : 7 ∈ N.primeFactors :=
      prime_mem_of_dvd_sigma_fifthPowerFree ho hh hfpf h13_mem (by norm_num) (by decide)
        (by rw [hσ13]; exact dvd_mul_left 7 2)
    rcases factorization_even_of_mod_four_eq_three_fpf ho hh hfpf h7_mem (by decide) with he7 | he7
    · have hσ7 : sigma 1 (7 ^ N.factorization 7) = 3 * 19 := by
        rw [he7, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
        norm_num [sum_range_succ]
      have h19_mem : 19 ∈ N.primeFactors :=
        prime_mem_of_dvd_sigma_fifthPowerFree ho hh hfpf h7_mem (by norm_num) (by decide)
          (by rw [hσ7]; exact dvd_mul_left 19 3)
      exact card_four_subset_lt_hb hcard3 ha_ne_7 ha_ne_13 ha_ne_19 (by decide) (by decide)
        (by decide) ha_mem h7_mem h13_mem h19_mem
    · have hσ7 : sigma 1 (7 ^ N.factorization 7) = 2801 := by
        rw [he7, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
        norm_num [sum_range_succ]
      have h2801_mem : 2801 ∈ N.primeFactors :=
        prime_mem_of_dvd_sigma_fifthPowerFree ho hh hfpf h7_mem (by norm_num) (by decide)
          (by rw [hσ7])
      exact card_four_subset_lt_hb hcard3 ha_ne_7 ha_ne_13 ha_ne_2801 (by decide) (by decide)
        (by decide) ha_mem h7_mem h13_mem h2801_mem
  · exfalso
    have hσ13 : sigma 1 (13 ^ N.factorization 13) = 3 * 61 := by
      rw [he13, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
      norm_num [sum_range_succ]
    have h61_mem : 61 ∈ N.primeFactors :=
      prime_mem_of_dvd_sigma_fifthPowerFree ho hh hfpf h13_mem (by norm_num) (by decide)
        (by rw [hσ13]; exact dvd_mul_left 61 3)
    rcases factorization_cases_fpf ho hfpf h61_mem with he61 | he61 | he61 | he61
    · have hσ61 : sigma 1 (61 ^ N.factorization 61) = 2 * 31 := by
        rw [he61, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 61)]
        norm_num [sum_range_succ]
      have h31_mem : 31 ∈ N.primeFactors :=
        prime_mem_of_dvd_sigma_fifthPowerFree ho hh hfpf h61_mem (by norm_num) (by decide)
          (by rw [hσ61]; exact dvd_mul_left 31 2)
      exact card_four_subset_lt_hb hcard3 ha_ne_13 ha_ne_31 ha_ne_61 (by decide) (by decide)
        (by decide) ha_mem h13_mem h31_mem h61_mem
    · have hσ61 : sigma 1 (61 ^ N.factorization 61) = 3 * 13 * 97 := by
        rw [he61, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 61)]
        norm_num [sum_range_succ]
      have h97_mem : 97 ∈ N.primeFactors :=
        prime_mem_of_dvd_sigma_fifthPowerFree ho hh hfpf h61_mem (by norm_num) (by decide)
          (by rw [hσ61]; exact dvd_mul_left 97 (3 * 13))
      exact card_four_subset_lt_hb hcard3 ha_ne_13 ha_ne_61 ha_ne_97 (by decide) (by decide)
        (by decide) ha_mem h13_mem h61_mem h97_mem
    · have hσ61 : sigma 1 (61 ^ N.factorization 61) = 4 * 1861 * 31 := by
        rw [he61, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 61)]
        norm_num [sum_range_succ]
      have h31_mem : 31 ∈ N.primeFactors :=
        prime_mem_of_dvd_sigma_fifthPowerFree ho hh hfpf h61_mem (by norm_num) (by decide)
          (by rw [hσ61]; exact dvd_mul_left 31 (4 * 1861))
      exact card_four_subset_lt_hb hcard3 ha_ne_13 ha_ne_31 ha_ne_61 (by decide) (by decide)
        (by decide) ha_mem h13_mem h31_mem h61_mem
    · have hσ61 : sigma 1 (61 ^ N.factorization 61) = 5 * 21491 * 131 := by
        rw [he61, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 61)]
        norm_num [sum_range_succ]
      have h131_mem : 131 ∈ N.primeFactors :=
        prime_mem_of_dvd_sigma_fifthPowerFree ho hh hfpf h61_mem (by norm_num) (by decide)
          (by rw [hσ61]; exact dvd_mul_left 131 (5 * 21491))
      exact card_four_subset_lt_hb hcard3 ha_ne_13 ha_ne_61 ha_ne_131 (by decide) (by decide)
        (by decide) ha_mem h13_mem h61_mem h131_mem
  · exfalso
    have hσ13 : sigma 1 (13 ^ N.factorization 13) = 20 * 7 * 17 := by
      rw [he13, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
      norm_num [sum_range_succ]
    have h7_mem : 7 ∈ N.primeFactors :=
      prime_mem_of_dvd_sigma_fifthPowerFree ho hh hfpf h13_mem (by norm_num) (by decide)
        (by rw [hσ13]; exact dvd_mul_of_dvd_left (dvd_mul_left 7 20) 17)
    have h17_mem : 17 ∈ N.primeFactors :=
      prime_mem_of_dvd_sigma_fifthPowerFree ho hh hfpf h13_mem (by norm_num) (by decide)
        (by rw [hσ13]; exact dvd_mul_left 17 (20 * 7))
    exact card_four_subset_lt_hb hcard3 ha_ne_7 ha_ne_13 ha_ne_17 (by decide) (by decide)
      (by decide) ha_mem h7_mem h13_mem h17_mem
  · have hσ13 : sigma 1 (13 ^ N.factorization 13) = 30941 := by
      rw [he13, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
      norm_num [sum_range_succ]
    have h30941_mem : 30941 ∈ N.primeFactors :=
      prime_mem_of_dvd_sigma_fifthPowerFree ho hh hfpf h13_mem (by norm_num) (by decide)
        (by rw [hσ13])
    have he30941_ge2 : 2 ≤ N.factorization 30941 := by
      have hpos : 0 < N.factorization 30941 :=
        (by norm_num : Nat.Prime 30941).factorization_pos_of_dvd ho.pos.ne'
          (Nat.dvd_of_mem_primeFactors h30941_mem)
      by_contra! hlt
      have he1 : N.factorization 30941 = 1 := by omega
      have hσ30941 : sigma 1 (30941 ^ N.factorization 30941) = 162 * 191 := by
        rw [he1, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 30941)]
        norm_num [sum_range_succ]
      have h191_mem : 191 ∈ N.primeFactors :=
        prime_mem_of_dvd_sigma_fifthPowerFree ho hh hfpf h30941_mem (by norm_num) (by decide)
          (by rw [hσ30941]; exact dvd_mul_left 191 162)
      exact card_four_subset_lt_hb hcard3 ha_ne_13 ha_ne_191 ha_ne_30941 (by decide) (by decide)
        (by decide) ha_mem h13_mem h191_mem h30941_mem
    exact ⟨he13, h30941_mem, he30941_ge2⟩

/-- No fifth-power-free odd Ore harmonic number with at most three distinct prime
factors is divisible by `3`. -/
theorem odd_oreHarmonic_fifthPowerFree_rank_three_three_not_dvd {N : ℕ}
    (ho : Odd N) (hh : OreHarmonic N) (hfpf : ∀ p, N.factorization p ≤ 4)
    (hcard : N.primeFactors.card ≤ 3) : ¬ 3 ∣ N := by
  intro h3_N
  have h3_le : 3 ≤ N.primeFactors.card := odd_oreHarmonic_three_le_primeFactors ho hh
  have hcard3 : N.primeFactors.card = 3 := by omega
  have h3_mem : 3 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨by decide, h3_N, ho.pos.ne'⟩
  rcases factorization_even_of_mod_four_eq_three_fpf ho hh hfpf h3_mem (by decide) with he3 | he3
  · have hσ3 : sigma 1 (3 ^ N.factorization 3) = 13 := by
      rw [he3, sigma_one_apply_prime_pow (by decide : Nat.Prime 3)]
      norm_num [sum_range_succ]
    have h13_mem : 13 ∈ N.primeFactors :=
      prime_mem_of_dvd_sigma_fifthPowerFree ho hh hfpf h3_mem (by norm_num) (by decide)
        (by rw [hσ3])
    obtain ⟨he13, h30941_mem, he30941_ge2⟩ :=
      thirteen_chain_fpf ho hh hfpf hcard3 h3_mem (Or.inl rfl) h13_mem
    obtain ⟨hset, hN_val, hσ_val⟩ := N_sigma_eq_three ho hcard3 (by decide) (by decide) (by decide)
      h3_mem h13_mem h30941_mem
    set e := N.factorization 30941
    have he_le4 : e ≤ 4 := hfpf 30941
    have hτ_val : N.divisors.card = 15 * (e + 1) := by
      rw [Nat.card_divisors ho.pos.ne', hset,
        Finset.prod_insert (by decide), Finset.prod_pair (by decide), he3, he13]
      ring
    have hσ13_val : sigma 1 (13 ^ N.factorization 13) = 30941 := by
      rw [he13, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
      norm_num [sum_range_succ]
    have hdvd : sigma 1 (30941 ^ e) ∣ (3 ^ 2 * 13 ^ 3 * 15 * (e + 1)) * 30941 ^ (e - 1) := by
      have h1 : 13 * 30941 * sigma 1 (30941 ^ e) ∣
          3 ^ 2 * 13 ^ 4 * 30941 ^ e * (15 * (e + 1)) := by
        have hh2 := hh.2
        rw [hσ_val, hσ3, hσ13_val, hτ_val] at hh2
        nth_rw 1 [hN_val] at hh2
        rw [he3, he13] at hh2
        exact hh2
      have hpow : 30941 ^ e = 30941 * 30941 ^ (e - 1) := by
        have : e = 1 + (e - 1) := by omega
        conv_lhs => rw [this, pow_add, pow_one]
      have h2 : (13 * 30941) * sigma 1 (30941 ^ e) ∣
          (13 * 30941) * ((3 ^ 2 * 13 ^ 3 * 15 * (e + 1)) * 30941 ^ (e - 1)) := by
        calc (13 * 30941) * sigma 1 (30941 ^ e)
            = 13 * 30941 * sigma 1 (30941 ^ e) := by ring
          _ ∣ 3 ^ 2 * 13 ^ 4 * 30941 ^ e * (15 * (e + 1)) := h1
          _ = (13 * 30941) * ((3 ^ 2 * 13 ^ 3 * 15 * (e + 1)) * 30941 ^ (e - 1)) := by
              rw [hpow]; ring
      exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 13 * 30941) h2
    have hdvd2 : sigma 1 (30941 ^ e) ∣ 3 ^ 2 * 13 ^ 3 * 15 * (e + 1) :=
      (sigma_prime_pow_coprime_pow (by norm_num : Nat.Prime 30941) e (e - 1)).dvd_of_dvd_mul_right
        hdvd
    have hle := Nat.le_of_dvd (by positivity) hdvd2
    have hgt := sigma_prime_pow_ge_sq (by norm_num : Nat.Prime 30941) he30941_ge2
    have hbound : 3 ^ 2 * 13 ^ 3 * 15 * (e + 1) ≤ 3 ^ 2 * 13 ^ 3 * 15 * 5 := by
      exact Nat.mul_le_mul_left _ (by omega)
    norm_num at hgt hbound
    omega
  · have hσ3 : sigma 1 (3 ^ N.factorization 3) = 11 ^ 2 := by
      rw [he3, sigma_one_apply_prime_pow (by decide : Nat.Prime 3)]
      norm_num [sum_range_succ]
    have h11_mem : 11 ∈ N.primeFactors :=
      prime_mem_of_dvd_sigma_fifthPowerFree ho hh hfpf h3_mem (by norm_num) (by decide)
        (by rw [hσ3]; exact dvd_pow_self 11 (by decide))
    rcases factorization_even_of_mod_four_eq_three_fpf ho hh hfpf h11_mem (by decide) with he11 | he11
    · have hσ11 : sigma 1 (11 ^ N.factorization 11) = 7 * 19 := by
        rw [he11, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
        norm_num [sum_range_succ]
      have h7_mem : 7 ∈ N.primeFactors :=
        prime_mem_of_dvd_sigma_fifthPowerFree ho hh hfpf h11_mem (by norm_num) (by decide)
          (by rw [hσ11]; exact dvd_mul_right 7 19)
      have h19_mem : 19 ∈ N.primeFactors :=
        prime_mem_of_dvd_sigma_fifthPowerFree ho hh hfpf h11_mem (by norm_num) (by decide)
          (by rw [hσ11]; exact dvd_mul_left 19 7)
      exact card_four_subset_lt_hb hcard3 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) h3_mem h7_mem h11_mem h19_mem
    · have hσ11 : sigma 1 (11 ^ N.factorization 11) = 5 * 3221 := by
        rw [he11, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
        norm_num [sum_range_succ]
      have h3221_mem : 3221 ∈ N.primeFactors :=
        prime_mem_of_dvd_sigma_fifthPowerFree ho hh hfpf h11_mem (by norm_num) (by decide)
          (by rw [hσ11]; exact dvd_mul_left 3221 5)
      have he3221_ge2 : 2 ≤ N.factorization 3221 := by
        have hpos : 0 < N.factorization 3221 :=
          (by norm_num : Nat.Prime 3221).factorization_pos_of_dvd ho.pos.ne'
            (Nat.dvd_of_mem_primeFactors h3221_mem)
        by_contra! hlt
        have he1 : N.factorization 3221 = 1 := by omega
        have hσ3221 : sigma 1 (3221 ^ N.factorization 3221) = 18 * 179 := by
          rw [he1, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3221)]
          norm_num [sum_range_succ]
        have h179_mem : 179 ∈ N.primeFactors :=
          prime_mem_of_dvd_sigma_fifthPowerFree ho hh hfpf h3221_mem (by norm_num) (by decide)
            (by rw [hσ3221]; exact dvd_mul_left 179 18)
        exact card_four_subset_lt_hb hcard3 (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) h3_mem h11_mem h179_mem h3221_mem
      obtain ⟨hset, hN_val, hσ_val⟩ := N_sigma_eq_three ho hcard3 (by decide) (by decide)
        (by decide) h3_mem h11_mem h3221_mem
      set e := N.factorization 3221
      have he_le4 : e ≤ 4 := hfpf 3221
      have hτ_val : N.divisors.card = 25 * (e + 1) := by
        rw [Nat.card_divisors ho.pos.ne', hset,
          Finset.prod_insert (by decide), Finset.prod_pair (by decide), he3, he11]
        ring
      have hdvd : sigma 1 (3221 ^ e) ∣ (3 ^ 4 * 11 ^ 2 * 5 * (e + 1)) * 3221 ^ (e - 1) := by
        have h1 : 11 ^ 2 * (5 * 3221) * sigma 1 (3221 ^ e) ∣
            3 ^ 4 * 11 ^ 4 * 3221 ^ e * (25 * (e + 1)) := by
          have hh2 := hh.2
          rw [hσ_val, hσ3, hσ11, hτ_val] at hh2
          nth_rw 1 [hN_val] at hh2
          rw [he3, he11] at hh2
          exact hh2
        have hpow : 3221 ^ e = 3221 * 3221 ^ (e - 1) := by
          have : e = 1 + (e - 1) := by omega
          conv_lhs => rw [this, pow_add, pow_one]
        have h2 : (11 ^ 2 * 5 * 3221) * sigma 1 (3221 ^ e) ∣
            (11 ^ 2 * 5 * 3221) * ((3 ^ 4 * 11 ^ 2 * 5 * (e + 1)) * 3221 ^ (e - 1)) := by
          calc (11 ^ 2 * 5 * 3221) * sigma 1 (3221 ^ e)
              = 11 ^ 2 * (5 * 3221) * sigma 1 (3221 ^ e) := by ring
            _ ∣ 3 ^ 4 * 11 ^ 4 * 3221 ^ e * (25 * (e + 1)) := h1
            _ = (11 ^ 2 * 5 * 3221) * ((3 ^ 4 * 11 ^ 2 * 5 * (e + 1)) * 3221 ^ (e - 1)) := by
                rw [hpow]; ring
        exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 11 ^ 2 * 5 * 3221) h2
      have hdvd2 : sigma 1 (3221 ^ e) ∣ 3 ^ 4 * 11 ^ 2 * 5 * (e + 1) :=
        (sigma_prime_pow_coprime_pow (by norm_num : Nat.Prime 3221) e (e - 1)).dvd_of_dvd_mul_right
          hdvd
      have hle := Nat.le_of_dvd (by positivity) hdvd2
      have hgt := sigma_prime_pow_ge_sq (by norm_num : Nat.Prime 3221) he3221_ge2
      have hbound : 3 ^ 4 * 11 ^ 2 * 5 * (e + 1) ≤ 3 ^ 4 * 11 ^ 2 * 5 * 5 :=
        Nat.mul_le_mul_left _ (by omega)
      norm_num at hgt hbound
      omega

private lemma five_factorization_eq_one_of_rank_three_fpf {N : ℕ}
    (ho : Odd N) (hh : OreHarmonic N) (hfpf : ∀ p, N.factorization p ≤ 4)
    (hcard3 : N.primeFactors.card = 3) (h5_mem : 5 ∈ N.primeFactors) :
    N.factorization 5 = 1 := by
  rcases factorization_cases_fpf ho hfpf h5_mem with he5 | he5 | he5 | he5
  · exact he5
  · exfalso
    have hσ5 : sigma 1 (5 ^ N.factorization 5) = 31 := by
      rw [he5, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
      norm_num [sum_range_succ]
    have h31_mem : 31 ∈ N.primeFactors :=
      prime_mem_of_dvd_sigma_fifthPowerFree ho hh hfpf h5_mem (by norm_num) (by decide)
        (by rw [hσ5])
    rcases factorization_even_of_mod_four_eq_three_fpf ho hh hfpf h31_mem (by decide) with he31 | he31
    · have hσ31 : sigma 1 (31 ^ N.factorization 31) = 3 * 331 := by
        rw [he31, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 31)]
        norm_num [sum_range_succ]
      have h331_mem : 331 ∈ N.primeFactors :=
        prime_mem_of_dvd_sigma_fifthPowerFree ho hh hfpf h31_mem (by norm_num) (by decide)
          (by rw [hσ31]; exact dvd_mul_left 331 3)
      have he331_ge2 : 2 ≤ N.factorization 331 := by
        rcases factorization_even_of_mod_four_eq_three_fpf ho hh hfpf h331_mem (by decide) with h2 | h4 <;>
          omega
      obtain ⟨hset, hN_val, hσ_val⟩ := N_sigma_eq_three ho hcard3 (by decide) (by decide)
        (by decide) h5_mem h31_mem h331_mem
      set e := N.factorization 331
      have he_le4 : e ≤ 4 := hfpf 331
      have hτ_val : N.divisors.card = 9 * (e + 1) := by
        rw [Nat.card_divisors ho.pos.ne', hset,
          Finset.prod_insert (by decide), Finset.prod_pair (by decide), he5, he31]
        ring
      have hdvd : sigma 1 (331 ^ e) ∣ (5 ^ 2 * 31 * 3 * (e + 1)) * 331 ^ (e - 1) := by
        have h1 : 31 * (3 * 331) * sigma 1 (331 ^ e) ∣
            5 ^ 2 * 31 ^ 2 * 331 ^ e * (9 * (e + 1)) := by
          have hh2 := hh.2
          rw [hσ_val, hσ5, hσ31, hτ_val] at hh2
          nth_rw 1 [hN_val] at hh2
          rw [he5, he31] at hh2
          exact hh2
        have hpow : 331 ^ e = 331 * 331 ^ (e - 1) := by
          have : e = 1 + (e - 1) := by omega
          conv_lhs => rw [this, pow_add, pow_one]
        have h2 : (3 * 31 * 331) * sigma 1 (331 ^ e) ∣
            (3 * 31 * 331) * ((5 ^ 2 * 31 * 3 * (e + 1)) * 331 ^ (e - 1)) := by
          calc (3 * 31 * 331) * sigma 1 (331 ^ e)
              = 31 * (3 * 331) * sigma 1 (331 ^ e) := by ring
            _ ∣ 5 ^ 2 * 31 ^ 2 * 331 ^ e * (9 * (e + 1)) := h1
            _ = (3 * 31 * 331) * ((5 ^ 2 * 31 * 3 * (e + 1)) * 331 ^ (e - 1)) := by
                rw [hpow]; ring
        exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 3 * 31 * 331) h2
      have hdvd2 : sigma 1 (331 ^ e) ∣ 5 ^ 2 * 31 * 3 * (e + 1) :=
        (sigma_prime_pow_coprime_pow (by norm_num : Nat.Prime 331) e (e - 1)).dvd_of_dvd_mul_right
          hdvd
      have hle := Nat.le_of_dvd (by positivity) hdvd2
      have hgt := sigma_prime_pow_ge_sq (by norm_num : Nat.Prime 331) he331_ge2
      have hbound : 5 ^ 2 * 31 * 3 * (e + 1) ≤ 5 ^ 2 * 31 * 3 * 5 :=
        Nat.mul_le_mul_left _ (by omega)
      norm_num at hgt hbound
      omega
    · have hσ31 : sigma 1 (31 ^ N.factorization 31) = 5 * 11 * 17351 := by
        rw [he31, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 31)]
        norm_num [sum_range_succ]
      have h11_mem : 11 ∈ N.primeFactors :=
        prime_mem_of_dvd_sigma_fifthPowerFree ho hh hfpf h31_mem (by norm_num) (by decide)
          (by rw [hσ31]; exact dvd_mul_of_dvd_left (dvd_mul_left 11 5) 17351)
      have h17351_mem : 17351 ∈ N.primeFactors :=
        prime_mem_of_dvd_sigma_fifthPowerFree ho hh hfpf h31_mem (by norm_num) (by decide)
          (by rw [hσ31]; exact dvd_mul_left 17351 (5 * 11))
      exact card_four_subset_lt_hb hcard3 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) h5_mem h11_mem h31_mem h17351_mem
  · exfalso
    have hσ5 : sigma 1 (5 ^ N.factorization 5) = 12 * 13 := by
      rw [he5, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
      norm_num [sum_range_succ]
    have h13_mem : 13 ∈ N.primeFactors :=
      prime_mem_of_dvd_sigma_fifthPowerFree ho hh hfpf h5_mem (by norm_num) (by decide)
        (by rw [hσ5]; exact dvd_mul_left 13 12)
    obtain ⟨he13, h30941_mem, he30941_ge2⟩ :=
      thirteen_chain_fpf ho hh hfpf hcard3 h5_mem (Or.inr rfl) h13_mem
    obtain ⟨hset, hN_val, hσ_val⟩ := N_sigma_eq_three ho hcard3 (by decide) (by decide) (by decide)
      h5_mem h13_mem h30941_mem
    set e := N.factorization 30941
    have he_le4 : e ≤ 4 := hfpf 30941
    have hτ_val : N.divisors.card = 20 * (e + 1) := by
      rw [Nat.card_divisors ho.pos.ne', hset,
        Finset.prod_insert (by decide), Finset.prod_pair (by decide), he5, he13]
      ring
    have hσ13_val : sigma 1 (13 ^ N.factorization 13) = 30941 := by
      rw [he13, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
      norm_num [sum_range_succ]
    have hdvd : sigma 1 (30941 ^ e) ∣ (5 ^ 3 * 13 ^ 4 * 20 * (e + 1)) * 30941 ^ (e - 1) := by
      have h1 : 12 * 13 * 30941 * sigma 1 (30941 ^ e) ∣
          5 ^ 3 * 13 ^ 4 * 30941 ^ e * (20 * (e + 1)) := by
        have hh2 := hh.2
        rw [hσ_val, hσ5, hσ13_val, hτ_val] at hh2
        nth_rw 1 [hN_val] at hh2
        rw [he5, he13] at hh2
        exact hh2
      have hpow : 30941 ^ e = 30941 * 30941 ^ (e - 1) := by
        have : e = 1 + (e - 1) := by omega
        conv_lhs => rw [this, pow_add, pow_one]
      have h2 : 30941 * sigma 1 (30941 ^ e) ∣
          30941 * ((5 ^ 3 * 13 ^ 4 * 20 * (e + 1)) * 30941 ^ (e - 1)) := by
        have hdiv : 30941 * sigma 1 (30941 ^ e) ∣ 12 * 13 * 30941 * sigma 1 (30941 ^ e) :=
          ⟨12 * 13, by ring⟩
        calc 30941 * sigma 1 (30941 ^ e)
            ∣ 12 * 13 * 30941 * sigma 1 (30941 ^ e) := hdiv
          _ ∣ 5 ^ 3 * 13 ^ 4 * 30941 ^ e * (20 * (e + 1)) := h1
          _ = 30941 * ((5 ^ 3 * 13 ^ 4 * 20 * (e + 1)) * 30941 ^ (e - 1)) := by
              rw [hpow]; ring
      exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 30941) h2
    have hdvd2 : sigma 1 (30941 ^ e) ∣ 5 ^ 3 * 13 ^ 4 * 20 * (e + 1) :=
      (sigma_prime_pow_coprime_pow (by norm_num : Nat.Prime 30941) e (e - 1)).dvd_of_dvd_mul_right
        hdvd
    have hle := Nat.le_of_dvd (by positivity) hdvd2
    have hgt := sigma_prime_pow_ge_sq (by norm_num : Nat.Prime 30941) he30941_ge2
    have hbound : 5 ^ 3 * 13 ^ 4 * 20 * (e + 1) ≤ 5 ^ 3 * 13 ^ 4 * 20 * 5 :=
      Nat.mul_le_mul_left _ (by omega)
    norm_num at hgt hbound
    omega
  · exfalso
    have hσ5 : sigma 1 (5 ^ N.factorization 5) = 11 * 71 := by
      rw [he5, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
      norm_num [sum_range_succ]
    have h11_mem : 11 ∈ N.primeFactors :=
      prime_mem_of_dvd_sigma_fifthPowerFree ho hh hfpf h5_mem (by norm_num) (by decide)
        (by rw [hσ5]; exact dvd_mul_right 11 71)
    have h71_mem : 71 ∈ N.primeFactors :=
      prime_mem_of_dvd_sigma_fifthPowerFree ho hh hfpf h5_mem (by norm_num) (by decide)
        (by rw [hσ5]; exact dvd_mul_left 71 11)
    rcases factorization_even_of_mod_four_eq_three_fpf ho hh hfpf h11_mem (by decide) with he11 | he11
    · have hσ11 : sigma 1 (11 ^ N.factorization 11) = 7 * 19 := by
        rw [he11, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
        norm_num [sum_range_succ]
      have h7_mem : 7 ∈ N.primeFactors :=
        prime_mem_of_dvd_sigma_fifthPowerFree ho hh hfpf h11_mem (by norm_num) (by decide)
          (by rw [hσ11]; exact dvd_mul_right 7 19)
      exact card_four_subset_lt_hb hcard3 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) h5_mem h7_mem h11_mem h71_mem
    · have hσ11 : sigma 1 (11 ^ N.factorization 11) = 5 * 3221 := by
        rw [he11, sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
        norm_num [sum_range_succ]
      have h3221_mem : 3221 ∈ N.primeFactors :=
        prime_mem_of_dvd_sigma_fifthPowerFree ho hh hfpf h11_mem (by norm_num) (by decide)
          (by rw [hσ11]; exact dvd_mul_left 3221 5)
      exact card_four_subset_lt_hb hcard3 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) h5_mem h11_mem h71_mem h3221_mem

/-!
## 4. Kernel-Verified Rank-3 Fifth-Power-Free Checker
-/

private def geomSum (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | e + 1 => geomSum p e + p ^ (e + 1)

private lemma sigma_prime_pow_eq_geomSum {p : ℕ} (hp : p.Prime) (e : ℕ) :
    sigma 1 (p ^ e) = geomSum p e := by
  rw [sigma_one_apply_prime_pow hp]
  induction e with
  | zero => simp [geomSum]
  | succ e ih => rw [sum_range_succ, ih]; rfl

private lemma geomSum_gt_pow {p e : ℕ} (_hp : 1 < p) (he : 1 ≤ e) : p ^ e < geomSum p e := by
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0) with ⟨k, rfl⟩
  have hpos : 0 < geomSum p k := by
    induction k with
    | zero => simp [geomSum]
    | succ k ih =>
      change 0 < geomSum p k + p ^ (k + 1)
      omega
  change p ^ (k + 1) < geomSum p k + p ^ (k + 1)
  omega

private lemma geomSum_sub_one_eq_mul {p e : ℕ} (he : 1 ≤ e) :
    geomSum p e - 1 = p * (geomSum p e - p ^ e) := by
  induction e with
  | zero => omega
  | succ e ih =>
    rcases e with _ | e
    · simp [geomSum]
    · have ih' := ih (by omega)
      have h1 : 1 ≤ geomSum p (e + 1) := by
        clear ih ih'
        induction (e + 1) with
        | zero => simp [geomSum]
        | succ k ihk => change 1 ≤ geomSum p k + p ^ (k + 1); omega
      have hsub : geomSum p (e + 2) - p ^ (e + 2) = geomSum p (e + 1) := by
        change geomSum p (e + 1) + p ^ (e + 2) - p ^ (e + 2) = geomSum p (e + 1)
        omega
      rw [hsub]
      change geomSum p (e + 1) + p ^ (e + 2) - 1 = p * geomSum p (e + 1)
      have hle : p ^ (e + 1) ≤ geomSum p (e + 1) := by
        change p ^ (e + 1) ≤ geomSum p e + p ^ (e + 1)
        omega
      have hsplit : geomSum p (e + 1) + p ^ (e + 2) - 1 =
          (geomSum p (e + 1) - 1) + p ^ (e + 2) := by omega
      rw [hsplit, ih', show p ^ (e + 2) = p * p ^ (e + 1) by rw [pow_succ'], ← mul_add,
        Nat.sub_add_cancel hle]

private def candidatePrimes : List ℕ :=
  [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103]

private lemma candidatePrimes_spec : ∀ q ∈ candidatePrimes, q.Prime ∧ 5 < q := by
  decide +kernel

private def checkThird (num1 den1 pa ea eb p1 : ℕ) : Bool :=
  if pa < 5 || pa == p1 then false
  else if pa ^ ea % 4 != 1 then false
  else if pa == 5 && ea != 1 then false
  else
    let A2 := num1 * pa ^ ea
    let B2 := den1 * geomSum pa ea
    let g2 := Nat.gcd A2 B2
    let num2 := A2 / g2
    let den2 := B2 / g2
    if num2 ≤ den2 then false
    else
      let pb := (num2 - 1) / (num2 - den2)
      pb ≥ 5 && pb != p1 && pb != pa &&
      den2 == pb ^ eb && num2 == geomSum pb eb &&
      pb ^ eb % 4 == 1 && (pb != 5 || eb == 1)

private def checkM (e1 e2 e3 M : ℕ) : Bool :=
  let tau := (e1 + 1) * (e2 + 1) * (e3 + 1)
  let g := Nat.gcd M tau
  let U := M / g
  let V := tau / g
  if U ≤ 1 || 77 * U ≤ 48 * V || U % 3 == 0 || U % 25 == 0 then false
  else
    let p1 := U.minFac
    if p1 ^ e1 % 4 != 1 || (p1 == 5 && e1 != 1) || U % p1 ^ (e1 + 1) == 0 then false
    else
      let A1 := V * p1 ^ e1
      let B1 := U * geomSum p1 e1
      let g1 := Nat.gcd A1 B1
      let num1 := A1 / g1
      let den1 := B1 / g1
      if num1 ≤ den1 then false
      else
        match candidatePrimes.find? (fun q => q != p1 && B1 % q == 0) with
        | some q => checkThird num1 den1 q e2 e3 p1 || checkThird num1 den1 q e3 e2 p1
        | none =>
          (List.range ((2 * num1) / (num1 - den1) + 1)).any
            (fun p2 => 5 ≤ p2 && p2 % 2 == 1 && checkThird num1 den1 p2 e2 e3 p1)

private def checkAllRank3 : Bool :=
  [1, 2, 3, 4].any fun e1 =>
  [1, 2, 3, 4].any fun e2 =>
  [1, 2, 3, 4].any fun e3 =>
    !(e1 % 2 == 1 && e2 % 2 == 1 && e3 % 2 == 1) &&
    let tau := (e1 + 1) * (e2 + 1) * (e3 + 1)
    (List.range tau).any fun M =>
      3 ≤ M && M % 2 == 1 && checkM e1 e2 e3 M

private lemma checkAllRank3_eq_false : checkAllRank3 = false := by
  decide +kernel

private lemma checkThird_sound {num1 den1 pa ea eb p1 pb : ℕ}
    (hpa_pr : pa.Prime) (hpb_pr : pb.Prime)
    (hpa5 : 5 ≤ pa) (hpb5 : 5 ≤ pb)
    (hpa1 : pa ≠ p1) (hpb1 : pb ≠ p1) (hpab : pb ≠ pa)
    (hea : 1 ≤ ea) (heb : 1 ≤ eb)
    (hpa_mod : pa ^ ea % 4 = 1) (hpb_mod : pb ^ eb % 4 = 1)
    (hpa5_eq : pa = 5 → ea = 1) (hpb5_eq : pb = 5 → eb = 1)
    (hnum1_pos : 0 < num1) (hden1_pos : 0 < den1)
    (heq : den1 * (geomSum pa ea * geomSum pb eb) = num1 * (pa ^ ea * pb ^ eb)) :
    checkThird num1 den1 pa ea eb p1 = true := by
  set A2 := num1 * pa ^ ea
  set B2 := den1 * geomSum pa ea
  set g2 := Nat.gcd A2 B2
  have hA2_pos : 0 < A2 := mul_pos hnum1_pos (pow_pos hpa_pr.pos ea)
  have hB2_pos : 0 < B2 :=
    mul_pos hden1_pos (lt_trans (pow_pos hpa_pr.pos ea) (geomSum_gt_pow hpa_pr.one_lt hea))
  have hg2_pos : 0 < g2 := Nat.gcd_pos_of_pos_left B2 hA2_pos
  set num2 := A2 / g2
  set den2 := B2 / g2
  have hcop2 : Nat.Coprime num2 den2 := Nat.coprime_div_gcd_div_gcd hg2_pos
  have hg2A : g2 ∣ A2 := Nat.gcd_dvd_left A2 B2
  have hg2B : g2 ∣ B2 := Nat.gcd_dvd_right A2 B2
  have heq2 : den2 * geomSum pb eb = num2 * pb ^ eb := by
    have hmul : g2 * (den2 * geomSum pb eb) = g2 * (num2 * pb ^ eb) := by
      calc g2 * (den2 * geomSum pb eb)
          = (g2 * den2) * geomSum pb eb := by ring
        _ = B2 * geomSum pb eb := by rw [Nat.mul_div_cancel' hg2B]
        _ = den1 * (geomSum pa ea * geomSum pb eb) := by ring
        _ = num1 * (pa ^ ea * pb ^ eb) := heq
        _ = A2 * pb ^ eb := by ring
        _ = (g2 * num2) * pb ^ eb := by rw [Nat.mul_div_cancel' hg2A]
        _ = g2 * (num2 * pb ^ eb) := by ring
    exact Nat.eq_of_mul_eq_mul_left hg2_pos hmul
  have hcop_pb : Nat.Coprime (geomSum pb eb) (pb ^ eb) := by
    rw [← sigma_prime_pow_eq_geomSum hpb_pr eb]
    exact sigma_prime_pow_coprime_pow hpb_pr eb eb
  have hnum2_dvd : num2 ∣ geomSum pb eb :=
    hcop2.dvd_of_dvd_mul_left ⟨pb ^ eb, by linarith [heq2]⟩
  have hσ_dvd : geomSum pb eb ∣ num2 :=
    hcop_pb.dvd_of_dvd_mul_right ⟨den2, by linarith [heq2]⟩
  have hnum2_eq : num2 = geomSum pb eb := Nat.dvd_antisymm hnum2_dvd hσ_dvd
  have hden2_eq : den2 = pb ^ eb := by
    have hσ_pos : 0 < geomSum pb eb :=
      lt_trans (pow_pos hpb_pr.pos eb) (geomSum_gt_pow hpb_pr.one_lt heb)
    have hmul : geomSum pb eb * den2 = geomSum pb eb * pb ^ eb := by
      calc geomSum pb eb * den2 = den2 * geomSum pb eb := mul_comm _ _
        _ = num2 * pb ^ eb := heq2
        _ = geomSum pb eb * pb ^ eb := by rw [hnum2_eq]
    exact Nat.eq_of_mul_eq_mul_left hσ_pos hmul
  have hlt2 : den2 < num2 := by
    rw [hden2_eq, hnum2_eq]
    exact geomSum_gt_pow hpb_pr.one_lt heb
  have hpb_div : (num2 - 1) / (num2 - den2) = pb := by
    rw [hnum2_eq, hden2_eq, geomSum_sub_one_eq_mul heb]
    have hdiff_pos : 0 < geomSum pb eb - pb ^ eb := by
      have := geomSum_gt_pow hpb_pr.one_lt heb
      omega
    exact Nat.mul_div_left pb hdiff_pos
  have hpa_not_5 : (pa == 5 && ea != 1) = false := by
    by_cases h : pa = 5
    · simp [h, hpa5_eq h]
    · simp [h]
  have hpb_not_5 : (pb != 5 || eb == 1) = true := by
    by_cases h : pb = 5
    · simp [h, hpb5_eq h]
    · simp [h]
  unfold checkThird
  dsimp only
  rw [show (pa < 5 || pa == p1) = false by simp [show ¬ pa < 5 by omega, hpa1]]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show (pa ^ ea % 4 != 1) = false by simp [hpa_mod]]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hpa_not_5]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (if num2 ≤ den2 then false else _) = true
  split_ifs with hle
  · omega
  · rw [hpb_div]
    have hpb5_b : decide (5 ≤ pb) = true := decide_eq_true hpb5
    have hpb1_b : (pb != p1) = true := bne_iff_ne.mpr hpb1
    have hpab_b : (pb != pa) = true := bne_iff_ne.mpr hpab
    have hden_b : (den2 == pb ^ eb) = true := beq_iff_eq.mpr hden2_eq
    have hnum_b : (num2 == geomSum pb eb) = true := beq_iff_eq.mpr hnum2_eq
    have hmod_b : (pb ^ eb % 4 == 1) = true := beq_iff_eq.mpr hpb_mod
    rw [hpb5_b, hpb1_b, hpab_b, hden_b, hnum_b, hmod_b, hpb_not_5]
    rfl

/-- No fifth-power-free odd Ore harmonic number has three or fewer distinct prime
factors. -/
theorem odd_oreHarmonic_four_le_primeFactors_of_fifthPowerFree {N : ℕ}
    (ho : Odd N) (hh : OreHarmonic N) (hfpf : ∀ p, N.factorization p ≤ 4) :
    4 ≤ N.primeFactors.card := by
  have h3_le : 3 ≤ N.primeFactors.card := odd_oreHarmonic_three_le_primeFactors ho hh
  by_contra! hlt
  have hcard3 : N.primeFactors.card = 3 := by omega
  have h3_not : ¬ 3 ∣ N :=
    odd_oreHarmonic_fifthPowerFree_rank_three_three_not_dvd ho hh hfpf (by omega)
  have h5_eq1 : 5 ∈ N.primeFactors → N.factorization 5 = 1 :=
    five_factorization_eq_one_of_rank_three_fpf ho hh hfpf hcard3
  obtain ⟨hM_eq, hM_odd, hM_3⟩ := odd_oreHarmonic_odd_harmonic_mean ho hh
  set M := N * N.divisors.card / sigma 1 N
  set τ := N.divisors.card
  change M * sigma 1 N = N * τ at hM_eq
  change Odd M at hM_odd
  change 3 ≤ M at hM_3
  have hM_ndvd : ¬ M ∣ τ :=
    odd_oreHarmonic_card_three_not_dvd_divisor_count ho hh (by omega)
  have hσ_gt : N < sigma 1 N := lt_sigma_one_of_one_lt_hb hh.1
  have hM_lt_τ : M < τ := by
    by_contra! hle
    have hmul : N * τ < M * sigma 1 N := by
      calc N * τ ≤ N * M := Nat.mul_le_mul_left N hle
        _ < sigma 1 N * M := Nat.mul_lt_mul_of_pos_right hσ_gt (by omega)
        _ = M * sigma 1 N := mul_comm _ _
    omega
  set g := Nat.gcd M τ
  set U := M / g
  set V := τ / g
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left τ (by omega)
  have hgM : g ∣ M := Nat.gcd_dvd_left M τ
  have hgτ : g ∣ τ := Nat.gcd_dvd_right M τ
  have hcopUV : Nat.Coprime U V := Nat.coprime_div_gcd_div_gcd hg_pos
  have hU_gt1 : 1 < U := by
    have hUg : U * g = M := Nat.div_mul_cancel hgM
    by_contra! hUle
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hUle with h0 | h1
    · rw [h0, zero_mul] at hUg; omega
    · rw [h1, one_mul] at hUg
      exact hM_ndvd (hUg ▸ hgτ)
  have hUV_eq : U * sigma 1 N = V * N := by
    have hmul : g * (U * sigma 1 N) = g * (V * N) := by
      calc g * (U * sigma 1 N) = (g * U) * sigma 1 N := by ring
        _ = M * sigma 1 N := by rw [Nat.mul_div_cancel' hgM]
        _ = N * τ := hM_eq
        _ = N * (g * V) := by rw [Nat.mul_div_cancel' hgτ]
        _ = g * (V * N) := by ring
    exact Nat.eq_of_mul_eq_mul_left hg_pos hmul
  have hU_dvd_N : U ∣ N := hcopUV.dvd_of_dvd_mul_left ⟨sigma 1 N, by linarith [hUV_eq]⟩
  have hU_not_3 : ¬ 3 ∣ U := fun h => h3_not (h.trans hU_dvd_N)
  have hU_not_25 : ¬ 25 ∣ U := by
    intro h25
    have h5_U : 5 ∣ U := (by decide : 5 ∣ 25).trans h25
    have h5_N : 5 ∣ N := h5_U.trans hU_dvd_N
    have h5_mem : 5 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨by norm_num, h5_N, ho.pos.ne'⟩
    have h25_N : 5 ^ 2 ∣ N := h25.trans hU_dvd_N
    have hle2 : 2 ≤ N.factorization 5 :=
      ((by norm_num : Nat.Prime 5).pow_dvd_iff_le_factorization ho.pos.ne').mp h25_N
    have he1 := h5_eq1 h5_mem
    omega
  -- Abundancy bound 48 * V < 77 * U
  have h48V_lt_77U : 48 * V < 77 * U := by
    obtain ⟨q₁, q₂, q₃, hq12, hq23, hqPF⟩ := exists_three_sorted_of_card_eq_three_hb hcard3
    have hq₁_mem : q₁ ∈ N.primeFactors := by rw [hqPF]; simp
    have hq₂_mem : q₂ ∈ N.primeFactors := by rw [hqPF]; simp
    have hq₃_mem : q₃ ∈ N.primeFactors := by rw [hqPF]; simp
    have hq₁ : q₁.Prime := Nat.prime_of_mem_primeFactors hq₁_mem
    have hq₂ : q₂.Prime := Nat.prime_of_mem_primeFactors hq₂_mem
    have hq₃ : q₃.Prime := Nat.prime_of_mem_primeFactors hq₃_mem
    have h_ge5 : ∀ q ∈ N.primeFactors, 5 ≤ q ∧ q % 2 = 1 := fun q hq => by
      have hpr := Nat.prime_of_mem_primeFactors hq
      have hodd := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hq)
      have hmod := Nat.odd_iff.mp hodd
      have h2 := hpr.two_le
      have hne3 : q ≠ 3 := fun h => h3_not (h ▸ Nat.dvd_of_mem_primeFactors hq)
      exact ⟨by omega, hmod⟩
    have hq₁_5 : 5 ≤ q₁ := (h_ge5 q₁ hq₁_mem).1
    have hq₂_7 : 7 ≤ q₂ := by
      have := h_ge5 q₂ hq₂_mem
      omega
    have hq₃_11 : 11 ≤ q₃ := by
      have := h_ge5 q₃ hq₃_mem
      rcases (show q₃ = 9 ∨ 11 ≤ q₃ by omega) with rfl | h11
      · exfalso; norm_num at hq₃
      · exact h11
    obtain ⟨_, hN_q, hσ_q⟩ := N_sigma_eq_three ho hcard3 hq12.ne (hq12.trans hq23).ne hq23.ne
      hq₁_mem hq₂_mem hq₃_mem
    have hb1 := sigma_bound_of_le hq₁ hq₁_5 (by decide) (N.factorization q₁)
    have hb2 := sigma_bound_of_le hq₂ hq₂_7 (by decide) (N.factorization q₂)
    have hb3 := sigma_bound_of_le hq₃ hq₃_11 (by decide) (N.factorization q₃)
    have hmul :
        (4 * sigma 1 (q₁ ^ N.factorization q₁)) *
        (6 * sigma 1 (q₂ ^ N.factorization q₂)) *
        (10 * sigma 1 (q₃ ^ N.factorization q₃)) <
        (5 * q₁ ^ N.factorization q₁) *
        (7 * q₂ ^ N.factorization q₂) *
        (11 * q₃ ^ N.factorization q₃) :=
      nat_mul_lt_mul (nat_mul_lt_mul hb1 hb2) hb3
    have h240 : 240 * sigma 1 N < 385 * N := by
      calc 240 * sigma 1 N
          = (4 * sigma 1 (q₁ ^ N.factorization q₁)) *
            (6 * sigma 1 (q₂ ^ N.factorization q₂)) *
            (10 * sigma 1 (q₃ ^ N.factorization q₃)) := by rw [hσ_q]; ring
        _ < (5 * q₁ ^ N.factorization q₁) *
            (7 * q₂ ^ N.factorization q₂) *
            (11 * q₃ ^ N.factorization q₃) := hmul
        _ = 385 * (q₁ ^ N.factorization q₁ * q₂ ^ N.factorization q₂ * q₃ ^ N.factorization q₃) := by ring
        _ = 385 * N := by rw [← hN_q]
    have h48 : 48 * sigma 1 N < 77 * N := by omega
    have hVN : 48 * V * N < 77 * U * N := by
      calc 48 * V * N = 48 * (V * N) := by ring
        _ = 48 * (U * sigma 1 N) := by rw [hUV_eq]
        _ = U * (48 * sigma 1 N) := by ring
        _ < U * (77 * N) := Nat.mul_lt_mul_of_pos_left h48 (by omega)
        _ = 77 * U * N := by ring
    exact Nat.lt_of_mul_lt_mul_right hVN
  -- Split N around p₁ = U.minFac
  set p₁ := U.minFac
  have hp₁_pr : p₁.Prime := Nat.minFac_prime (by omega)
  have hp₁_dvd_U : p₁ ∣ U := Nat.minFac_dvd U
  have hp₁_mem : p₁ ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp₁_pr, hp₁_dvd_U.trans hU_dvd_N, ho.pos.ne'⟩
  have h_er_card : (N.primeFactors.erase p₁).card = 2 := by
    rw [Finset.card_erase_of_mem hp₁_mem, hcard3]
  obtain ⟨a, b, hab, h_er_eq⟩ := Finset.card_eq_two.mp h_er_card
  have h_er_sorted : ∃ p₂ p₃, p₂ < p₃ ∧ N.primeFactors.erase p₁ = {p₂, p₃} := by
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨a, b, h, h_er_eq⟩
    · exact ⟨b, a, h, by rw [h_er_eq, Finset.pair_comm]⟩
  obtain ⟨p₂, p₃, hp23, h_er⟩ := h_er_sorted
  have hp₂_mem : p₂ ∈ N.primeFactors := by
    have : p₂ ∈ N.primeFactors.erase p₁ := by rw [h_er]; simp
    exact Finset.mem_of_mem_erase this
  have hp₃_mem : p₃ ∈ N.primeFactors := by
    have : p₃ ∈ N.primeFactors.erase p₁ := by rw [h_er]; simp
    exact Finset.mem_of_mem_erase this
  have hp12_ne : p₁ ≠ p₂ := by
    have : p₂ ∈ N.primeFactors.erase p₁ := by rw [h_er]; simp
    exact (Finset.mem_erase.mp this).1.symm
  have hp13_ne : p₁ ≠ p₃ := by
    have : p₃ ∈ N.primeFactors.erase p₁ := by rw [h_er]; simp
    exact (Finset.mem_erase.mp this).1.symm
  have hp₂_pr : p₂.Prime := Nat.prime_of_mem_primeFactors hp₂_mem
  have hp₃_pr : p₃.Prime := Nat.prime_of_mem_primeFactors hp₃_mem
  have hp_ge5 : ∀ p ∈ N.primeFactors, 5 ≤ p ∧ p % 2 = 1 := fun p hp => by
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hodd := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
    have hmod := Nat.odd_iff.mp hodd
    have h2 := hpr.two_le
    have hne3 : p ≠ 3 := fun h => h3_not (h ▸ Nat.dvd_of_mem_primeFactors hp)
    exact ⟨by omega, hmod⟩
  have hp₁_5 : 5 ≤ p₁ := (hp_ge5 p₁ hp₁_mem).1
  have hp₂_5 : 5 ≤ p₂ := (hp_ge5 p₂ hp₂_mem).1
  have hp₂_odd : p₂ % 2 = 1 := (hp_ge5 p₂ hp₂_mem).2
  have hp₃_5 : 5 ≤ p₃ := (hp_ge5 p₃ hp₃_mem).1
  set e₁ := N.factorization p₁
  set e₂ := N.factorization p₂
  set e₃ := N.factorization p₃
  have he₁_1 : 1 ≤ e₁ :=
    hp₁_pr.factorization_pos_of_dvd ho.pos.ne' (Nat.dvd_of_mem_primeFactors hp₁_mem)
  have he₂_1 : 1 ≤ e₂ :=
    hp₂_pr.factorization_pos_of_dvd ho.pos.ne' (Nat.dvd_of_mem_primeFactors hp₂_mem)
  have he₃_1 : 1 ≤ e₃ :=
    hp₃_pr.factorization_pos_of_dvd ho.pos.ne' (Nat.dvd_of_mem_primeFactors hp₃_mem)
  have he₁_4 : e₁ ≤ 4 := hfpf p₁
  have he₂_4 : e₂ ≤ 4 := hfpf p₂
  have he₃_4 : e₃ ≤ 4 := hfpf p₃
  have he₁_mod : p₁ ^ e₁ % 4 = 1 := odd_harmonic_component_one_mod_four ho hh hp₁_mem
  have he₂_mod : p₂ ^ e₂ % 4 = 1 := odd_harmonic_component_one_mod_four ho hh hp₂_mem
  have he₃_mod : p₃ ^ e₃ % 4 = 1 := odd_harmonic_component_one_mod_four ho hh hp₃_mem
  have hp₁_5_eq : p₁ = 5 → e₁ = 1 := fun h => by simpa [e₁, h] using h5_eq1 (h ▸ hp₁_mem)
  have hp₂_5_eq : p₂ = 5 → e₂ = 1 := fun h => by simpa [e₂, h] using h5_eq1 (h ▸ hp₂_mem)
  have hp₃_5_eq : p₃ = 5 → e₃ = 1 := fun h => by simpa [e₃, h] using h5_eq1 (h ▸ hp₃_mem)
  have hU_ndvd_p1 : ¬ p₁ ^ (e₁ + 1) ∣ U := by
    intro hd
    have hdN : p₁ ^ (e₁ + 1) ∣ N := hd.trans hU_dvd_N
    have hle := (hp₁_pr.pow_dvd_iff_le_factorization ho.pos.ne').mp hdN
    omega
  obtain ⟨hPF, hN_p, hσ_p⟩ := N_sigma_eq_three ho hcard3 hp12_ne hp13_ne hp23.ne
    hp₁_mem hp₂_mem hp₃_mem
  have hτ_eq : τ = (e₁ + 1) * (e₂ + 1) * (e₃ + 1) := by
    rw [show τ = N.divisors.card from rfl, Nat.card_divisors ho.pos.ne', hPF,
      Finset.prod_insert (by simp [hp12_ne, hp13_ne]), Finset.prod_pair hp23.ne]
    ring
  have h_not_all_odd : ¬ (e₁ % 2 = 1 ∧ e₂ % 2 = 1 ∧ e₃ % 2 = 1) := by
    rintro ⟨ho1, ho2, ho3⟩
    have hpow2 : ∀ e, 1 ≤ e → e ≤ 4 → e % 2 = 1 → e + 1 = 2 ∨ e + 1 = 4 := fun e h1 h4 ho => by
      omega
    rcases hpow2 e₁ he₁_1 he₁_4 ho1 with h1 | h1 <;>
    rcases hpow2 e₂ he₂_1 he₂_4 ho2 with h2 | h2 <;>
    rcases hpow2 e₃ he₃_1 he₃_4 ho3 with h3 | h3
    · exact odd_oreHarmonic_divisor_count_not_pow_two ho hh 3 (by rw [← show τ = N.divisors.card from rfl, hτ_eq, h1, h2, h3]; norm_num)
    · exact odd_oreHarmonic_divisor_count_not_pow_two ho hh 4 (by rw [← show τ = N.divisors.card from rfl, hτ_eq, h1, h2, h3]; norm_num)
    · exact odd_oreHarmonic_divisor_count_not_pow_two ho hh 4 (by rw [← show τ = N.divisors.card from rfl, hτ_eq, h1, h2, h3]; norm_num)
    · exact odd_oreHarmonic_divisor_count_not_pow_two ho hh 5 (by rw [← show τ = N.divisors.card from rfl, hτ_eq, h1, h2, h3]; norm_num)
    · exact odd_oreHarmonic_divisor_count_not_pow_two ho hh 4 (by rw [← show τ = N.divisors.card from rfl, hτ_eq, h1, h2, h3]; norm_num)
    · exact odd_oreHarmonic_divisor_count_not_pow_two ho hh 5 (by rw [← show τ = N.divisors.card from rfl, hτ_eq, h1, h2, h3]; norm_num)
    · exact odd_oreHarmonic_divisor_count_not_pow_two ho hh 5 (by rw [← show τ = N.divisors.card from rfl, hτ_eq, h1, h2, h3]; norm_num)
    · exact odd_oreHarmonic_divisor_count_not_pow_two ho hh 6 (by rw [← show τ = N.divisors.card from rfl, hτ_eq, h1, h2, h3]; norm_num)
  -- Eliminate p₁ into num₁ / den₁
  set A₁ := V * p₁ ^ e₁
  set B₁ := U * geomSum p₁ e₁
  set g₁ := Nat.gcd A₁ B₁
  set num₁ := A₁ / g₁
  set den₁ := B₁ / g₁
  have hV_pos : 0 < V := by
    have hτ_pos : 0 < τ := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr ho.pos.ne'⟩
    have hVg : V * g = τ := Nat.div_mul_cancel hgτ
    by_contra! hV0
    have hV0' : V = 0 := by omega
    rw [hV0', zero_mul] at hVg
    omega
  have hA₁_pos : 0 < A₁ := mul_pos hV_pos (pow_pos hp₁_pr.pos e₁)
  have hB₁_pos : 0 < B₁ :=
    mul_pos (by omega) (lt_trans (pow_pos hp₁_pr.pos e₁) (geomSum_gt_pow hp₁_pr.one_lt he₁_1))
  have hg₁_pos : 0 < g₁ := Nat.gcd_pos_of_pos_left B₁ hA₁_pos
  have hg₁A : g₁ ∣ A₁ := Nat.gcd_dvd_left A₁ B₁
  have hg₁B : g₁ ∣ B₁ := Nat.gcd_dvd_right A₁ B₁
  have hnum₁_pos : 0 < num₁ := Nat.div_pos (Nat.le_of_dvd hA₁_pos hg₁A) hg₁_pos
  have hden₁_pos : 0 < den₁ := Nat.div_pos (Nat.le_of_dvd hB₁_pos hg₁B) hg₁_pos
  have h_red1 : den₁ * (geomSum p₂ e₂ * geomSum p₃ e₃) = num₁ * (p₂ ^ e₂ * p₃ ^ e₃) := by
    have h_raw : B₁ * (geomSum p₂ e₂ * geomSum p₃ e₃) = A₁ * (p₂ ^ e₂ * p₃ ^ e₃) := by
      calc B₁ * (geomSum p₂ e₂ * geomSum p₃ e₃)
          = U * (sigma 1 (p₁ ^ e₁) * sigma 1 (p₂ ^ e₂) * sigma 1 (p₃ ^ e₃)) := by
              rw [sigma_prime_pow_eq_geomSum hp₁_pr, sigma_prime_pow_eq_geomSum hp₂_pr,
                sigma_prime_pow_eq_geomSum hp₃_pr]
              dsimp [B₁]
              ring
        _ = U * sigma 1 N := by rw [← hσ_p]
        _ = V * N := hUV_eq
        _ = V * (p₁ ^ e₁ * p₂ ^ e₂ * p₃ ^ e₃) := by rw [hN_p]
        _ = A₁ * (p₂ ^ e₂ * p₃ ^ e₃) := by dsimp [A₁]; ring
    have hmul : g₁ * (den₁ * (geomSum p₂ e₂ * geomSum p₃ e₃)) =
        g₁ * (num₁ * (p₂ ^ e₂ * p₃ ^ e₃)) := by
      calc g₁ * (den₁ * (geomSum p₂ e₂ * geomSum p₃ e₃))
          = (g₁ * den₁) * (geomSum p₂ e₂ * geomSum p₃ e₃) := by ring
        _ = B₁ * (geomSum p₂ e₂ * geomSum p₃ e₃) := by rw [Nat.mul_div_cancel' hg₁B]
        _ = A₁ * (p₂ ^ e₂ * p₃ ^ e₃) := h_raw
        _ = (g₁ * num₁) * (p₂ ^ e₂ * p₃ ^ e₃) := by rw [Nat.mul_div_cancel' hg₁A]
        _ = g₁ * (num₁ * (p₂ ^ e₂ * p₃ ^ e₃)) := by ring
    exact Nat.eq_of_mul_eq_mul_left hg₁_pos hmul
  have hden₁_lt_num₁ : den₁ < num₁ := by
    have h2 : p₂ ^ e₂ < geomSum p₂ e₂ := geomSum_gt_pow hp₂_pr.one_lt he₂_1
    have h3 : p₃ ^ e₃ < geomSum p₃ e₃ := geomSum_gt_pow hp₃_pr.one_lt he₃_1
    have hp23_pow_pos : 0 < p₂ ^ e₂ * p₃ ^ e₃ :=
      mul_pos (pow_pos hp₂_pr.pos e₂) (pow_pos hp₃_pr.pos e₃)
    have hprod_lt : p₂ ^ e₂ * p₃ ^ e₃ < geomSum p₂ e₂ * geomSum p₃ e₃ :=
      nat_mul_lt_mul h2 h3
    have hmul : den₁ * (p₂ ^ e₂ * p₃ ^ e₃) < num₁ * (p₂ ^ e₂ * p₃ ^ e₃) := by
      calc den₁ * (p₂ ^ e₂ * p₃ ^ e₃)
          < den₁ * (geomSum p₂ e₂ * geomSum p₃ e₃) := Nat.mul_lt_mul_of_pos_left hprod_lt hden₁_pos
        _ = num₁ * (p₂ ^ e₂ * p₃ ^ e₃) := h_red1
    exact Nat.lt_of_mul_lt_mul_right hmul
  -- Show checkM e₁ e₂ e₃ M = true
  have hcheckM : checkM e₁ e₂ e₃ M = true := by
    unfold checkM
    dsimp only
    rw [← hτ_eq]
    change (if U ≤ 1 || 77 * U ≤ 48 * V || U % 3 == 0 || U % 25 == 0 then false else _) = true
    have h_cond1 : (U ≤ 1 || 77 * U ≤ 48 * V || U % 3 == 0 || U % 25 == 0) = false := by
      have hU3 : U % 3 ≠ 0 := fun h => hU_not_3 (Nat.dvd_of_mod_eq_zero h)
      have hU25 : U % 25 ≠ 0 := fun h => hU_not_25 (Nat.dvd_of_mod_eq_zero h)
      simp [show ¬ U ≤ 1 by omega, show ¬ 77 * U ≤ 48 * V by omega, hU3, hU25]
    rw [h_cond1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hp₁_not_5 : (p₁ == 5 && e₁ != 1) = false := by
      by_cases h : p₁ = 5
      · simp [h, hp₁_5_eq h]
      · simp [h]
    have hU_mod_p1 : (U % p₁ ^ (e₁ + 1) == 0) = false := by
      have hne : U % p₁ ^ (e₁ + 1) ≠ 0 := fun h => hU_ndvd_p1 (Nat.dvd_of_mod_eq_zero h)
      simp [hne]
    have h_cond2 :
        (p₁ ^ e₁ % 4 != 1 || (p₁ == 5 && e₁ != 1) || U % p₁ ^ (e₁ + 1) == 0) = false := by
      simp [he₁_mod, hp₁_not_5, hU_mod_p1]
    change (if p₁ ^ e₁ % 4 != 1 || (p₁ == 5 && e₁ != 1) || U % p₁ ^ (e₁ + 1) == 0
      then false else _) = true
    rw [h_cond2]
    simp only [Bool.false_eq_true, ↓reduceIte]
    change (if num₁ ≤ den₁ then false else _) = true
    split_ifs with hle1
    · omega
    cases hfind : candidatePrimes.find? (fun q => q != p₁ && B₁ % q == 0) with
    | some q =>
      simp only []
      have hpred : (q != p₁ && B₁ % q == 0) = true :=
        @List.find?_some _ (fun x => x != p₁ && B₁ % x == 0) _ _ hfind
      have hq_mem_list : q ∈ candidatePrimes := List.mem_of_find?_eq_some hfind
      obtain ⟨hq_pr, hq_5⟩ := candidatePrimes_spec q hq_mem_list
      have hq_ne_p1 : q ≠ p₁ := by
        simp only [Bool.and_eq_true, bne_iff_ne] at hpred
        exact hpred.1
      have hq_dvd_B1 : q ∣ B₁ := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hpred
        exact Nat.dvd_of_mod_eq_zero hpred.2
      have hq_mem_N : q ∈ N.primeFactors := by
        rcases hq_pr.dvd_mul.mp hq_dvd_B1 with hqU | hqσ
        · exact Nat.mem_primeFactors.mpr ⟨hq_pr, hqU.trans hU_dvd_N, ho.pos.ne'⟩
        · rw [← sigma_prime_pow_eq_geomSum hp₁_pr] at hqσ
          exact prime_mem_of_dvd_sigma_fifthPowerFree ho hh hfpf hp₁_mem hq_pr hq_5 hqσ
      have hq_23 : q = p₂ ∨ q = p₃ := by
        rw [hPF] at hq_mem_N
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq_mem_N
        rcases hq_mem_N with rfl | rfl | rfl
        · exact (hq_ne_p1 rfl).elim
        · exact Or.inl rfl
        · exact Or.inr rfl
      rw [Bool.or_eq_true]
      rcases hq_23 with rfl | rfl
      · left
        exact checkThird_sound hp₂_pr hp₃_pr hp₂_5 hp₃_5 hp12_ne.symm hp13_ne.symm hp23.ne'
          he₂_1 he₃_1 he₂_mod he₃_mod hp₂_5_eq hp₃_5_eq hnum₁_pos hden₁_pos h_red1
      · right
        have h_red1' : den₁ * (geomSum q e₃ * geomSum p₂ e₂) = num₁ * (q ^ e₃ * p₂ ^ e₂) := by
          calc den₁ * (geomSum q e₃ * geomSum p₂ e₂)
              = den₁ * (geomSum p₂ e₂ * geomSum q e₃) := by ring
            _ = num₁ * (p₂ ^ e₂ * q ^ e₃) := h_red1
            _ = num₁ * (q ^ e₃ * p₂ ^ e₂) := by ring
        exact checkThird_sound hp₃_pr hp₂_pr hp₃_5 hp₂_5 hp13_ne.symm hp12_ne.symm hp23.ne
          he₃_1 he₂_1 he₃_mod he₂_mod hp₃_5_eq hp₂_5_eq hnum₁_pos hden₁_pos h_red1'
    | none =>
      simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq]
      refine ⟨p₂, ?_, ⟨hp₂_5, hp₂_odd⟩, ?_⟩
      · have hb2 : (p₂ - 1) * sigma 1 (p₂ ^ e₂) < p₂ * p₂ ^ e₂ :=
          prime_pred_mul_sigma_lt hp₂_pr e₂
        have hb3 : (p₂ - 1) * sigma 1 (p₃ ^ e₃) < p₂ * p₃ ^ e₃ :=
          sigma_bound_of_le hp₃_pr hp23.le (by omega) e₃
        have hmul_prod :
            (p₂ - 1) ^ 2 * (geomSum p₂ e₂ * geomSum p₃ e₃) < p₂ ^ 2 * (p₂ ^ e₂ * p₃ ^ e₃) := by
          rw [← sigma_prime_pow_eq_geomSum hp₂_pr, ← sigma_prime_pow_eq_geomSum hp₃_pr]
          calc (p₂ - 1) ^ 2 * (sigma 1 (p₂ ^ e₂) * sigma 1 (p₃ ^ e₃))
              = ((p₂ - 1) * sigma 1 (p₂ ^ e₂)) * ((p₂ - 1) * sigma 1 (p₃ ^ e₃)) := by ring
            _ < (p₂ * p₂ ^ e₂) * (p₂ * p₃ ^ e₃) :=
                nat_mul_lt_mul hb2 hb3
            _ = p₂ ^ 2 * (p₂ ^ e₂ * p₃ ^ e₃) := by ring
        have h_sq_ineq : (p₂ - 1) ^ 2 * num₁ < p₂ ^ 2 * den₁ := by
          have hp23_pos : 0 < p₂ ^ e₂ * p₃ ^ e₃ :=
            mul_pos (pow_pos hp₂_pr.pos e₂) (pow_pos hp₃_pr.pos e₃)
          have h1 : (p₂ - 1) ^ 2 * num₁ * (p₂ ^ e₂ * p₃ ^ e₃) =
              den₁ * ((p₂ - 1) ^ 2 * (geomSum p₂ e₂ * geomSum p₃ e₃)) := by
            calc (p₂ - 1) ^ 2 * num₁ * (p₂ ^ e₂ * p₃ ^ e₃)
                = (p₂ - 1) ^ 2 * (num₁ * (p₂ ^ e₂ * p₃ ^ e₃)) := by ring
              _ = (p₂ - 1) ^ 2 * (den₁ * (geomSum p₂ e₂ * geomSum p₃ e₃)) := by rw [← h_red1]
              _ = den₁ * ((p₂ - 1) ^ 2 * (geomSum p₂ e₂ * geomSum p₃ e₃)) := by ring
          have h2 : den₁ * ((p₂ - 1) ^ 2 * (geomSum p₂ e₂ * geomSum p₃ e₃)) <
              p₂ ^ 2 * den₁ * (p₂ ^ e₂ * p₃ ^ e₃) := by
            calc den₁ * ((p₂ - 1) ^ 2 * (geomSum p₂ e₂ * geomSum p₃ e₃))
                < den₁ * (p₂ ^ 2 * (p₂ ^ e₂ * p₃ ^ e₃)) :=
                  Nat.mul_lt_mul_of_pos_left hmul_prod hden₁_pos
              _ = p₂ ^ 2 * den₁ * (p₂ ^ e₂ * p₃ ^ e₃) := by ring
          exact Nat.lt_of_mul_lt_mul_right (h1.trans_lt h2)
        have hp₂_bound : p₂ * (num₁ - den₁) < 2 * num₁ :=
          mul_sub_lt_two_mul_of_sq_lt (by omega) hden₁_lt_num₁ h_sq_ineq
        have hlt_div : p₂ ≤ 2 * num₁ / (num₁ - den₁) := by
          exact (Nat.le_div_iff_mul_le (by omega : 0 < num₁ - den₁)).mpr hp₂_bound.le
        exact Nat.lt_succ_of_le hlt_div
      · exact checkThird_sound hp₂_pr hp₃_pr hp₂_5 hp₃_5 hp12_ne.symm hp13_ne.symm hp23.ne'
          he₂_1 he₃_1 he₂_mod he₃_mod hp₂_5_eq hp₃_5_eq hnum₁_pos hden₁_pos h_red1
  -- Contradict checkAllRank3_eq_false
  have htrue : checkAllRank3 = true := by
    unfold checkAllRank3
    simp only [List.any_eq_true, List.mem_cons, List.not_mem_nil, or_false,
      Bool.and_eq_true, Bool.not_eq_true', List.mem_range, decide_eq_true_eq,
      beq_iff_eq]
    refine ⟨e₁, by omega, e₂, by omega, e₃, by omega, ?_, M, ?_, ⟨hM_3, Nat.odd_iff.mp hM_odd⟩,
      hcheckM⟩
    · simp only [Bool.and_eq_false_eq_eq_false_or_eq_false, beq_eq_false_iff_ne]
      rcases Nat.mod_two_eq_zero_or_one e₁ with h1 | h1
      · left; left; omega
      · rcases Nat.mod_two_eq_zero_or_one e₂ with h2 | h2
        · left; right; omega
        · right; intro h3; exact h_not_all_odd ⟨h1, h2, h3⟩
    · rw [← hτ_eq]; exact hM_lt_τ
  rw [checkAllRank3_eq_false] at htrue
  contradiction

/-- No fourth-power-free odd Ore harmonic number has three or fewer distinct prime
factors. -/
theorem odd_oreHarmonic_four_le_primeFactors_of_fourthPowerFree {N : ℕ}
    (ho : Odd N) (hh : OreHarmonic N) (hfpf : ∀ p, N.factorization p ≤ 3) :
    4 ≤ N.primeFactors.card :=
  odd_oreHarmonic_four_le_primeFactors_of_fifthPowerFree ho hh fun p => (hfpf p).trans (by decide)

/-- No `3`-free fifth-power-free odd Ore harmonic number has three or fewer distinct
prime factors. -/
theorem odd_oreHarmonic_four_le_primeFactors_of_three_free_fifthPowerFree {N : ℕ}
    (ho : Odd N) (hh : OreHarmonic N) (_h3 : ¬ 3 ∣ N) (hfpf : ∀ p, N.factorization p ≤ 4) :
    4 ≤ N.primeFactors.card :=
  odd_oreHarmonic_four_le_primeFactors_of_fifthPowerFree ho hh hfpf

end OddPerfect
